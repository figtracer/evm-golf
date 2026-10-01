//! Minimal tree code generation, checked against revm under Cancun gas rules.

use anyhow::{Result, ensure};
use egg::{Id, RecExpr};
use revm::{
    Context, ExecuteEvm, MainBuilder, MainContext,
    bytecode::Bytecode,
    context::TxEnv,
    database::InMemoryDB,
    primitives::{Address, Bytes, TxKind, U256, hardfork::SpecId, hex},
    state::AccountInfo,
};
use serde::Serialize;

use crate::expr::{Expr, evaluate};

// Store one word in initially empty memory, then return it: 13 gas, including
// memory expansion. Transaction intrinsic gas is accounted for separately.
const RETURN_WRAPPER: &[u8] = &[0x5f, 0x52, 0x60, 0x20, 0x5f, 0xf3];
const WRAPPER_GAS: u64 = 13;
// Well above the maximum cost of a 128-node puzzle plus intrinsic gas.
const TRANSACTION_GAS_LIMIT: u64 = 100_000;

#[derive(Debug, Serialize)]
pub struct Program {
    pub body_hex: String,
    pub runtime_hex: String,
    pub body_gas: u64,
    pub runtime_bytes: usize,
    #[serde(skip)]
    body: Vec<u8>,
    #[serde(skip)]
    runtime: Vec<u8>,
}

impl Program {
    pub fn compile(expr: &RecExpr<Expr>) -> Result<Self> {
        let mut body = Vec::new();
        let body_gas = emit(expr, Id::from(expr.as_ref().len() - 1), &mut body);
        let mut runtime = body.clone();
        runtime.extend_from_slice(RETURN_WRAPPER);
        Ok(Self {
            body_hex: hex::encode(&body),
            runtime_hex: hex::encode(&runtime),
            body_gas,
            runtime_bytes: runtime.len(),
            body,
            runtime,
        })
    }

    pub fn body(&self) -> &[u8] {
        &self.body
    }

    /// Return the output and expression-body gas measured by a real EVM.
    pub fn execute(&self, x: U256, y: U256) -> Result<(U256, u64)> {
        let contract = Address::repeat_byte(0x22);
        let caller = Address::repeat_byte(0x11);
        let bytecode = Bytecode::new_legacy(Bytes::copy_from_slice(&self.runtime));
        let mut db = InMemoryDB::default();
        db.insert_account_info(
            contract,
            AccountInfo {
                code_hash: bytecode.hash_slow(),
                code: Some(bytecode),
                ..Default::default()
            },
        );
        let mut data = Vec::with_capacity(64);
        data.extend_from_slice(&x.to_be_bytes::<32>());
        data.extend_from_slice(&y.to_be_bytes::<32>());
        let intrinsic = 21_000
            + data
                .iter()
                .map(|byte| if *byte == 0 { 4 } else { 16 })
                .sum::<u64>();
        let mut evm = Context::mainnet()
            .modify_cfg_chained(|cfg| cfg.set_spec_and_mainnet_gas_params(SpecId::CANCUN))
            .with_db(db)
            .build_mainnet();
        let result = evm.transact_one(
            TxEnv::builder()
                .caller(caller)
                .kind(TxKind::Call(contract))
                .gas_limit(TRANSACTION_GAS_LIMIT)
                .data(Bytes::from(data))
                .build()?,
        )?;
        ensure!(result.is_success(), "EVM execution failed: {result:?}");
        let output = result.output().unwrap();
        ensure!(
            output.len() == 32,
            "expected one output word, got {} bytes",
            output.len()
        );
        Ok((
            U256::from_be_slice(output),
            result.tx_gas_used() - intrinsic - WRAPPER_GAS,
        ))
    }
}

fn emit(expr: &RecExpr<Expr>, id: Id, bytes: &mut Vec<u8>) -> u64 {
    match expr[id] {
        Expr::Num(n) => {
            if n.is_zero() {
                bytes.push(0x5f);
                2
            } else {
                let word = n.to_be_bytes::<32>();
                let start = word.iter().position(|&byte| byte != 0).unwrap();
                bytes.push(0x5f + (32 - start) as u8);
                bytes.extend_from_slice(&word[start..]);
                3
            }
        }
        Expr::Var(name) => {
            if name.as_str() == "x" {
                bytes.extend_from_slice(&[0x5f, 0x35]);
                5
            } else {
                bytes.extend_from_slice(&[0x60, 0x20, 0x35]);
                6
            }
        }
        Expr::Not(child) => {
            let gas = emit(expr, child, bytes);
            bytes.push(0x19);
            gas + 3
        }
        Expr::Shl1(child) => {
            let gas = emit(expr, child, bytes);
            bytes.extend_from_slice(&[0x60, 1, 0x1b]);
            gas + 6
        }
        Expr::Add([a, b])
        | Expr::Sub([a, b])
        | Expr::Mul([a, b])
        | Expr::And([a, b])
        | Expr::Or([a, b])
        | Expr::Xor([a, b]) => {
            // EVM SUB computes top minus second; emit the right operand first.
            let gas = emit(expr, b, bytes) + emit(expr, a, bytes);
            let (opcode, cost) = match expr[id] {
                Expr::Add(_) => (1, 3),
                Expr::Mul(_) => (2, 5),
                Expr::Sub(_) => (3, 3),
                Expr::And(_) => (0x16, 3),
                Expr::Or(_) => (0x17, 3),
                Expr::Xor(_) => (0x18, 3),
                _ => unreachable!(),
            };
            bytes.push(opcode);
            gas + cost
        }
    }
}

/// Boundary grid plus deterministic full-width samples; this is a cross-check,
/// not the equivalence proof. Both programs also receive a universal Lean proof.
pub fn cross_check(
    original: &RecExpr<Expr>,
    candidate: &RecExpr<Expr>,
    baseline: &Program,
    optimized: &Program,
) -> Result<usize> {
    let edges = [
        U256::ZERO,
        U256::from(1),
        U256::from(2),
        U256::from(255),
        U256::from(256),
        U256::from(1) << 255,
        U256::MAX - U256::from(1),
        U256::MAX,
    ];
    let mut inputs = edges
        .iter()
        .flat_map(|&x| edges.iter().map(move |&y| (x, y)))
        .collect::<Vec<_>>();
    // Fixed xorshift64 seed keeps the supplementary 64 cases reproducible.
    let mut seed = 0x243f6a8885a308d3_u64;
    for _ in 0..64 {
        let mut limbs = [0; 8];
        for limb in &mut limbs {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            *limb = seed;
        }
        inputs.push((
            U256::from_limbs(limbs[..4].try_into().unwrap()),
            U256::from_limbs(limbs[4..].try_into().unwrap()),
        ));
    }
    for &(x, y) in &inputs {
        let reference = evaluate(original, x, y);
        ensure!(
            evaluate(candidate, x, y) == reference,
            "expression mismatch at x={x}, y={y}"
        );
        for program in [baseline, optimized] {
            let (actual, gas) = program.execute(x, y)?;
            ensure!(actual == reference, "bytecode mismatch at x={x}, y={y}");
            ensure!(
                gas == program.body_gas,
                "gas model mismatch: expected {}, revm measured {gas}",
                program.body_gas
            );
        }
    }
    Ok(inputs.len())
}
