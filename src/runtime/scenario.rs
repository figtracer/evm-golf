//! Concrete Cancun replay against complete local account fixtures.
//!
//! This checker accepts arbitrary legacy runtime candidates. It does not perform
//! optimization, CFG analysis, or Lean verification.

use anyhow::{Context as _, Result, ensure};
use revm::{
    bytecode::Bytecode,
    context::{BlockEnv, CfgEnv, TxEnv},
    database::InMemoryDB,
    primitives::{
        Address, B256, Bytes, TxKind, U256, eip4844::BLOB_BASE_FEE_UPDATE_FRACTION_CANCUN,
        hardfork::SpecId, hex,
    },
    state::AccountInfo,
};
use serde::{Deserialize, Serialize};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::Path,
};

use super::{
    CaseResult, ReplayPolicy, Transaction,
    calls::Calls,
    compare_results, execute_env, from_hex,
    input::{self, unique_map},
    layout,
};

#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Scenario {
    pub target: String,
    pub caller: String,
    #[serde(deserialize_with = "unique_map")]
    pub accounts: BTreeMap<String, Account>,
    pub transactions: Vec<Transaction>,
    #[serde(default)]
    pub environment: Environment,
}

#[derive(Debug, Default, Deserialize, Serialize)]
#[serde(default, deny_unknown_fields)]
pub struct Account {
    pub balance: String,
    pub nonce: u64,
    pub code: String,
    #[serde(deserialize_with = "unique_map")]
    pub storage: BTreeMap<String, String>,
}

#[derive(Debug, Default, Deserialize, Serialize)]
#[serde(default, deny_unknown_fields)]
pub struct Environment {
    pub number: Option<u64>,
    pub timestamp: Option<u64>,
    pub gas_limit: Option<u64>,
    pub beneficiary: Option<String>,
    pub prevrandao: Option<String>,
    pub chain_id: Option<u64>,
    pub blob_excess_gas: Option<u64>,
    #[serde(deserialize_with = "unique_map")]
    pub block_hashes: BTreeMap<String, String>,
}

#[derive(Debug, Serialize)]
pub struct ReplayReport {
    pub evm_version: &'static str,
    pub baseline_bytes: usize,
    pub candidate_bytes: usize,
    pub scenarios: usize,
    /// Input scenario order, then transaction order within each scenario.
    pub cases: Vec<CaseResult>,
    pub verification: &'static str,
}

/// Compare candidates only on supplied transactions. This is not a proof or an
/// optimization result. Preserve proposed input on failure.
pub fn check(
    original: &[u8],
    candidate: &[u8],
    scenarios: &[Scenario],
    out: &Path,
) -> Result<ReplayReport> {
    input::validate(
        &scenarios,
        scenarios
            .iter()
            .flat_map(|s| s.transactions.iter().map(|tx| tx.gas_limit)),
    )?;
    ensure!(
        !scenarios.is_empty(),
        "supply at least one fixture scenario"
    );
    validate_code(original)?;
    validate_code(candidate)?;
    fs::create_dir(out)?;
    fs::write(out.join("original.hex"), hex::encode(original) + "\n")?;
    fs::write(out.join("proposed.hex"), hex::encode(candidate) + "\n")?;
    fs::write(
        out.join("scenarios.json"),
        serde_json::to_string(scenarios)?,
    )?;
    let checked = scenarios
        .iter()
        .enumerate()
        .map(|(i, scenario)| {
            replay(original, candidate, scenario, ReplayPolicy::Transactions)
                .with_context(|| format!("scenario {i}"))
        })
        .collect::<Result<Vec<_>>>();
    let cases = match checked {
        Ok(results) => results.into_iter().flatten().collect(),
        Err(error) => {
            fs::write(out.join("failure.log"), format!("{error:#}\n"))?;
            return Err(error);
        }
    };
    let report = ReplayReport {
        evm_version: "Cancun",
        baseline_bytes: original.len(),
        candidate_bytes: candidate.len(),
        scenarios: scenarios.len(),
        cases,
        verification: "revm: supplied fixture transactions only, with persistent state and external accounts. Target code identity is excluded from state comparison. No Lean, whole-contract, all-input, all-gas, or deployment equivalence proof.",
    };
    fs::write(out.join("candidate.hex"), hex::encode(candidate) + "\n")?;
    fs::write(
        out.join("result.json"),
        serde_json::to_string_pretty(&report)? + "\n",
    )?;
    Ok(report)
}

pub(super) fn replay(
    original: &[u8],
    candidate: &[u8],
    scenario: &Scenario,
    policy: ReplayPolicy<'_>,
) -> Result<Vec<CaseResult>> {
    ensure!(
        !scenario.transactions.is_empty(),
        "scenario must contain at least one transaction"
    );
    let target: Address = scenario.target.parse().context("invalid target address")?;
    let caller: Address = scenario.caller.parse().context("invalid caller address")?;
    ensure!(caller != target, "caller and target must differ");
    ensure!(
        !(1..=10).any(|n| target == Address::from_word(U256::from(n).into())),
        "target cannot be a Cancun precompile"
    );
    let mut left = InMemoryDB::default();
    let mut addresses = BTreeSet::new();
    let mut total_balance = U256::ZERO;
    for (address, account) in &scenario.accounts {
        let address: Address = address.parse().context("invalid fixture account address")?;
        ensure!(
            addresses.insert(address),
            "duplicate normalized account address"
        );
        let code = from_hex(&account.code)?;
        validate_code(&code)?;
        ensure!(
            address != target || code.is_empty(),
            "target fixture code must be empty; use the original and candidate inputs"
        );
        let bytecode = Bytecode::new_legacy(Bytes::from(code));
        let balance = if account.balance.is_empty() {
            U256::ZERO
        } else {
            account.balance.parse()?
        };
        // Conserved fixture funds must fit one EVM word, preventing impossible
        // initial allocations from overflowing ordinary value transfers.
        total_balance = total_balance
            .checked_add(balance)
            .context("total fixture balance exceeds U256")?;
        left.insert_account_info(
            address,
            AccountInfo {
                balance,
                nonce: account.nonce,
                code_hash: bytecode.hash_slow(),
                code: Some(bytecode),
                ..Default::default()
            },
        );
        let mut keys = BTreeSet::new();
        for (key, value) in &account.storage {
            let key: U256 = key.parse()?;
            ensure!(keys.insert(key), "duplicate numeric storage key");
            left.insert_account_storage(address, key, value.parse()?)?;
        }
    }
    ensure!(
        addresses.contains(&target),
        "target account is missing from fixture"
    );
    ensure!(
        addresses.contains(&caller),
        "caller account is missing from fixture"
    );
    let environment = &scenario.environment;
    let mut block = BlockEnv::default();
    if let Some(number) = environment.number {
        block.number = U256::from(number);
    }
    if let Some(timestamp) = environment.timestamp {
        block.timestamp = U256::from(timestamp);
    }
    if let Some(gas_limit) = environment.gas_limit {
        block.gas_limit = gas_limit;
    }
    if let Some(beneficiary) = &environment.beneficiary {
        block.beneficiary = beneficiary.parse()?;
    }
    if let Some(prevrandao) = &environment.prevrandao {
        block.prevrandao = Some(prevrandao.parse()?);
    }
    block.set_blob_excess_gas_and_price(
        environment.blob_excess_gas.unwrap_or(0),
        BLOB_BASE_FEE_UPDATE_FRACTION_CANCUN,
    );
    let chain_id = environment
        .chain_id
        .unwrap_or(CfgEnv::<SpecId>::default().chain_id);
    let number = environment.number.unwrap_or(0);
    // EmptyDB fabricates block hashes. Seed the whole reachable history window
    // explicitly, defining omitted fixture hashes as zero instead.
    for height in number.saturating_sub(256)..number {
        left.cache
            .block_hashes
            .insert(U256::from(height), B256::ZERO);
    }
    let mut hashes = BTreeSet::new();
    for (height, hash) in &environment.block_hashes {
        let height = u64::try_from(height.parse::<U256>()?)?;
        ensure!(hashes.insert(height), "duplicate numeric block hash number");
        ensure!(
            height < number && height >= number.saturating_sub(256),
            "block hash number is outside the previous 256 blocks"
        );
        left.cache
            .block_hashes
            .insert(U256::from(height), hash.parse()?);
    }
    let mut right = left.clone();
    for (db, code) in [(&mut left, original), (&mut right, candidate)] {
        let mut info = db.load_account(target)?.info.clone();
        let code = Bytecode::new_legacy(Bytes::copy_from_slice(code));
        info.code_hash = code.hash_slow();
        info.code = Some(code);
        db.insert_account_info(target, info);
    }
    let copies = if let ReplayPolicy::GuardedCalls(directory) = policy {
        let copies = layout::analyze(original, true)?.copies;
        for copy in &copies {
            ensure!(
                candidate.get(copy.prefix_start..=copy.pc)
                    == original.get(copy.prefix_start..=copy.pc)
                    && candidate.get(copy.source..copy.source + copy.len)
                        == original.get(copy.source..copy.source + copy.len),
                "constant CODECOPY prefix or copied bytes changed"
            );
        }
        fs::create_dir(directory)?;
        copies
    } else {
        Vec::new()
    };
    scenario
        .transactions
        .iter()
        .enumerate()
        .map(|(i, transaction)| {
            (|| {
                let nonce = left.load_account(caller)?.info.nonce;
                ensure!(
                    right.load_account(caller)?.info.nonce == nonce,
                    "caller nonce diverged before transaction"
                );
                let destination = transaction
                    .to
                    .as_deref()
                    .map(str::parse::<Address>)
                    .transpose()
                    .context("invalid transaction destination")?
                    .unwrap_or(target);
                ensure!(
                    addresses.contains(&destination),
                    "transaction destination account is missing from fixture"
                );
                let tx = TxEnv::builder()
                    .caller(caller)
                    .kind(TxKind::Call(destination))
                    .nonce(nonce)
                    .chain_id(Some(chain_id))
                    .gas_limit(transaction.gas_limit)
                    .gas_price(0)
                    .value(if transaction.value.is_empty() {
                        U256::ZERO
                    } else {
                        transaction.value.parse()?
                    })
                    .data(Bytes::from(from_hex(&transaction.calldata)?))
                    .build()?;
                if let ReplayPolicy::GuardedCalls(directory) = policy {
                    let path = directory.join(format!("transaction-{i}.trace"));
                    let mut baseline = Calls::record(&path, target, &addresses, original, &copies)?;
                    let a = execute_env(
                        &mut left,
                        tx.clone(),
                        block.clone(),
                        chain_id,
                        target,
                        policy,
                        Some(&mut baseline),
                    )?;
                    baseline.finish()?;
                    let mut candidate =
                        Calls::compare(&path, target, &addresses, candidate, &copies)?;
                    let b = execute_env(
                        &mut right,
                        tx,
                        block.clone(),
                        chain_id,
                        target,
                        policy,
                        Some(&mut candidate),
                    )?;
                    candidate.finish()?;
                    compare_results(a, b)
                } else {
                    compare_results(
                        execute_env(
                            &mut left,
                            tx.clone(),
                            block.clone(),
                            chain_id,
                            target,
                            policy,
                            None,
                        )?,
                        execute_env(
                            &mut right,
                            tx,
                            block.clone(),
                            chain_id,
                            target,
                            policy,
                            None,
                        )?,
                    )
                }
            })()
            .with_context(|| format!("transaction {i}"))
        })
        .collect()
}

fn validate_code(code: &[u8]) -> Result<()> {
    ensure!(
        code.len() <= super::MAX_RUNTIME_BYTES,
        "runtime exceeds EIP-170 size limit"
    );
    ensure!(
        !code.starts_with(&[0xef, 0x00]),
        "EOF bytecode is unsupported"
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    fn fixture() -> Scenario {
        let target = Address::repeat_byte(0x22).to_string();
        let caller = Address::repeat_byte(0x11).to_string();
        Scenario {
            target: target.clone(),
            caller: caller.clone(),
            accounts: BTreeMap::from([
                (target, Account::default()),
                (
                    caller,
                    Account {
                        balance: "1000000".into(),
                        ..Account::default()
                    },
                ),
            ]),
            transactions: vec![Transaction {
                to: None,
                calldata: String::new(),
                gas_limit: 500_000,
                value: String::new(),
            }],
            environment: Environment::default(),
        }
    }

    #[test]
    fn calls_and_delegatecalls_compare_external_and_root_storage() {
        for op in ["f1", "f4"] {
            let mut scenario = fixture();
            let child = Address::repeat_byte(0x33).to_string();
            scenario.accounts.insert(
                child.clone(),
                Account {
                    code: "60015f5560015f5260205ff3".into(),
                    ..Account::default()
                },
            );
            let value = if op == "f1" { "5f" } else { "" };
            let call = from_hex(&format!(
                "60205f5f5f{value}73{}620186a0{op}5060205ff3",
                &child[2..]
            ))
            .unwrap();
            let mut baseline = from_hex("600050").unwrap();
            baseline.extend_from_slice(&call);
            assert_eq!(
                replay(&baseline, &call, &scenario, ReplayPolicy::Transactions)
                    .unwrap()
                    .len(),
                1
            );
            // Same output but missing the callee's write must be rejected.
            let pure = from_hex("60015f5260205ff3").unwrap();
            assert!(
                format!(
                    "{:#}",
                    replay(&call, &pure, &scenario, ReplayPolicy::Transactions).unwrap_err()
                )
                .contains("observable execution mismatch")
            );
        }
    }

    #[test]
    fn creation_compares_deployed_code_and_introspection_is_observable() {
        let scenario = fixture();
        // Copy an initializer from the code tail, create a child, then STOP.
        let original = from_hex("6009600d5f3960095f5ff0500060005f5360015ff3").unwrap();
        let candidate = from_hex("6009600d5f3960095f5ff0500060015f5360015ff3").unwrap();
        replay(&original, &original, &scenario, ReplayPolicy::Transactions).unwrap();
        assert!(
            format!(
                "{:#}",
                replay(&original, &candidate, &scenario, ReplayPolicy::Transactions).unwrap_err()
            )
            .contains("observable execution mismatch")
        );
        let original = from_hex("600050385f5260205ff3").unwrap();
        let candidate = from_hex("385f5260205ff3").unwrap();
        assert!(replay(&original, &candidate, &scenario, ReplayPolicy::Transactions).is_err());
    }

    #[test]
    fn fixture_hashes_are_explicit_and_normalized_keys_are_unique() {
        let mut scenario = fixture();
        scenario.environment.number = Some(2);
        let original = from_hex("6001405f5260205ff3").unwrap();
        let zero = from_hex("5f5f5260205ff3").unwrap();
        replay(&original, &zero, &scenario, ReplayPolicy::Transactions).unwrap();
        scenario
            .environment
            .block_hashes
            .insert("1".into(), B256::ZERO.to_string());
        scenario
            .environment
            .block_hashes
            .insert("0x1".into(), B256::ZERO.to_string());
        assert!(
            replay(&original, &zero, &scenario, ReplayPolicy::Transactions)
                .unwrap_err()
                .to_string()
                .contains("duplicate numeric block hash")
        );
        scenario.environment.block_hashes.clear();
        scenario.accounts.get_mut(&scenario.target).unwrap().storage =
            BTreeMap::from([("0".into(), "1".into()), ("0x0".into(), "2".into())]);
        assert!(
            replay(&original, &zero, &scenario, ReplayPolicy::Transactions)
                .unwrap_err()
                .to_string()
                .contains("duplicate numeric storage")
        );
        scenario
            .accounts
            .get_mut(&scenario.target)
            .unwrap()
            .storage
            .clear();
        scenario
            .accounts
            .insert(format!("0x{}", "ab".repeat(20)), Account::default());
        scenario
            .accounts
            .insert(format!("0x{}", "AB".repeat(20)), Account::default());
        assert!(
            replay(&original, &zero, &scenario, ReplayPolicy::Transactions)
                .unwrap_err()
                .to_string()
                .contains("duplicate normalized account")
        );
    }

    #[test]
    fn failed_replay_keeps_inputs_without_accepted_artifacts() {
        let dir = tempdir().unwrap();
        let out = dir.path().join("failed");
        let error = check(
            &from_hex("60015f5260205ff3").unwrap(),
            &from_hex("60025f5260205ff3").unwrap(),
            &[fixture()],
            &out,
        )
        .unwrap_err();
        assert!(format!("{error:#}").contains("scenario 0: transaction 0"));
        for file in [
            "original.hex",
            "proposed.hex",
            "scenarios.json",
            "failure.log",
        ] {
            assert!(out.join(file).exists());
        }
        for file in ["candidate.hex", "result.json"] {
            assert!(!out.join(file).exists());
        }
        assert!(check(&[0], &[0], &[fixture()], &out).is_err());
    }
    fn world(root: &[u8], child: &[u8]) -> InMemoryDB {
        let mut db = InMemoryDB::default();
        for (address, bytes, balance) in [
            (Address::repeat_byte(0x11), &[][..], 1_000_000),
            (Address::repeat_byte(0x22), root, 7),
            (Address::repeat_byte(0x33), child, 3),
        ] {
            let code = Bytecode::new_legacy(Bytes::copy_from_slice(bytes));
            db.insert_account_info(
                address,
                AccountInfo {
                    balance: U256::from(balance),
                    code_hash: code.hash_slow(),
                    code: Some(code),
                    ..Default::default()
                },
            );
        }
        db.insert_account_storage(Address::repeat_byte(0x22), U256::ZERO, U256::from(9))
            .unwrap();
        db.insert_account_storage(Address::repeat_byte(0x33), U256::ZERO, U256::from(7))
            .unwrap();
        db
    }

    fn step(
        db: &mut InMemoryDB,
    ) -> (
        revm::context::result::ExecutionResult,
        BTreeMap<Address, crate::runtime::AccountState>,
    ) {
        let caller = Address::repeat_byte(0x11);
        let target = Address::repeat_byte(0x22);
        let tx = TxEnv::builder()
            .caller(caller)
            .kind(TxKind::Call(target))
            .nonce(db.load_account(caller).unwrap().info.nonce)
            .gas_limit(500_000)
            .gas_price(0)
            .build()
            .unwrap();
        {
            let execution = execute_env(
                db,
                tx,
                BlockEnv::default(),
                1,
                target,
                ReplayPolicy::Transactions,
                None,
            )
            .unwrap();
            (execution.result, execution.state)
        }
    }

    #[test]
    fn call_variants_use_the_expected_storage_and_address_context() {
        let target = Address::repeat_byte(0x22);
        let child = Address::repeat_byte(0x33);
        let code = from_hex("60015f55305f5260205ff3").unwrap();
        for op in ["f1", "f2", "f4"] {
            let value = if op == "f4" { "" } else { "5f" };
            let root = from_hex(&format!(
                "60205f5f5f{value}73{}620186a0{op}5060205ff3",
                hex::encode(child)
            ))
            .unwrap();
            let mut db = world(&root, &code);
            let (result, state) = step(&mut db);
            assert!(result.is_success());
            let context = if op == "f1" { child } else { target };
            assert_eq!(
                U256::from_be_slice(result.output().unwrap()),
                U256::from_be_slice(context.as_slice())
            );
            assert_eq!(
                state[&target].storage[&U256::ZERO],
                U256::from(if op == "f1" { 9 } else { 1 })
            );
            assert_eq!(
                state[&child].storage[&U256::ZERO],
                U256::from(if op == "f1" { 1 } else { 7 })
            );
        }
    }

    #[test]
    fn staticcall_reads_storage_but_rejects_writes() {
        let child = Address::repeat_byte(0x33);
        let root = from_hex(&format!(
            "60205f5f5f73{}620186a0fa5060205ff3",
            hex::encode(child)
        ))
        .unwrap();
        let mut db = world(&root, &from_hex("5f545f5260205ff3").unwrap());
        let (result, state) = step(&mut db);
        assert!(result.is_success());
        assert_eq!(U256::from_be_slice(result.output().unwrap()), U256::from(7));
        assert_eq!(state[&child].storage[&U256::ZERO], U256::from(7));
        // Return STATICCALL's success flag instead of its returndata.
        let root = from_hex(&format!(
            "5f5f5f5f73{}620186a0fa5f5260205ff3",
            hex::encode(child)
        ))
        .unwrap();
        let mut db = world(&root, &from_hex("60015f5500").unwrap());
        let (result, state) = step(&mut db);
        assert!(result.is_success());
        assert_eq!(U256::from_be_slice(result.output().unwrap()), U256::ZERO);
        assert_eq!(state[&child].storage[&U256::ZERO], U256::from(7));
    }

    #[test]
    fn cancun_existing_selfdestruct_keeps_code_and_storage_after_transfer() {
        let target = Address::repeat_byte(0x22);
        let recipient = Address::repeat_byte(0x33);
        let code = from_hex(&format!("73{}ff", hex::encode(recipient))).unwrap();
        let mut db = world(&code, &[]);
        let hash = db.load_account(target).unwrap().info.code_hash;
        for expected_nonce in [1, 2] {
            let (result, state) = step(&mut db);
            assert!(result.is_success());
            assert_eq!(state[&target].balance, U256::ZERO);
            assert_eq!(state[&target].storage[&U256::ZERO], U256::from(9));
            assert_eq!(state[&recipient].balance, U256::from(10));
            assert_eq!(state[&Address::repeat_byte(0x11)].nonce, expected_nonce);
            assert_eq!(db.load_account(target).unwrap().info.code_hash, hash);
        }
    }

    #[test]
    fn precompile_fallbacks_match_known_hash_and_identity_vectors() {
        for (address, size, expected) in [
            (
                2,
                32,
                "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
            ),
            (
                3,
                32,
                "0000000000000000000000008eb208f7e05d987a9b044a8e98c6b087f15a0bfc",
            ),
            (4, 3, "616263"),
        ] {
            // MSTORE places "abc" at offsets 29..31; STATICCALL the precompile.
            let root = from_hex(&format!(
                "626162635f5260{size:02x}5f6003601d60{address:02x}620186a0fa5060{size:02x}5ff3"
            ))
            .unwrap();
            let mut db = world(&root, &[]);
            let (result, _) = step(&mut db);
            assert!(result.is_success());
            assert_eq!(hex::encode(result.output().unwrap()), expected);
        }
    }

    #[test]
    fn fixture_funding_and_code_roles_are_validated() {
        let mut scenario = fixture();
        scenario.accounts.get_mut(&scenario.caller).unwrap().balance = U256::MAX.to_string();
        scenario.accounts.get_mut(&scenario.target).unwrap().balance = "1".into();
        assert!(
            replay(&[0], &[0], &scenario, ReplayPolicy::Transactions)
                .unwrap_err()
                .to_string()
                .contains("total fixture balance")
        );
        let mut scenario = fixture();
        scenario.accounts.get_mut(&scenario.target).unwrap().code = "00".into();
        assert!(
            replay(&[0], &[0], &scenario, ReplayPolicy::Transactions)
                .unwrap_err()
                .to_string()
                .contains("target fixture code")
        );
        let mut scenario = fixture();
        scenario.accounts.get_mut(&scenario.caller).unwrap().code = "00".into();
        assert!(replay(&[0], &[0], &scenario, ReplayPolicy::Transactions).is_err()); // EIP-3607, no validation bypass.
    }
    #[test]
    fn external_code_and_forwarded_gas_observations_are_not_masked() {
        for helper in ["333f5f5260205ff3", "5a5f5260205ff3"] {
            let mut scenario = fixture();
            let child = Address::repeat_byte(0x33);
            scenario.accounts.insert(
                child.to_string(),
                Account {
                    code: helper.into(),
                    ..Account::default()
                },
            );
            let candidate = from_hex(&format!(
                "60205f5f5f5f73{}5af15060205ff3",
                hex::encode(child)
            ))
            .unwrap();
            let mut original = from_hex("600050").unwrap();
            original.extend_from_slice(&candidate);
            assert!(
                format!(
                    "{:#}",
                    replay(&original, &candidate, &scenario, ReplayPolicy::Transactions)
                        .unwrap_err()
                )
                .contains("observable execution mismatch")
            );
        }
    }
    #[test]
    fn fixture_json_rejects_literal_duplicate_keys_before_collection() {
        let account =
            serde_json::from_str::<Account>(r#"{"storage":{"0":"1","0":"2"}}"#).unwrap_err();
        assert!(account.to_string().contains("duplicate map key: 0"));
        let environment =
            serde_json::from_str::<Environment>(r#"{"block_hashes":{"1":"0x00","1":"0x01"}}"#)
                .unwrap_err();
        assert!(environment.to_string().contains("duplicate map key: 1"));
        let scenario = serde_json::from_str::<Scenario>(r#"{"target":"target","caller":"caller","accounts":{"caller":{},"caller":{}},"transactions":[]}"#).unwrap_err();
        assert!(scenario.to_string().contains("duplicate map key: caller"));
    }

    fn guarded_call(target: Address, opcode: u8, input_len: u8) -> Vec<u8> {
        let value = if opcode == 0xf1 { "5f" } else { "" };
        from_hex(&format!(
            "5f5f60{input_len:02x}5f{value}73{}5a{opcode:02x}50",
            hex::encode(target)
        ))
        .unwrap()
    }

    fn assert_guarded_replay(
        scenario: &Scenario,
        original: &[u8],
        candidate: &[u8],
        rejection: Option<&str>,
    ) {
        // Each negative control deliberately passes ordinary fixture comparison:
        // its rejection must come from the stronger observation policy.
        replay(original, candidate, scenario, ReplayPolicy::Transactions).unwrap();
        let directory = tempdir().unwrap();
        let traces = directory.path().join("calls");
        let result = replay(
            original,
            candidate,
            scenario,
            ReplayPolicy::GuardedCalls(&traces),
        );
        if let Some(expected) = rejection {
            let error = format!("{:#}", result.unwrap_err());
            assert!(error.contains(expected), "expected {expected}: {error}");
        } else {
            result.unwrap();
        }
    }

    #[test]
    fn guarded_calls_preserve_persistent_state_static_results_and_child_reverts() {
        let child = Address::repeat_byte(0x33);
        for (opcode, helper) in [
            (0xf1, "60015f5560075f5260205ff3"),
            (0xfa, "60075f5260205ff3"),
            (0xf1, "60075f5260205ffd"),
        ] {
            let mut scenario = fixture();
            scenario.transactions.push(Transaction {
                to: None,
                calldata: String::new(),
                value: String::new(),
                gas_limit: 500_000,
            });
            scenario.accounts.insert(
                child.to_string(),
                Account {
                    code: helper.into(),
                    ..Default::default()
                },
            );
            let call = guarded_call(child, opcode, 0);
            let mut original = from_hex("600260020250").unwrap();
            let mut candidate = from_hex("600260011b50").unwrap();
            original.extend(&call);
            candidate.extend(&call);
            original.push(0);
            candidate.push(0);
            assert_guarded_replay(&scenario, &original, &candidate, None);
        }
    }

    #[test]
    fn guarded_calls_follow_nested_callbacks_into_the_substituted_target() {
        let child = Address::repeat_byte(0x33);
        let target = Address::repeat_byte(0x22);
        let mut scenario = fixture();
        let mut helper = guarded_call(target, 0xf1, 1);
        helper.push(0);
        scenario.accounts.insert(
            child.to_string(),
            Account {
                code: hex::encode(helper),
                ..Default::default()
            },
        );
        let mut body = from_hex("365f1460005760075f55005b").unwrap();
        let prefix_bytes = 6;
        body[4] = (prefix_bytes + body.len() - 1) as u8;
        body.extend(guarded_call(child, 0xf1, 0));
        body.push(0);
        let mut original = from_hex("600260020250").unwrap();
        let mut candidate = from_hex("600260011b50").unwrap();
        original.extend(&body);
        candidate.extend(&body);
        assert_eq!(original[usize::from(body[4])], 0x5b);
        assert_guarded_replay(&scenario, &original, &candidate, None);
    }

    #[test]
    fn guarded_calls_reject_exceptional_children_and_gas_observation() {
        let child = Address::repeat_byte(0x33);
        for (helper, expected) in [
            ("fe", "exceptional call halt"),
            ("5a5000", "unsupported gas, code or call observation"),
        ] {
            let mut scenario = fixture();
            scenario.accounts.insert(
                child.to_string(),
                Account {
                    code: helper.into(),
                    ..Default::default()
                },
            );
            let mut code = guarded_call(child, 0xf1, 0);
            code.push(0);
            assert_guarded_replay(&scenario, &code, &code, Some(expected));
        }
    }

    #[test]
    fn guarded_calls_reject_target_code_hash_including_high_word_aliases() {
        let child = Address::repeat_byte(0x33);
        let target = Address::repeat_byte(0x22);
        for address in [
            hex::encode(target),
            format!("{}{}", "ff".repeat(12), hex::encode(target)),
        ] {
            let push = 0x5f + address.len() / 2;
            let mut scenario = fixture();
            scenario.accounts.insert(
                child.to_string(),
                Account {
                    code: format!("{push:02x}{address}3f5000"),
                    ..Default::default()
                },
            );
            let mut code = guarded_call(child, 0xf1, 0);
            code.push(0);
            assert_guarded_replay(
                &scenario,
                &code,
                &code,
                Some("unsupported gas, code or call observation"),
            );
        }
    }

    #[test]
    fn guarded_calls_require_explicit_callees_and_reject_other_precompiles() {
        let scenario = fixture();
        // Missing fixture code executes as an empty account in ordinary replay.
        // Native identity succeeds too, but neither is admitted by this policy.
        for child in [Address::repeat_byte(0x33), Address::with_last_byte(4)] {
            let mut code = guarded_call(child, 0xf1, 0);
            code.push(0);
            assert_guarded_replay(&scenario, &code, &code, Some("callee or call scheme"));
        }
    }

    #[test]
    fn guarded_calls_reject_delegatecall_creation_and_selfdestruct_in_children() {
        let child = Address::repeat_byte(0x33);
        let target = Address::repeat_byte(0x22);
        let mut delegate = guarded_call(target, 0xf4, 1);
        delegate.push(0);
        // The delegated root stops when called with nonempty calldata, avoiding
        // recursion in the ordinary replay control.
        let mut root = from_hex("3615600657005b").unwrap();
        root.extend(guarded_call(child, 0xf1, 0));
        root.push(0);
        for helper in [
            delegate,
            from_hex("5f5f5ff05000").unwrap(),
            from_hex(&format!("73{}ff", hex::encode(Address::repeat_byte(0x11)))).unwrap(),
        ] {
            let mut scenario = fixture();
            scenario.accounts.insert(
                child.to_string(),
                Account {
                    code: hex::encode(helper),
                    ..Default::default()
                },
            );
            assert_guarded_replay(
                &scenario,
                &root,
                &root,
                Some("unsupported gas, code or call observation"),
            );
        }
    }

    #[test]
    fn guarded_replay_compares_rolled_back_storage_transient_writes_and_logs() {
        let scenario = fixture();
        for suffix in ["5f555f5ffd", "5f5d5f5ffd", "5f5260205fa05f5ffd"] {
            let original = from_hex(&format!("6001{suffix}")).unwrap();
            let candidate = from_hex(&format!("6002{suffix}")).unwrap();
            assert_guarded_replay(
                &scenario,
                &original,
                &candidate,
                Some("call, storage-write or log observations diverged"),
            );
        }
    }

    #[test]
    fn transaction_destination_defaults_and_validation() {
        let mut scenario = fixture();
        let original = from_hex("60015f5260205ff3").unwrap();
        let implicit = replay(&original, &original, &scenario, ReplayPolicy::Transactions).unwrap();
        scenario.transactions[0].to = Some(scenario.target.clone());
        let explicit = replay(&original, &original, &scenario, ReplayPolicy::Transactions).unwrap();
        assert_eq!(
            serde_json::to_value(implicit).unwrap(),
            serde_json::to_value(explicit).unwrap()
        );
        for destination in [
            "not-an-address".to_owned(),
            Address::repeat_byte(0x44).to_string(),
        ] {
            scenario.transactions[0].to = Some(destination);
            assert!(replay(&original, &original, &scenario, ReplayPolicy::Transactions).is_err());
        }
        let helper = Address::repeat_byte(0x33).to_string();
        scenario.accounts.insert(
            helper.clone(),
            Account {
                code: "00".into(),
                ..Account::default()
            },
        );
        scenario.transactions[0].to = Some(helper);
        // A helper-only transaction is allowed, without asserting target coverage.
        replay(&original, &original, &scenario, ReplayPolicy::Transactions).unwrap();
        scenario.accounts.get_mut(&scenario.caller).unwrap().code = "00".into();
        assert!(replay(&original, &original, &scenario, ReplayPolicy::Transactions).is_err());
    }

    fn callback_programs(revert_outer: bool) -> (Vec<u8>, Vec<u8>) {
        let target = Address::repeat_byte(0x22);
        let helper = Address::repeat_byte(0x33);
        let mut router = from_hex(&format!("3373{}14600057", hex::encode(target))).unwrap();
        let label_byte = router.len() - 2;
        router.extend(
            from_hex(&format!(
                "60205f5f5f600373{}5af15060205f{}",
                hex::encode(target),
                if revert_outer { "fd" } else { "f3" }
            ))
            .unwrap(),
        );
        router[label_byte] = u8::try_from(router.len()).unwrap();
        // Callback: store and log 9, return its full word.
        router.extend(from_hex("5b60095f5560095f5260205fa060205ff3").unwrap());
        let root = from_hex(&format!(
            "60015f5560205f5f5f600173{}5af15060205ff3",
            hex::encode(helper)
        ))
        .unwrap();
        (root, router)
    }

    #[test]
    fn helper_destination_callbacks_preserve_effects_and_rollback() {
        let caller = Address::repeat_byte(0x11);
        let target = Address::repeat_byte(0x22);
        let helper = Address::repeat_byte(0x33);
        for reverted in [false, true] {
            let (root, router) = callback_programs(reverted);
            let mut scenario = fixture();
            scenario.accounts.get_mut(&scenario.target).unwrap().balance = "7".into();
            scenario.accounts.insert(
                helper.to_string(),
                Account {
                    code: hex::encode(&router),
                    balance: "3".into(),
                    ..Account::default()
                },
            );
            scenario.transactions[0].to = Some(helper.to_string());
            scenario.transactions[0].value = "5".into();
            let evidence = tempdir().unwrap();
            replay(
                &root,
                &root,
                &scenario,
                ReplayPolicy::GuardedCalls(&evidence.path().join("replay")),
            )
            .unwrap();
            let mut db = world(&root, &router);
            let helper_hash = db.load_account(helper).unwrap().info.code_hash;
            let accounts = BTreeSet::from([caller, target, helper]);
            let mut guard = Calls::record(
                &evidence.path().join("state.trace"),
                target,
                &accounts,
                &root,
                &[],
            )
            .unwrap();
            let tx = TxEnv::builder()
                .caller(caller)
                .kind(TxKind::Call(helper))
                .nonce(0)
                .gas_limit(500_000)
                .gas_price(0)
                .value(U256::from(5))
                .build()
                .unwrap();
            let execution = execute_env(
                &mut db,
                tx,
                BlockEnv::default(),
                1,
                target,
                ReplayPolicy::GuardedCalls(evidence.path()),
                Some(&mut guard),
            )
            .unwrap();
            guard.finish().unwrap();
            assert_eq!(execution.result.is_success(), !reverted);
            assert_eq!(
                U256::from_be_slice(execution.result.output().unwrap()),
                U256::from(9)
            );
            assert_eq!(execution.result.logs().len(), usize::from(!reverted));
            assert_eq!(execution.state[&caller].nonce, 1);
            assert_eq!(
                execution.state[&caller].balance,
                U256::from(if reverted { 1_000_000 } else { 999_995 })
            );
            assert_eq!(
                execution.state[&target].balance,
                U256::from(if reverted { 7 } else { 9 })
            );
            assert_eq!(
                execution.state[&helper].balance,
                U256::from(if reverted { 3 } else { 6 })
            );
            assert_eq!(
                execution.state[&target].storage[&U256::ZERO],
                U256::from(if reverted { 9 } else { 1 })
            );
            assert_eq!(
                execution.state[&helper].storage[&U256::ZERO],
                U256::from(if reverted { 7 } else { 9 })
            );
            assert_eq!(execution.state[&target].code_hash, B256::ZERO);
            assert_eq!(execution.state[&helper].code_hash, helper_hash);
            // Same returned word cannot conceal removal of the callback and its effects,
            // even when the outer transaction rolls them back.
            let pure = from_hex("60095f5260205ff3").unwrap();
            let error = replay(
                &root,
                &pure,
                &scenario,
                ReplayPolicy::GuardedCalls(&evidence.path().join("changed")),
            )
            .unwrap_err();
            assert!(format!("{error:#}").contains("external-call guard"));
        }
    }

    #[test]
    fn helper_destination_keeps_target_code_observation_guards() {
        let target = Address::repeat_byte(0x22);
        let helper = Address::repeat_byte(0x33);
        let mut scenario = fixture();
        scenario.transactions[0].to = Some(helper.to_string());
        scenario.accounts.insert(
            helper.to_string(),
            Account {
                code: hex::encode(guarded_call(target, 0xf1, 0)),
                ..Account::default()
            },
        );
        let dir = tempdir().unwrap();
        // Nested target CODECOPY is checked against the fixed optimized target.
        let copied = from_hex("600160085f390000ab").unwrap();
        replay(
            &copied,
            &copied,
            &scenario,
            ReplayPolicy::GuardedCalls(&dir.path().join("copy")),
        )
        .unwrap();
        let mut changed = copied.clone();
        changed[8] = 0xcd;
        assert!(
            replay(
                &copied,
                &changed,
                &scenario,
                ReplayPolicy::GuardedCalls(&dir.path().join("changed-copy"))
            )
            .is_err()
        );
        scenario.accounts.get_mut(&helper.to_string()).unwrap().code =
            format!("73{}3f5000", hex::encode(target));
        let error = replay(
            &[0],
            &[0],
            &scenario,
            ReplayPolicy::GuardedCalls(&dir.path().join("hash")),
        )
        .unwrap_err();
        assert!(format!("{error:#}").contains("unsupported gas, code or call observation"));
    }
}
