//! Bounded, exact observations for fixture-validated external calls.
//!
//! revm owns execution. This observer never changes call inputs or outcomes and
//! does not establish whole-contract or all-gas equivalence.

use anyhow::{Context as _, Result, ensure};
use revm::{
    Inspector,
    context::ContextTr,
    interpreter::{
        CallInputs, CallOutcome, CallScheme, CreateInputs, CreateOutcome, InstructionResult,
        Interpreter,
        interpreter_types::{Jumps, LegacyBytecode},
    },
    primitives::{Address, B256, Log, U256, keccak256},
};
use serde_json::json;
use std::{
    collections::{BTreeMap, BTreeSet},
    fs::{self, File},
    io::{BufReader, BufWriter, Read, Write},
    path::Path,
};

use super::layout::CodeCopy;

// Match the fixture-input size budget per transaction. Gas does not bound
// repeated observer reads of reused memory. This operational bound limits both
// payload inspection and disk evidence; exceeding it rejects the entire run.
const MAX_TRACE_BYTES: usize = 1_048_576;

enum Stream {
    Record(BufWriter<File>),
    Compare(BufReader<File>),
}

#[derive(Debug, PartialEq, Eq)]
struct CallSite {
    code_address: Address,
    pc: usize,
}

struct ObservedCall {
    depth: usize,
    site: Option<CallSite>,
    caller: Address,
    code_address: Address,
    storage_address: Address,
    gas_limit: u64,
    calldata_keccak256: B256,
    scheme: CallScheme,
    is_static: bool,
}

pub(super) struct Calls<'a> {
    stream: Stream,
    target: Address,
    accounts: &'a BTreeSet<Address>,
    runtime: &'a [u8],
    copies: &'a [CodeCopy],
    depth: usize,
    bytes: usize,
    failure: Option<String>,
    site: Option<CallSite>,
    observed: Vec<ObservedCall>,
}

impl<'a> Calls<'a> {
    pub(super) fn record(
        path: &Path,
        target: Address,
        accounts: &'a BTreeSet<Address>,
        runtime: &'a [u8],
        copies: &'a [CodeCopy],
    ) -> Result<Self> {
        Ok(Self {
            stream: Stream::Record(BufWriter::new(File::create_new(path)?)),
            target,
            accounts,
            runtime,
            copies,
            depth: 0,
            bytes: 0,
            failure: None,
            site: None,
            observed: Vec::new(),
        })
    }

    pub(super) fn compare(
        path: &Path,
        target: Address,
        accounts: &'a BTreeSet<Address>,
        runtime: &'a [u8],
        copies: &'a [CodeCopy],
    ) -> Result<Self> {
        Ok(Self {
            stream: Stream::Compare(BufReader::new(File::open(path)?)),
            target,
            accounts,
            runtime,
            copies,
            depth: 0,
            bytes: 0,
            failure: None,
            site: None,
            observed: Vec::new(),
        })
    }

    pub(super) fn finish(&mut self) -> Result<()> {
        if let Stream::Record(writer) = &mut self.stream {
            writer.flush()?;
        }
        ensure!(
            self.failure.is_none(),
            "external-call guard: {}",
            self.failure.as_deref().unwrap_or_default()
        );
        ensure!(self.depth == 0, "external-call guard: unclosed call frames");
        if let Stream::Compare(reader) = &mut self.stream {
            let mut trailing = [0];
            ensure!(
                reader.read(&mut trailing)? == 0,
                "external-call guard: candidate omitted events"
            );
        }
        Ok(())
    }

    /// Observed calls guide the next proof obligations; they do not establish
    /// which calls can occur for other inputs, states or gas budgets.
    pub(super) fn write_dependencies(
        &self,
        candidate: &Self,
        code_hashes: &BTreeMap<Address, B256>,
        path: &Path,
    ) -> Result<()> {
        ensure!(
            self.observed.len() == candidate.observed.len(),
            "call inventory diverged"
        );
        let candidate_hash = keccak256(candidate.runtime);
        let calls = self.observed.iter().zip(&candidate.observed).map(|(a, b)| {
            ensure!(a.site == b.site, "call site diverged");
            let code_hash = if a.code_address == Address::with_last_byte(1) {
                None
            } else {
                Some(*code_hashes.get(&a.code_address).context("missing dependency code hash")?)
            };
            let candidate_hash = if a.code_address == self.target {
                Some(candidate_hash)
            } else {
                code_hash
            };
            let obligation = if a.depth == 0 && a.code_address == self.target {
                "target_entry"
            } else if a.code_address == self.target {
                "reentry_unproved"
            } else if a.code_address == Address::with_last_byte(1) && a.gas_limit >= 3000 {
                "ecrecover_model_lemma_available"
            } else {
                "callee_summary_unproved"
            };
            Ok(json!({
                "depth": a.depth,
                "site": a.site.as_ref().map(|site| json!({"code_address": site.code_address.to_string(), "pc": site.pc})),
                "caller": a.caller.to_string(),
                "code_address": a.code_address.to_string(), "storage_address": a.storage_address.to_string(),
                "original_code_keccak256": code_hash.map(|hash| hash.to_string()),
                "candidate_code_keccak256": candidate_hash.map(|hash| hash.to_string()),
                "original_gas_limit": a.gas_limit, "candidate_gas_limit": b.gas_limit,
                "calldata_keccak256": a.calldata_keccak256.to_string(),
                "scheme": format!("{:?}", a.scheme), "static": a.is_static,
                "obligation": obligation,
            }))
        }).collect::<Result<Vec<_>>>()?;
        let report = json!({
            "coverage": "Observed calls in this supplied transaction only, including reverted paths. Not a complete call graph or an all-input dependency proof.",
            "formal_status": "not_proved",
            "model_note": "An available model lemma does not prove correspondence between revm observations and EVMYulLean.",
            "calls": calls,
        });
        fs::write(path, serde_json::to_string_pretty(&report)? + "\n")?;
        Ok(())
    }

    fn event(&mut self, header: serde_json::Value, payload: &[u8]) {
        if self.failure.is_some() {
            return;
        }
        let recorded = (|| -> Result<()> {
            let header = serde_json::to_vec(&header)?;
            let size = 16usize
                .checked_add(header.len())
                .and_then(|size| size.checked_add(payload.len()))
                .context("trace size overflow")?;
            ensure!(
                size <= MAX_TRACE_BYTES - self.bytes,
                "external-call trace exceeds 1 MiB per transaction"
            );
            // Size is checked before traversing either exact payload. Borrowed
            // calldata must be consumed during call entry, before memory reuse.
            let header_len = (header.len() as u64).to_le_bytes();
            let payload_len = (payload.len() as u64).to_le_bytes();
            for bytes in [&header_len[..], &header, &payload_len, payload] {
                match &mut self.stream {
                    Stream::Record(writer) => writer.write_all(bytes)?,
                    Stream::Compare(reader) => {
                        let mut buffer = [0; 4096];
                        for chunk in bytes.chunks(buffer.len()) {
                            reader.read_exact(&mut buffer[..chunk.len()])?;
                            ensure!(
                                &buffer[..chunk.len()] == chunk,
                                "call, storage-write or log observations diverged"
                            );
                        }
                    }
                }
            }
            self.bytes += size;
            Ok(())
        })();
        if let Err(error) = recorded {
            self.failure = Some(format!("{error:#}"));
        }
    }
}

impl<CTX: ContextTr> Inspector<CTX> for Calls<'_> {
    fn initialize_interp(&mut self, interpreter: &mut Interpreter, _context: &mut CTX) {
        if self.failure.is_some() {
            return;
        }
        let code_address = interpreter
            .input
            .bytecode_address
            .unwrap_or(interpreter.input.target_address);
        // This hook also runs for callbacks. revm keeps the frame's bytecode
        // immutable; bind it once rather than scan it for every copied word.
        if code_address == self.target && interpreter.bytecode.bytecode_slice() != self.runtime {
            self.failure = Some("target runtime differs from the checked bytecode image".into());
        }
    }

    fn step(&mut self, interpreter: &mut Interpreter, _context: &mut CTX) {
        if self.failure.is_some() {
            return;
        }
        let opcode = interpreter.bytecode.opcode();
        let code_address = interpreter
            .input
            .bytecode_address
            .unwrap_or(interpreter.input.target_address);
        if matches!(opcode, 0xf1 | 0xfa) {
            self.site = Some(CallSite {
                code_address,
                pc: interpreter.bytecode.pc(),
            });
        }
        let forbidden = match opcode {
            0x5a => !matches!(
                interpreter
                    .bytecode
                    .bytecode_slice()
                    .get(interpreter.bytecode.pc() + 1),
                Some(0xf1 | 0xfa)
            ),
            0xf0 | 0xf2 | 0xf4 | 0xf5 | 0xff => true,
            0x39 if code_address == self.target => !self.copies.iter().any(|copy| {
                copy.pc == interpreter.bytecode.pc()
                    && [
                        copy.destination,
                        U256::from(copy.source),
                        U256::from(copy.len),
                    ]
                    .into_iter()
                    .enumerate()
                    .all(|(index, expected)| interpreter.stack.peek(index) == Ok(expected))
            }),
            0x3c | 0x3f => interpreter
                .stack
                .peek(0)
                .is_ok_and(|word| Address::from_word(word.into()) == self.target),
            _ => false,
        };
        if forbidden {
            self.failure = Some(format!(
                "unsupported gas, code or call observation: opcode 0x{opcode:02x} at {}:{}",
                code_address,
                interpreter.bytecode.pc()
            ));
            return;
        }
        if opcode == 0x39 && code_address == self.target {
            // The static certificate binds both images' copied bytes. Record
            // the site and depth to compare path observations without repeatedly
            // copying constant data or bypassing the existing trace budget.
            self.event(
                json!({"event":"codecopy", "depth":self.depth,
                    "pc":interpreter.bytecode.pc()}),
                &[],
            );
        }
        if matches!(opcode, 0x55 | 0x5d) {
            let (Ok(key), Ok(value)) = (interpreter.stack.peek(0), interpreter.stack.peek(1))
            else {
                self.failure = Some("storage-write stack underflow".into());
                return;
            };
            // These are attempts, including writes later rolled back. revm
            // remains responsible for charging gas and performing the writes.
            self.event(
                json!({"event":"write", "depth":self.depth,
                    "opcode":opcode, "address":interpreter.input.target_address.to_string(),
                    "key":key.to_string(), "value":value.to_string()}),
                &[],
            );
        }
    }

    fn call(&mut self, context: &mut CTX, inputs: &mut CallInputs) -> Option<CallOutcome> {
        if self.failure.is_some() {
            return None;
        }
        let native = inputs.bytecode_address == Address::with_last_byte(1);
        if !matches!(inputs.scheme, CallScheme::Call | CallScheme::StaticCall)
            || (2..=10).any(|n| inputs.bytecode_address == Address::with_last_byte(n))
            || (!native && !self.accounts.contains(&inputs.bytecode_address))
        {
            self.failure =
                Some("callee or call scheme is outside the explicit fixture policy".into());
            return None;
        }
        let bytes = inputs.input.as_bytes(context);
        if bytes.len() != inputs.input.len() {
            self.failure = Some("invalid shared call-input range".into());
            return None;
        }
        self.event(
            json!({"event":"enter", "depth":self.depth,
                "scheme":format!("{:?}",inputs.scheme), "caller":inputs.caller.to_string(),
                "code":inputs.bytecode_address.to_string(), "target":inputs.target_address.to_string(),
                "value":format!("{:?}",inputs.value), "static":inputs.is_static,
                "output_start":inputs.return_memory_offset.start,
                "output_end":inputs.return_memory_offset.end}),
            &bytes,
        );
        if self.failure.is_none() {
            self.observed.push(ObservedCall {
                depth: self.depth,
                site: self.site.take(),
                caller: inputs.caller,
                code_address: inputs.bytecode_address,
                storage_address: inputs.target_address,
                gas_limit: inputs.gas_limit,
                calldata_keccak256: keccak256(&*bytes),
                scheme: inputs.scheme,
                is_static: inputs.is_static,
            });
        }
        self.depth += 1;
        None
    }

    fn call_end(&mut self, _context: &mut CTX, inputs: &CallInputs, outcome: &mut CallOutcome) {
        if self.failure.is_some() {
            return;
        }
        let Some(depth) = self.depth.checked_sub(1) else {
            self.failure = Some("unmatched call exit".into());
            return;
        };
        self.depth = depth;
        let result = outcome.result.result;
        if inputs.bytecode_address == Address::with_last_byte(1)
            && (!outcome.was_precompile_called
                || !matches!(result, InstructionResult::Stop | InstructionResult::Return))
        {
            self.failure = Some(format!(
                "optimization requires successful ECRECOVER calls; result {result:?}, native precompile {}",
                outcome.was_precompile_called
            ));
            return;
        }
        if !matches!(
            result,
            InstructionResult::Stop | InstructionResult::Return | InstructionResult::Revert
        ) {
            self.failure = Some(format!("exceptional call halt: {result:?}"));
            return;
        }
        self.event(
            json!({"event":"exit", "depth":self.depth,
                "result":format!("{result:?}"), "precompile":outcome.was_precompile_called}),
            &outcome.result.output,
        );
    }

    fn create(&mut self, _context: &mut CTX, _inputs: &mut CreateInputs) -> Option<CreateOutcome> {
        if self.failure.is_none() {
            self.failure =
                Some("contract creation is unsupported by the external-call guard".into());
        }
        None
    }

    fn log(&mut self, _context: &mut CTX, log: Log) {
        if self.failure.is_some() {
            return;
        }
        self.event(
            json!({"event":"log", "depth":self.depth, "address":log.address.to_string(),
                "topics":log.data.topics().iter().map(ToString::to_string).collect::<Vec<_>>()}),
            &log.data.data,
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use revm::{Context, MainContext, bytecode::Bytecode, interpreter::interpreter::ExtBytecode};
    use tempfile::tempdir;

    #[test]
    fn target_codecopy_requires_checked_image_site_and_all_operands() {
        let runtime = [0x60, 1, 0x60, 8, 0x5f, 0x39, 0x39, 0, 0xab];
        let copies = super::super::layout::code_copies(&runtime);
        assert_eq!(copies.len(), 1);
        let accounts = BTreeSet::new();
        let directory = tempdir().unwrap();
        let mut context = Context::mainnet();
        for (name, pc, operands, changed_image, child, accepted) in [
            ("valid", 5, vec![1u64, 8, 0], false, false, true),
            ("length", 5, vec![2, 8, 0], false, false, false),
            ("source", 5, vec![1, 7, 0], false, false, false),
            ("destination", 5, vec![1, 8, 1], false, false, false),
            ("underflow", 5, vec![8, 0], false, false, false),
            ("uncertified", 6, vec![1, 8, 0], false, false, false),
            ("different_image", 5, vec![1, 8, 0], true, false, false),
            ("child_own_code", 6, vec![1, 8, 0], true, true, true),
        ] {
            let mut guard = Calls::record(
                &directory.path().join(name),
                Address::ZERO,
                &accounts,
                &runtime,
                &copies,
            )
            .unwrap();
            let mut interpreter = Interpreter::default_ext();
            let mut actual = runtime.to_vec();
            if changed_image {
                actual[8] = 0xcd;
            }
            interpreter.bytecode = ExtBytecode::new(Bytecode::new_legacy(actual.into()));
            if child {
                interpreter.input.bytecode_address = Some(Address::with_last_byte(11));
            }
            guard.initialize_interp(&mut interpreter, &mut context);
            interpreter.bytecode.absolute_jump(pc);
            for operand in operands {
                assert!(interpreter.stack.push(U256::from(operand)));
            }
            guard.step(&mut interpreter, &mut context);
            assert_eq!(guard.finish().is_ok(), accepted, "{name}");
        }
    }

    #[test]
    fn target_callback_rechecks_runtime_identity() {
        let directory = tempdir().unwrap();
        let accounts = BTreeSet::new();
        let mut guard = Calls::record(
            &directory.path().join("callback"),
            Address::ZERO,
            &accounts,
            &[0],
            &[],
        )
        .unwrap();
        let mut context = Context::mainnet();
        let mut interpreter = Interpreter::default_ext();
        interpreter.bytecode = ExtBytecode::new(Bytecode::new_legacy(vec![0].into()));
        guard.initialize_interp(&mut interpreter, &mut context);
        assert!(guard.failure.is_none());
        interpreter.input.bytecode_address = Some(Address::with_last_byte(11));
        interpreter.bytecode = ExtBytecode::new(Bytecode::new_legacy(vec![1].into()));
        guard.initialize_interp(&mut interpreter, &mut context);
        assert!(guard.failure.is_none());
        interpreter.input.bytecode_address = Some(Address::ZERO);
        guard.initialize_interp(&mut interpreter, &mut context);
        assert!(guard.finish().is_err());
    }

    #[test]
    fn exact_stream_requires_all_events_and_preserves_existing_evidence() {
        let directory = tempdir().unwrap();
        let path = directory.path().join("calls.trace");
        let accounts = BTreeSet::new();
        let mut baseline = Calls::record(&path, Address::ZERO, &accounts, &[], &[]).unwrap();
        baseline.event(json!({"event":"sample"}), b"exact bytes");
        baseline.finish().unwrap();
        assert!(Calls::record(&path, Address::ZERO, &accounts, &[], &[]).is_err());
        let mut candidate = Calls::compare(&path, Address::ZERO, &accounts, &[], &[]).unwrap();
        assert!(candidate.finish().is_err());
        let mut candidate = Calls::compare(&path, Address::ZERO, &accounts, &[], &[]).unwrap();
        candidate.event(json!({"event":"sample"}), b"exact bytes");
        candidate.finish().unwrap();
        let mut candidate = Calls::compare(&path, Address::ZERO, &accounts, &[], &[]).unwrap();
        candidate.event(json!({"event":"sample"}), b"other bytes");
        assert!(candidate.finish().is_err());
    }

    #[test]
    fn repeated_payloads_share_one_transaction_budget() {
        let directory = tempdir().unwrap();
        let path = directory.path().join("calls.trace");
        let accounts = BTreeSet::new();
        let payload = vec![0; 32 * 1024];
        let mut baseline = Calls::record(&path, Address::ZERO, &accounts, &[], &[]).unwrap();
        for _ in 0..64 {
            baseline.event(json!({"event":"sample"}), &payload);
        }
        assert!(baseline.finish().is_err());
        let retained = std::fs::metadata(path).unwrap().len();
        assert!(retained > 0 && retained <= MAX_TRACE_BYTES as u64);
    }

    #[test]
    fn trace_budget_rejects_before_writing_an_oversized_payload() {
        let directory = tempdir().unwrap();
        let path = directory.path().join("calls.trace");
        let accounts = BTreeSet::new();
        let mut baseline = Calls::record(&path, Address::ZERO, &accounts, &[], &[]).unwrap();
        baseline.event(json!({"event":"sample"}), &vec![0; MAX_TRACE_BYTES]);
        assert!(baseline.finish().is_err());
        assert_eq!(std::fs::metadata(path).unwrap().len(), 0);
    }
}
