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
    primitives::{Address, Log},
};
use serde_json::json;
use std::{
    collections::BTreeSet,
    fs::File,
    io::{BufReader, BufWriter, Read, Write},
    path::Path,
};

// Match the fixture-input size budget per transaction. Gas does not bound
// repeated observer reads of reused memory. This operational bound limits both
// payload inspection and disk evidence; exceeding it rejects the entire run.
const MAX_TRACE_BYTES: usize = 1_048_576;

enum Stream {
    Record(BufWriter<File>),
    Compare(BufReader<File>),
}

pub(super) struct Calls<'a> {
    stream: Stream,
    target: Address,
    accounts: &'a BTreeSet<Address>,
    depth: usize,
    bytes: usize,
    failure: Option<String>,
}

impl<'a> Calls<'a> {
    pub(super) fn record(
        path: &Path,
        target: Address,
        accounts: &'a BTreeSet<Address>,
    ) -> Result<Self> {
        Ok(Self {
            stream: Stream::Record(BufWriter::new(File::create_new(path)?)),
            target,
            accounts,
            depth: 0,
            bytes: 0,
            failure: None,
        })
    }

    pub(super) fn compare(
        path: &Path,
        target: Address,
        accounts: &'a BTreeSet<Address>,
    ) -> Result<Self> {
        Ok(Self {
            stream: Stream::Compare(BufReader::new(File::open(path)?)),
            target,
            accounts,
            depth: 0,
            bytes: 0,
            failure: None,
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
    fn step(&mut self, interpreter: &mut Interpreter, _context: &mut CTX) {
        if self.failure.is_some() {
            return;
        }
        let opcode = interpreter.bytecode.opcode();
        let code_address = interpreter
            .input
            .bytecode_address
            .unwrap_or(interpreter.input.target_address);
        let forbidden = match opcode {
            0x5a => !matches!(
                interpreter
                    .bytecode
                    .bytecode_slice()
                    .get(interpreter.bytecode.pc() + 1),
                Some(0xf1 | 0xfa)
            ),
            0xf0 | 0xf2 | 0xf4 | 0xf5 | 0xff => true,
            0x39 => code_address == self.target,
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
    use tempfile::tempdir;

    #[test]
    fn exact_stream_requires_all_events_and_preserves_existing_evidence() {
        let directory = tempdir().unwrap();
        let path = directory.path().join("calls.trace");
        let accounts = BTreeSet::new();
        let mut baseline = Calls::record(&path, Address::ZERO, &accounts).unwrap();
        baseline.event(json!({"event":"sample"}), b"exact bytes");
        baseline.finish().unwrap();
        assert!(Calls::record(&path, Address::ZERO, &accounts).is_err());
        let mut candidate = Calls::compare(&path, Address::ZERO, &accounts).unwrap();
        assert!(candidate.finish().is_err());
        let mut candidate = Calls::compare(&path, Address::ZERO, &accounts).unwrap();
        candidate.event(json!({"event":"sample"}), b"exact bytes");
        candidate.finish().unwrap();
        let mut candidate = Calls::compare(&path, Address::ZERO, &accounts).unwrap();
        candidate.event(json!({"event":"sample"}), b"other bytes");
        assert!(candidate.finish().is_err());
    }

    #[test]
    fn repeated_payloads_share_one_transaction_budget() {
        let directory = tempdir().unwrap();
        let path = directory.path().join("calls.trace");
        let accounts = BTreeSet::new();
        let payload = vec![0; 32 * 1024];
        let mut baseline = Calls::record(&path, Address::ZERO, &accounts).unwrap();
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
        let mut baseline = Calls::record(&path, Address::ZERO, &accounts).unwrap();
        baseline.event(json!({"event":"sample"}), &vec![0; MAX_TRACE_BYTES]);
        assert!(baseline.finish().is_err());
        assert_eq!(std::fs::metadata(path).unwrap().len(), 0);
    }
}
