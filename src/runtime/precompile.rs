//! Optimization-only observations of the admitted ECRECOVER calls. Execution,
//! gas charging and memory behavior remain entirely revm's responsibility.

use anyhow::{Result, ensure};
use revm::{
    Inspector,
    context::ContextTr,
    interpreter::{CallInput, CallInputs, CallOutcome, CallScheme},
    primitives::{Address, Bytes},
};
use std::ops::Range;

use super::ReplayPolicy;

#[derive(Debug, PartialEq, Eq)]
struct EcrecoverCall {
    // ECRECOVER consumes exactly four zero-padded words and ignores the rest.
    input: [u8; 128],
    input_len: usize,
    input_range: Option<Range<usize>>,
    output_range: Range<usize>,
    output: Bytes,
}

#[derive(Debug)]
pub(super) struct EcrecoverTrace {
    enabled: bool,
    calls: Vec<EcrecoverCall>,
    pending: Option<EcrecoverCall>,
    failure: Option<String>,
}

impl EcrecoverTrace {
    pub(super) fn new(policy: ReplayPolicy<'_>) -> Self {
        Self {
            enabled: policy == ReplayPolicy::SuccessfulEcrecover,
            calls: Vec::new(),
            pending: None,
            failure: None,
        }
    }

    pub(super) fn compare(&self, other: &Self) -> Result<()> {
        ensure!(
            self.enabled == other.enabled,
            "precompile replay policy mismatch"
        );
        ensure!(
            self.failure.is_none() && other.failure.is_none(),
            "optimization requires successful ECRECOVER calls; baseline={:?}, candidate={:?}",
            self.failure,
            other.failure
        );
        ensure!(
            self.pending.is_none() && other.pending.is_none() && self.calls == other.calls,
            "ECRECOVER call inputs, output regions or results diverged"
        );
        Ok(())
    }
}

impl<CTX: ContextTr> Inspector<CTX> for EcrecoverTrace {
    fn call(&mut self, context: &mut CTX, inputs: &mut CallInputs) -> Option<CallOutcome> {
        if !self.enabled
            || self.failure.is_some()
            || inputs.scheme != CallScheme::StaticCall
            || inputs.bytecode_address != Address::with_last_byte(1)
        {
            return None;
        }
        let bytes = inputs.input.as_bytes(context);
        let mut input = [0; 128];
        let count = input.len().min(bytes.len());
        input[..count].copy_from_slice(&bytes[..count]);
        // Capture the shared memory before revm returns to the caller. Never
        // retain or copy arbitrarily large input buffers for this fixed precompile.
        self.pending = Some(EcrecoverCall {
            input,
            input_len: inputs.input.len(),
            input_range: match &inputs.input {
                CallInput::SharedBuffer(range) => Some(range.clone()),
                CallInput::Bytes(_) => None,
            },
            output_range: inputs.return_memory_offset.clone(),
            output: Bytes::new(),
        });
        None
    }

    fn call_end(&mut self, _context: &mut CTX, inputs: &CallInputs, outcome: &mut CallOutcome) {
        if !self.enabled
            || self.failure.is_some()
            || inputs.scheme != CallScheme::StaticCall
            || inputs.bytecode_address != Address::with_last_byte(1)
        {
            return;
        }
        // Saving gas can change an underfunded call into a successful call even
        // when both outer transactions succeed. Reject failures on either side,
        // including calls whose result is discarded or whose parent reverts.
        // An invalid signature, however, is a successful call with empty output.
        if !outcome.was_precompile_called || !outcome.result.result.is_ok() {
            self.failure = Some(format!(
                "forwarded gas {}, result {:?}, native precompile {}",
                inputs.gas_limit, outcome.result.result, outcome.was_precompile_called
            ));
            self.pending = None;
            return;
        }
        if let Some(mut call) = self.pending.take() {
            call.output = outcome.result.output.clone();
            self.calls.push(call);
        } else {
            self.failure = Some("missing ECRECOVER call input observation".into());
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::runtime::{Case, analyze, compare, execute, from_hex, scenario, transform};
    use std::collections::BTreeMap;

    // Public test key 1, signing a fixed digest; no live account is involved.
    const SIGNATURE: &str = "6c3153c52bbecc21f470a76f6e3feeb8fc485c27882855c683a00eeca57c94e2000000000000000000000000000000000000000000000000000000000000001b20d8bb267736289acd57c6d8fd7c46804ef861c80887b7892c22a2870c2fb393779c5549d67f52801ce67af4227b8dd1a7f2f06078b65f64665969fdc82eb1cc";
    const PREFIX: &str = "7faaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa60805260805f5f376020608060805f6001";
    const OUTPUT: &str = "5f523d60205260805160405260605ff3";

    fn case() -> Case {
        Case {
            calldata: SIGNATURE.into(),
            gas_limit: 200_000,
            value: String::new(),
            storage: BTreeMap::new(),
        }
    }

    #[test]
    fn observer_distinguishes_underfunding_from_invalid_signature() {
        for gas in [2999, 3000] {
            for valid in [true, false] {
                let code = from_hex(&format!("{PREFIX}61{gas:04x}fa{OUTPUT}")).unwrap();
                let mut input = case();
                if !valid {
                    input.calldata.replace_range(126..128, "00");
                }
                let execution = execute(&code, &input).unwrap();
                assert!(execution.result.is_success());
                let output = execution.result.output().unwrap();
                let success = gas >= 3000;
                assert_eq!(output[31], u8::from(success));
                assert_eq!(output[63], if success && valid { 32 } else { 0 });
                if !success || !valid {
                    assert_eq!(&output[64..], &[0xaa; 32]);
                } else {
                    assert_eq!(
                        &output[64..],
                        &from_hex(
                            "0000000000000000000000007e5f4552091a69125d5dfcb7b8c2659029395bdf"
                        )
                        .unwrap()
                    );
                }
                if success {
                    assert!(execution.precompiles.failure.is_none());
                    assert_eq!(execution.precompiles.calls.len(), 1);
                    assert_eq!(
                        execution.precompiles.calls[0].output.len(),
                        if valid { 32 } else { 0 }
                    );
                    compare(&code, &code, &input).unwrap();
                } else {
                    assert!(
                        execution
                            .precompiles
                            .failure
                            .as_ref()
                            .unwrap()
                            .contains("2999")
                    );
                    assert!(
                        compare(&code, &code, &input)
                            .unwrap_err()
                            .to_string()
                            .contains("successful ECRECOVER")
                    );
                }
            }
        }
    }

    #[test]
    fn one_gas_saved_cannot_hide_failed_call_in_outer_success_or_revert() {
        for ending in ["5000", "505f5ffd"] {
            let original = from_hex(&format!("{PREFIX}6000505afa{ending}")).unwrap();
            let (candidate, _) = transform(&analyze(&original).unwrap()).unwrap();
            assert_eq!(
                candidate,
                from_hex(&format!("{PREFIX}5f505afa{ending}")).unwrap()
            );
            let mut input = case();
            input.gas_limit = 25_889;
            let left = execute(&original, &input).unwrap();
            let right = execute(&candidate, &input).unwrap();
            assert_eq!(left.result.output(), right.result.output());
            assert_eq!(left.result.is_success(), ending == "5000");
            assert_eq!(right.result.is_success(), ending == "5000");
            assert!(left.precompiles.failure.is_some());
            assert!(right.precompiles.failure.is_none());
            assert_eq!(right.precompiles.calls.len(), 1);
            assert!(
                compare(&original, &candidate, &input)
                    .unwrap_err()
                    .to_string()
                    .contains("successful ECRECOVER")
            );
            input.gas_limit = 200_000;
            compare(&original, &candidate, &input).unwrap();
        }
    }

    #[test]
    fn general_checker_retains_failed_subcall_behavior() {
        let code = from_hex(&format!("{PREFIX}610bb7fa5000")).unwrap();
        let target = Address::repeat_byte(0x22).to_string();
        let caller = Address::repeat_byte(0x11).to_string();
        let fixture = scenario::Scenario {
            target: target.clone(),
            caller: caller.clone(),
            accounts: BTreeMap::from([
                (target, scenario::Account::default()),
                (
                    caller,
                    scenario::Account {
                        balance: "1000000".into(),
                        ..Default::default()
                    },
                ),
            ]),
            transactions: vec![crate::runtime::Transaction {
                calldata: SIGNATURE.into(),
                gas_limit: 200_000,
                value: String::new(),
            }],
            environment: scenario::Environment::default(),
        };
        let directory = tempfile::tempdir().unwrap();
        scenario::check(&code, &code, &[fixture], &directory.path().join("checked")).unwrap();
    }
}
