use serde_json::Value;
use std::{fs, process::Command};
use tempfile::tempdir;

#[test]
fn cli_analyzes_hex_files_and_rejects_unsupported_control_flow() {
    let dir = tempdir().unwrap();
    let input = dir.path().join("runtime.hex");
    fs::write(&input, "0x60026003015f5260205ff3\n").unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_evm-golf"))
        .args(["analyze-runtime", "--bytecode"])
        .arg(&input)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let report: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(report["max_stack"], 2);
    fs::write(&input, "5f3556").unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_evm-golf"))
        .args(["analyze-runtime", "--bytecode"])
        .arg(&input)
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("dynamic jump"));
}

#[test]
#[ignore = "requires Lean 4.34.0"]
fn cli_saves_only_checked_candidates_and_keeps_failure_evidence() {
    let dir = tempdir().unwrap();
    let input = dir.path().join("runtime.hex");
    let cases = dir.path().join("cases.json");
    fs::write(&input, "600060000100").unwrap();
    fs::write(&cases, r#"[{"calldata":"0x","gas_limit":100000}]"#).unwrap();
    let run = |out: &str| {
        Command::new(env!("CARGO_BIN_EXE_evm-golf"))
            .args(["optimize-runtime", "--bytecode"])
            .arg(&input)
            .arg("--cases")
            .arg(&cases)
            .arg("--out")
            .arg(dir.path().join(out))
            .output()
            .unwrap()
    };
    let output = run("accepted");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stdout).contains("local gas-erased stack rewrites only")
    );
    assert!(dir.path().join("accepted/Rewrites.log").exists());
    assert!(dir.path().join("accepted/result.json").exists());
    assert!(!run("accepted").status.success());
    fs::write(&cases, r#"[{"calldata":"0x","gas_limit":21002}]"#).unwrap();
    assert!(!run("rejected").status.success());
    for name in ["original.hex", "cases.json", "rewrites.json", "failure.log"] {
        assert!(dir.path().join("rejected").join(name).exists(), "{name}");
    }
    assert!(!dir.path().join("rejected/result.json").exists());
    assert!(!dir.path().join("rejected/candidate.hex").exists());
}

#[test]
fn cli_replays_sequences_and_retains_step_failure_evidence() {
    let dir = tempdir().unwrap();
    let input = dir.path().join("runtime.hex");
    let sequences = dir.path().join("sequences.json");
    // Increment slot zero and return the previous value. No rewrite needed.
    fs::write(&input, "5f54805f526001015f5560205ff3").unwrap();
    let run = |out: &str, extra: &[&str]| {
        Command::new(env!("CARGO_BIN_EXE_evm-golf"))
            .args(["optimize-runtime", "--bytecode"])
            .arg(&input)
            .arg("--sequences")
            .arg(&sequences)
            .arg("--out")
            .arg(dir.path().join(out))
            .args(extra)
            .output()
            .unwrap()
    };
    fs::write(
        &sequences,
        r#"[
      {"transactions":[{"calldata":"","gas_limit":100000},{"calldata":"","gas_limit":100000}]},
      {"transactions":[{"calldata":"","gas_limit":100000}]}
    ]"#,
    )
    .unwrap();
    let output = run("accepted", &[]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let report: Value =
        serde_json::from_str(&fs::read_to_string(dir.path().join("accepted/result.json")).unwrap())
            .unwrap();
    let cases = report["cases"].as_array().unwrap();
    assert_eq!(cases.len(), 3);
    assert!(
        cases[0]["baseline_gas"].as_u64().unwrap() > cases[1]["baseline_gas"].as_u64().unwrap()
    );
    assert_eq!(cases[0], cases[2]); // Each sequence starts fresh.
    assert!(
        report["verification"]
            .as_str()
            .unwrap()
            .contains("transaction sequences")
    );
    assert!(dir.path().join("accepted/sequences.json").exists());
    assert!(!dir.path().join("accepted/cases.json").exists());
    assert!(
        !run("conflict", &["--cases", "unused.json"])
            .status
            .success()
    );
    for (name, json) in [
        ("empty", "[]"),
        ("empty-steps", r#"[{"transactions":[]}]"#),
        (
            "step-storage",
            r#"[{"transactions":[{"calldata":"","gas_limit":100000,"storage":{"0":"1"}}]}]"#,
        ),
    ] {
        fs::write(&sequences, json).unwrap();
        assert!(!run(name, &[]).status.success());
        assert!(!dir.path().join(name).exists());
    }
    fs::write(&sequences, r#"[{"transactions":[{"calldata":"","gas_limit":100000},{"calldata":"","gas_limit":21000}]}]"#).unwrap();
    assert!(!run("rejected", &[]).status.success());
    let failure = fs::read_to_string(dir.path().join("rejected/failure.log")).unwrap();
    assert!(failure.contains("sequence 0: transaction 1"), "{failure}");
    for name in ["candidate.hex", "result.json"] {
        assert!(!dir.path().join("rejected").join(name).exists());
    }
}

#[test]
#[ignore = "requires Lean 4.34.0"]
fn cli_preserves_layout_for_computed_jumps() {
    let dir = tempdir().unwrap();
    let input = dir.path().join("runtime.hex");
    let cases = dir.path().join("cases.json");
    let code = "60035f35565b6002025f5260205ff3";
    fs::write(&input, code).unwrap();
    fs::write(
        &cases,
        format!(r#"[{{"calldata":"{:064x}","gas_limit":100000}}]"#, 5),
    )
    .unwrap();
    let run = |mode: bool, output: &str| {
        let mut command = Command::new(env!("CARGO_BIN_EXE_evm-golf"));
        command
            .args(["optimize-runtime", "--bytecode"])
            .arg(&input)
            .arg("--cases")
            .arg(&cases)
            .arg("--out")
            .arg(dir.path().join(output));
        if mode {
            command.arg("--preserve-layout");
        }
        command.output().unwrap()
    };
    assert!(!run(false, "compact").status.success());
    let result = run(true, "layout");
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    let report: Value =
        serde_json::from_str(&fs::read_to_string(dir.path().join("layout/result.json")).unwrap())
            .unwrap();
    assert_eq!(report["baseline_bytes"], report["candidate_bytes"]);
    assert_eq!(report["rewrites"].as_array().unwrap().len(), 1);
    assert_eq!(
        report["cases"][0]["baseline_gas"].as_u64().unwrap()
            - report["cases"][0]["candidate_gas"].as_u64().unwrap(),
        2
    );
    assert!(report["lean_version"].is_string());
    assert!(
        report["verification"]
            .as_str()
            .unwrap()
            .contains("no global stack-height proof")
    );
    let candidate = fs::read_to_string(dir.path().join("layout/candidate.hex")).unwrap();
    assert_eq!(&candidate.trim()[..12], &code[..12]);
}

#[test]
fn cli_checks_general_scenarios_without_claiming_a_proof() {
    let dir = tempdir().unwrap();
    let original = dir.path().join("original.hex");
    let candidate = dir.path().join("candidate.hex");
    let scenarios = dir.path().join("scenarios.json");
    fs::write(&original, "60005000").unwrap();
    fs::write(&candidate, "00").unwrap();
    fs::write(
        &scenarios,
        r#"[{
      "target":"0x2222222222222222222222222222222222222222",
      "caller":"0x1111111111111111111111111111111111111111",
      "accounts":{
        "0x2222222222222222222222222222222222222222":{},
        "0x1111111111111111111111111111111111111111":{"balance":"100"}
      },
      "transactions":[{"calldata":"","gas_limit":100000,"value":"7"}]
    }]"#,
    )
    .unwrap();
    let out = dir.path().join("checked");
    let output = Command::new(env!("CARGO_BIN_EXE_evm-golf"))
        .arg("check-runtime")
        .arg("--original")
        .arg(original)
        .arg("--candidate")
        .arg(candidate)
        .arg("--scenarios")
        .arg(scenarios)
        .arg("--out")
        .arg(&out)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stdout).contains("No whole-contract equivalence proof")
    );
    let report: Value =
        serde_json::from_str(&fs::read_to_string(out.join("result.json")).unwrap()).unwrap();
    assert!(report["verification"].as_str().unwrap().contains("No Lean"));
    assert_eq!(report["cases"][0]["outcome"], "success");
    assert!(out.join("candidate.hex").exists());
    assert!(!out.join("Rewrites.lean").exists());
}

#[test]
fn legacy_runtime_inputs_reject_duplicate_storage_keys() {
    use evm_golf::runtime::{Case, Sequence};
    for storage in [r#"{"0":"7","0":"0"}"#, r#"{"0":"7","\u0030":"0"}"#] {
        let case = format!(r#"{{"calldata":"","gas_limit":100000,"storage":{storage}}}"#);
        assert!(
            serde_json::from_str::<Case>(&case)
                .unwrap_err()
                .to_string()
                .contains("duplicate map key")
        );
        let sequence = format!(
            r#"{{"storage":{storage},"transactions":[{{"calldata":"","gas_limit":100000}}]}}"#
        );
        assert!(
            serde_json::from_str::<Sequence>(&sequence)
                .unwrap_err()
                .to_string()
                .contains("duplicate map key")
        );
    }
    assert!(
        serde_json::from_str::<Case>(r#"{"calldata":"","gas_limit":100000}"#)
            .unwrap()
            .storage
            .is_empty()
    );
    assert!(
        serde_json::from_str::<Sequence>(
            r#"{"transactions":[{"calldata":"","gas_limit":100000}]}"#
        )
        .unwrap()
        .storage
        .is_empty()
    );
}

#[test]
fn runtime_library_entry_points_bound_work_before_creating_evidence() {
    use evm_golf::runtime::{self, Case, Sequence, Transaction, scenario};
    let dir = tempdir().unwrap();
    let excessive = 30_000_001;
    let cases = [Case {
        calldata: String::new(),
        gas_limit: excessive,
        value: String::new(),
        storage: Default::default(),
    }];
    let out = dir.path().join("cases");
    assert!(
        runtime::optimize(&[0], &cases, &out)
            .unwrap_err()
            .to_string()
            .contains("gas limit exceeds")
    );
    assert!(!out.exists());
    let sequences = [Sequence {
        storage: Default::default(),
        transactions: (0..11)
            .map(|_| Transaction {
                calldata: String::new(),
                gas_limit: 30_000_000,
                value: String::new(),
            })
            .collect(),
    }];
    let out = dir.path().join("sequences");
    assert!(
        runtime::optimize_sequences(&[0], &sequences, &out)
            .unwrap_err()
            .to_string()
            .contains("total transaction gas")
    );
    assert!(!out.exists());
    let scenarios = [scenario::Scenario {
        target: String::new(),
        caller: String::new(),
        accounts: Default::default(),
        environment: Default::default(),
        transactions: vec![Transaction {
            calldata: String::new(),
            gas_limit: excessive,
            value: String::new(),
        }],
    }];
    let out = dir.path().join("scenario");
    assert!(
        scenario::check(&[0], &[0], &scenarios, &out)
            .unwrap_err()
            .to_string()
            .contains("gas limit exceeds")
    );
    assert!(!out.exists());
    let out = dir.path().join("optimize-scenarios");
    assert!(
        runtime::optimize_scenarios(&[0], &scenarios, &out, runtime::RuntimeMode::Compact)
            .unwrap_err()
            .to_string()
            .contains("gas limit exceeds")
    );
    assert!(!out.exists());
}

#[test]
#[ignore = "requires Lean 4.34.0"]
fn cli_optimizes_with_account_fixtures_without_changing_proof_gates() {
    let dir = tempdir().unwrap();
    let input = dir.path().join("runtime.hex");
    let scenarios = dir.path().join("scenarios.json");
    let caller = "44".repeat(20);
    let target = "55".repeat(20);
    // Require the supplied caller, target, initialized slot and transferred value.
    // Revert if a legacy default account/state silently replaces the fixture.
    let mut code = format!("3373{caller}143073{target}14165f54600714163460031416");
    let destination = code.len() / 2 + 6;
    code.push_str(&format!(
        "60{destination:02x}575f5ffd5b5f546002025f5260205ff3"
    ));
    fs::write(&input, &code).unwrap();
    let fixture = serde_json::json!([{
        "caller": format!("0x{caller}"), "target": format!("0x{target}"),
        "accounts": {
            format!("0x{caller}"): {"balance":"10", "nonce":3},
            format!("0x{target}"): {"balance":"5", "nonce":1,"storage":{"0":"7"}}
        },
        "transactions": [
            {"calldata":"", "gas_limit":100000,"value":"3"},
            {"calldata":"", "gas_limit":100000,"value":"0"}
        ]
    }]);
    fs::write(&scenarios, serde_json::to_vec(&fixture).unwrap()).unwrap();
    let run = |name: &str, extra: &[&str]| {
        Command::new(env!("CARGO_BIN_EXE_evm-golf"))
            .args(["optimize-runtime", "--bytecode"])
            .arg(&input)
            .arg("--scenarios")
            .arg(&scenarios)
            .arg("--out")
            .arg(dir.path().join(name))
            .args(extra)
            .output()
            .unwrap()
    };
    for (name, extra) in [("compact", vec![]), ("layout", vec!["--preserve-layout"])] {
        let output = run(name, &extra);
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let out = dir.path().join(name);
        let report: Value =
            serde_json::from_slice(&fs::read(out.join("result.json")).unwrap()).unwrap();
        assert_eq!(report["cases"][0]["outcome"], "success");
        assert_eq!(report["cases"][1]["outcome"], "revert");
        assert!(!report["rewrites"].as_array().unwrap().is_empty());
        assert!(report["lean_version"].is_string());
        assert!(out.join("Rewrites.log").exists());
        assert!(
            report["cases"][0]["candidate_gas"].as_u64().unwrap()
                < report["cases"][0]["baseline_gas"].as_u64().unwrap()
        );
        if name == "layout" {
            assert_eq!(report["baseline_bytes"], report["candidate_bytes"]);
            assert!(
                fs::read_to_string(out.join("Rewrites.log"))
                    .unwrap()
                    .contains("layout_artifact")
            );
        }
        let saved: Value =
            serde_json::from_slice(&fs::read(out.join("scenarios.json")).unwrap()).unwrap();
        assert_eq!(saved[0]["accounts"][format!("0x{caller}")]["nonce"], 3);
        assert_eq!(
            saved[0]["accounts"][format!("0x{target}")]["storage"]["0"],
            "7"
        );
    }
    for flag in ["--cases", "--sequences"] {
        assert!(!run("conflict", &[flag, "unused.json"]).status.success());
        assert!(!dir.path().join("conflict").exists());
    }
    let mut invalid = fixture.clone();
    invalid[0]["accounts"][format!("0x{caller}")]["balance"] = "0".into();
    fs::write(&scenarios, serde_json::to_vec(&invalid).unwrap()).unwrap();
    assert!(!run("unfunded", &[]).status.success());
    assert!(dir.path().join("unfunded/failure.log").exists());
    assert!(!dir.path().join("unfunded/candidate.hex").exists());
    assert!(!dir.path().join("unfunded/result.json").exists());
    fs::write(&input, "5a00").unwrap();
    assert!(!run("sensitive", &["--preserve-layout"]).status.success());
    assert!(!dir.path().join("sensitive").exists());
}

#[test]
#[ignore = "requires Lean 4.34.0"]
fn cli_precompile_gate_applies_to_every_optimizer_input_format() {
    let dir = tempdir().unwrap();
    let input = dir.path().join("runtime.hex");
    // A real MUL rewrite before an empty-input ECRECOVER call. Empty input is
    // an invalid signature, which succeeds with empty returndata when funded.
    fs::write(&input, "6002600202505f5f5f5f60015afa5000").unwrap();
    for layout in [false, true] {
        for format in ["cases", "sequences", "scenarios"] {
            for (name, gas) in [("funded", 200_000), ("underfunded", 24_000)] {
                let transaction = serde_json::json!({"calldata":"", "gas_limit":gas});
                let data = match format {
                    "cases" => serde_json::json!([transaction]),
                    "sequences" => serde_json::json!([{"transactions":[transaction]}]),
                    _ => serde_json::json!([{
                        "target":"0x2222222222222222222222222222222222222222",
                        "caller":"0x1111111111111111111111111111111111111111",
                        "accounts":{
                            "0x2222222222222222222222222222222222222222":{},
                            "0x1111111111111111111111111111111111111111":{"balance":"1000000"}
                        },
                        "transactions":[transaction]
                    }]),
                };
                let cases = dir.path().join(format!("{format}.json"));
                fs::write(&cases, serde_json::to_vec(&data).unwrap()).unwrap();
                let out = dir.path().join(format!("{format}-{layout}-{name}"));
                let mut command = Command::new(env!("CARGO_BIN_EXE_evm-golf"));
                command
                    .args(["optimize-runtime", "--bytecode"])
                    .arg(&input)
                    .arg(format!("--{format}"))
                    .arg(&cases)
                    .arg("--out")
                    .arg(&out);
                if layout {
                    command.arg("--preserve-layout");
                }
                let output = command.output().unwrap();
                if name == "funded" {
                    assert!(
                        output.status.success(),
                        "{}",
                        String::from_utf8_lossy(&output.stderr)
                    );
                    let report: Value =
                        serde_json::from_slice(&fs::read(out.join("result.json")).unwrap())
                            .unwrap();
                    assert!(!report["rewrites"].as_array().unwrap().is_empty());
                    assert_eq!(report["cases"][0]["outcome"], "success");
                } else {
                    assert!(!output.status.success());
                    assert!(
                        fs::read_to_string(out.join("failure.log"))
                            .unwrap()
                            .contains("successful ECRECOVER")
                    );
                    assert!(!out.join("candidate.hex").exists());
                    assert!(!out.join("result.json").exists());
                }
            }
        }
    }
}

#[test]
#[ignore = "requires Lean 4.34.0"]
fn cli_preserves_unknown_halt_branches_without_accepting_halted_cases() {
    let directory = tempdir().unwrap();
    let bytecode = directory.path().join("runtime.hex");
    let cases = directory.path().join("cases.json");
    // The unknown byte halts before GAS on the zero-input path. Nonzero input
    // jumps past it and exercises an actual multiplication rewrite.
    fs::write(&bytecode, "5f356007574d5a5b60026002025000").unwrap();
    for layout in [false, true] {
        for input in [1, 0] {
            fs::write(
                &cases,
                format!(r#"[{{"calldata":"{input:064x}","gas_limit":100000}}]"#),
            )
            .unwrap();
            let out = directory.path().join(format!("{layout}-{input}"));
            let mut command = Command::new(env!("CARGO_BIN_EXE_evm-golf"));
            command
                .args(["optimize-runtime", "--bytecode"])
                .arg(&bytecode)
                .arg("--cases")
                .arg(&cases)
                .arg("--out")
                .arg(&out);
            if layout {
                command.arg("--preserve-layout");
            }
            let result = command.output().unwrap();
            if input == 1 {
                assert!(
                    result.status.success(),
                    "{}",
                    String::from_utf8_lossy(&result.stderr)
                );
                let report: Value =
                    serde_json::from_slice(&fs::read(out.join("result.json")).unwrap()).unwrap();
                assert!(!report["rewrites"].as_array().unwrap().is_empty());
                let candidate = fs::read_to_string(out.join("candidate.hex")).unwrap();
                assert_eq!(&candidate[10..14], "4d5a");
            } else {
                assert!(!result.status.success());
                assert!(
                    fs::read_to_string(out.join("failure.log"))
                        .unwrap()
                        .contains("OpcodeNotFound")
                );
                assert!(!out.join("candidate.hex").exists());
                assert!(!out.join("result.json").exists());
            }
        }
    }
}

#[test]
#[ignore = "requires Lean 4.34.0"]
fn cli_guards_external_calls_only_with_layout_account_fixtures() {
    let directory = tempdir().unwrap();
    let input = directory.path().join("runtime.hex");
    let scenarios = directory.path().join("scenarios.json");
    let caller = format!("0x{}", "11".repeat(20));
    let target = format!("0x{}", "22".repeat(20));
    let child = format!("0x{}", "33".repeat(20));
    fs::write(
        &input,
        format!("60026002025060205f5f5f5f73{}5af15060205ff3", &child[2..]),
    )
    .unwrap();
    let mut fixture = serde_json::json!([{
        "caller":caller, "target":target,
        "accounts":{
            &caller:{"balance":"1000000"}, &target:{},
            &child:{"code":"60075f5560015f5260205ff3"}
        },
        "transactions":[{"calldata":"","gas_limit":200000},{"calldata":"","gas_limit":200000}]
    }]);
    fs::write(&scenarios, serde_json::to_vec(&fixture).unwrap()).unwrap();
    let run = |name: &str, layout: bool| {
        let mut command = Command::new(env!("CARGO_BIN_EXE_evm-golf"));
        command
            .args(["optimize-runtime", "--bytecode"])
            .arg(&input)
            .arg("--scenarios")
            .arg(&scenarios)
            .arg("--out")
            .arg(directory.path().join(name));
        if layout {
            command.arg("--preserve-layout");
        }
        command.output().unwrap()
    };
    assert!(!run("compact", false).status.success());
    let output = run("guarded", true);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let report: Value =
        serde_json::from_slice(&fs::read(directory.path().join("guarded/result.json")).unwrap())
            .unwrap();
    assert_eq!(report["rewrites"].as_array().unwrap().len(), 1);
    assert!(
        report["verification"]
            .as_str()
            .unwrap()
            .contains("guarded nested calls")
    );
    assert!(report["lean_version"].is_string());
    for case in report["cases"].as_array().unwrap() {
        assert_eq!(case["outcome"], "success");
        assert_eq!(
            case["baseline_gas"].as_u64().unwrap() - case["candidate_gas"].as_u64().unwrap(),
            2
        );
    }
    assert!(
        directory
            .path()
            .join("guarded/scenario-0-calls/transaction-1.trace")
            .exists()
    );
    fixture[0]["accounts"][&child]["code"] = "5a5f5260205ff3".into();
    fs::write(&scenarios, serde_json::to_vec(&fixture).unwrap()).unwrap();
    let output = run("sensitive-child", true);
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("external-call guard"));
    assert!(
        directory
            .path()
            .join("sensitive-child/failure.log")
            .exists()
    );
    assert!(
        !directory
            .path()
            .join("sensitive-child/candidate.hex")
            .exists()
    );
    assert!(
        !directory
            .path()
            .join("sensitive-child/result.json")
            .exists()
    );
}

#[test]
#[ignore = "requires Lean 4.34.0"]
fn cli_certifies_constant_code_reads_and_preserves_observed_rewrites() {
    let directory = tempdir().unwrap();
    let input = directory.path().join("runtime.hex");
    let scenarios = directory.path().join("scenarios.json");
    let caller = format!("0x{}", "11".repeat(20));
    let target = format!("0x{}", "22".repeat(20));
    fs::write(
        &scenarios,
        serde_json::to_vec(&serde_json::json!([{
            "caller":caller, "target":target,
            "accounts":{&caller:{"balance":"1000000"}, &target:{}},
            "transactions":[{"calldata":"","gas_limit":100000}]
        }]))
        .unwrap(),
    )
    .unwrap();
    for (name, code, count) in [
        ("disjoint", "600760020250600360105f3960035ff300abcdef", 1),
        ("observed", "600760020250600360025f3960035ff300abcdef", 0),
    ] {
        fs::write(&input, code).unwrap();
        let out = directory.path().join(name);
        let result = Command::new(env!("CARGO_BIN_EXE_evm-golf"))
            .args(["optimize-runtime", "--preserve-layout", "--bytecode"])
            .arg(&input)
            .arg("--scenarios")
            .arg(&scenarios)
            .arg("--out")
            .arg(&out)
            .output()
            .unwrap();
        assert!(
            result.status.success(),
            "{}",
            String::from_utf8_lossy(&result.stderr)
        );
        let report: Value =
            serde_json::from_slice(&fs::read(out.join("result.json")).unwrap()).unwrap();
        assert_eq!(report["rewrites"].as_array().unwrap().len(), count);
        assert_eq!(
            report["cases"][0]["baseline_gas"].as_u64().unwrap()
                - report["cases"][0]["candidate_gas"].as_u64().unwrap(),
            (count * 2) as u64
        );
        let proof = fs::read_to_string(out.join("Rewrites.lean")).unwrap();
        assert!(proof.contains("codecopy_artifact"));
    }
}

#[test]
#[ignore = "requires Lean 4.34.0"]
fn cli_proves_literal_folds_with_zero_required_stack() {
    let directory = tempdir().unwrap();
    let input = directory.path().join("runtime.hex");
    let cases = directory.path().join("cases.json");
    fs::write(&input, "60076003165f5260205ff3").unwrap();
    fs::write(&cases, r#"[{"calldata":"","gas_limit":100000}]"#).unwrap();
    let out = directory.path().join("folded");
    let result = Command::new(env!("CARGO_BIN_EXE_evm-golf"))
        .args(["optimize-runtime", "--preserve-layout", "--bytecode"])
        .arg(&input)
        .arg("--cases")
        .arg(&cases)
        .arg("--out")
        .arg(&out)
        .output()
        .unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    let report: Value =
        serde_json::from_slice(&fs::read(out.join("result.json")).unwrap()).unwrap();
    assert_eq!(report["rewrites"].as_array().unwrap().len(), 1);
    assert_eq!(report["rewrites"][0]["required_stack"], 0);
    assert_eq!(
        report["cases"][0]["baseline_gas"].as_u64().unwrap()
            - report["cases"][0]["candidate_gas"].as_u64().unwrap(),
        1
    );
    assert_eq!(
        fs::read_to_string(out.join("candidate.hex"))
            .unwrap()
            .trim(),
        "60036000505f5260205ff3"
    );
}
