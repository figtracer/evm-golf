use evm_golf::contest::{self, RULESET, Submission};
use serde_json::Value;
use std::{fs, process::Command};
use tempfile::tempdir;

#[test]
fn fixed_specs_and_submission_schema_are_enforced() {
    assert_eq!(contest::challenges().unwrap().len(), 7);
    let dir = tempdir().unwrap();
    let mut submission = Submission {
        ruleset: RULESET.into(),
        challenge: "missing".into(),
        author: "alice".into(),
        candidate: "x".into(),
    };
    assert!(
        contest::submit(&submission, &dir.path().join("unknown"))
            .unwrap_err()
            .to_string()
            .contains("unknown challenge")
    );
    submission.challenge = "double".into();
    submission.ruleset = "evm-golf-v1-cancun".into();
    assert!(
        contest::submit(&submission, &dir.path().join("wrong-ruleset"))
            .unwrap_err()
            .to_string()
            .contains("unsupported ruleset")
    );
    submission.ruleset = RULESET.into();
    submission.author = "bad|label".into();
    assert!(contest::submit(&submission, &dir.path().join("wrong-author")).is_err());
    assert!(serde_json::from_str::<Submission>(r#"{"ruleset":"evm-golf-v2-cancun","challenge":"double","author":"alice","candidate":"x","reference":"x"}"#).is_err());
}

#[test]
#[ignore = "requires Lean 4.34.0"]
fn cli_rechecks_scores_orders_entries_and_rejects_invalid_submissions() {
    let dir = tempdir().unwrap();
    let submissions = dir.path().join("submissions");
    fs::create_dir(&submissions).unwrap();
    for (id, candidate) in [
        ("baseline", "(* x 2)"),
        ("best", "(shl1 x)"),
        ("tied", "(shl1 x)"),
    ] {
        let result = Command::new(env!("CARGO_BIN_EXE_evm-golf"))
            .args(["submit", "double", candidate, "--author", id, "--out"])
            .arg(submissions.join(id))
            .output()
            .unwrap();
        assert!(
            result.status.success(),
            "{}",
            String::from_utf8_lossy(&result.stderr)
        );
    }
    // A forged persisted score must not outrank an actually cheaper candidate.
    fs::write(
        submissions.join("baseline/result.json"),
        r#"{"optimized":{"body_gas":0}}"#,
    )
    .unwrap();
    let out = dir.path().join("board");
    let result = Command::new(env!("CARGO_BIN_EXE_evm-golf"))
        .args(["leaderboard", "--submissions"])
        .arg(&submissions)
        .arg("--out")
        .arg(&out)
        .output()
        .unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    let rows: Value =
        serde_json::from_str(&fs::read_to_string(out.join("leaderboard.json")).unwrap()).unwrap();
    assert_eq!(rows[0]["id"], "best");
    assert_eq!(rows[1]["id"], "tied");
    assert_eq!(rows[2]["id"], "baseline");
    assert_eq!(rows[2]["result"]["optimized"]["body_gas"], 13);
    let markdown = fs::read_to_string(out.join("README.md")).unwrap();
    assert!(markdown.contains("| 1 | best | 11 | 11 | 2 |"));
    assert!(markdown.contains("| 1 | tied | 11 | 11 | 2 |"));
    assert!(markdown.contains("| 3 | baseline | 13 | 11 | 0 |"));
    assert!(out.join("best/Proof.lean").is_file());

    let bad = submissions.join("false");
    fs::create_dir(&bad).unwrap();
    fs::write(
        bad.join("submission.json"),
        serde_json::to_string(&Submission {
            ruleset: RULESET.into(),
            challenge: "double".into(),
            author: "false".into(),
            candidate: "0".into(),
        })
        .unwrap(),
    )
    .unwrap();
    let rejected = dir.path().join("rejected");
    assert!(contest::leaderboard(&submissions, &rejected).is_err());
    assert!(!rejected.join("README.md").exists());
    assert!(!rejected.join("leaderboard.json").exists());
}
