use evm_golf::{
    campaign,
    contest::{RULESET, Submission},
};
use serde_json::Value;
use std::{fs, process::Command};
use tempfile::tempdir;

#[test]
fn campaign_rejects_empty_oversized_and_malformed_batches() {
    let dir = tempdir().unwrap();
    let input = dir.path().join("proposals.json");
    for data in [
        "[]".to_owned(),
        "not json".to_owned(),
        " ".repeat(1024 * 1024 + 1),
    ] {
        fs::write(&input, data).unwrap();
        let out = dir.path().join("output");
        assert!(campaign::run(&input, &out).is_err());
        assert!(!out.exists());
    }
    let proposals = (0..65)
        .map(|_| Submission {
            ruleset: RULESET.into(),
            challenge: "double".into(),
            author: "agent".into(),
            candidate: "(shl1 x)".into(),
        })
        .collect::<Vec<_>>();
    fs::write(&input, serde_json::to_string(&proposals).unwrap()).unwrap();
    assert!(campaign::run(&input, &dir.path().join("too-many")).is_err());
}

#[test]
#[ignore = "requires Lean 4.34.0"]
fn cli_campaign_preserves_failures_and_only_ranks_verified_candidates() {
    let dir = tempdir().unwrap();
    let input = dir.path().join("proposals.json");
    let proposals = [
        Submission {
            ruleset: RULESET.into(),
            challenge: "double".into(),
            author: "bad|[label]<b>".into(),
            candidate: "x".into(),
        },
        Submission {
            ruleset: RULESET.into(),
            challenge: "double".into(),
            author: "wrong".into(),
            candidate: "x".into(),
        },
        Submission {
            ruleset: RULESET.into(),
            challenge: "double".into(),
            author: "winner".into(),
            candidate: "(shl1 x)".into(),
        },
    ];
    fs::write(&input, serde_json::to_string(&proposals).unwrap()).unwrap();
    let out = dir.path().join("campaign");
    let result = Command::new(env!("CARGO_BIN_EXE_evm-golf"))
        .arg("campaign")
        .arg("--proposals")
        .arg(&input)
        .arg("--out")
        .arg(&out)
        .output()
        .unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    assert!(String::from_utf8_lossy(&result.stdout).contains("1 verified, 2 unverified"));
    let report: Value =
        serde_json::from_str(&fs::read_to_string(out.join("campaign.json")).unwrap()).unwrap();
    assert_eq!(report["attempted"], 3);
    assert!(report["attempts"][0]["result"].is_null());
    assert!(
        report["attempts"][1]["error"]
            .as_str()
            .unwrap()
            .contains("Lean rejected")
    );
    assert_eq!(report["attempts"][2]["result"]["optimized"]["body_gas"], 11);
    assert_eq!(fs::read_dir(out.join("accepted")).unwrap().count(), 1);
    let board: Value = serde_json::from_str(
        &fs::read_to_string(out.join("leaderboard/leaderboard.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(board.as_array().unwrap().len(), 1);
    assert_eq!(board[0]["submission"]["author"], "winner");
    assert!(out.join("attempts/attempt-002/Proof.log").is_file());
    assert!(out.join("egraph/carry-add/result.json").is_file());
    let markdown = fs::read_to_string(out.join("README.md")).unwrap();
    assert!(!markdown.contains("bad|[label]<b>"));
    assert!(markdown.contains("bad&#124;&#91;label&#93;&lt;b&gt;"));
    let saved = fs::read_to_string(out.join("campaign.json")).unwrap();
    assert!(campaign::run(&input, &out).is_err());
    assert_eq!(
        fs::read_to_string(out.join("campaign.json")).unwrap(),
        saved
    );
}
