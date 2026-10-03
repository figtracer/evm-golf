//! Conditional internal-region certificates against pinned upstream EVM semantics.

use anyhow::{Context as _, Result, ensure};
use revm::primitives::{hex, keccak256};
use serde::Serialize;
use std::{fmt::Write as _, fs, path::Path};

use super::MAX_RUNTIME_BYTES;
use crate::proof;

const IMAGES: &str = include_str!("../../lean/upstream/templates/Images.lean.in");
const DECODE: &str = include_str!("../../lean/upstream/templates/Decode.lean.in");
const REGION: &str = include_str!("../../lean/upstream/templates/RegionProof.lean.in");

/// Conditions and scope of the generated theorem, not a whole-contract verdict.
#[derive(Debug, Serialize)]
pub struct RegionCertificate {
    pub claim: &'static str,
    pub original_keccak256: String,
    pub candidate_keccak256: String,
    pub entry_pc: usize,
    pub exit_pc: usize,
    pub pushed_destination: u16,
    pub source_gas_minimum: u64,
    pub gas_surplus_increase: u64,
    pub input_stack: &'static str,
    pub maximum_tail_length: usize,
    pub output_stack: String,
    pub interpreter_fuel: &'static str,
    pub state_relation: &'static str,
    pub unproved: [&'static str; 5],
    pub lean_version: String,
}

struct Region {
    entry_pc: usize,
    destination: u16,
}

impl Region {
    fn select(original: &[u8], candidate: &[u8], entry_pc: usize) -> Result<Self> {
        ensure!(
            original.len() <= MAX_RUNTIME_BYTES && candidate.len() <= MAX_RUNTIME_BYTES,
            "runtime exceeds EIP-170 size limit"
        );
        ensure!(
            original.len() == candidate.len(),
            "region certificates require fixed layout"
        );
        let end = entry_pc.checked_add(12).context("region PC overflow")?;
        let before = original
            .get(entry_pc..end)
            .context("truncated source region")?;
        let after = candidate
            .get(entry_pc..end)
            .context("truncated candidate region")?;
        ensure!(
            before[..9] == [0x60, 0x20, 0x02, 0x01, 0x90, 0x5f, 0x80, 0x80, 0x61]
                && before[11] == 0x56,
            "unsupported source region: expected PUSH1 32; MUL; ADD; SWAP1; PUSH0; DUP1; DUP1; PUSH2; JUMP"
        );
        ensure!(
            after[..3] == [0x60, 0x05, 0x1b] && after[3..] == before[3..],
            "unsupported candidate region: expected PUSH1 5; SHL and unchanged region remainder"
        );
        Ok(Self {
            entry_pc,
            destination: u16::from_be_bytes([before[9], before[10]]),
        })
    }

    fn sources(&self, original: &[u8], candidate: &[u8]) -> [(&'static str, String); 3] {
        let images = IMAGES
            .replace("$namespace", "GolfCertificates")
            .replace("$original_list", &format!("{original:?}"))
            .replace("$candidate_list", &format!("{candidate:?}"));
        let mut facts = String::new();
        for side in ["original", "candidate"] {
            for (offset, name, opcode) in [
                (3, "Add", "ADD"),
                (4, "Swap", "SWAP1"),
                (5, "Zero", "PUSH0"),
                (6, "DupA", "DUP1"),
                (7, "DupB", "DUP1"),
                (8, "Target", "PUSH2"),
                (11, "Jump", "JUMP"),
            ] {
                let immediate = if offset == 8 {
                    format!("some (UInt256.ofNat {},2)", self.destination)
                } else {
                    "none".to_owned()
                };
                writeln!(facts,
                    "theorem {side}{name}Decoded : decode {side}Code (UInt256.ofNat {}) = some (.{opcode},{immediate}) := by decide +kernel",
                    self.entry_pc + offset).unwrap();
            }
        }
        let decode = DECODE
            .replace("$image_module", "Images")
            .replace("$namespace", "GolfCertificates.Region")
            .replace("$entry_pc", &self.entry_pc.to_string())
            .replace("$decoded_facts", &facts);
        let region = REGION
            .replace("$decode_module", "Decode")
            .replace("$namespace", "GolfCertificates.Region")
            .replace("$entry_pc", &self.entry_pc.to_string())
            .replace("$exit_pc", &(self.entry_pc + 11).to_string())
            .replace("$destination", &self.destination.to_string());
        [
            ("Images.lean", images),
            ("Decode.lean", decode),
            ("RegionProof.lean", region),
        ]
    }
}

/// Check the selected eight-instruction prefix, ending before JUMP.
///
/// The surrounding bytecode may differ; it is embedded independently on both
/// sides and is not covered by this region's conclusion. No reachability,
/// transaction replay, jump execution, or whole-runtime equivalence is implied.
pub fn certify(
    original: &[u8],
    candidate: &[u8],
    entry_pc: usize,
    out: &Path,
) -> Result<RegionCertificate> {
    let region = Region::select(original, candidate, entry_pc)?;
    fs::create_dir(out)
        .with_context(|| format!("use a new output directory: {}", out.display()))?;
    fs::write(out.join("original.hex"), hex::encode(original) + "\n")?;
    fs::write(out.join("candidate.hex"), hex::encode(candidate) + "\n")?;
    for (name, source) in region.sources(original, candidate) {
        fs::write(out.join(name), source)?;
    }
    let lean_version = proof::verify_region(out)?;
    let report = RegionCertificate {
        claim: "conditional internal-region residual interpreter calls",
        original_keccak256: keccak256(original).to_string(),
        candidate_keccak256: keccak256(candidate).to_string(),
        entry_pc,
        exit_pc: entry_pc + 11,
        pushed_destination: region.destination,
        source_gas_minimum: 25,
        gas_surplus_increase: 2,
        input_stack: "a :: b :: c :: tail (top first; arbitrary 256-bit words)",
        maximum_tail_length: 1018,
        output_stack: format!(
            "{} :: 0 :: 0 :: 0 :: c :: (32*a+b modulo 2^256) :: tail",
            region.destination
        ),
        interpreter_fuel: "for every natural fuel, each X(fuel+9) reduces to its own X(fuel+1) at the exit",
        state_relation: "arbitrary nonnegative incoming gas surplus; related current/original account maps differing only in designated deployed code; both execution-code links; all other frame fields preserved",
        unproved: [
            "entry reachability",
            "exit JUMP execution",
            "suffix outcomes",
            "whole-contract equivalence",
            "revm correspondence",
        ],
        lean_version,
    };
    fs::write(
        out.join("result.json"),
        serde_json::to_string_pretty(&report)? + "\n",
    )?;
    Ok(report)
}

#[cfg(test)]
mod tests {
    use super::*;

    const ORIGINAL: [u8; 12] = [
        0x60, 32, 0x02, 0x01, 0x90, 0x5f, 0x80, 0x80, 0x61, 0x12, 0x34, 0x56,
    ];
    const CANDIDATE: [u8; 12] = [
        0x60, 5, 0x1b, 0x01, 0x90, 0x5f, 0x80, 0x80, 0x61, 0x12, 0x34, 0x56,
    ];

    #[test]
    fn selection_rejects_wrong_rewrites_and_partial_regions() {
        let region = Region::select(&ORIGINAL, &CANDIDATE, 0).unwrap();
        assert_eq!(region.destination, 0x1234);
        for (position, value) in [(1, 6), (2, 2), (10, 0x35), (11, 0)] {
            let mut wrong = CANDIDATE;
            wrong[position] = value;
            assert!(Region::select(&ORIGINAL, &wrong, 0).is_err());
        }
        assert!(Region::select(&ORIGINAL, &CANDIDATE[..11], 0).is_err());
        assert!(Region::select(&ORIGINAL[..11], &CANDIDATE[..11], 0).is_err());
        assert!(Region::select(&ORIGINAL, &CANDIDATE, usize::MAX).is_err());
        assert!(Region::select(&CANDIDATE, &CANDIDATE, 0).is_err());
    }

    #[test]
    fn malformed_input_and_existing_outputs_preserve_evidence() {
        let temp = tempfile::tempdir().unwrap();
        let out = temp.path().join("certificate");
        assert!(certify(&ORIGINAL, &ORIGINAL, 0, &out).is_err());
        assert!(!out.exists());
        fs::create_dir(&out).unwrap();
        fs::write(out.join("result.json"), "existing evidence").unwrap();
        assert!(certify(&ORIGINAL, &CANDIDATE, 0, &out).is_err());
        assert_eq!(
            fs::read_to_string(out.join("result.json")).unwrap(),
            "existing evidence"
        );
    }
}
