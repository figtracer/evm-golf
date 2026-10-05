//! Whole-program refinement certificates against pinned EVMYulLean.
//!
//! The generator covers every instruction reachable from pc 0 or a JUMPDEST and
//! emits one Lean obligation per instruction. Lean then proves, for the whole
//! program, that every successful or reverting original run is matched by the
//! candidate. Only small images with the supported opcode profile are accepted.

use anyhow::{Context as _, Result, bail, ensure};
use revm::primitives::{U256, hex, keccak256};
use serde::Serialize;
use std::{collections::BTreeSet, fmt::Write as _, fs, path::Path};

use super::{Instruction, decode};
use crate::proof;

/// Each obligation decodes against the full image in the kernel, so cost grows
/// with size times instruction count.
pub const MAX_WHOLE_BYTES: usize = 1024;

#[derive(Debug, Serialize)]
pub struct WholeCertificate {
    pub claim: &'static str,
    pub original_keccak256: String,
    pub candidate_keccak256: String,
    pub runtime_bytes: usize,
    pub covered_instructions: usize,
    pub power_sites: Vec<usize>,
    pub assumptions: [&'static str; 3],
    pub unproved: [&'static str; 4],
    pub lean_version: String,
}

struct PowerSite {
    pc: usize,
    width: usize,
    exponent: usize,
}

enum Obligation {
    Same {
        op: String,
        arg: String,
        same: String,
    },
    Jump,
    Jumpi,
    Halt {
        op: &'static str,
        which: &'static str,
        congruent: &'static str,
    },
    FallOff,
    Invalid,
    Power(PowerSite),
}

pub fn certify(original: &[u8], candidate: &[u8], out: &Path) -> Result<WholeCertificate> {
    let plan = plan(original, candidate)?;
    fs::create_dir(out)
        .with_context(|| format!("use a new output directory: {}", out.display()))?;
    fs::write(out.join("original.hex"), hex::encode(original) + "\n")?;
    fs::write(out.join("candidate.hex"), hex::encode(candidate) + "\n")?;
    let modules = render(original, candidate, &plan);
    for (name, source) in &modules {
        fs::write(out.join(format!("{name}.lean")), source)?;
    }
    let lean_version = proof::verify_region(out, proof::RegionKind::Whole(modules.len() - 2))?;
    let report = WholeCertificate {
        claim: "whole-program refinement of the canonical interpreter X from pc 0",
        original_keccak256: keccak256(original).to_string(),
        candidate_keccak256: keccak256(candidate).to_string(),
        runtime_bytes: original.len(),
        covered_instructions: plan.points.len(),
        power_sites: plan
            .points
            .iter()
            .filter_map(|(pc, obligation)| {
                matches!(obligation, Obligation::Power(_)).then_some(*pc)
            })
            .collect(),
        assumptions: [
            "both runs start at pc 0 from states equal except deployed code, execution count and extra candidate gas",
            "valid jump tables are computed by the checked-scanner profile of D_J",
            "if the original run returns success or revert, so does the candidate, with equal output; success states stay related and revert gas is not lower",
        ],
        unproved: [
            "transaction-level (Ξ/Υ) equivalence",
            "opcodes outside the supported profile, including calls, storage and logs",
            "exceptional original runs (the claim is conditioned on original success or revert)",
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

struct Plan {
    points: Vec<(usize, Obligation)>,
    jumpdests: Vec<usize>,
}

fn plan(original: &[u8], candidate: &[u8]) -> Result<Plan> {
    ensure!(
        original.len() == candidate.len(),
        "whole-program certificates need equal-length images"
    );
    ensure!(
        !original.is_empty() && original.len() <= MAX_WHOLE_BYTES,
        "whole-program certificates accept 1..={MAX_WHOLE_BYTES} runtime bytes"
    );
    let instructions = decode(original);
    let last = instructions.last().context("empty runtime")?;
    ensure!(
        last.bytes.len() == push_width(last.bytes[0]) + 1,
        "truncated final PUSH is unsupported"
    );
    let starts: BTreeSet<usize> = instructions.iter().map(|i| i.pc).collect();
    let jumpdests = jump_table(original);
    ensure!(
        jumpdests == jump_table(candidate),
        "rewrite changes the valid jump table"
    );
    let sites = power_sites(original, candidate, &instructions, &starts)?;
    // Cover pc 0, every JUMPDEST and their fall-through successors; bytes such as
    // trailing metadata that no execution can reach need no obligation.
    let mut pending: Vec<usize> = std::iter::once(0)
        .chain(jumpdests.iter().copied())
        .collect();
    let mut seen = BTreeSet::new();
    let mut points = Vec::new();
    while let Some(pc) = pending.pop() {
        if !seen.insert(pc) {
            continue;
        }
        if pc >= original.len() {
            points.push((pc, Obligation::FallOff));
            continue;
        }
        ensure!(
            starts.contains(&pc),
            "execution reaches pc {pc}, which is not an instruction boundary"
        );
        let (obligation, next) = if let Some(site) = sites.iter().find(|s| s.pc == pc) {
            let next = pc + site.width + 2;
            (
                Obligation::Power(PowerSite {
                    pc,
                    width: site.width,
                    exponent: site.exponent,
                }),
                Some(next),
            )
        } else {
            ensure!(
                !sites.iter().any(|s| s.pc < pc && pc < s.pc + s.width + 2),
                "execution reaches pc {pc} inside a rewrite site"
            );
            let instruction = instructions
                .iter()
                .find(|i| i.pc == pc)
                .expect("boundary has an instruction");
            let obligation = classify(instruction)?;
            let next = matches!(obligation, Obligation::Same { .. } | Obligation::Jumpi)
                .then_some(pc + instruction.bytes.len());
            (obligation, next)
        };
        points.push((pc, obligation));
        pending.extend(next);
    }
    points.sort_by_key(|(pc, _)| *pc);
    Ok(Plan { points, jumpdests })
}

fn push_width(op: u8) -> usize {
    if (0x60..=0x7f).contains(&op) {
        usize::from(op - 0x5f)
    } else {
        0
    }
}

/// JUMPDEST offsets at instruction boundaries, in scan order.
fn jump_table(code: &[u8]) -> Vec<usize> {
    decode(code)
        .iter()
        .filter(|i| i.bytes[0] == 0x5b)
        .map(|i| i.pc)
        .collect()
}

/// Every byte difference must lie inside `PUSHn 2^k; MUL` rewritten to `PUSHn k; SHL`.
fn power_sites(
    original: &[u8],
    candidate: &[u8],
    instructions: &[Instruction],
    starts: &BTreeSet<usize>,
) -> Result<Vec<PowerSite>> {
    let mut sites: Vec<PowerSite> = Vec::new();
    for (pc, (a, b)) in original.iter().zip(candidate).enumerate() {
        if a == b || sites.last().is_some_and(|s| pc < s.pc + s.width + 2) {
            continue;
        }
        let start = *starts
            .range(..=pc)
            .next_back()
            .context("difference before the first instruction")?;
        let index = instructions
            .iter()
            .position(|i| i.pc == start)
            .expect("start is an instruction");
        let push = &instructions[index];
        let width = push_width(push.bytes[0]);
        let next = instructions.get(index + 1);
        let value = U256::from_be_slice(&push.bytes[1..]);
        let exponent = (width > 0 && value.count_ones() == 1).then(|| value.trailing_zeros());
        let shift = U256::from_be_slice(&candidate[start + 1..start + 1 + width]);
        match (exponent, next) {
            (Some(k), Some(mul))
                if mul.bytes == [0x02]
                    && candidate[start] == push.bytes[0]
                    && candidate[mul.pc] == 0x1b
                    && shift == U256::from(k)
                    && pc < mul.pc + 1 =>
            {
                sites.push(PowerSite {
                    pc: start,
                    width,
                    exponent: k,
                })
            }
            _ => bail!("unsupported difference at byte {pc}: only PUSH 2^k; MUL to PUSH k; SHL"),
        }
    }
    Ok(sites)
}

fn classify(instruction: &Instruction) -> Result<Obligation> {
    let op = instruction.bytes[0];
    let simple = |name: &str| Obligation::Same {
        op: format!("Operation.{name}"),
        arg: "none".to_owned(),
        same: format!("same_{}", name.to_lowercase()),
    };
    Ok(match op {
        0x60..=0x7f => {
            let width = instruction.bytes.len() - 1;
            Obligation::Same {
                op: format!("(Operation.Push .PUSH{width})"),
                arg: format!(
                    "(some (UInt256.ofNat {}, {width}))",
                    U256::from_be_slice(&instruction.bytes[1..])
                ),
                same: format!("(same_push .PUSH{width} (by decide))"),
            }
        }
        0x5f => Obligation::Same {
            op: "(Operation.Push .PUSH0)".to_owned(),
            arg: "none".to_owned(),
            same: "same_push0".to_owned(),
        },
        0x80..=0x8f => simple(&format!("DUP{}", op - 0x7f)),
        0x90..=0x9f => simple(&format!("SWAP{}", op - 0x8f)),
        0x56 => Obligation::Jump,
        0x57 => Obligation::Jumpi,
        0x00 => Obligation::Halt {
            op: "Operation.STOP",
            which: "(Or.inl rfl)",
            congruent: "congruent_stop",
        },
        0xf3 => Obligation::Halt {
            op: "Operation.RETURN",
            which: "(Or.inr (Or.inl rfl))",
            congruent: "congruent_return",
        },
        0xfd => Obligation::Halt {
            op: "Operation.REVERT",
            which: "(Or.inr (Or.inr rfl))",
            congruent: "congruent_revert",
        },
        0x0c..=0x0f
        | 0x1e..=0x1f
        | 0x21..=0x2f
        | 0x4b..=0x4f
        | 0xa5..=0xef
        | 0xf6..=0xf9
        | 0xfb..=0xfc
        | 0xfe => Obligation::Invalid,
        _ => match simple_name(op) {
            Some(name) => simple(name),
            None => bail!(
                "unsupported opcode 0x{op:02x} at pc {} for whole-program certificates",
                instruction.pc
            ),
        },
    })
}

fn simple_name(op: u8) -> Option<&'static str> {
    Some(match op {
        0x01 => "ADD",
        0x02 => "MUL",
        0x03 => "SUB",
        0x04 => "DIV",
        0x05 => "SDIV",
        0x06 => "MOD",
        0x07 => "SMOD",
        0x08 => "ADDMOD",
        0x09 => "MULMOD",
        0x0a => "EXP",
        0x0b => "SIGNEXTEND",
        0x10 => "LT",
        0x11 => "GT",
        0x12 => "SLT",
        0x13 => "SGT",
        0x14 => "EQ",
        0x15 => "ISZERO",
        0x16 => "AND",
        0x17 => "OR",
        0x18 => "XOR",
        0x19 => "NOT",
        0x1a => "BYTE",
        0x1b => "SHL",
        0x1c => "SHR",
        0x1d => "SAR",
        0x30 => "ADDRESS",
        0x32 => "ORIGIN",
        0x33 => "CALLER",
        0x34 => "CALLVALUE",
        0x35 => "CALLDATALOAD",
        0x36 => "CALLDATASIZE",
        0x3a => "GASPRICE",
        0x50 => "POP",
        0x51 => "MLOAD",
        0x52 => "MSTORE",
        0x53 => "MSTORE8",
        0x5b => "JUMPDEST",
        _ => return None,
    })
}

fn byte_array(code: &[u8]) -> String {
    let bytes: Vec<String> = code.iter().map(u8::to_string).collect();
    format!("⟨#[{}]⟩", bytes.join(", "))
}

fn word_array(values: &[usize]) -> String {
    let words: Vec<String> = values
        .iter()
        .map(|v| format!("UInt256.ofNat {v}"))
        .collect();
    format!("#[{}]", words.join(", "))
}

/// Obligations per point module; each module must compile within the
/// per-module proof budget.
const POINTS_PER_MODULE: usize = 64;

const HEADER: &str = "set_option Elab.async false\nset_option maxRecDepth 131072\nset_option maxHeartbeats 4000000\nopen EvmYul EvmYul.EVM GolfUpstream GolfCountOffset GolfComposition GolfWhole\nnamespace GolfWholeCertificate\n\n";

fn render(original: &[u8], candidate: &[u8], plan: &Plan) -> Vec<(String, String)> {
    let mut modules = Vec::new();
    let mut image = format!("import WholeProgram\n{HEADER}");
    let pcs: Vec<String> = plan
        .points
        .iter()
        .map(|(pc, _)| format!("UInt256.ofNat {pc}"))
        .collect();
    writeln!(
        image,
        "def oldCode : ByteArray := {}\ndef newCode : ByteArray := {}\ndef jumps : Array UInt256 := {}\ndef points : List UInt256 := [{}]\nabbrev P (pc : UInt256) : Prop := points.contains pc = true\n\ntheorem targets : ∀ x, jumps.contains x = true → P x :=\n  jumps_sub jumps points (by decide +kernel)\ntheorem old_jumps : D_J oldCode (UInt256.ofNat 0) = jumps := by decide +kernel\ntheorem new_jumps : D_J newCode (UInt256.ofNat 0) = jumps := by decide +kernel\nend GolfWholeCertificate",
        byte_array(original),
        byte_array(candidate),
        word_array(&plan.jumpdests),
        pcs.join(", ")
    )
    .unwrap();
    modules.push(("WholeImage".to_owned(), image));
    let chunks: Vec<_> = plan.points.chunks(POINTS_PER_MODULE).collect();
    for (index, chunk) in chunks.iter().enumerate() {
        let mut s = format!("import WholeImage\n{HEADER}");
        for (pc, obligation) in *chunk {
            writeln!(
                s,
                "theorem point_{pc} : Point oldCode newCode jumps P (UInt256.ofNat {pc}) :=\n  {}",
                obligation_term(obligation)
            )
            .unwrap();
        }
        s.push_str("end GolfWholeCertificate\n");
        modules.push((format!("WholePoints{index}"), s));
    }
    let imports: String = (0..chunks.len())
        .map(|i| format!("import WholePoints{i}\n"))
        .collect();
    let mut s = format!("{imports}{HEADER}");
    s.push_str("theorem cover : ∀ pc, P pc → Point oldCode newCode jumps P pc :=\n");
    for (pc, _) in &plan.points {
        writeln!(s, "  cover_cons point_{pc} <|").unwrap();
    }
    s.push_str(
        "  cover_nil

/-- From any pair of states at pc 0 that differ only in deployed code, execution
count and extra candidate gas, every successful or reverting original run of `X`
is matched by a candidate run with equal output and related final state. -/
theorem whole_certificate (owner : AccountAddress) (fuel surplus skipped : ℕ) (s t : State)
    (r : ExecutionResult State)
    (rel : DeployedOffset owner oldCode newCode surplus skipped s t)
    (start : s.pc = UInt256.ofNat 0)
    (ok : X fuel (D_J oldCode (UInt256.ofNat 0)) s = .ok r) :
    ∃ f r', X f (D_J newCode (UInt256.ofNat 0)) t = .ok r' ∧
      OutcomeRelated owner oldCode newCode r r' := by
  rw [old_jumps] at ok
  rw [new_jumps]
  exact whole_refines owner oldCode newCode jumps jumps P cover (fun _ h => h)
    fuel s t surplus skipped r rel (by rw [start]; decide +kernel) ok

#print axioms whole_certificate
end GolfWholeCertificate
",
    );
    modules.push(("WholeCertificate".to_owned(), s));
    modules
}

fn obligation_term(obligation: &Obligation) -> String {
    const K: &str = "(by decide +kernel)";
    match obligation {
        Obligation::Same { op, arg, same } => {
            format!(".same _ {op} {arg} {same}.1 {same}.2.1 {same}.2.2 {K} {K} {K}")
        }
        Obligation::Jump => format!(".jump _ {K} {K} targets"),
        Obligation::Jumpi => format!(".jumpi _ {K} {K} {K} targets"),
        Obligation::Halt {
            op,
            which,
            congruent,
        } => {
            format!(".halt _ {op} none {congruent} {which} {K} {K}")
        }
        Obligation::FallOff => {
            format!(".halt _ Operation.STOP none congruent_stop (Or.inl rfl) {K} {K}")
        }
        Obligation::Invalid => format!(".invalid _ {K}"),
        Obligation::Power(site) => format!(
            ".power _ .PUSH{} {} {} (by decide) (by decide) ⟨{K}, {K}⟩ ⟨{K}, {K}⟩ {K}",
            site.width, site.width, site.exponent
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn plans_power_site_and_rejects_other_differences() {
        let original = hex::decode("34600a576007600402005b600080fd").unwrap();
        let candidate = hex::decode("34600a57600760021b005b600080fd").unwrap();
        let planned = plan(&original, &candidate).unwrap();
        assert_eq!(planned.jumpdests, vec![10]);
        let pcs: Vec<usize> = planned.points.iter().map(|(pc, _)| *pc).collect();
        assert_eq!(pcs, vec![0, 1, 3, 4, 6, 9, 10, 11, 13, 14]);
        // Unreachable trailing bytes need no obligation.
        let tail = hex::decode("34600a576007600402005b600080fdf1").unwrap();
        assert_eq!(plan(&tail, &tail).unwrap().points.len(), 11);
        assert!(matches!(planned.points[4].1, Obligation::Power(_)));
        let wrong = hex::decode("34600a57600760031b005b600080fd").unwrap();
        assert!(plan_err(&original, &wrong).contains("unsupported difference"));
        let call = hex::decode("f100").unwrap();
        assert!(plan_err(&call, &call).contains("unsupported opcode 0xf1"));
    }

    fn plan_err(a: &[u8], b: &[u8]) -> String {
        match plan(a, b) {
            Ok(_) => String::new(),
            Err(error) => error.to_string(),
        }
    }
}
