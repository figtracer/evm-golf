//! Bounded discovery produces unverified data for the existing proposal gate.
use anyhow::Result;
use revm::primitives::{HashMap, hex, keccak256};

use super::{
    Instruction, MAX_PROPOSAL_SITES, Rewrite, RewriteProposalBatch, RewriteProposalSite, decode,
    layout, push_value, window_proposal,
};

// A finite heuristic, not exhaustive optimization. These bounds cover the
// observed compiler cleanup windows without changing proposal acceptance caps.
// Sixteen choices through depth four define 69,905 raw sequences; invalid
// prefixes are pruned before their descendants are visited.
const ALPHABET: [u8; 16] = [
    0x50, 0x80, 0x81, 0x82, 0x83, 0x84, 0x85, 0x86, 0x87, 0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96,
];
const MAX_REPLACEMENT_OPS: usize = 4;
const MIN_SOURCE_OPS: usize = 2;
const MAX_SOURCE_OPS: usize = 6;
const INPUT_WORDS: usize = 8;
const MAX_PEAK: usize = 2;

#[derive(Clone, Eq, PartialEq, Hash)]
struct State {
    // Every surviving input alias, including untouched inputs; a deeper tail
    // is never indexed by this bounded alphabet and derived input requirement.
    words: Vec<u8>,
    required: usize,
    peak: usize,
}

struct Replacement {
    ops: Vec<u8>,
    gas: u64,
}

struct Candidate {
    start: usize,
    end: usize,
    before: Vec<u8>,
    after: Vec<u8>,
    required: usize,
    saving: u64,
}

impl State {
    fn initial() -> Self {
        Self {
            words: (0..INPUT_WORDS as u8).collect(),
            required: 0,
            peak: 0,
        }
    }

    fn apply(&self, op: u8) -> Option<Self> {
        let mut next = self.clone();
        let need = match op {
            0x50 => 1,
            0x80..=0x87 => usize::from(op - 0x7f),
            0x90..=0x96 => usize::from(op - 0x8e),
            _ => return None,
        };
        let height = self.words.len() as isize - INPUT_WORDS as isize;
        next.required = next.required.max((need as isize - height).max(0) as usize);
        if next.required > INPUT_WORDS {
            return None;
        }
        match op {
            0x50 => {
                next.words.remove(0);
            }
            0x80..=0x87 => {
                let word = *next.words.get(usize::from(op - 0x80))?;
                next.words.insert(0, word);
            }
            _ => {
                let index = usize::from(op - 0x8f);
                if index >= next.words.len() {
                    return None;
                }
                next.words.swap(0, index);
            }
        }
        next.peak = next.peak.max(next.words.len().saturating_sub(INPUT_WORDS));
        (next.peak <= MAX_PEAK).then_some(next)
    }
}

fn enumerate(
    state: State,
    ops: &mut Vec<u8>,
    gas: u64,
    table: &mut HashMap<State, Vec<Replacement>>,
) {
    table.entry(state.clone()).or_default().push(Replacement {
        ops: ops.clone(),
        gas,
    });
    if ops.len() == MAX_REPLACEMENT_OPS {
        return;
    }
    for op in ALPHABET {
        if let Some(next) = state.apply(op) {
            ops.push(op);
            enumerate(next, ops, gas + if op == 0x50 { 2 } else { 3 }, table);
            ops.pop();
        }
    }
}

pub(super) fn discover(original: &[u8]) -> Result<RewriteProposalBatch> {
    let analysis = layout::analyze(original, true)?;
    let instructions = decode(original);
    let mut table = HashMap::default();
    enumerate(State::initial(), &mut Vec::new(), 0, &mut table);
    let mut eligibility = HashMap::<(Vec<u8>, Vec<u8>), bool>::default();
    let mut candidates = Vec::new();
    for (index, first) in instructions.iter().enumerate() {
        if !analysis.reachable.contains(&first.pc) {
            continue;
        }
        if let Some(candidate) = literal_candidate(&instructions[index..]) {
            candidates.push(candidate);
        }
        let mut state = State::initial();
        let mut source_ops = 0;
        let mut gas = 0;
        for instruction in instructions[index..].iter().take(MAX_SOURCE_OPS + 1) {
            let op = instruction.bytes[0];
            if ALPHABET.contains(&op) && source_ops < MAX_SOURCE_OPS {
                let Some(next) = state.apply(op) else {
                    break;
                };
                state = next;
                source_ops += 1;
                gas += if op == 0x50 { 2 } else { 3 };
                continue;
            }
            if source_ops < MIN_SOURCE_OPS || push_value(&instruction.bytes).is_none() {
                break;
            }
            let final_growth = state.words.len() as isize + 1 - INPUT_WORDS as isize;
            if state.peak.max(final_growth.max(0) as usize) > MAX_PEAK {
                break;
            }
            let end = instruction.pc + instruction.bytes.len();
            let before = &original[first.pc..end];
            let old_width = instruction.bytes.len() - 1;
            for replacement in table.get(&state).into_iter().flatten() {
                let Some(padding) = source_ops.checked_sub(replacement.ops.len()) else {
                    continue;
                };
                let width = old_width + padding;
                if width > 32 {
                    continue;
                }
                let old_gas = gas + if old_width == 0 { 2 } else { 3 };
                let new_gas = replacement.gas + if width == 0 { 2 } else { 3 };
                if new_gas >= old_gas {
                    continue;
                }
                let mut after = replacement.ops.clone();
                after.push(0x5f + width as u8);
                after.extend(std::iter::repeat_n(0, padding));
                after.extend_from_slice(&instruction.bytes[1..]);
                let eligible = *eligibility
                    .entry((before.to_vec(), after.clone()))
                    .or_insert_with(|| {
                        // Includes all 1,025 sufficient-gas fault heights. Matching
                        // aliases/profile alone does not equate DUP and SWAP faults.
                        window_proposal::certificate(before, &after).is_ok()
                    });
                if !eligible {
                    continue;
                }
                candidates.push(Candidate {
                    start: first.pc,
                    end,
                    before: before.to_vec(),
                    after,
                    required: state.required,
                    saving: old_gas - new_gas,
                });
            }
            break;
        }
    }
    candidates.sort_by(|a, b| {
        b.saving
            .cmp(&a.saving)
            .then_with(|| (a.end - a.start).cmp(&(b.end - b.start)))
            .then_with(|| a.start.cmp(&b.start))
            .then_with(|| a.after.cmp(&b.after))
    });
    let mut selected: Vec<Candidate> = Vec::new();
    for candidate in candidates {
        if selected
            .iter()
            .any(|old| candidate.start < old.end && old.start < candidate.end)
        {
            continue;
        }
        // Whole-image guards run in global rank order, avoiding scans for
        // dominated alternatives. A rejected candidate reserves no interval.
        let rewrite = Rewrite {
            original_pc: candidate.start,
            before: hex::encode(&candidate.before),
            after: hex::encode(&candidate.after),
            required_stack: candidate.required,
        };
        if layout::transform_proposal(&analysis, &rewrite).is_err() {
            continue;
        }
        selected.push(candidate);
        if selected.len() == MAX_PROPOSAL_SITES {
            break;
        }
    }
    selected.sort_by_key(|site| site.start);
    let rewrites: Vec<_> = selected
        .iter()
        .map(|site| Rewrite {
            original_pc: site.start,
            before: hex::encode(&site.before),
            after: hex::encode(&site.after),
            required_stack: site.required,
        })
        .collect();
    // A final combined check prevents independently eligible windows from
    // silently becoming an invalid catalog. It remains neither proof nor replay.
    layout::transform_proposals(&analysis, &rewrites)?;
    Ok(RewriteProposalBatch {
        original_keccak256: keccak256(original).to_string(),
        sites: rewrites
            .into_iter()
            .map(|site| RewriteProposalSite {
                original_pc: site.original_pc,
                before: site.before,
                after: site.after,
            })
            .collect(),
    })
}

// Literal-bearing windows missed by the stack-only enumeration. Every proposal
// still passes the shared symbolic/fault checker and the whole-image guards.
fn literal_candidate(instructions: &[Instruction]) -> Option<Candidate> {
    let first = instructions.first()?;
    let second = instructions.get(1)?;
    let third = instructions.get(2)?;
    let (count, after, saving) = if first.bytes == [0x5f]
        && (0x81..=0x88).contains(&second.bytes[0])
        && third.bytes == [0x01]
    {
        (3, vec![second.bytes[0] - 1, 0x5f, 0x50], 1)
    } else {
        let fourth = instructions.get(3)?;
        if first.bytes == [0x90]
            && push_value(&second.bytes).is_some()
            && second.bytes.len() <= 31
            && third.bytes == [0x91]
            && fourth.bytes == [0x90]
        {
            let mut after = vec![second.bytes[0] + 2, 0, 0];
            after.extend_from_slice(&second.bytes[1..]);
            after.push(0x91);
            (4, after, if second.bytes[0] == 0x5f { 5 } else { 6 })
        } else if push_value(&first.bytes).is_some()
            && first.bytes.len() <= 31
            && (0x91..=0x97).contains(&second.bytes[0])
            && third.bytes == [0x90]
            && fourth.bytes == second.bytes
        {
            // PUSH c; SWAPn; SWAP1; SWAPn = SWAP(n-1); PUSH c.
            // Widen the literal by two bytes to preserve all instruction offsets
            // outside the window. The shared checker still checks stack faults.
            let mut after = vec![second.bytes[0] - 1, first.bytes[0] + 2, 0, 0];
            after.extend_from_slice(&first.bytes[1..]);
            (4, after, if first.bytes[0] == 0x5f { 5 } else { 6 })
        } else if push_value(&first.bytes).is_some()
            && first.bytes.len() <= 31
            && instructions.get(1..6).is_some_and(|tail| {
                tail.iter()
                    .zip([0x90, 0x93, 0x92, 0x91, 0x90])
                    .all(|(instruction, op)| instruction.bytes == [op])
            })
        {
            let mut after = vec![0x92, 0x91, 0x90, first.bytes[0] + 2, 0, 0];
            after.extend_from_slice(&first.bytes[1..]);
            (6, after, if first.bytes[0] == 0x5f { 5 } else { 6 })
        } else if push_value(&first.bytes).is_some()
            && first.bytes.len() <= 31
            && instructions.get(1..7).is_some_and(|tail| {
                tail.iter()
                    .zip([0x81, 0x90, 0x50, 0x91, 0x90, 0x50])
                    .all(|(instruction, op)| instruction.bytes == [op])
            })
        {
            let mut after = vec![first.bytes[0] + 2, 0, 0];
            after.extend_from_slice(&first.bytes[1..]);
            after.extend([0x81, 0x50, 0x50, 0x90]);
            (7, after, if first.bytes[0] == 0x5f { 5 } else { 6 })
        } else if push_value(&first.bytes).is_some()
            && first.bytes.len() <= 32
            && instructions.get(1..6).is_some_and(|tail| {
                tail.iter()
                    .zip([0x82, 0x91, 0x50, 0x83, 0x90])
                    .all(|(instruction, op)| instruction.bytes == [op])
            })
        {
            let mut after = vec![0x81, 0x90, 0x50, 0x82, first.bytes[0] + 1, 0];
            after.extend_from_slice(&first.bytes[1..]);
            (6, after, if first.bytes[0] == 0x5f { 2 } else { 3 })
        } else if second.bytes == [0x16]
            && fourth.bytes == [0x16]
            && push_value(&first.bytes).is_some()
            && push_value(&first.bytes) == push_value(&third.bytes)
        {
            let mut after: Vec<_> = instructions[..4]
                .iter()
                .flat_map(|instruction| instruction.bytes.iter().copied())
                .collect();
            *after.last_mut()? = 0x50;
            (4, after, 1)
        } else {
            return None;
        }
    };
    let before: Vec<_> = instructions[..count]
        .iter()
        .flat_map(|instruction| instruction.bytes.iter().copied())
        .collect();
    let proof = window_proposal::certificate(&before, &after).ok()?;
    Some(Candidate {
        start: first.pc,
        end: first.pc + before.len(),
        before,
        after,
        required: proof.required,
        saving,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::runtime::from_hex;

    #[test]
    fn discovers_literal_windows_with_shared_certificate_guards() {
        for (before, after) in [
            ("5f8101", "805f50"),
            ("5f8801", "875f50"),
            ("906101c69190", "63000001c691"),
            ("905f9190", "61000091"),
            ("610f9a9093929190", "9291906300000f9a"),
            ("5f9093929190", "929190610000"),
            ("60ff1660ff16", "60ff1660ff50"),
            ("5f819050919050", "61000081505090"),
            ("6005819050919050", "6200000581505090"),
            ("5f8291508390", "819050826000"),
            ("60058291508390", "81905082610005"),
            ("6020939093", "9262000020"),
            ("6040919091", "9062000040"),
            ("5f979097", "96610000"),
        ] {
            let code = from_hex(&format!("5f5f5f5f5f5f5f5f{before}00")).unwrap();
            let batch = discover(&code).unwrap();
            assert_eq!(batch.sites.len(), 1, "{before}");
            assert_eq!(batch.sites[0].original_pc, 8);
            assert_eq!(batch.sites[0].before, before);
            assert_eq!(batch.sites[0].after, after);
        }
        for hidden in ["005f8101", "625f810100", "5f5f60ff1660fe1600"] {
            assert!(
                discover(&from_hex(hidden).unwrap())
                    .unwrap()
                    .sites
                    .is_empty()
            );
        }
    }

    #[test]
    fn literal_swap_conjugation_respects_push_and_stack_bounds() {
        for width in [0usize, 1, 30, 31, 32] {
            for swap in 0x91..=0x98 {
                let mut before = vec![0x5f + width as u8];
                before.extend(std::iter::repeat_n(0xff, width));
                before.extend([swap, 0x90, swap]);
                let candidate = literal_candidate(&decode(&before));
                if width <= 30 && swap <= 0x97 {
                    let candidate = candidate.unwrap();
                    assert_eq!(candidate.before.len(), candidate.after.len());
                    assert_eq!(candidate.required, usize::from(swap - 0x8f));
                    assert_eq!(candidate.after[0], swap - 1);
                    assert_eq!(candidate.after[1], 0x5f + width as u8 + 2);
                    assert_eq!(&candidate.after[4..], &before[1..1 + width]);
                } else {
                    assert!(candidate.is_none());
                }
            }
        }
    }

    #[test]
    fn discovers_deterministic_permutations_and_checked_dup_aliases() {
        for (before, expected) in [
            ("9092509050612270", "9150915062002270"),
            ("918291906020", "908192610020"),
        ] {
            let code = from_hex(&format!("5f5f5f5f5f5f5f5f{before}00")).unwrap();
            let a = discover(&code).unwrap();
            let b = discover(&code).unwrap();
            assert_eq!(
                serde_json::to_string(&a).unwrap(),
                serde_json::to_string(&b).unwrap()
            );
            assert_eq!(a.original_keccak256, keccak256(&code).to_string());
            assert_eq!(a.sites.len(), 1);
            assert_eq!(a.sites[0].original_pc, 8);
            assert_eq!(a.sites[0].before, before);
            assert_eq!(a.sites[0].after, expected);
        }
    }

    #[test]
    fn does_not_confuse_equal_profiles_with_equal_fault_classes() {
        let before = from_hex("9090506001").unwrap();
        let after = from_hex("5080506001").unwrap();
        assert!(window_proposal::certificate(&before, &after).is_err());
        let code = [vec![0x5f, 0x5f], before, vec![0]].concat();
        assert!(discover(&code).unwrap().sites.is_empty());
    }

    #[test]
    fn excludes_unreachable_windows_and_push_payloads() {
        let hidden = from_hex("00679092509050612270").unwrap();
        assert!(discover(&hidden).unwrap().sites.is_empty());
        assert!(discover(&[0x00]).unwrap().sites.is_empty());
    }
}
