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
// Up to two PUSH literals per window, modelled as opaque words distinct from
// inputs. In replacement op lists, these marker bytes place each literal.
const LITERAL_OPS: [u8; 2] = [0x5f, 0x60];

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
            0x5f | 0x60 => 0,
            0x50 => 1,
            0x80..=0x87 => usize::from(op - 0x7f),
            0x90..=0x97 => usize::from(op - 0x8e),
            _ => return None,
        };
        let height = self.words.len() as isize - INPUT_WORDS as isize;
        next.required = next.required.max((need as isize - height).max(0) as usize);
        if next.required > INPUT_WORDS {
            return None;
        }
        match op {
            0x5f | 0x60 => next.words.insert(0, 0xff - (op - 0x5f)),
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

/// Record sequences placing exactly `literals` opaque PUSH words (each marker
/// once) among up to MAX_REPLACEMENT_OPS stack ops. Gas excludes the PUSHes,
/// whose cost depends on the final immediate width.
fn enumerate(
    state: State,
    ops: &mut Vec<u8>,
    gas: u64,
    literals: usize,
    table: &mut HashMap<State, Vec<Replacement>>,
) {
    let placed = ops.iter().filter(|op| LITERAL_OPS.contains(op)).count();
    if placed == literals {
        table.entry(state.clone()).or_default().push(Replacement {
            ops: ops.clone(),
            gas,
        });
    }
    let stack_full = ops.len() - placed == MAX_REPLACEMENT_OPS;
    let pushes: Vec<_> = LITERAL_OPS[..literals]
        .iter()
        .copied()
        .filter(|op| !ops.contains(op))
        .collect();
    let stack = ALPHABET.into_iter().filter(|_| !stack_full);
    for op in stack.chain(pushes) {
        if let Some(next) = state.apply(op) {
            let cost = match op {
                0x50 => 2,
                op if LITERAL_OPS.contains(&op) => 0,
                _ => 3,
            };
            ops.push(op);
            enumerate(next, ops, gas + cost, literals, table);
            ops.pop();
        }
    }
}

fn push_gas(width: usize) -> u64 {
    if width == 0 { 2 } else { 3 }
}

/// Windows with one or two PUSH literals and up to MAX_SOURCE_OPS stack ops,
/// rewritten to any cheaper enumerated placement. PUSHes are widened by the
/// removed stack-op count to keep offsets fixed; the shared certificate filters.
fn literal_placements(
    instructions: &[Instruction],
    tables: &[HashMap<State, Vec<Replacement>>; 2],
    eligibility: &mut HashMap<(Vec<u8>, Vec<u8>), bool>,
) -> Option<Candidate> {
    let first = instructions.first()?;
    let mut state = State::initial();
    let mut stack_ops = 0;
    let mut stack_gas = 0;
    let mut literals: Vec<&[u8]> = Vec::new();
    let mut before = Vec::new();
    let mut best: Option<Candidate> = None;
    for instruction in instructions.iter().take(MAX_SOURCE_OPS + LITERAL_OPS.len()) {
        let op = instruction.bytes[0];
        let next = if literals.len() < LITERAL_OPS.len() && push_value(&instruction.bytes).is_some()
        {
            literals.push(&instruction.bytes[1..]);
            state.apply(LITERAL_OPS[literals.len() - 1])
        } else if (ALPHABET.contains(&op) || op == 0x97) && stack_ops < MAX_SOURCE_OPS {
            stack_ops += 1;
            stack_gas += if op == 0x50 { 2 } else { 3 };
            state.apply(op)
        } else {
            None
        };
        let Some(next) = next else { break };
        state = next;
        before.extend_from_slice(&instruction.bytes);
        if literals.is_empty() || stack_ops == 0 {
            continue;
        }
        let old_gas = stack_gas + literals.iter().map(|l| push_gas(l.len())).sum::<u64>();
        // Pad nonzero-width literals first: widening PUSH0 costs one gas.
        let mut order: Vec<_> = (0..literals.len()).collect();
        order.sort_by_key(|&i| literals[i].is_empty());
        let mut options: Vec<_> = tables[literals.len() - 1]
            .get(&state)
            .into_iter()
            .flatten()
            .filter_map(|replacement| {
                let mut padding =
                    (stack_ops + literals.len()).checked_sub(replacement.ops.len())?;
                let mut pads = vec![0; literals.len()];
                for &i in &order {
                    pads[i] = padding.min(32 - literals[i].len());
                    padding -= pads[i];
                }
                let gas = replacement.gas
                    + (0..literals.len())
                        .map(|i| push_gas(literals[i].len() + pads[i]))
                        .sum::<u64>();
                (padding == 0 && gas < old_gas).then_some((gas, pads, replacement))
            })
            .collect();
        options.sort_by(|a, b| a.0.cmp(&b.0).then_with(|| a.2.ops.cmp(&b.2.ops)));
        for (gas, pads, replacement) in options {
            if best
                .as_ref()
                .is_some_and(|best| best.saving >= old_gas - gas)
            {
                break;
            }
            let mut after = Vec::with_capacity(before.len());
            for &op in &replacement.ops {
                if let Some(i) = LITERAL_OPS.iter().position(|&marker| marker == op) {
                    after.push(0x5f + (literals[i].len() + pads[i]) as u8);
                    after.extend(std::iter::repeat_n(0, pads[i]));
                    after.extend_from_slice(literals[i]);
                } else {
                    after.push(op);
                }
            }
            let eligible = *eligibility
                .entry((before.clone(), after.clone()))
                .or_insert_with(|| window_proposal::check(&before, &after).is_ok());
            if eligible {
                best = Some(Candidate {
                    start: first.pc,
                    end: first.pc + before.len(),
                    before: before.clone(),
                    after,
                    required: state.required,
                    saving: old_gas - gas,
                });
                break;
            }
        }
    }
    best
}

pub(super) fn discover(original: &[u8]) -> Result<RewriteProposalBatch> {
    let analysis = layout::analyze(original, true)?;
    let instructions = decode(original);
    let [table, one, two] = [0, 1, 2].map(|literals| {
        let mut table = HashMap::default();
        enumerate(State::initial(), &mut Vec::new(), 0, literals, &mut table);
        table
    });
    let literal_tables = [one, two];
    let mut eligibility = HashMap::<(Vec<u8>, Vec<u8>), bool>::default();
    let mut candidates = Vec::new();
    for (index, first) in instructions.iter().enumerate() {
        if !analysis.reachable.contains(&first.pc) {
            continue;
        }
        if let Some(candidate) = literal_candidate(&instructions[index..]) {
            candidates.push(candidate);
        }
        if let Some(candidate) =
            literal_placements(&instructions[index..], &literal_tables, &mut eligibility)
        {
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
                        window_proposal::check(before, &after).is_ok()
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
            && fourth.bytes == second.bytes
            && (((0x91..=0x97).contains(&second.bytes[0]) && third.bytes == [0x90])
                || (second.bytes == [0x90] && (0x91..=0x97).contains(&third.bytes[0])))
        {
            // Either SWAPn; SWAP1; SWAPn or SWAP1; SWAPn; SWAP1
            // after PUSH c becomes SWAP(n-1); PUSH c.
            // Widen the literal by two bytes to preserve all instruction offsets
            // outside the window. The shared checker still checks stack faults.
            let swap = second.bytes[0].max(third.bytes[0]);
            let mut after = vec![swap - 1, first.bytes[0] + 2, 0, 0];
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
    let required = window_proposal::check(&before, &after).ok()?;
    Some(Candidate {
        start: first.pc,
        end: first.pc + before.len(),
        before,
        after,
        required,
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
            ("613140909190", "906300003140"),
            ("5f909790", "96610000"),
            ("60208190", "80610020"),
            ("506116c392505050", "50505050620016c3"),
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
                for permutation in [[swap, 0x90, swap], [0x90, swap, 0x90]] {
                    let mut before = vec![0x5f + width as u8];
                    before.extend(std::iter::repeat_n(0xff, width));
                    before.extend(permutation);
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
    }

    #[test]
    fn literal_placement_respects_push_width_and_literal_count() {
        let tables = [1, 2].map(|literals| {
            let mut table = HashMap::default();
            enumerate(State::initial(), &mut Vec::new(), 0, literals, &mut table);
            table
        });
        let mut eligibility = HashMap::default();
        // PUSHw c; DUP2; SWAP1 = DUP1; PUSH(w+1) c, only while w + 1 <= 32.
        for width in [0usize, 1, 31, 32] {
            let mut before = vec![0x5f + width as u8];
            before.extend(std::iter::repeat_n(0xab, width));
            before.extend([0x81, 0x90]);
            let found = literal_placements(&decode(&before), &tables, &mut eligibility);
            if width < 32 {
                let found = found.unwrap();
                let mut after = vec![0x80, 0x60 + width as u8, 0];
                after.extend(std::iter::repeat_n(0xab, width));
                assert_eq!((found.before, found.after), (before, after));
            } else {
                assert!(found.is_none());
            }
        }
        // Two literals swap by reordering the PUSHes; the nonzero one is widened.
        for (before, after) in [
            ("600160029000", "6002610001"),
            ("5f60029000", "6100025f00"),
            ("5f5f9000", "5f60000000"),
        ] {
            let found = literal_placements(
                &decode(&from_hex(before).unwrap()),
                &tables,
                &mut eligibility,
            )
            .unwrap();
            assert_eq!(
                hex::encode(found.after),
                &after[..found.before.len() * 2],
                "{before}"
            );
        }
        // A third literal ends the window.
        assert!(
            literal_placements(
                &decode(&[0x60, 1, 0x60, 2, 0x60, 3]),
                &tables,
                &mut eligibility
            )
            .is_none()
        );
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
        // CALLDATASIZE supplies stack words without forming a literal window.
        let code = [vec![0x36, 0x36], before, vec![0]].concat();
        assert!(discover(&code).unwrap().sites.is_empty());
    }

    #[test]
    fn excludes_unreachable_windows_and_push_payloads() {
        let hidden = from_hex("00679092509050612270").unwrap();
        assert!(discover(&hidden).unwrap().sites.is_empty());
        assert!(discover(&[0x00]).unwrap().sites.is_empty());
    }
}
