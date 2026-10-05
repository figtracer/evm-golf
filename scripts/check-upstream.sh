#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
bash scripts/setup-upstream.sh --check

# Test the real CLI and kernel path, keeping every generated artifact outside git.
work="$(mktemp -d "${TMPDIR:-/tmp}/evm-golf-region.XXXXXX")"
printf '%s\n' 60200201905f808061123456 > "$work/original.hex"
printf '%s\n' 60051b01905f808061123456 > "$work/candidate.hex"
if ! cargo run --locked -- certify-runtime-region \
  --original "$work/original.hex" --candidate "$work/candidate.hex" \
  --entry-pc 0 --out "$work/accepted"; then
  cat "$work/accepted"/*.log 2>/dev/null || true
  echo "Failed certificate evidence: $work" >&2
  exit 1
fi
python3 - "$work/accepted/result.json" <<'PY'
import json
import sys

with open(sys.argv[1]) as handle:
    report = json.load(handle)
assert report["entry_pc"] == 0 and report["exit_pc"] == 11
assert report["pushed_destination"] == 0x1234
assert report["source_gas_minimum"] == 25
assert report["gas_surplus_increase"] == 2
assert report["maximum_tail_length"] == 1018
assert "whole-contract equivalence" in report["unproved"]
PY
printf '%s\n' 60061b01905f808061123456 > "$work/wrong.hex"
if cargo run --locked -- certify-runtime-region \
  --original "$work/original.hex" --candidate "$work/wrong.hex" \
  --entry-pc 0 --out "$work/rejected"; then
  echo 'Incorrect candidate was accepted.' >&2
  exit 1
fi
[[ ! -e "$work/rejected/result.json" ]]
# Exact canonical mask region at a nonzero internal PC; surrounding bytes differ.
printf '%s\n' 00006001600160e01b03166001600160e01b031900 > "$work/mask-original.hex"
printf '%s\n' fefe6001600160e01b03166400ffffffff60e01b5b > "$work/mask-candidate.hex"
if ! cargo run --locked -- certify-runtime-region \
  --original "$work/mask-original.hex" --candidate "$work/mask-candidate.hex" \
  --entry-pc 2 --out "$work/mask-accepted"; then
  cat "$work/mask-accepted"/*.log 2>/dev/null || true
  echo "Failed mask certificate evidence: $work" >&2
  exit 1
fi
python3 - "$work/accepted" "$work/mask-accepted" <<'PY'
import json
import pathlib
import sys

legacy, mask = map(pathlib.Path, sys.argv[1:])
report = json.loads((mask / "result.json").read_text())
assert report["entry_pc"] == 2 and report["exit_pc"] == 20
assert report["source_instruction_count"] == 12
assert report["candidate_instruction_count"] == 9
assert report["execution_count_offset_increase"] == 3
assert report["source_gas_minimum"] == 36
assert report["candidate_gas_cost"] == 27
assert report["gas_surplus_increase"] == 9
assert report["maximum_tail_length"] == 1020
assert "pushed_destination" not in report
assert "whole-contract equivalence" in report["unproved"]
for module in ("CountOffset", "MaskSupport", "CanonicalMask"):
    assert not (legacy / f"{module}.lean").exists()
    assert (mask / f"{module}.olean").is_file()
PY
# At entry zero with exactly the region bytes, both surrounding segments are empty.
printf '%s\n' 6001600160e01b03166001600160e01b0319 > "$work/mask-empty-original.hex"
printf '%s\n' 6001600160e01b03166400ffffffff60e01b > "$work/mask-empty-candidate.hex"
if ! cargo run --locked -- certify-runtime-region \
  --original "$work/mask-empty-original.hex" --candidate "$work/mask-empty-candidate.hex" \
  --entry-pc 0 --out "$work/mask-empty-accepted"; then
  cat "$work/mask-empty-accepted"/*.log 2>/dev/null || true
  echo "Failed empty-segment mask certificate evidence: $work" >&2
  exit 1
fi
python3 - "$work/mask-empty-accepted/result.json" <<'PY_CHECK'
import json
import sys

with open(sys.argv[1]) as handle:
    report = json.load(handle)
assert report["entry_pc"] == 0 and report["exit_pc"] == 18
assert report["source_instruction_count"] == 12
assert report["candidate_instruction_count"] == 9
assert report["source_gas_minimum"] == 36 and report["candidate_gas_cost"] == 27
PY_CHECK
printf '%s\n' fefe6001600160e01b03166400fffffffe60e01b5b > "$work/mask-wrong.hex"
if cargo run --locked -- certify-runtime-region \
  --original "$work/mask-original.hex" --candidate "$work/mask-wrong.hex" \
  --entry-pc 2 --out "$work/mask-rejected"; then
  echo 'Incorrect mask candidate was accepted.' >&2
  exit 1
fi
[[ ! -e "$work/mask-rejected/result.json" ]]

# An explicit span composes the mask with a power rewrite before STOP.
printf '%s\n' 6001600160e01b03166001600160e01b031960200200 > "$work/span-original.hex"
printf '%s\n' 6001600160e01b03166400ffffffff60e01b60051b00 > "$work/span-candidate.hex"
if ! cargo run --locked -- certify-runtime-region \
  --original "$work/span-original.hex" --candidate "$work/span-candidate.hex" \
  --entry-pc 0 --exit-pc 21 --out "$work/span-accepted"; then
  cat "$work/span-accepted"/*.log 2>/dev/null || true
  echo "Failed span certificate evidence: $work" >&2
  exit 1
fi
python3 - "$work/span-accepted/result.json" <<'PY_SPAN'
import json
import sys

with open(sys.argv[1]) as handle:
    report = json.load(handle)
assert report["entry_pc"] == 0 and report["exit_pc"] == 21
assert report["source_instruction_count"] == 14
assert report["candidate_instruction_count"] == 11
assert report["source_gas_minimum"] == 44
assert report["candidate_gas_cost"] == 33
assert report["gas_surplus_increase"] == 11
assert report["execution_count_offset_increase"] == 3
assert report["required_input_stack_words"] == 1
assert report["maximum_input_stack_words"] == 1021
assert report["output_stack_delta"] == 1
assert "whole-contract and all-gas equivalence" in report["unproved"]
PY_SPAN
# The same selection cannot include the terminal instruction or end in PUSH data.
for end in 19 22; do
  if cargo run --locked -- certify-runtime-region \
    --original "$work/span-original.hex" --candidate "$work/span-candidate.hex" \
    --entry-pc 0 --exit-pc "$end" --out "$work/span-rejected-$end"; then
    echo 'Unsupported span was accepted.' >&2
    exit 1
  fi
  [[ ! -e "$work/span-rejected-$end/result.json" ]]
done

# Cover every supported unchanged opcode family with an arbitrary input tail.
printf '%s\n' 5f80600190017f0000000000000000000000000000000000000000000000000000000000000002021b > "$work/unchanged-span.hex"
if ! cargo run --locked -- certify-runtime-region \
  --original "$work/unchanged-span.hex" --candidate "$work/unchanged-span.hex" \
  --entry-pc 0 --exit-pc 41 --out "$work/unchanged-span-accepted"; then
  cat "$work/unchanged-span-accepted"/*.log 2>/dev/null || true
  echo "Failed unchanged span certificate evidence: $work" >&2
  exit 1
fi
python3 - "$work/unchanged-span-accepted/result.json" <<'PY_UNCHANGED'
import json
import sys

with open(sys.argv[1]) as handle:
    report = json.load(handle)
assert report["entry_pc"] == 0 and report["exit_pc"] == 41
assert report["source_instruction_count"] == report["candidate_instruction_count"] == 8
assert report["source_gas_minimum"] == report["candidate_gas_cost"] == 25
assert report["gas_surplus_increase"] == report["execution_count_offset_increase"] == 0
assert report["required_input_stack_words"] == 0
assert report["maximum_input_stack_words"] == 1021
assert report["output_stack_delta"] == 1
PY_UNCHANGED

# Exercise SUB operand order, unary NOT, and AND with an arbitrary input tail.
printf '%s\n' 600760020319600f16 > "$work/extra-span.hex"
if ! cargo run --locked -- certify-runtime-region \
  --original "$work/extra-span.hex" --candidate "$work/extra-span.hex" \
  --entry-pc 0 --exit-pc 9 --out "$work/extra-span-accepted"; then
  cat "$work/extra-span-accepted"/*.log 2>/dev/null || true
  echo "Failed arithmetic span certificate evidence: $work" >&2
  exit 1
fi
python3 - "$work/extra-span-accepted/result.json" <<'PY_EXTRA'
import json
import sys

with open(sys.argv[1]) as handle:
    report = json.load(handle)
assert report["entry_pc"] == 0 and report["exit_pc"] == 9
assert report["source_instruction_count"] == report["candidate_instruction_count"] == 6
assert report["source_gas_minimum"] == report["candidate_gas_cost"] == 18
assert report["gas_surplus_increase"] == report["execution_count_offset_increase"] == 0
assert report["required_input_stack_words"] == 0
assert report["maximum_input_stack_words"] == 1022
assert report["output_stack_delta"] == 1
PY_EXTRA

# All exchange depths followed by OR exercise symbolic stack lengths and ordering.
printf '%s\n' 909192939495969798999a9b9c9d9e9f17 > "$work/swaps.hex"
cargo run --locked -- certify-runtime-region \
  --original "$work/swaps.hex" --candidate "$work/swaps.hex" \
  --entry-pc 0 --exit-pc 17 --out "$work/swaps-accepted"
python3 - "$work/swaps-accepted/result.json" <<'PY_SWAPS'
import json
import sys

with open(sys.argv[1]) as handle:
    report = json.load(handle)
assert report["entry_pc"] == 0 and report["exit_pc"] == 17
assert report["source_instruction_count"] == report["candidate_instruction_count"] == 17
assert report["source_gas_minimum"] == report["candidate_gas_cost"] == 51
assert report["required_input_stack_words"] == 17
assert report["maximum_input_stack_words"] == 1024
assert report["output_stack_delta"] == -1
assert report["gas_surplus_increase"] == report["execution_count_offset_increase"] == 0
PY_SWAPS

# Repeated memory writes followed by a rewrite with different instruction counts.
printf '%s\n' 52526001600160e01b03166001600160e01b0319 > "$work/memory-original.hex"
printf '%s\n' 52526001600160e01b03166400ffffffff60e01b > "$work/memory-candidate.hex"
cargo run --locked -- certify-runtime-region \
  --original "$work/memory-original.hex" --candidate "$work/memory-candidate.hex" \
  --entry-pc 0 --exit-pc 20 --out "$work/memory-accepted"
python3 - "$work/memory-accepted/result.json" <<'PY_MEMORY'
import json
import sys

with open(sys.argv[1]) as handle:
    report = json.load(handle)
assert report["source_instruction_count"] == 14
assert report["candidate_instruction_count"] == 11
assert report["source_base_gas"] == 42 and report["candidate_base_gas"] == 33
assert report["required_input_stack_words"] == 5
assert report["maximum_input_stack_words"] == 1024
assert report["memory_operations"] == 2 and report["output_stack_delta"] == -3
assert report["gas_surplus_increase"] == 9
assert report["execution_count_offset_increase"] == 3
assert "source_gas_minimum" not in report
assert "sourceCost" in report["gas_requirement"]
PY_MEMORY

# Terminal certificates execute STOP/RETURN rather than leave a residual suffix.
printf '%s\n' 600760200200 > "$work/stop-original.hex"
printf '%s\n' 600760051b00 > "$work/stop-candidate.hex"
printf '%s\n' 60076020025f5260205ff3 > "$work/return-original.hex"
printf '%s\n' 600760051b5f5260205ff3 > "$work/return-candidate.hex"
for terminal in stop return; do
  end=5
  [[ "$terminal" != return ]] || end=10
  if ! cargo run --locked -- certify-runtime-region \
    --original "$work/$terminal-original.hex" --candidate "$work/$terminal-candidate.hex" \
    --entry-pc 0 --exit-pc "$end" --through-halt --out "$work/$terminal-accepted"; then
    cat "$work/$terminal-accepted"/*.log 2>/dev/null || true
    echo "Failed terminal certificate evidence: $work" >&2
    exit 1
  fi
done
python3 - "$work/stop-accepted" "$work/return-accepted" <<'PY_TERMINAL'
import json
import pathlib
import sys

for path, terminal, pc, exit_pc, count, source_gas, target_gas, stores, delta in [
    (sys.argv[1], "STOP", 5, 5, 4, 11, 9, 0, 1),
    (sys.argv[2], "RETURN", 10, 11, 8, 21, 19, 1, 0),
]:
    path = pathlib.Path(path)
    report = json.loads((path / "result.json").read_text())
    assert report["terminal"] == terminal and report["terminal_pc"] == pc
    assert report["entry_pc"] == 0 and report["exit_pc"] == exit_pc
    assert report["source_instruction_count"] == report["candidate_instruction_count"] == count
    assert report["source_base_gas"] == source_gas and report["candidate_base_gas"] == target_gas
    assert report["memory_operations"] == stores and report["output_stack_delta"] == delta
    assert report["required_input_stack_words"] == 0
    assert report["gas_surplus_increase"] == 2 and report["execution_count_offset_increase"] == 0
    assert report["proof_root"] == "GolfCertificates.Terminal.terminal_success"
    assert "sourceCost(initial state)" in report["gas_requirement"]
    assert "source_gas_minimum" not in report
    assert "entry reachability" in report["unproved"]
    assert (path / "TerminalProof.olean").is_file()
    assert "'GolfCertificates.Terminal.terminal_success' depends on axioms:" in (path / "TerminalProof.log").read_text()
    if terminal == "RETURN":
        assert "RETURN expansion evaluated after the body" in report["gas_requirement"]
        assert "size.toNat < 2^64" in report["output_condition"]
    else:
        assert "empty canonical output" in report["output_condition"]
PY_TERMINAL
# Invalid terminal opcode, PUSH payload boundary, and missing explicit terminal byte.
for end in 4 3 6; do
  if cargo run --locked -- certify-runtime-region \
    --original "$work/stop-original.hex" --candidate "$work/stop-candidate.hex" \
    --entry-pc 0 --exit-pc "$end" --through-halt --out "$work/halt-rejected-$end"; then
    echo 'Invalid terminal boundary was accepted.' >&2
    exit 1
  fi
  [[ ! -e "$work/halt-rejected-$end" ]]
done
if cargo run --locked -- certify-runtime-region \
  --original "$work/stop-original.hex" --candidate "$work/stop-candidate.hex" \
  --entry-pc 0 --through-halt --out "$work/halt-missing-exit"; then
  echo 'Terminal selection without --exit-pc was accepted.' >&2
  exit 1
fi
[[ ! -e "$work/halt-missing-exit" ]]
if cargo run --locked -- certify-runtime-region \
  --original "$work/stop-original.hex" --candidate "$work/stop-candidate.hex" \
  --entry-pc 0 --exit-pc 5 --through-halt --through-jump --out "$work/halt-conflict"; then
  echo 'Conflicting terminal and jump selection was accepted.' >&2
  exit 1
fi
[[ ! -e "$work/halt-conflict" ]]

# Exercise the separate fresh-entry STOP template.
if ! cargo run --locked -- certify-runtime-region \
  --original "$work/stop-original.hex" --candidate "$work/stop-candidate.hex" \
  --entry-pc 0 --exit-pc 5 --through-halt --from-call-entry --out "$work/call-entry-stop-accepted"; then
  cat "$work/call-entry-stop-accepted"/*.log 2>/dev/null || true
  echo "Failed call-entry STOP certificate evidence: $work" >&2
  exit 1
fi
python3 - "$work/call-entry-stop-accepted" <<'PY_CALL_STOP'
import json
import pathlib
import sys

path = pathlib.Path(sys.argv[1])
report = json.loads((path / "result.json").read_text())
assert report["entry_pc"] == 0 and report["terminal_pc"] == report["exit_pc"] == 5
assert report["terminal"] == "STOP" and report["required_input_stack_words"] == 0
assert report["source_instruction_count"] == report["candidate_instruction_count"] == 4
assert report["source_base_gas"] == 11 and report["candidate_base_gas"] == 9
assert report["proof_root"] == "GolfCertificates.CallEntry.call_entry_success"
assert (path / "CallEntryProof.olean").is_file()
assert "'GolfCertificates.CallEntry.call_entry_success' depends on axioms:" in (path / "CallEntryProof.log").read_text()
PY_CALL_STOP

# The same RETURN path is now rooted at fresh canonical call entry, not a supplied stack.
if ! cargo run --locked -- certify-runtime-region \
  --original "$work/return-original.hex" --candidate "$work/return-candidate.hex" \
  --entry-pc 0 --exit-pc 10 --through-halt --from-call-entry --out "$work/call-entry-accepted"; then
  cat "$work/call-entry-accepted"/*.log 2>/dev/null || true
  echo "Failed call-entry certificate evidence: $work" >&2
  exit 1
fi
python3 - "$work/call-entry-accepted" <<'PY_CALL_ENTRY'
import json
import pathlib
import sys

path = pathlib.Path(sys.argv[1])
report = json.loads((path / "result.json").read_text())
assert report["entry_pc"] == 0 and report["terminal_pc"] == 10 and report["exit_pc"] == 11
assert report["terminal"] == "RETURN" and report["required_input_stack_words"] == 0
assert report["source_instruction_count"] == report["candidate_instruction_count"] == 8
assert report["source_base_gas"] == 21 and report["candidate_base_gas"] == 19
assert report["proof_root"] == "GolfCertificates.CallEntry.call_entry_success"
assert (path / "CallEntryProof.olean").is_file() and (path / "XiEntry.olean").is_file()
assert "'GolfCertificates.CallEntry.call_entry_success' depends on axioms:" in (path / "CallEntryProof.log").read_text()
PY_CALL_ENTRY
if cargo run --locked -- certify-runtime-region \
  --original "$work/stop-original.hex" --candidate "$work/stop-candidate.hex" \
  --entry-pc 2 --exit-pc 5 --through-halt --from-call-entry --out "$work/call-entry-nonzero"; then
  echo 'Nonzero fresh call entry was accepted.' >&2
  exit 1
fi
[[ ! -e "$work/call-entry-nonzero" ]]
printf '%s\n' 5200 > "$work/call-entry-underflow.hex"
if cargo run --locked -- certify-runtime-region \
  --original "$work/call-entry-underflow.hex" --candidate "$work/call-entry-underflow.hex" \
  --entry-pc 0 --exit-pc 1 --through-halt --from-call-entry --out "$work/call-entry-underflow"; then
  echo 'Call-entry path requiring supplied stack words was accepted.' >&2
  exit 1
fi
[[ ! -e "$work/call-entry-underflow" ]]
if cargo run --locked -- certify-runtime-region \
  --original "$work/stop-original.hex" --candidate "$work/stop-candidate.hex" \
  --entry-pc 0 --exit-pc 5 --from-call-entry --out "$work/call-entry-missing-halt"; then
  echo 'Call-entry mode without terminal mode was accepted.' >&2
  exit 1
fi
[[ ! -e "$work/call-entry-missing-halt" ]]

# The body accepts an empty stack, but RETURN still needs its second operand.
printf '%s\n' 5ff3 > "$work/call-entry-return-underflow.hex"
if cargo run --locked -- certify-runtime-region \
  --original "$work/call-entry-return-underflow.hex" --candidate "$work/call-entry-return-underflow.hex" \
  --entry-pc 0 --exit-pc 1 --through-halt --from-call-entry --out "$work/call-entry-return-underflow"; then
  echo 'Call-entry RETURN with only one output operand was accepted.' >&2
  exit 1
fi
[[ ! -e "$work/call-entry-return-underflow" ]]

# Canonical LT and ISZERO compose from an empty call-entry stack through STOP.
printf '%s\n' 60076002101500 > "$work/compare-stop.hex"
if ! cargo run --locked -- certify-runtime-region \
  --original "$work/compare-stop.hex" --candidate "$work/compare-stop.hex" \
  --entry-pc 0 --exit-pc 6 --through-halt --from-call-entry --out "$work/compare-stop-accepted"; then
  cat "$work/compare-stop-accepted"/*.log 2>/dev/null || true
  echo "Failed comparison certificate evidence: $work" >&2
  exit 1
fi
python3 - "$work/compare-stop-accepted/result.json" <<'PY_COMPARE_STOP'
import json
import sys

with open(sys.argv[1]) as handle:
    report = json.load(handle)
assert report["entry_pc"] == 0 and report["terminal_pc"] == report["exit_pc"] == 6
assert report["terminal"] == "STOP"
assert report["source_instruction_count"] == report["candidate_instruction_count"] == 5
assert report["source_base_gas"] == report["candidate_base_gas"] == 12
assert report["gas_surplus_increase"] == report["execution_count_offset_increase"] == 0
assert report["required_input_stack_words"] == 0 and report["output_stack_delta"] == 1
assert report["proof_root"] == "GolfCertificates.CallEntry.call_entry_success"
PY_COMPARE_STOP

echo "Upstream region checks passed. Local evidence: $work"
