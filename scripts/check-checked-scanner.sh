#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

# Validate an existing installation only; this gate never downloads or builds it.
bash scripts/setup-upstream.sh --check --checked-scanner
work="$(mktemp -d "${TMPDIR:-/tmp}/evm-golf-checked-scanner.XXXXXX")"
trap 'status=$?; if [[ $status -ne 0 ]]; then echo "Checked-scanner failure evidence: $work" >&2; fi' EXIT
printf 'Checked-scanner evidence: %s\n' "$work"
printf '%s\n' 60200201905f808061000c565b00 > "$work/forward-original.hex"
printf '%s\n' 60051b01905f808061000c565b00 > "$work/forward-candidate.hex"
printf '%s\n' 5b60200201905f80806100005600 > "$work/backward-original.hex"
printf '%s\n' 5b60051b01905f80806100005600 > "$work/backward-candidate.hex"

for name in forward backward; do
  entry=0
  destination=12
  if [[ "$name" == backward ]]; then entry=1; destination=0; fi
  cargo run --locked -- certify-runtime-region \
    --original "$work/$name-original.hex" --candidate "$work/$name-candidate.hex" \
    --entry-pc "$entry" --through-jump --out "$work/$name-accepted" \
    2>&1 | tee "$work/$name.log"
  python3 - "$work/$name-accepted" "$entry" "$destination" <<'PY'
import json
import pathlib
import sys

out = pathlib.Path(sys.argv[1])
report = json.loads((out / "result.json").read_text())
environment = json.loads((out / "environment.json").read_text())
assert report["claim"] == "conditional checked-scanner internal path through JUMP"
assert report["entry_pc"] == int(sys.argv[2])
assert report["exit_pc"] == report["pushed_destination"] == int(sys.argv[3])
assert report["source_gas_minimum"] == 33
assert report["gas_surplus_increase"] == 2
assert report["maximum_tail_length"] == 1018
assert report["output_stack"] == "0 :: 0 :: 0 :: c :: (32*a+b modulo 2^256) :: tail"
assert report["interpreter_fuel"] == (
    "for every natural fuel, each X(fuel+10) reduces to its own X(fuel+1) at the destination"
)
assert "whole-contract equivalence" in report["unproved"]
assert "equivalence with the original opaque upstream scanner" in report["unproved"]
assert "exit JUMP execution" not in report["unproved"]
profile = environment["semantics_profile"]
assert profile["identity"] == "evm-golf-checked-scanner"
assert profile["base_revision"] == environment["upstream_revision"]
assert profile["original_opaque_scanner_equality_proved"] is False
manifest = json.loads(pathlib.Path(profile["manifest"]).read_text())
assert profile["overlay_sha256"] == manifest["inputs"]["overlay_sha256"]
assert profile["revised_source_sha256"] == manifest["inputs"]["revised_source_sha256"]
assert profile["semantics_object_sha256"] == manifest["build"]["object_sha256"]
assert environment["module_timeout_seconds"] == 45
assert len(bytes.fromhex((out / "original.hex").read_text())) == 14
assert len(bytes.fromhex((out / "candidate.hex").read_text())) == 14
PY
 done

# A mask rewrite exercises unequal instruction counts through the same JUMP.
printf '%s\n' 6001600160e01b03166001600160e01b03196015565b00 > "$work/mask-original.hex"
printf '%s\n' 6001600160e01b03166400ffffffff60e01b6015565b00 > "$work/mask-candidate.hex"
cargo run --locked -- certify-runtime-region \
  --original "$work/mask-original.hex" --candidate "$work/mask-candidate.hex" \
  --entry-pc 0 --exit-pc 20 --through-jump --out "$work/mask-accepted" \
  2>&1 | tee "$work/mask.log"
python3 - "$work/mask-accepted" <<'PY_CHECK'
import json
import pathlib
import sys

out = pathlib.Path(sys.argv[1])
report = json.loads((out / "result.json").read_text())
assert report["claim"] == "conditional checked-scanner internal span through JUMP"
assert report["jump_pc"] == 20
assert report["exit_pc"] == report["pushed_destination"] == 21
assert report["source_instruction_count"] == 14
assert report["candidate_instruction_count"] == 11
assert report["source_gas_minimum"] == 47
assert report["candidate_gas_cost"] == 38
assert report["gas_surplus_increase"] == 9
assert report["execution_count_offset_increase"] == 3
assert report["required_input_stack_words"] == 1
assert report["maximum_input_stack_words"] == 1021
assert report["output_stack_delta"] == 1
assert "whole-contract and all-gas equivalence" in report["unproved"]
assert "original opaque upstream scanner is unproved" in report["scanner_scope"]
assert json.loads((out / "environment.json").read_text())["semantics_profile"]["identity"] == "evm-golf-checked-scanner"
PY_CHECK

# Only the candidate loses the real JUMPDEST. Rejecting either-side mismatch matters.
printf '%s\n' 60051b01905f808061000c560000 > "$work/invalid-candidate.hex"
# Byte13 is 0x5b, but belongs to the PUSH1 payload beginning at byte12.
printf '%s\n' 60200201905f808061000d56605b00 > "$work/payload-original.hex"
printf '%s\n' 60051b01905f808061000d56605b00 > "$work/payload-candidate.hex"
for name in one-image-invalid payload invalid-span-exit; do
  original="$work/forward-original.hex"
  candidate="$work/forward-candidate.hex"
  extra=()
  case "$name" in
    one-image-invalid) candidate="$work/invalid-candidate.hex" ;;
    payload) original="$work/payload-original.hex"; candidate="$work/payload-candidate.hex" ;;
    invalid-span-exit) extra=(--exit-pc 10) ;;
  esac
  if cargo run --locked -- certify-runtime-region \
    --original "$original" --candidate "$candidate" --entry-pc 0 --through-jump \
    "${extra[@]}" --out "$work/$name-rejected" 2>&1 | tee "$work/$name.log"; then
    echo "Invalid checked-scanner case accepted: $name" >&2
    exit 1
  fi
  python3 - "$work/$name-rejected" "$work/$name.log" "$name" <<'PY'
import pathlib
import sys

out, log = map(pathlib.Path, sys.argv[1:3])
assert not (out / "result.json").exists()
text = log.read_text()
expected = {
    "one-image-invalid": "jump destination must contain JUMPDEST in both images",
    "payload": "jump destination is inside PUSH data",
    "invalid-span-exit": "exit PC is inside a PUSH immediate",
}[sys.argv[3]]
assert expected in text, text
PY
 done
# Memory expansion remains state-dependent when the terminal JUMP is executed.
printf '%s\n' 52526001600160e01b03166001600160e01b03196017565b00 > "$work/memory-original.hex"
printf '%s\n' 52526001600160e01b03166400ffffffff60e01b6017565b00 > "$work/memory-candidate.hex"
cargo run --locked -- certify-runtime-region \
  --original "$work/memory-original.hex" --candidate "$work/memory-candidate.hex" \
  --entry-pc 0 --exit-pc 22 --through-jump --out "$work/memory-accepted" \
  2>&1 | tee "$work/memory.log"
python3 - "$work/memory-accepted" <<'PY_MEMORY'
import json
import pathlib
import sys

out = pathlib.Path(sys.argv[1])
report = json.loads((out / "result.json").read_text())
assert report["jump_pc"] == 22
assert report["exit_pc"] == report["pushed_destination"] == 23
assert report["source_instruction_count"] == 16
assert report["candidate_instruction_count"] == 13
assert report["source_base_gas"] == 53
assert report["candidate_base_gas"] == 44
assert report["gas_surplus_increase"] == 9
assert report["execution_count_offset_increase"] == 3
assert report["memory_operations"] == 2
assert report["required_input_stack_words"] == 5
assert report["maximum_input_stack_words"] == 1024
assert report["output_stack_delta"] == -3
assert "source_gas_minimum" not in report
assert report["proof_root"] == "GolfCertificates.MemoryJump.memory_jump_boundary"
assert "sourceCost" in report["gas_requirement"]
assert json.loads((out / "environment.json").read_text())["semantics_profile"]["identity"] == "evm-golf-checked-scanner"
PY_MEMORY
# Whole-program refinement: a branch, a revert path and one PUSH 2^k; MUL site.
printf '%s\n' 34600a576007600402005b600080fd > "$work/whole-original.hex"
printf '%s\n' 34600a57600760021b005b600080fd > "$work/whole-candidate.hex"
cargo run --locked -- certify-runtime-whole \
  --original "$work/whole-original.hex" --candidate "$work/whole-candidate.hex" \
  --out "$work/whole-accepted" 2>&1 | tee "$work/whole.log"
python3 - "$work/whole-accepted" <<'PY_WHOLE'
import json
import pathlib
import sys

out = pathlib.Path(sys.argv[1])
report = json.loads((out / "result.json").read_text())
assert report["covered_instructions"] == 10
assert report["power_sites"] == [6]
assert "Υ" in report["claim"] and any("Υ" in item for item in report["unproved"])
assert json.loads((out / "environment.json").read_text())["semantics_profile"]["identity"] == "evm-golf-checked-scanner"
PY_WHOLE
# One-hop JUMPI threading through an unchanged trampoline.
printf '%s\n' 346007570000005b600b565b600080fd > "$work/thread-original.hex"
printf '%s\n' 34600b570000005b600b565b600080fd > "$work/thread-candidate.hex"
cargo run --locked -- certify-runtime-whole \
  --original "$work/thread-original.hex" --candidate "$work/thread-candidate.hex" \
  --out "$work/thread-accepted" 2>&1 | tee "$work/thread.log"
python3 - "$work/thread-accepted/result.json" <<'PY_THREAD'
import json
import sys

report = json.load(open(sys.argv[1]))
assert report["thread_sites"] == [1] and report["power_sites"] == []
PY_THREAD
# Stack window that needs the unchanged PUSH0 before it.
printf '%s\n' 345f80fd > "$work/window-original.hex"
printf '%s\n' 345f5ffd > "$work/window-candidate.hex"
cargo run --locked -- certify-runtime-whole \
  --original "$work/window-original.hex" --candidate "$work/window-candidate.hex" \
  --out "$work/window-accepted" 2>&1 | tee "$work/window.log"
python3 - "$work/window-accepted/result.json" <<'PY_WINDOW'
import json
import sys

report = json.load(open(sys.argv[1]))
assert report["window_sites"] == [1]
PY_WINDOW
# Stack facts cross a JUMP: CALLER is below 2^160 at the JUMPDEST, so the
# mask after it can go. With a destination read from calldata it cannot.
printf '%s\n' 33600556005b73ffffffffffffffffffffffffffffffffffffffff165f5260205ff3 > "$work/facts-original.hex"
printf '%s\n' 33600556005b730000000000000000000000000000000000000000505f5260205ff3 > "$work/facts-candidate.hex"
cargo run --locked -- certify-runtime-whole \
  --original "$work/facts-original.hex" --candidate "$work/facts-candidate.hex" \
  --out "$work/facts-accepted" 2>&1 | tee "$work/facts.log"
python3 - "$work/facts-accepted/result.json" <<'PY_FACTS'
import json
import sys

report = json.load(open(sys.argv[1]))
assert report["window_sites"] == [6] and report["checked_entries"] == 10
PY_FACTS
# Calls: GAS feeding STATICCALL, DELEGATECALL and CALLCODE, a bare CALL, one
# PUSH 2^k; MUL site, a CODECOPY of two data bytes after the STOP, and
# EXTCODEHASH and EXTCODECOPY of constant addresses.
printf '%s\n' 6004600202505f5f5f5f5f5afa505f5f5f5f5f5f5ff1505f5f5f5f5f5af4505f5f5f5f5f5f5af250600260395f3960013f505f5f5f60023c00aabb > "$work/call-original.hex"
printf '%s\n' 600460011b505f5f5f5f5f5afa505f5f5f5f5f5f5ff1505f5f5f5f5f5af4505f5f5f5f5f5f5af250600260395f3960013f505f5f5f60023c00aabb > "$work/call-candidate.hex"
cargo run --locked -- certify-runtime-whole \
  --original "$work/call-original.hex" --candidate "$work/call-candidate.hex" \
  --out "$work/call-accepted" 2>&1 | tee "$work/call.log"
python3 - "$work/call-accepted/result.json" <<'PY_CALL'
import json
import sys

report = json.load(open(sys.argv[1]))
assert report["power_sites"] == [2] and report["call_sites"] == [11, 21, 28, 37]
assert report["codecopy_sites"] == [45] and report["inspected"] == [1, 2]
assert any("CalleeSummary" in item for item in report["assumptions"])
assert any("Reentry" in item for item in report["assumptions"])
PY_CALL
# SELFDESTRUCT halts the owner after a PUSH 2^k; MUL site.
printf '%s\n' 34600b57600760040250005b5fff > "$work/destruct-original.hex"
printf '%s\n' 34600b57600760021b50005b5fff > "$work/destruct-candidate.hex"
cargo run --locked -- certify-runtime-whole \
  --original "$work/destruct-original.hex" --candidate "$work/destruct-candidate.hex" \
  --out "$work/destruct-accepted" 2>&1 | tee "$work/destruct.log"
python3 - "$work/destruct-accepted/result.json" <<'PY_DESTRUCT'
import json
import sys

report = json.load(open(sys.argv[1]))
assert report["power_sites"] == [6] and report["window_sites"] == []
assert report["covered_instructions"] == 10
PY_DESTRUCT
printf '%s\n' 335f3556005b73ffffffffffffffffffffffffffffffffffffffff165f5260205ff3 > "$work/nofacts-original.hex"
printf '%s\n' 335f3556005b730000000000000000000000000000000000000000505f5260205ff3 > "$work/nofacts-candidate.hex"
if cargo run --locked -- certify-runtime-whole \
  --original "$work/nofacts-original.hex" --candidate "$work/nofacts-candidate.hex" \
  --out "$work/nofacts-rejected"; then
  echo 'A mask needing unknown facts was accepted.' >&2
  exit 1
fi
[[ ! -e "$work/nofacts-rejected/result.json" ]]
printf '%s\n' 34600a57600760031b005b600080fd > "$work/whole-wrong.hex"
if cargo run --locked -- certify-runtime-whole \
  --original "$work/whole-original.hex" --candidate "$work/whole-wrong.hex" \
  --out "$work/whole-rejected"; then
  echo 'Incorrect whole-program candidate was accepted.' >&2
  exit 1
fi
[[ ! -e "$work/whole-rejected/result.json" ]]
printf 'Checked-scanner region checks passed. Local evidence: %s\n' "$work"
