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
printf 'Checked-scanner region checks passed. Local evidence: %s\n' "$work"
