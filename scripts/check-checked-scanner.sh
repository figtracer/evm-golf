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

# Only the candidate loses the real JUMPDEST. Rejecting either-side mismatch matters.
printf '%s\n' 60051b01905f808061000c560000 > "$work/invalid-candidate.hex"
# Byte13 is 0x5b, but belongs to the PUSH1 payload beginning at byte12.
printf '%s\n' 60200201905f808061000d56605b00 > "$work/payload-original.hex"
printf '%s\n' 60051b01905f808061000d56605b00 > "$work/payload-candidate.hex"
for name in one-image-invalid payload conflicting-exit; do
  original="$work/forward-original.hex"
  candidate="$work/forward-candidate.hex"
  extra=()
  case "$name" in
    one-image-invalid) candidate="$work/invalid-candidate.hex" ;;
    payload) original="$work/payload-original.hex"; candidate="$work/payload-candidate.hex" ;;
    conflicting-exit) extra=(--exit-pc 11) ;;
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
    "conflicting-exit": "cannot be used with",
}[sys.argv[3]]
assert expected in text, text
if sys.argv[3] == "conflicting-exit":
    assert "--through-jump" in text and "--exit-pc" in text
PY
 done
printf 'Checked-scanner region checks passed. Local evidence: %s\n' "$work"
