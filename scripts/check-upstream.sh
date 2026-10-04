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

echo "Upstream region checks passed. Local evidence: $work"
