#!/usr/bin/env bash
set -euo pipefail

# Install the pinned official binary in this checkout, without changing PATH or
# the user's global Lean/elan setup. Requires curl, tar, and zstd.
cd "$(dirname "$0")/.."
version=4.34.0
if [[ -x .tools/lean/bin/lean ]]; then
  .tools/lean/bin/lean --version
  exit 0
fi
case "$(uname -s)-$(uname -m)" in
  Darwin-arm64) platform=darwin_aarch64 ;;
  Darwin-x86_64) platform=darwin ;;
  Linux-x86_64) platform=linux ;;
  Linux-aarch64) platform=linux_aarch64 ;;
  *) echo 'Unsupported platform; install Lean 4.34.0 and set LEAN to its binary.' >&2; exit 1 ;;
esac
command -v zstd >/dev/null
mkdir -p .tools
archive=".tools/lean-${version}-${platform}.tar.zst"
curl --fail --location --retry 2 \
  "https://github.com/leanprover/lean4/releases/download/v${version}/lean-${version}-${platform}.tar.zst" \
  --output "$archive"
mkdir -p .tools/lean
tar --use-compress-program=zstd --strip-components=1 -xf "$archive" -C .tools/lean
.tools/lean/bin/lean --version
