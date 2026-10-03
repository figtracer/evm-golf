#!/usr/bin/env bash
set -euo pipefail

# Keep the upstream semantics toolchain separate from the expression checker.
cd "$(dirname "$0")/.."
setup_script="$PWD/scripts/setup-upstream.sh"
root="${EVM_GOLF_UPSTREAM:-$PWD/.tools/upstream}"
case "$root" in /*) ;; *) root="$PWD/$root" ;; esac
version=4.22.0
revision=047f63070309f436b66c61e276ab3b6d1169265a
check_only=false
case "${1:-}" in
  '') ;;
  --check) check_only=true ;;
  *) echo 'Usage: scripts/setup-upstream.sh [--check]' >&2; exit 2 ;;
esac
if [[ $# -gt 1 ]]; then
  echo 'Usage: scripts/setup-upstream.sh [--check]' >&2
  exit 2
fi
command -v python3 >/dev/null
command -v git >/dev/null

if [[ ! -x "$root/lean/bin/lean" ]]; then
  if $check_only || [[ -e "$root/lean" ]]; then
    echo "Missing or incomplete pinned Lean installation: $root/lean" >&2
    exit 1
  fi
  case "$(uname -s)-$(uname -m)" in
    Darwin-arm64) platform=darwin_aarch64 ;;
    Darwin-x86_64) platform=darwin ;;
    Linux-x86_64) platform=linux ;;
    Linux-aarch64) platform=linux_aarch64 ;;
    *) echo 'Unsupported platform for upstream Lean 4.22.0.' >&2; exit 1 ;;
  esac
  command -v zstd >/dev/null
  mkdir -p "$root"
  archive="$root/lean-${version}-${platform}.tar.zst"
  curl --fail --location --retry 2 \
    "https://github.com/leanprover/lean4/releases/download/v${version}/lean-${version}-${platform}.tar.zst" \
    --output "$archive"
  staging="$(mktemp -d "$root/lean-install.XXXXXX")"
  tar --use-compress-program=zstd --strip-components=1 -xf "$archive" -C "$staging"
  mv "$staging" "$root/lean"
fi
if ! "$root/lean/bin/lean" --version | grep -Eq '^Lean \(version 4\.22\.0,'; then
  echo "Expected Lean $version in $root/lean; refusing to reuse this installation." >&2
  exit 1
fi
[[ -x "$root/lean/bin/lake" ]] || { echo 'Pinned Lake binary is missing.' >&2; exit 1; }

# Fetch the locked revisions directly. Do not run lake update or its package hooks.
python3 - "$root/semantics" "$revision" "$check_only" <<'PY'
import json
import pathlib
import re
import subprocess
import sys

semantics = pathlib.Path(sys.argv[1])
revision = sys.argv[2]
check_only = sys.argv[3] == "true"


def git(path, *args):
    return subprocess.check_output(["git", "-C", str(path), *args], text=True).strip()


def checkout(path, url, rev):
    if not path.exists():
        if check_only:
            raise SystemExit(f"Missing pinned checkout: {path}")
        path.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(["git", "init", "--quiet", str(path)], check=True)
        subprocess.run(["git", "-C", str(path), "remote", "add", "origin", url], check=True)
        subprocess.run(["git", "-C", str(path), "fetch", "--quiet", "--depth", "1", "origin", rev], check=True)
        subprocess.run(["git", "-C", str(path), "checkout", "--quiet", "--detach", "FETCH_HEAD"], check=True)
    if git(path, "rev-parse", "HEAD") != rev:
        raise SystemExit(f"Wrong revision in {path}; expected {rev}. No files were reset.")
    if git(path, "status", "--porcelain", "--untracked-files=no"):
        raise SystemExit(f"Tracked source changes in {path}; refusing to reuse them.")


checkout(semantics, "https://github.com/NethermindEth/EVMYulLean.git", revision)
if (semantics / "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.22.0":
    raise SystemExit("Unexpected pinned upstream Lean toolchain")
manifest = json.loads((semantics / "lake-manifest.json").read_text())
if manifest["packagesDir"] != ".lake/packages":
    raise SystemExit("Unexpected upstream package directory")
for package in manifest["packages"]:
    name, rev = package["name"], package["rev"]
    if package["type"] != "git" or package.get("subDir") is not None or not re.fullmatch(r"[A-Za-z0-9_-]+", name) or not re.fullmatch(r"[0-9a-f]{40}", rev):
        raise SystemExit("Unsupported or unlocked upstream package")
    checkout(semantics / ".lake/packages" / name, package["url"], rev)
    if name == "proofwidgets" and not check_only:
        # Lake's cloud-release lookup needs the locked tag as well as its commit.
        tag = package["inputRev"]
        if not re.fullmatch(r"v[0-9]+\.[0-9]+\.[0-9]+", tag):
            raise SystemExit("Unsupported ProofWidgets release tag")
        path = semantics / ".lake/packages" / name
        tag_ref = "refs/tags/" + tag
        found = subprocess.run(["git", "-C", str(path), "show-ref", "--verify", "--quiet", tag_ref])
        if found.returncode:
            subprocess.run(["git", "-C", str(path), "fetch", "--quiet", "--depth", "1",
                            "origin", tag_ref + ":" + tag_ref], check=True)
        if git(path, "rev-parse", tag_ref + "^{commit}") != rev:
            raise SystemExit("ProofWidgets release tag does not match its locked commit")
PY

if $check_only; then
  echo "Pinned upstream sources and Lean $version verified: $root"
  exit 0
fi

export EVM_GOLF_UPSTREAM="$root"
export PATH="$root/lean/bin:$PATH"
unset LEAN_PATH
cd "$root/semantics"
# Fetch the pinned Mathlib dependency cache through its explicit cache executable.
# This does not request the upstream project's default/native-library targets.
lake exe cache get
# The explicit olean target avoids the project's default native-library targets.
lake --no-cache build +EvmYul.EVM.Semantics:olean
"$setup_script" --check
