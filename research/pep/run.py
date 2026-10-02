#!/usr/bin/env python3
"""Reproduce the trusted, local Pep proof experiment (Python standard library)."""

import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import re
import shutil
import signal
import statistics
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
METHODS = ("z3", "cvc5", "lean-auto", "lean-guided")
FOUNDATIONAL = {"propext", "Classical.choice", "Quot.sound"}


def run_process(command, timeout, log):
    start = time.monotonic()
    with log.open("w") as stream:
        process = subprocess.Popen(command, stdout=stream, stderr=subprocess.STDOUT,
                                   start_new_session=True, cwd=ROOT)
        try:
            code = process.wait(timeout=timeout)
            status = "finished"
        except subprocess.TimeoutExpired:
            status, code = "timeout", None
        finally:
            # Lean can spawn a SAT solver. Clean the entire group, including on interrupt.
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            process.wait()
    return {"elapsed_seconds": time.monotonic() - start,
            "exit_code": code, "status": status}


def classify(method, result, output, theorems=("claim",)):
    if result["status"] == "timeout":
        return result
    result["status"] = "error"
    if result["exit_code"] != 0:
        if method.startswith("lean-") and "The SAT solver timed out" in output:
            result["status"] = "solver-timeout"
        if method.startswith("lean-") and "The prover found a counterexample" in output:
            result["status"] = "counterexample-reported"
        return result
    if method in ("z3", "cvc5"):
        answers = [line.strip() for line in output.splitlines()
                   if line.strip() in ("sat", "unsat", "unknown")]
        if len(answers) == 1:
            result["status"] = answers[0]
        return result
    if "sorryAx" in output or "uses 'sorry'" in output:
        result["status"] = "rejected-axioms"
        return result
    dependencies = {}
    for theorem in theorems:
        match = re.search(rf"'{theorem}' depends on axioms:\s*\[([^]]*)\]", output, re.S)
        if match:
            axioms = [name.strip() for name in match[1].split(",") if name.strip()]
        elif f"'{theorem}' does not depend on any axioms" in output:
            axioms = []
        else:
            return result
        dependencies[theorem] = axioms
    axioms = set().union(*dependencies.values())
    result["axioms"] = dependencies
    native = {name for name in axioms if name.startswith("claim._native.bv_decide.")}
    unexpected = axioms - FOUNDATIONAL - native
    result["status"] = "rejected-axioms" if unexpected else "checked"
    result["native_evaluation"] = bool(native)
    return result


def replay_counterexample(result, output, generated, out, timeout):
    values = {}
    if result["method"].startswith("lean-"):
        values = {name: value for name, value in re.findall(r"([xy]) = (\d+)#256", output)}
    else:
        # Ask for the actual model in a separate, untimed rerun; archive it too.
        query = out / f'{result["case"]}.{result["method"]}.{result["repetition"]}.model.smt2'
        source = (generated / f'{result["case"]}.smt2').read_text()
        query.write_text('(set-option :produce-models true)\n' + source + '(get-value (x y))\n')
        log = query.with_suffix(".log")
        probe = run_process([*result["command"][:-1], str(query)], timeout, log)
        result["model_query"] = dict(probe, log=log.name)
        if probe["status"] != "finished" or probe["exit_code"] != 0:
            return
        output = log.read_text()
        for name, value in re.findall(r"\(\s*([xy])\s+(#x[0-9a-fA-F]+|#b[01]+|\(_\s+bv\d+\s+256\))\s*\)", output):
            if value.startswith("#"):
                values[name] = str(int(value[2:], 16 if value[1] == "x" else 2))
            else:
                values[name] = re.search(r"bv(\d+)", value)[1]
    if set(values) != {"x", "y"}:
        result["counterexample_replay"] = "model unavailable"
        return
    log = out / f'{result["case"]}.{result["method"]}.{result["repetition"]}.replay.log'
    command = ["cargo", "run", "--locked", "--quiet", "--example", "proof_cases", "--",
               "--replay", str(ROOT / "research/pep/cases.json"), result["case"],
               values["x"], values["y"]]
    replay = run_process(command, timeout, log)
    result["replay_process"] = dict(replay, log=log.name)
    if replay["status"] != "finished" or replay["exit_code"] != 0:
        result["counterexample_replay"] = "failed"
        return
    result["counterexample"] = json.loads(log.read_text())
    result["counterexample_replay"] = "confirmed by U256 evaluation and revm"
    if result["status"] == "counterexample-reported":
        result["status"] = "counterexample"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    # A short, explicit exploratory budget; a timeout is never a disproof.
    parser.add_argument("--timeout", type=float, default=15)
    parser.add_argument("--repetitions", type=int, default=2)
    parser.add_argument("--case", action="append", dest="cases")
    parser.add_argument("--z3", default="z3")
    parser.add_argument("--cvc5", default="cvc5")
    parser.add_argument("--lean", default=str(ROOT / ".tools/lean/bin/lean"))
    args = parser.parse_args()
    if not math.isfinite(args.timeout) or args.timeout <= 0 or args.repetitions < 1:
        parser.error("timeout must be finite and positive; repetitions must be positive")
    if os.name != "posix":
        parser.error("POSIX process groups are required for solver cleanup")
    executables = {}
    versions = {}
    for name in ("z3", "cvc5", "lean"):
        executable = shutil.which(getattr(args, name))
        if not executable:
            parser.error(f"missing {name}: {getattr(args, name)}")
        executables[name] = str(Path(executable).resolve())
        versions[name] = subprocess.check_output(
            [executable, "--version"], text=True, timeout=10).strip()
    if "version 4.34.0," not in versions["lean"]:
        parser.error("this corpus requires Lean 4.34.0")
    lean_flags = ["-j1"]
    source_cases = json.loads((ROOT / "research/pep/cases.json").read_text())
    ids = {case["id"] for case in source_cases}
    if args.cases and not set(args.cases) <= ids:
        parser.error(f"unknown cases: {set(args.cases) - ids}")
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    generated = out / "inputs"
    subprocess.run(["cargo", "run", "--locked", "--quiet", "--example", "proof_cases", "--",
                    str(ROOT / "research/pep/cases.json"), str(generated), str(math.ceil(args.timeout))],
                   cwd=ROOT, check=True)
    cases = json.loads((generated / "manifest.json").read_text())
    if args.cases:
        cases = [case for case in cases if case["id"] in args.cases]
    files = [ROOT / "examples/proof_cases.rs", Path(__file__).resolve(),
             ROOT / "research/pep/cases.json", ROOT / "Cargo.lock", ROOT / "src/expr.rs", ROOT / "src/evm.rs", ROOT / "lean/Model.lean"]
    metadata = {"schema": 1, "width": 256, "timeout_seconds": args.timeout,
                "repetitions": args.repetitions, "versions": versions,
                "executables": executables, "platform": platform.platform(),
                "cpu_count": os.cpu_count(), "python": platform.python_version(),
                "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
                "base_commit": subprocess.check_output(["git", "rev-parse", "HEAD"],
                                                       cwd=ROOT, text=True).strip(),
                "working_tree": subprocess.check_output(["git", "status", "--porcelain"],
                                                        cwd=ROOT, text=True),
                "source_sha256": {str(file.relative_to(ROOT)): hashlib.sha256(file.read_bytes()).hexdigest()
                                  for file in files},
                "timing": "Sequential fresh processes; includes startup/import/search/check. Guided proof authoring excluded. Warmup before measurements; deterministic rotated method order.",
                "resources": "Wall timeout per process group. Lean -j1 and bv_decide timeout rounded up to the external wall budget; other engine defaults. No memory cap or peak memory measurement. No CPU pinning."}
    (out / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
    # Warm library/filesystem caches and solver startup consistently, outside measurements.
    for name in ("z3", "cvc5", "lean"):
        file = generated / ("add-zero.auto.lean" if name == "lean" else "add-zero.smt2")
        flags = lean_flags if name == "lean" else (["--lang=smt2"] if name == "cvc5" else [])
        result = run_process([executables[name], *flags, str(file)], args.timeout, out / f"warmup-{name}.log")
        if result["status"] != "finished" or result["exit_code"] != 0:
            raise RuntimeError(f"{name} warmup failed: {result}")
    results = []
    for repetition in range(args.repetitions):
        for index, case in enumerate(cases):
            offset = (index + repetition) % len(METHODS)
            order = METHODS[offset:] + METHODS[:offset]
            for method in order:
                engine = "lean" if method.startswith("lean-") else method
                suffix = {"lean-auto": "auto.lean", "lean-guided": "guided.lean"}.get(method, "smt2")
                flags = lean_flags if engine == "lean" else (["--lang=smt2"] if engine == "cvc5" else [])
                command = [executables[engine], *flags, str(generated / f'{case["id"]}.{suffix}')]
                log = out / f'{case["id"]}.{method}.{repetition + 1}.log'
                result = run_process(command, args.timeout, log)
                classify(method, result, log.read_text())
                result.update(case=case["id"], method=method, repetition=repetition + 1,
                              command=command, log=log.name)
                if result["status"] in ("sat", "counterexample-reported"):
                    replay_counterexample(result, log.read_text(), generated, out, args.timeout)
                results.append(result)
                (out / "results.json").write_text(json.dumps(results, indent=2) + "\n")
                print(f'{case["id"]:20} {method:12} {result["status"]:16} {result["elapsed_seconds"]:.3f}s', flush=True)
                if result.get("counterexample_replay") == "failed":
                    raise RuntimeError("counterexample replay failed; see saved results and log")
                if not case["valid"] and result["status"] in ("checked", "unsat"):
                    raise RuntimeError("negative control incorrectly proved: stop and inspect artifacts")
                if case["valid"] and result["status"] in ("sat", "counterexample", "counterexample-reported"):
                    raise RuntimeError("positive case returned sat: stop and inspect translation")
    bytecode_results = []
    for case in cases:
        if not case["valid"]:
            continue
        log = out / f'{case["id"]}.bytecode.log'
        command = [executables["lean"], *lean_flags, str(generated / f'{case["id"]}.bytecode.lean')]
        result = run_process(command, args.timeout, log)
        classify("lean-guided", result, log.read_text(), ("claim", "baseline_correct", "candidate_correct"))
        result.update(case=case["id"], command=command, log=log.name)
        bytecode_results.append(result)
        print(f'bytecode {case["id"]}: {result["status"]}', flush=True)
    (out / "bytecode-results.json").write_text(json.dumps(bytecode_results, indent=2) + "\n")
    lines = ["# Pep proof experiment", "", f"{args.repetitions} repetitions, {args.timeout:g}s wall limit per process. Width: 256 bits.", "",
             "Cells show status and median observed wall time (including startup). Timeouts are censored; Lean errors are unresolved proofs.", "",
             "| Case | Z3 | cvc5 | Lean automatic | Lean guided replay |", "| --- | --- | --- | --- | --- |"]
    for case in cases:
        cells = []
        for method in METHODS:
            rows = [row for row in results if row["case"] == case["id"] and row["method"] == method]
            statuses = "/".join(sorted({row["status"] for row in rows}))
            cells.append(f'{statuses} {statistics.median(row["elapsed_seconds"] for row in rows):.3f}s')
        lines.append(f'| {case["id"]} | ' + " | ".join(cells) + " |")
    lines += ["", "Guided proof discovery is excluded from these timings; see the corpus discovery record. Expression timings exclude bytecode proofs. Separate bytecode-results.json records full three-theorem checks with the guided proof.", "", "Raw SMT unsat answers have not been certificate-checked. Lean axiom dependencies are recorded in results.json. Native evaluation remains part of the automatic lane's trust boundary.", ""]
    (out / "README.md").write_text("\n".join(lines))


if __name__ == "__main__":
    main()
