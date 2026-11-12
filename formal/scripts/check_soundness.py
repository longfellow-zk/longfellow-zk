#!/usr/bin/env python3
"""Sequential Lake checks for soundness and its public API, with worker deadlines."""
from pathlib import Path
import argparse
import fcntl
import json
import os
import re
import signal
import subprocess
import sys
import time
import tomllib

ROOT = Path(__file__).resolve().parents[1]
IMPORT = re.compile(r"^\s*(?:(?:public|meta|private)\s+)*import\s+(?:all\s+)?([A-Za-z0-9_.]+)", re.M)


def imports(text):
    # Lean block comments nest. Documentation sometimes contains fake imports.
    depth, index, output = 0, 0, []
    while index < len(text):
        pair = text[index:index + 2]
        if pair == "/-":
            depth += 1
            index += 2
        elif depth and pair == "-/":
            depth -= 1
            index += 2
        elif not depth and pair == "--":
            end = text.find("\n", index)
            index = len(text) if end < 0 else end
        else:
            if not depth or text[index] == "\n":
                output.append(text[index])
            index += 1
    return IMPORT.findall("".join(output))


def check_import_boundaries(modules):
    """Keep runtime predicates and soundness separate from simulator assemblies."""
    rules = {
        "LfzkV2.Current.MdocStrandOracle": (
            "LfzkV1", "LfzkV2.Current.ZeroKnowledge"),
        "LfzkV2.Joint.Pair.Basic": (
            "LfzkV2.Joint.Replay", "LfzkV2.Linear.Runtime"),
        "LfzkV2.Current.BackendPrefix": (
            "LfzkV2.PolygeroZk", "LfzkV2.Current.ZeroKnowledge"),
        "Bcs.SameDistribution": ("LfzkV1", "LfzkV2"),
        "LfzkV2.Current.ZeroKnowledge.SHAOracleProbability": (
            "LfzkV1.FromLigeroZKV1",),
    }
    dependencies = {name: imports(source.read_text()) for name, source in modules.items()}
    for root, forbidden in rules.items():
        if root not in modules:
            raise RuntimeError(f"Missing import-boundary root: {root}")
        pending, seen = [(root, [root])], set()
        while pending:
            name, path = pending.pop()
            if name in seen:
                continue
            seen.add(name)
            if any(name == prefix or name.startswith(prefix + ".") for prefix in forbidden):
                raise RuntimeError("Forbidden import path: " + " -> ".join(path))
            pending.extend((dependency, path + [dependency])
                           for dependency in dependencies.get(name, []))
    print(f"PASS: {len(rules)} import boundaries.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("targets", nargs="*", default=["Survival", "Survival.Axioms", "LfzkV2.Current.Tests.APITest"])
    parser.add_argument("--module-timeout", type=float, default=180)
    parser.add_argument("--imports-only", action="store_true", help="check source import boundaries without building")
    args = parser.parse_args()
    if args.module_timeout <= 0:
        parser.error("module-timeout must be positive")
    work = ROOT / ".lake/soundness-check"
    work.mkdir(parents=True, exist_ok=True)
    lock = (work / "lock").open("w")
    try:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError as error:
        raise RuntimeError("Another bounded soundness check is running") from error
    config = tomllib.loads((ROOT / "lakefile.toml").read_text())
    modules = {}
    roots = {ROOT} | {ROOT / lib.get("srcDir", ".") for lib in config["lean_lib"]}
    for directory in sorted(roots, key=lambda p: len(p.parts)):
        for parent, directories, files in os.walk(directory):
            directories[:] = [d for d in directories if d not in {".lake", ".git"}]
            for filename in files:
                if filename.endswith(".lean"):
                    source = Path(parent) / filename
                    modules[".".join(source.relative_to(directory).with_suffix("").parts)] = source
    check_import_boundaries(modules)
    if args.imports_only:
        return
    visited, active, records = set(), set(), []
    started = time.monotonic()
    targets = args.targets or ["Survival", "Survival.Axioms", "LfzkV2.Current.Tests.APITest"]

    def run(module):
        log = work / "logs" / Path(*module.split(".")).with_suffix(".log")
        log.parent.mkdir(parents=True, exist_ok=True)
        print(f"CHECK {module}", flush=True)
        begin, status = time.monotonic(), "failed"
        with log.open("w") as stream:
            process = subprocess.Popen(["lake", "build", f"+{module}:olean"], cwd=ROOT,
                                       stdout=stream, stderr=subprocess.STDOUT, start_new_session=True)
            try:
                code = process.wait(timeout=args.module_timeout)
            except subprocess.TimeoutExpired as error:
                status = "timeout"
                os.killpg(process.pid, signal.SIGTERM)
                try:
                    process.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid, signal.SIGKILL)
                    process.wait()
                raise RuntimeError(f"{module} exceeded {args.module_timeout:g}s; log: {log}") from error
            finally:
                elapsed = time.monotonic()-begin
                if process.returncode == 0:
                    status = "passed"
                records.append({"module":module,"seconds":round(elapsed,3),"status":status,
                                "log":str(log.relative_to(ROOT))})
                print(f"{status.upper()} {module} ({elapsed:.2f}s)", flush=True)
        if code:
            print(log.read_text()[-18000:], file=sys.stderr)
            raise RuntimeError(f"Lake check failed: {module}; full log: {log}")
        for line in log.read_text().splitlines():
            if "Audited " in line:
                print(line, flush=True)

    def build(module):
        if module in visited or module not in modules:
            return
        if module in active:
            raise RuntimeError(f"Import cycle at {module}")
        active.add(module)
        source = modules[module]
        dependencies = imports(source.read_text())
        for dependency in dependencies:
            build(dependency)
        output = ROOT / ".lake/build/lib/lean" / Path(*module.split(".")).with_suffix(".olean")
        inputs = [source] + [ROOT / ".lake/build/lib/lean" / Path(*d.split(".")).with_suffix(".olean")
                            for d in dependencies if d in modules]
        if module in targets or not output.exists() or max(p.stat().st_mtime_ns for p in inputs) > output.stat().st_mtime_ns:
            # Dependencies have already been checked in source order, avoiding
            # several large Lean workers being launched together by Lake.
            run(module)
        active.remove(module)
        visited.add(module)

    try:
        for target in targets:
            if target not in modules:
                raise RuntimeError(f"Unknown local module: {target}")
            build(target)
        print(f"PASS: {len(visited)} modules in closure; {len(records)} Lake checks.")
    finally:
        (work / "timings.json").write_text(json.dumps({"module_timeout_seconds":args.module_timeout,
            "wall_seconds":round(time.monotonic()-started,3),"closure_modules":len(visited),"checks":records},indent=2)+"\n")


if __name__ == "__main__":
    try:
        main()
    except RuntimeError as error:
        print(error,file=sys.stderr)
        raise SystemExit(1)
