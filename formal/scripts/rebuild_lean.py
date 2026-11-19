#!/usr/bin/env python3
"""Recompile project Lean sources into a fresh, isolated directory and profile workers.

Run with `lake env python3 scripts/rebuild_lean.py`. External dependencies stay
cached; every project import resolves into this run's initially empty output.
"""
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from pathlib import Path
import argparse
import datetime
import heapq
import json
import os
import signal
import subprocess
import threading
import time
import tomllib

from check_soundness import imports

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("targets", nargs="*", help="module roots; default: every project source")
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--module-timeout", type=float, default=180)
    parser.add_argument("--memory-mib", type=int, default=8192)
    parser.add_argument("--threads", type=int, default=2)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--resume", type=Path)
    args = parser.parse_args()
    if min(args.jobs, args.module_timeout, args.memory_mib, args.threads) <= 0:
        parser.error("worker limits must be positive")
    if "LEAN_PATH" not in os.environ:
        parser.error("run through `lake env` to obtain dependency paths")
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%d-%H%M%S")
    output = (args.resume or args.output or ROOT / ".lake" / f"rebuild-{stamp}").resolve()
    if not args.resume and output.exists():
        parser.error("fresh output already exists; use --resume to continue it")
    output.mkdir(parents=True, exist_ok=True)
    previous_report = output / "report.json"
    previous = json.loads(previous_report.read_text()).get("modules", {}) if args.resume and previous_report.exists() else {}
    binary = output / "lib"
    binary.mkdir(exist_ok=True)
    (ROOT / ".lake" / "rebuild-latest").write_text(str(output) + "\n")
    environment = dict(os.environ)
    old = (ROOT / ".lake/build/lib/lean").resolve()
    paths = [p for p in environment["LEAN_PATH"].split(os.pathsep)
             if p and Path(p).resolve() != old]
    environment["LEAN_PATH"] = os.pathsep.join([str(binary)] + paths)
    config = tomllib.loads((ROOT / "lakefile.toml").read_text())
    libraries = config["lean_lib"]
    roots = sorted({ROOT} | {(ROOT / lib.get("srcDir", ".")).resolve() for lib in libraries},
                   key=lambda p: len(p.parts), reverse=True)
    modules, module_roots, options = {}, {}, {}
    for parent, directories, files in os.walk(ROOT):
        directories[:] = [d for d in directories if not d.startswith(".")]
        for filename in files:
            if not filename.endswith(".lean"):
                continue
            source = Path(parent) / filename
            owner = next(r for r in roots if source.is_relative_to(r))
            module = ".".join(source.relative_to(owner).with_suffix("").parts)
            if module in modules:
                raise RuntimeError(f"Duplicate module: {module}")
            modules[module], module_roots[module] = source, owner
            local = dict(config.get("leanOptions", {}))
            for lib in libraries:
                if (ROOT / lib.get("srcDir", ".")).resolve() != owner:
                    continue
                if any(module == root or module.startswith(root + ".")
                       for root in lib.get("roots", [lib["name"]])):
                    local.update(lib.get("leanOptions", {}))
                    break
            options[module] = local
    dependencies = {m: set(imports(p.read_text())) & modules.keys() for m, p in modules.items()}
    selected, active = set(), set()

    def visit(module):
        if module in active:
            raise RuntimeError(f"Import cycle at {module}")
        if module in selected:
            return
        active.add(module)
        for dependency in dependencies[module]:
            visit(dependency)
        active.remove(module)
        selected.add(module)

    for target in args.targets or sorted(modules):
        if target not in modules:
            parser.error(f"Unknown local module: {target}")
        visit(target)
    dependents = {m: [] for m in selected}
    pending = {m: len(dependencies[m]) for m in selected}
    for module in selected:
        for dependency in dependencies[module]:
            dependents[dependency].append(module)
    ready = [m for m in selected if not pending[m]]
    heapq.heapify(ready)
    records, processes = {}, {}
    process_lock = threading.Lock()
    started = time.monotonic()
    report_path = output / "report.json"

    def save():
        report_path.write_text(json.dumps({"output": str(output), "source_modules": len(selected),
            "jobs": args.jobs, "lean_threads": args.threads, "memory_mib": args.memory_mib,
            "module_timeout_seconds": args.module_timeout,
            "wall_seconds": round(time.monotonic() - started, 3),
            "completed": len(records), "modules": records}, indent=2) + "\n")

    def compile_module(module):
        source = modules[module]
        artifact = binary / Path(*module.split(".")).with_suffix(".olean")
        artifact.parent.mkdir(parents=True, exist_ok=True)
        if args.resume and artifact.exists():
            inputs = [source] + [binary / Path(*d.split(".")).with_suffix(".olean")
                                 for d in dependencies[module]]
            if max(p.stat().st_mtime_ns for p in inputs) <= artifact.stat().st_mtime_ns:
                return previous.get(module, {"seconds": 0, "peak_rss_mib": 0}) | {"status": "reused"}
        log = output / "logs" / Path(*module.split(".")).with_suffix(".log")
        log.parent.mkdir(parents=True, exist_ok=True)
        command = ["lean", f"-j{args.threads}", f"-M{args.memory_mib}", "-R", str(module_roots[module])]
        for key, value in options[module].items():
            rendered = str(value).lower() if isinstance(value, bool) else str(value)
            command.append(f"-D{key}={rendered}")
        command += [str(source), "-o", str(artifact), "-i", str(artifact.with_suffix(".ilean"))]
        begin = time.monotonic()
        status = "passed"
        with log.open("w") as stream:
            process = subprocess.Popen(command, cwd=ROOT, env=environment, stdout=stream,
                                       stderr=subprocess.STDOUT, start_new_session=True)
            with process_lock:
                processes[module] = process
            while True:
                pid, result, usage = os.wait4(process.pid, os.WNOHANG)
                if pid:
                    process.returncode = os.waitstatus_to_exitcode(result)
                    break
                if time.monotonic() - begin > args.module_timeout:
                    status = "timeout"
                    os.killpg(process.pid, signal.SIGKILL)
                    _, result, usage = os.wait4(process.pid, 0)
                    process.returncode = os.waitstatus_to_exitcode(result)
                    break
                time.sleep(0.1)
            with process_lock:
                del processes[module]
        if process.returncode and status != "timeout":
            status = "failed"
        if status != "passed":
            artifact.unlink(missing_ok=True)
        return {"status": status, "seconds": round(time.monotonic() - begin, 3),
                "peak_rss_mib": round(usage.ru_maxrss / 1024, 1), "log": str(log),
                "command": command}

    print(f"FRESH REBUILD: {len(selected)} modules, {args.jobs} workers; output: {output}", flush=True)
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        running = {}
        try:
            while ready or running:
                while ready and len(running) < args.jobs:
                    module = heapq.heappop(ready)
                    running[pool.submit(compile_module, module)] = module
                completed, _ = wait(running, return_when=FIRST_COMPLETED)
                for future in completed:
                    module = running.pop(future)
                    record = records[module] = future.result()
                    print(f"{len(records)}/{len(selected)} {record['status'].upper()} {module} "
                          f"{record['seconds']:.2f}s {record['peak_rss_mib']:.0f}MiB", flush=True)
                    save()
                    if record["status"] in {"passed", "reused"}:
                        for dependent in dependents[module]:
                            pending[dependent] -= 1
                            if not pending[dependent]:
                                heapq.heappush(ready, dependent)
            failures = [m for m, r in records.items() if r["status"] not in {"passed", "reused"}]
            print(f"FINISHED: {len(records)}/{len(selected)} checked; {len(failures)} failed; "
                  f"report: {report_path}", flush=True)
            if failures or len(records) != len(selected):
                raise RuntimeError("Rebuild incomplete: " + ", ".join(failures))
        except BaseException:
            with process_lock:
                for process in processes.values():
                    try:
                        os.killpg(process.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
            raise
        finally:
            save()


if __name__ == "__main__":
    main()
