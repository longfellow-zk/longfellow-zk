#!/usr/bin/env python3
"""Check `Lfzk.Arith.QuadCircuit.Isolated`, `DeadEnd` and `Lfzk.ZkArithProfile.WellFormedP` (at
the circuit's own width profile: `logv`, per-layer `logw`) on the REGISTERED mdoc circuits of one
version (default the deployed v7), loaded from the stored artifacts the way the deployed runtime
loads them (`inspect_v7_assertions.rs`; the loader is `inspect_v7_circuit_profile.rs`'s).
Prints one `ASSERTS` line per circuit and fails
unless every circuit has `non_isolated=0 dead_end_violations=0 wf_violations=0`.

    inspect_v7_assertions.py [--version 7] [--target-dir DIR]

Read-only: it builds the Rust file in a temporary Cargo package against the checked-out workspace.
"""
import argparse
import json
import re
import subprocess
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent


def inspect(root, version, target_dir):
    with tempfile.TemporaryDirectory(prefix='longfellow-v7-assert-inspector-') as directory:
        package = Path(directory)
        (package / 'src').mkdir()
        (package / 'src/main.rs').write_text((HERE / 'inspect_v7_assertions.rs').read_text())
        deps = {'mdoc-zk-runtime': 'applications/mdoc_zk/runtime',
                'core-proto': 'core/proto', 'core-algebra': 'core/algebra',
                'runtime-algebra': 'runtime/algebra'}
        manifest = ('[package]\nname="longfellow-v7-assert-inspector"\nversion="0.0.0"\n'
                    'edition="2021"\n[workspace]\n[dependencies]\n')
        for name, path in deps.items():
            manifest += f'{name}={{path={json.dumps(str(root / "rust" / path))}}}\n'
        (package / 'Cargo.toml').write_text(manifest)
        lock = root / 'rust' / 'Cargo.lock'
        if lock.exists():
            (package / 'Cargo.lock').write_text(lock.read_text())
        cmd = ['cargo', 'run', '--release', '--manifest-path', str(package / 'Cargo.toml')]
        if target_dir:
            cmd += ['--target-dir', str(target_dir)]
        return subprocess.check_output(cmd + ['--', str(version)], text=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('--source', type=Path, default=HERE.parents[2])
    parser.add_argument('--version', type=int, default=7)
    parser.add_argument('--target-dir', type=Path, default=None)
    args = parser.parse_args()
    out = inspect(args.source.resolve(), args.version, args.target_dir)
    bad, seen = 0, 0
    for line in out.splitlines():
        if line.startswith('ARCHIVE'):
            print(line[:120])
        m = re.match(r'^ASSERTS .* non_isolated=(\d+) dead_end_violations=(\d+) '
                     r'wf_violations=(\d+)$', line)
        if m:
            seen += 1
            print(line)
            bad += int(m[1]) + int(m[2]) + int(m[3])
    assert seen == 5, f'expected 5 circuits (sig + hash 1..4), saw {seen}'
    print('Isolated, DeadEnd and WellFormedP hold on all five circuits' if bad == 0
          else f'{bad} violations')
    return 1 if bad else 0


if __name__ == '__main__':
    raise SystemExit(main())
