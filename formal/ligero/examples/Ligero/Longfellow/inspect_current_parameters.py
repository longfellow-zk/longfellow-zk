#!/usr/bin/env python3
"""Regenerate CURRENT Rust circuits and check their registered Ligero geometry.

This is a source/parameter inspection, not a Lean implementation-correspondence
proof. Generated circuit IDs and registry labels are recorded separately.
No repository source or circuit artifact is written by this program.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
REGISTRY = Path('rust/applications/mdoc_zk/runtime/src/zk_spec.rs')
VERSION = Path('rust/applications/mdoc_zk/circuits/src/lib.rs')


def registry(root):
    version = int(re.search(r'CURRENT_VERSION: usize = (\d+);',
                           (root / VERSION).read_text())[1])
    source = (root / REGISTRY).read_text().split('pub static CURRENT_ZK_SPECS:', 1)[1]
    rows = []
    for record in re.findall(r'ZkSpecStruct\s*\{(.*?)\n    \}', source, re.S):
        digest = re.search(r'combined_hash:\s*\[(.*?)\]', record, re.S)[1]
        digest = bytes(int(x, 16) for x in re.findall(r'0x([0-9a-f]{2})', digest)).hex()
        attributes = int(re.search(r'num_attributes:\s*(\d+)', record)[1])
        assert 'version: CURRENT_VERSION' in record
        configs = {component: tuple(map(int, re.search(
            rf'ligero_{component}: ligero_config\((\d+), (\d+), (\d+)\)', record).groups()))
                   for component in ('sig', 'hash')}
        rows.append(dict(attributes=attributes, combined_hash=digest, configs=configs))
    assert len(rows) == 4 and {r['attributes'] for r in rows} == {1, 2, 3, 4}
    assert len({r['configs'][c][:2] for r in rows for c in ('sig', 'hash')}) == 1
    return version, rows


def parse_output(root, output):
    version, specs = registry(root)
    sig = re.search(r'^PARAM sig (\d+) (\d+) (\d+) ([0-9a-f]{64})$', output, re.M)
    # Accept the original inspection log, which also printed layer counts.
    if sig is None:
        sig = re.search(r'^PARAM sig (\d+) (\d+) (\d+) ([0-9a-f]{64}) \d+$', output, re.M)
    assert sig, 'Missing signature inspection record'
    hashes = {}
    for line in output.splitlines():
        if line.startswith('PARAM hash '):
            values = line.split()[2:]
            if len(values) == 7: values.pop(5)  # original log's redundant layer count
            a, enc, nw, nq, circuit_id, combined_id = values
            hashes[int(a)] = (int(enc), int(nw), int(nq), circuit_id, combined_id)
    assert set(hashes) == {1, 2, 3, 4}
    source_hash = hashlib.sha256()
    paths = sorted(p for p in (root / 'rust').rglob('*')
                   if p.is_file() and (p.suffix == '.rs' or p.name in ('Cargo.toml', 'Cargo.lock'))
                   and 'target' not in p.parts)
    for path in paths:
        source_hash.update(str(path.relative_to(root)).encode() + b'\0')
        source_hash.update(path.read_bytes())
    rows = []
    for spec in specs:
        generated_id = hashes[spec['attributes']][-1]
        for component in ('sig', 'hash'):
            rate, queries, enc = spec['configs'][component]
            if component == 'sig':
                actual_enc, nw, nq, circuit_id = sig.groups()
                actual_enc, nw, nq = map(int, (actual_enc, nw, nq))
            else:
                actual_enc, nw, nq, circuit_id, _ = hashes[spec['attributes']]
            assert actual_enc == enc, 'Generated and registered geometry differ'
            k = (enc + 1) // (rate + 2)
            n = enc - (2 * k - 1)
            w = k - queries
            nwrow, nqtriples = (nw + w - 1) // w, (nq + w - 1) // w
            rows.append(dict(version=version, attributes=spec['attributes'], component=component,
                source='Rust CURRENT circuit generator', source_tree_sha256=source_hash.hexdigest(),
                registry=str(REGISTRY), circuit_id=circuit_id,
                registered_combined_id=spec['combined_hash'], generated_combined_id=generated_id,
                combined_id_matches_registry=(generated_id == spec['combined_hash']),
                field='P256Base' if component == 'sig' else 'GF2_128',
                field_size=(2**256-2**224+2**192+2**96-1 if component == 'sig' else 2**128),
                block_enc=enc, rateinv=rate, queries=queries, k=k, n=n, w=w,
                d_base=n-k+1, response_dimension_model=2*k,
                response_dimension_implementation=2*k-1, nw=nw, nq=nq, nwrow=nwrow,
                nqtriples=nqtriples, nrow=nwrow+3*nqtriples+3))
    return rows


def inspect(root):
    _, specs = registry(root)
    rate, queries, _ = specs[0]['configs']['sig']
    with tempfile.TemporaryDirectory(prefix='longfellow-current-inspector-') as directory:
        package = Path(directory)
        (package / 'src').mkdir()
        (package / 'src/main.rs').write_text((HERE / 'inspect_current_circuits.rs').read_text())
        deps = {'mdoc-zk-compile': 'applications/mdoc_zk/compile',
                'compile-algebra': 'compile/algebra', 'runtime-proto': 'runtime/proto'}
        manifest = '[package]\nname="longfellow-current-inspector"\nversion="0.0.0"\nedition="2021"\n[workspace]\n[dependencies]\n'
        for name, path in deps.items():
            manifest += f'{name}={{path={json.dumps(str(root / "rust" / path))}}}\n'
        manifest += 'sha2="0.10"\n'
        (package / 'Cargo.toml').write_text(manifest)
        output = subprocess.check_output(['cargo', 'run', '--release', '--manifest-path',
            str(package / 'Cargo.toml'), '--', str(rate), str(queries)], text=True)
    return parse_output(root, output)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, default=HERE.parents[4])
    parser.add_argument('--output', type=Path, default=HERE / 'v8-extracted-parameters.json')
    args = parser.parse_args()
    rows = inspect(args.source.resolve())
    args.output.write_text(json.dumps(rows, indent=2) + '\n')
    mismatches = sum(not r['combined_id_matches_registry'] for r in rows if r['component'] == 'hash')
    print(f'Checked {len(rows)} component geometries; {mismatches} registry ID mismatches.')


if __name__ == '__main__':
    main()
