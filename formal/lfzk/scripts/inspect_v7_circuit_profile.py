#!/usr/bin/env python3
"""Print the sumcheck layer profile of the REGISTERED mdoc circuits of one version (default the
deployed v7: `ZK_SPECS` in `rust/applications/mdoc_zk/runtime/src/zk_spec.rs`), loaded from the
stored artifacts the way the deployed runtime loads them, and write them to
`v7-circuit-profiles.json`, the profile the Lean v7 rows use (`v7_rows.py --check`).

v7 is no longer what the checked-out compiler produces, so this driver reads the stored archives
(`rust/applications/mdoc_zk/artifacts/circuits/<combined_hash>.lfa2`, via
`mdoc_zk_runtime::materialize`).  `inspect_v7_circuit_profile.rs` checks, per attribute count,
that the archive's combined ID and the combined ID recomputed from its entries both equal the
registry's `combined_hash`, that each circuit's ID recomputed from the parsed circuit equals the
entry's ID, and it reports the deployed verifier's Ligero geometry (`ZkVerifier::geometry`).

Each JSON record carries the circuit profile (`component`, `attributes`, `logv`,
`npublic_input`, `nlayers`, `logw`, `nw`, `total_sumcheck_rounds`) plus the provenance and
geometry keys `version`, `combined_hash` (the archive's), `circuit_id`, `ninput`, and the Ligero
geometry `block`, `dblock`, `block_enc`, `nreq`, `nrow` and the derived Lean geometry
`ligero_n = block_enc - dblock`, `ligero_k = block`, `ligero_w = block - nreq`.

    inspect_v7_circuit_profile.py                       # v7 -> scripts/v7-circuit-profiles.json
    inspect_v7_circuit_profile.py --target-dir DIR      # reuse a Cargo build directory

Read-only: it builds `inspect_v7_circuit_profile.rs` in a temporary Cargo package against the
checked-out Rust workspace; nothing in the repository other than the output JSON is written.
"""
import argparse
import json
import re
import subprocess
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
REGISTRY = Path('rust/applications/mdoc_zk/runtime/src/zk_spec.rs')


def registry(root, version):
    """`(attributes, combined_hash_hex, hash config, sig config)` for every `ZK_SPECS` record of
    `version`, read from the registry source (an independent cross-check of the Rust side)."""
    source = (root / REGISTRY).read_text()
    source = source.split('pub static ZK_SPECS:', 1)[1].split('pub static CURRENT_ZK_SPECS:', 1)[0]
    out = {}
    for record in re.findall(r'ZkSpecStruct\s*\{(.*?)\n    \}', source, re.S):
        if int(re.search(r'version: (\d+)', record)[1]) != version:
            continue
        attrs = int(re.search(r'num_attributes: (\d+)', record)[1])
        digest = ''.join(f'{int(b, 16):02x}' for b in
                         re.findall(r'0x([0-9a-f]{2})', re.search(r'combined_hash: \[(.*?)\]',
                                                                  record, re.S)[1]))
        hcfg = tuple(map(int, re.search(r'ligero_hash: ligero_config\((\d+), (\d+), (\d+)\)',
                                        record).groups()))
        scfg = tuple(map(int, re.search(r'ligero_sig: ligero_config\((\d+), (\d+), (\d+)\)',
                                        record).groups()))
        out[attrs] = (digest, hcfg, scfg)
    return out


def inspect(root, version, target_dir):
    with tempfile.TemporaryDirectory(prefix='longfellow-v7-profile-inspector-') as directory:
        package = Path(directory)
        (package / 'src').mkdir()
        (package / 'src/main.rs').write_text((HERE / 'inspect_v7_circuit_profile.rs').read_text())
        deps = {'mdoc-zk-runtime': 'applications/mdoc_zk/runtime',
                'core-proto': 'core/proto', 'core-algebra': 'core/algebra',
                'runtime-algebra': 'runtime/algebra', 'runtime-proto': 'runtime/proto',
                'runtime-zk': 'runtime/zk'}
        manifest = ('[package]\nname="longfellow-v7-profile-inspector"\nversion="0.0.0"\n'
                    'edition="2021"\n[workspace]\n[dependencies]\n')
        for name, path in deps.items():
            manifest += f'{name}={{path={json.dumps(str(root / "rust" / path))}}}\n'
        (package / 'Cargo.toml').write_text(manifest)
        lock = root / 'rust' / 'Cargo.lock'
        if lock.exists():   # pin the workspace's resolved versions
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
    parser.add_argument('--output', type=Path, default=None)
    args = parser.parse_args()
    root = args.source.resolve()
    output_path = args.output or HERE / f'v{args.version}-circuit-profiles.json'
    reg = registry(root, args.version)
    assert sorted(reg) == [1, 2, 3, 4], reg
    output = inspect(root, args.version, args.target_dir)

    archives, geoms, rows = {}, {}, []
    for line in output.splitlines():
        m = re.match(r'^ARCHIVE (\d+) (\S+) version=(\d+) circuit_version=(\d+) combined=(\w+) '
                     r'sig_id=(\w+) hash_id=(\w+) ligero_hash=\((\d+),(\d+),(\d+)\) '
                     r'ligero_sig=\((\d+),(\d+),(\d+)\)$', line)
        if m:
            attrs = int(m[1])
            digest, hcfg, scfg = reg[attrs]
            assert int(m[3]) == args.version
            assert m[5] == digest, (attrs, m[5], digest)
            assert tuple(map(int, m.groups()[7:10])) == hcfg
            assert tuple(map(int, m.groups()[10:13])) == scfg
            archives[attrs] = dict(combined=m[5], sig_id=m[6], hash_id=m[7], hcfg=hcfg,
                                   scfg=scfg, circuit_version=int(m[4]))
            print(f"archive attrs={attrs}: combined {m[5]} = registry v{args.version}; "
                  f"circuit_version={m[4]} sig_id={m[6][:16]}… hash_id={m[7][:16]}…")
            continue
        m = re.match(r'^GEOMETRY (\w+) (\d+) block=(\d+) dblock=(\d+) block_enc=(\d+) nreq=(\d+) '
                     r'r=(\d+) nrow=(\d+) mc_pathlen=(\d+) logw=\[([\d,]*)\]$', line)
        if m:
            geoms[(m[1], int(m[2]))] = dict(
                block=int(m[3]), dblock=int(m[4]), block_enc=int(m[5]), nreq=int(m[6]),
                r=int(m[7]), nrow=int(m[8]), mc_pathlen=int(m[9]),
                logw=[int(x) for x in m[10].split(',') if x])
            continue
        m = re.match(r'^PROFILE (\w+) (\d+) logv=(\d+) npublic=(\d+) nlayers=(\d+) '
                     r'logw=\[([\d,]*)\] nw=\[([\d,]*)\] ninput=(\d+) id=(\w+)$', line)
        if not m:
            continue
        component, attributes, logv, npublic, nlayers, logw, nw, ninput, cid = m.groups()
        logw = [int(x) for x in logw.split(',') if x]
        nw = [int(x) for x in nw.split(',') if x]
        assert len(logw) == int(nlayers) == len(nw)
        rows.append(dict(component=component, attributes=int(attributes), logv=int(logv),
                         npublic_input=int(npublic), nlayers=int(nlayers), logw=logw, nw=nw,
                         total_sumcheck_rounds=2 * sum(logw), version=args.version,
                         circuit_id=cid, ninput=int(ninput)))

    assert sorted(archives) == [1, 2, 3, 4]
    assert len({a['sig_id'] for a in archives.values()}) == 1
    for row in rows:
        g = geoms[(row['component'], row['attributes'])]
        assert g['logw'] == row['logw'], row['component']
        assert g['r'] == g['nreq'] and g['dblock'] == 2 * g['block'] - 1
        if row['component'] == 'sig':
            arch = archives[1]
            assert row['circuit_id'] == arch['sig_id']
            cfg = arch['scfg']
        else:
            arch = archives[row['attributes']]
            assert row['circuit_id'] == arch['hash_id']
            cfg = arch['hcfg']
        rateinv, nreq, block_enc = cfg
        # the Ligero parameter code (`runtime/ligero/src/param.rs`, `lib/ligero/ligero_param.h`):
        # block = (block_enc + 1) / (2 + rateinv), dblock = 2 block - 1, block_ext = block_enc - dblock
        assert g['block'] == (block_enc + 1) // (2 + rateinv)
        assert g['block_enc'] == block_enc and g['nreq'] == nreq
        row['combined_hash'] = arch['combined']
        row.update(block=g['block'], dblock=g['dblock'], block_enc=g['block_enc'],
                   nreq=g['nreq'], nrow=g['nrow'], ligero_n=g['block_enc'] - g['dblock'],
                   ligero_k=g['block'], ligero_w=g['block'] - g['nreq'])
        print(f"{row['component']} attrs={row['attributes']}: logv={row['logv']} "
              f"npublic={row['npublic_input']} nl={row['nlayers']} logw={row['logw']} "
              f"rounds={row['total_sumcheck_rounds']} ninput_wires={row['nw'][-1]} "
              f"ninput={row['ninput']}  Ligero n={row['ligero_n']} k={row['ligero_k']} "
              f"w={row['ligero_w']} nrow={row['nrow']}")
    output_path.write_text(json.dumps(rows, indent=2) + '\n')
    print(f"wrote {output_path}")


if __name__ == '__main__':
    main()
