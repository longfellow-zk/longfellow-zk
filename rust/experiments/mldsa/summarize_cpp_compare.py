#!/usr/bin/env python3
"""Report matched-slicing release C++/Rust MLDSA measurements."""
import csv
import hashlib
import json
from pathlib import Path
import re
import statistics

HERE = Path(__file__).resolve().parent
ROOT = Path("target/cpp-aligned")
def records(path, marker):
    return [dict(re.findall(r"(\w+)=([^\s]+)", line)) for line in path.read_text().splitlines() if line.startswith(marker + " ")]
def peak(path):
    return int(re.search(r"Maximum resident set size \(kbytes\):\s*(\d+)", path.read_text())[1])
def lfc2_dimensions(path):
    data=path.read_bytes(); assert data[:4]==b"LFC2"; pos=4
    def u():
        nonlocal pos
        result=shift=0
        while True:
            b=data[pos]; pos+=1; result|=(b & 127)<<shift
            if b < 128: return result
            shift+=7
    field, outputs, copies, public, subfield, inputs, nl, constants=[u() for _ in range(8)]
    assert field==0 and copies==1 and subfield==inputs
    pos+=18*constants
    layers=[]
    for _ in range(nl):
        logw,nw,nd=u(),u(),u()
        for _ in range(4*nd): u()
        lengths=[]
        for _ in range(u()):
            n=u(); lengths.append(n)
            for _ in range(n): u()
        terms=0
        for _ in range(u()): terms+=lengths[u()]
        layers.append(dict(logw=logw,nw=nw,deltas=nd,terms=terms))
    assert pos+32==len(data)
    return dict(outputs=outputs,max_width=max([outputs]+[l['nw'] for l in layers]),constants=constants,layers_detail=layers)

grid=list(csv.DictReader((HERE/"results/plucker-sf18/plucker-grid-summary.csv").open()))
summary=[]; timing_rows=[]
for variant in [44,65]:
    base=next(r for r in grid if r['dataset']==f'mldsa{variant}' and (r['period'],r['bits'],r['first'])==('4','0','1'))
    for lang in ['cpp','rust']:
        stem=f'mldsa{variant}' if lang=='cpp' else f'rust{variant}'
        timing=records(ROOT/f'{stem}-timing.log','CPP_PROOF' if lang=='cpp' else 'ORDER_PROOF')
        memory=records(ROOT/f'{stem}-memory.log','CPP_PROOF' if lang=='cpp' else 'ORDER_PROOF')
        assert len(timing)==5 and len(memory)==1
        if lang=='cpp':
            assert all(r['verified']=='1' for r in timing+memory)
            g=records(ROOT/f'{stem}-compile.log','CPP_GEOMETRY')[0]
            s=records(ROOT/f'{stem}-compile.log','CPP_CIRCUIT')[0]
            row=dict(variant=variant,language=lang,**{k:int(g[k]) for k in ['inputs','public','outputs','wires','noninput_wires','terms','layers','max_width','deltas','global_deltas','constants','field_bytes','subfield_bytes','subfield_boundary']},
                     lfc1_raw=int(s['raw']),lfc1_z16=int(s['z16']),lfc1_z22=int(s['z22']))
        else:
            for p in [ROOT/f'{stem}-timing.log',ROOT/f'{stem}-memory.log']: assert 'test result: ok.' in p.read_text()
            path=Path(f'target/plucker-grid-sf18/p4-b0-r1/mldsa{variant}/mldsa{variant}-wire_whole-b3-w10000000-o4-shape_classes-reuse.lfc2')
            dims=lfc2_dimensions(path)
            row=dict(variant=variant,language=lang,**{k:int(base[k]) for k in ['inputs','public','wires','terms','layers','deltas','field_bytes','subfield_bytes','subfield_boundary','lfc1_raw','lfc1_z22']},
                     outputs=dims['outputs'],max_width=dims['max_width'],constants=dims['constants'],noninput_wires=int(base['wires'])-int(base['inputs']),
                     lfc2_raw=int(base['raw']),lfc2_z16=int(base['z16']),lfc2_z22=int(base['z22']))
            assert row['wires']==row['outputs']+sum(l['nw'] for l in dims['layers_detail'])
            assert row['terms']==sum(l['terms'] for l in dims['layers_detail'])
        row['private_inputs']=row['inputs']-row['public']
        for k in ['commit_ms','prove_ms','total_prover_ms','verify_ms','load_ms','proof']:
            row[k]=statistics.median(float(r[k]) for r in timing)
        row['proof_min']=min(int(r['proof']) for r in timing)
        row['proof_max']=max(int(r['proof']) for r in timing)
        for k in ['witnesses','constraints','block_enc']: row[k]=int(timing[0][k]); assert all(int(r[k])==row[k] for r in timing+memory)
        row['padding_witnesses']=row['witnesses']-row['private_inputs']
        row['peak_rss_kib']=peak(ROOT/f'{stem}-memory.log')
        summary.append(row)
        for r in timing: timing_rows.append(dict(language=lang,variant=variant,**r))

def write_csv(path,rows):
    keys=list(dict.fromkeys(k for r in rows for k in r))
    with path.open('w',newline='') as f:
        w=csv.DictWriter(f,keys); w.writeheader(); w.writerows(rows)
write_csv(HERE/'results/cpp-aligned-summary.csv',summary)
write_csv(HERE/'results/cpp-aligned-timings.csv',timing_rows)
index={(r['language'],r['variant']):r for r in summary}
columns=[index[lang,v] for v in [44,65] for lang in ['rust','cpp']]
def table(metrics):
    result=['| Metric | Rust 44 | C++ 44 | Rust 65 | C++ 65 |','|---|---:|---:|---:|---:|']
    for label,key,div,precision in metrics:
        values=[]
        for r in columns:
            values.append('—' if key not in r else f"{r[key]/div:,.{precision}f}")
        result.append('| '+label+' | '+' | '.join(values)+' |')
    return '\n'.join(result)
text=['# Release C++ versus selected Rust MLDSA', '',
'## Configuration and scope', '',
'Both MLDSA-44 and MLDSA-65 use period 4, an extra cut after round 0, no bit pluckers, and `subfield_boundary = ninput`. '
'Cuts are after zero-based rounds [0,3,7,11,15,19,23]. Both prove the first committed C++ fixture, with an expanded public key and a supplied private mu. '
'Key expansion and message-to-mu hashing are outside these circuits. Both use the same fp24 degree-six extension (q=8,380,417, x^6−7), XOR-basis SHAKE operations, '
'CRT-based Reed–Solomon interpolation, Ligero rate inverse 4, and 128 opened columns.', '',
'The only C++ configuration changes are the requested slicing overlay and full-input subfield metadata. The harness includes the committed C++ test source. '
'The C++ source tree under lib/ is unchanged; the isolated include overlay is used by both circuit and witness templates. '
'Native SHAKE witness construction records all 24 rounds and is unaffected in the reused object code. All original input witnesses were checked to lie in the subfield.', '',
'| Remaining difference | Rust | C++ |','|---|---|---|',
'| Sumcheck | Dense hand-major | Existing round-major / sparse binding |',
'| Circuit order | Whole / shape_classes / reuse | Existing Morton ordering |',
'| Main stored format | Segmented LFC2 | LFC1 |',
'| Field serialization | 18-byte extension / 3-byte base | 24-byte extension / 4-byte base |',
'| Ligero block selection | Existing CRT-aware optimizer | Existing power-of-two optimizer |',
'| Release compilation | rustc 1.97.1, O3/LTO, native CPU | GCC 14.2.0, O3, NDEBUG, mpclmul; existing CMake optimization settings |',
'| Benchmark RNG | Existing deterministic test RNG | Existing SecureRandomEngine |', '',
'Hardware: AMD Ryzen 9 9950X. All four timing batches ran serially, with no compilation or compression overlap; five complete verified flows per implementation/variant. '
'Prover time is commit + prove; setup, loading, witness generation and serialization are excluded. Verification includes commitment receipt and verification of the parsed proof, '
'but excludes proof parsing and verifier construction. Each proof was serialized, parsed, and verified. Rust additionally asserted byte equality with the previously saved selected proof.', '',
'Peak RSS is measured with `/usr/bin/time -v` in a separate fresh one-flow process per implementation/variant. It includes circuit loading, native witnesses, proving, proof parsing, and verification; '
'it excludes offline circuit compilation and compression. C++ loads its raw LFC1 file; Rust loads raw LFC2. Loading is part of memory use, not prover time. '
'The timing-process multi-flow high-water marks are not used as the headline memory measurement.', '',
'These are implementation/configuration comparisons, not a controlled claim about the intrinsic speed of C++ versus Rust. Serialization, scheduling, geometry selection, and compiler settings still differ as requested.', '',
'## Circuit geometry', '', table([(label,key,1,0) for label,key in [
('Input wires','inputs'),('Public input wires','public'),('Private input wires','private_inputs'),('Output wires','outputs'),('Total wires, including inputs/outputs','wires'),
('Non-input wires','noninput_wires'),('Terms','terms'),('Layers','layers'),('Maximum layer/input width','max_width'),('Sum of layer-local distinct deltas','deltas'),('Distinct coefficients','constants'),
('Proof witnesses, including padding','witnesses'),('Padding witnesses','padding_witnesses'),('Proof constraints','constraints'),('Ligero block_enc','block_enc')]]), '',
'C++ retains 64 public bytes (512 input wires) for `Pk::tr`; `assert_valid_signature_on_mu` does not consume them. Rust omits that unused field. '
'Private input counts therefore match exactly. This difference was not changed in C++, per the instruction to leave everything else alone. '
'Total wires use the same convention on both sides: final output width plus the sum of each layer input width.', '',
'## Bytes', '', table([(label,key,1,0) for label,key in [
('Raw LFC1','lfc1_raw'),('LFC1 zstd-22','lfc1_z22'),('Raw LFC2','lfc2_raw'),('LFC2 zstd-22','lfc2_z22'),('Proof, median','proof'),('Proof, minimum','proof_min'),('Proof, maximum','proof_max')]]), '',
'All sizes are exact bytes. C++ has no LFC2 implementation, so those entries are intentionally blank. Both compression paths use zstd 1.5.7 at level 22. '
'Rust LFC1 is smaller after compression than LFC2, but LFC2 is the selected directly usable compact runtime representation. The experimental relative-reference LFR1 format is not used in these benchmarks. '
'C++ proof byte counts vary across samples because its RNG is nondeterministic and Merkle paths are batched. Circuit and public-input bytes are not included in proof size.', '',
'## Performance', '', table([('Commit, ms','commit_ms',1,3),('Prove excluding commit, ms','prove_ms',1,3),('Total prover, ms','total_prover_ms',1,3),('Verifier, ms','verify_ms',1,3),('Load + ID, ms','load_ms',1,3),('Fresh-process peak RSS, MiB','peak_rss_kib',1024,1)]), '',
'Load+ID is diagnostic: C++ loads once per five-flow process while Rust reloads before each flow. It includes file reading and ID validation, not zstd decompression. '
'No isolated FFT/CRT microbenchmark was rerun; the table measures complete end-to-end proof arithmetic.', '',
'## Interpretation', '']
for v in [44,65]:
    r,c=index['rust',v],index['cpp',v]
    text.append(f"- MLDSA-{v}: Rust has {100*(1-r['terms']/c['terms']):.2f}% fewer terms and {100*(r['wires']/c['wires']-1):.2f}% more wires. "
                f"Its selected compressed LFC2 is {100*(1-r['lfc2_z22']/c['lfc1_z22']):.2f}% smaller than C++ compressed LFC1. "
                f"Proving is {c['total_prover_ms']/r['total_prover_ms']:.2f}× faster, verification {c['verify_ms']/r['verify_ms']:.2f}× faster; "
                f"proofs are {100*(1-r['proof']/c['proof']):.2f}% smaller and peak RSS {100*(1-r['peak_rss_kib']/c['peak_rss_kib']):.2f}% lower.")
text+=['','The earlier 2.3× term regression is not present in this aligned comparison. The remaining compressed-size gap is much larger than the small term-count difference: '
        'Rust has far fewer distinct coordinate deltas and a different traversal/storage policy. Proof-size savings should not all be attributed to scheduling: '
        'the 18/3 versus 24/4 byte encoding and different block selection are substantial confounders. No additional C++ optimization was applied.','',
        '## Artifacts','',
        '[C++ harness](cpp_compare.cc) · [Slicing overlay](cpp_compare_include/circuits/tests/sha3/sha3_slicing.h) · [Summary CSV](results/cpp-aligned-summary.csv) · [Individual timing samples](results/cpp-aligned-timings.csv)','',
        'Raw circuits, compressed C++ circuits, serialized C++ proofs, geometry logs, timing logs and fresh-memory logs are under `target/cpp-aligned`. '
        'C++ compilation/compression ran separately and in parallel; the compile times and compiler peak RSS in those logs are diagnostics, not comparable prover measurements.','']
(HERE/'CPP_ALIGNED_REPORT.md').write_text('\n'.join(text))
paths=[HERE/'cpp_compare.cc',HERE/'cpp_compare_include/circuits/tests/sha3/sha3_slicing.h',ROOT/'cpp_compare',Path('target/release/deps/template_proofs-1eba8861353003c4')]
(ROOT/'provenance.json').write_text(json.dumps({str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},indent=2)+'\n')
print(table([('Prover ms','total_prover_ms',1,3),('Verifier ms','verify_ms',1,3),('Proof bytes','proof',1,0),('Peak MiB','peak_rss_kib',1024,1)]))
