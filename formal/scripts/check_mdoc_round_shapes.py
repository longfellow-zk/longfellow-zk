#!/usr/bin/env python3
"""Check the closed Lean mdoc round metadata against all current compiler sizes."""
from pathlib import Path
import ast
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
RUST = ROOT.parent / 'rust'
WORK = ROOT / '.lake/mdoc-round-shapes-check'
WORK.mkdir(parents=True, exist_ok=True)
# Compile current sources: never select an unchecked stale circuit library.
subprocess.run(['cargo','build','--release','--lib','--jobs','2'], cwd=RUST, check=True, timeout=300)
deps = RUST / 'target/release/deps'
library = RUST / 'target/release/liblongfellow_zk.rlib'
program = WORK / 'extract'
subprocess.run(['rustc','--edition=2021','-C','panic=abort','-C','target-cpu=native',str(ROOT/'scripts/mdoc_round_shapes.rs'),
                '-L','dependency='+str(deps),'--extern','longfellow_zk='+str(library),'-o',str(program)],
               cwd=RUST, check=True, timeout=180)
result = subprocess.run([str(program)], text=True, capture_output=True, check=True, timeout=180)
(WORK/'compiler-shapes.jsonl').write_text(result.stdout)
rows = [json.loads(line) for line in result.stdout.splitlines()]
source = (ROOT/'lfzk-v2/LfzkV2/Current/MdocRoundShape.lean').read_text()
body = source.split('def binaryRounds',1)[1].split('def primeRounds',1)[0]
binary = [ast.literal_eval(s) for s in re.findall(r'=>\s*(\[[^\]]*\])',body)]
prime = ast.literal_eval(re.search(r'def primeRounds[^\n]*:=\s*(\[[^\]]*\])',source).group(1))
assert len(rows)==len(binary)==4
for index,row in enumerate(rows):
    assert row['attributes']==index+1
    assert row['binary_rounds']==binary[index],row
    assert row['prime_rounds']==prime,row
    rounds=sum(binary[index])+sum(prime)+3*(len(binary[index])+len(prime))+7
    print(f"{index+1} attributes: {rounds} rounds; compiler metadata matches Lean")
