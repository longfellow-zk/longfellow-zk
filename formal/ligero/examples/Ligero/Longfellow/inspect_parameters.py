#!/usr/bin/env python3
import argparse,hashlib,json,re,subprocess,struct
from pathlib import Path
parser=argparse.ArgumentParser(description='Verify registered V7 circuit IDs and extract actual Ligero parameters.')
parser.add_argument('--source',type=Path,default=Path(__file__).resolve().parents[5])
parser.add_argument('--output',type=Path,default=Path('extracted-parameters.json'))
args=parser.parse_args()
ROOT=args.source.resolve()
SPECS=ROOT/'lib/circuits/mdoc/zk_spec.cc'
pattern=re.compile(r'\{"longfellow-libzk-v1",\s*"([0-9a-f]{64})",\s*(\d+),\s*(7),\s*(\d+),\s*(\d+)\}')
class Reader:
 def __init__(self,data):self.data=data;self.offset=0
 def take(self,n):
  b=self.data[self.offset:self.offset+n];assert len(b)==n;self.offset+=n;return b
 def num(self):return int.from_bytes(self.take(3),'little')
 def circuit(self):
  assert self.take(1)==b'\x01'
  keys=['field_id','noutputs','ncopies','npublic','subfield_boundary','ninputs','nlayers','nconstants']
  c=dict(zip(keys,[self.num() for _ in keys]))
  assert c['field_id'] in (1,4)
  size=32 if c['field_id']==1 else 16
  constants=[self.take(size) for _ in range(c['nconstants'])]
  sha=hashlib.sha256()
  def num(n):sha.update(struct.pack('<Q',n))
  if c['field_id']==1:
   num(1);sha.update((2**256-2**224+2**192+2**96-2).to_bytes(32,'little'))
  else:num(2);num(128)
  for value in [c['noutputs'],(c['noutputs']-1).bit_length(),c['ncopies'],0,c['nlayers'],c['ninputs'],c['npublic'],c['subfield_boundary']]:num(value)
  c['layers']=[]
  for _ in range(c['nlayers']):
   layer=dict(zip(['logw','nwires','nterms'],[self.num() for _ in range(3)]))
   for value in [layer['nwires'],layer['logw'],layer['nterms']]:num(value)
   terms=self.take(layer['nterms']*12);g=h0=h1=0;batch=bytearray()
   for i in range(0,len(terms),12):
    ds=[int.from_bytes(terms[i+j:i+j+3],'little') for j in (0,3,6,9)]
    def delta(n):return -(n>>1) if n&1 else n>>1
    g=(g+delta(ds[0]))&0xffffffff;h0=(h0+delta(ds[1]))&0xffffffff;h1=(h1+delta(ds[2]))&0xffffffff
    batch.extend(struct.pack('<QQQ',g,h0,h1));batch.extend(constants[ds[3]])
    if len(batch)>65536:sha.update(batch);batch.clear()
   sha.update(batch);c['layers'].append(layer)
  c['circuit_id']=self.take(32).hex()
  assert sha.hexdigest()==c['circuit_id'],(sha.hexdigest(),c['circuit_id'])
  c['pad_size']=sum(4*x['logw']+3 for x in c['layers'])
  c['nw']=c['ninputs']-c['npublic']+c['pad_size'];c['nq']=c['nlayers']
  return c
rows=[]
for digest,attributes,version,enc_hash,enc_sig in pattern.findall(SPECS.read_text()):
 file=ROOT/'rust/src/mdoc/artifacts/circuits'/digest
 compressed=file.read_bytes();actual=hashlib.sha256(compressed).hexdigest()
 r=Reader(subprocess.check_output(['zstd','-q','-d','-c',str(file)]))
 circuits=[r.circuit(),r.circuit()];assert r.offset==len(r.data)
 assert [c['field_id'] for c in circuits]==[1,4]
 assert hashlib.sha256(b''.join(bytes.fromhex(c['circuit_id']) for c in circuits)).hexdigest()==digest
 for circuit,enc,component in zip(circuits,[int(enc_sig),int(enc_hash)],['sig','hash']):
  rate=7;queries=132
  block=(enc+1)//(2+rate);dblock=2*block-1;n=enc-dblock;w=block-queries
  nwrow=(circuit['nw']+w-1)//w;nqtriples=(circuit['nq']+w-1)//w
  rows.append(dict(version=int(version),attributes=int(attributes),component=component,artifact=str(file.relative_to(ROOT)),artifact_sha256=actual,circuit_id=circuit['circuit_id'],field='P256Base' if component=='sig' else 'GF2_128',field_size=2**256-2**224+2**192+2**96-1 if component=='sig' else 2**128,block_enc=enc,rateinv=rate,queries=queries,k=block,n=n,w=w,d_base=n-block+1,response_dimension_model=2*block,response_dimension_implementation=dblock,nw=circuit['nw'],nq=circuit['nq'],nwrow=nwrow,nqtriples=nqtriples,nrow=nwrow+3*nqtriples+3,pad_size=circuit['pad_size'],ninputs=circuit['ninputs'],npublic=circuit['npublic'],layer_logw=[x['logw'] for x in circuit['layers']]))
args.output.write_text(json.dumps(rows,indent=2)+'\n')
print(f'Validated {len(rows)} component parameter records against their canonical circuit IDs')
