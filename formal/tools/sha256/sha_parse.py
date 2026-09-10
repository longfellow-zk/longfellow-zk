import re, glob, os, json

# Which artifact to read.  `Sha256Blk` is the p256 circuit these generators were written for;
# `Sha256Gf2` is the same circuit compiled over GF(2^128), whose assertion tree is identical but
# whose cones are not.  Override with `SHA_ARTIFACT=Sha256Gf2`.
NAME = os.environ.get("SHA_ARTIFACT", "Sha256Blk")
_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
GEN = os.path.join(_ROOT, "circuits", "quadcert", "Gen", NAME)
P256 = 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff

def parse_nodes():
    chunks = {}
    for f in glob.glob(os.path.join(GEN, f"{NAME}Nodes*.lean")):
        m = re.search(r'def nodes_(\d+) : List RawNode :=\s*\n\s*\[(.*?)\]\s*\n\s*\n', open(f).read(), re.S)
        if not m: 
            m = re.search(r'def nodes_(\d+) : List RawNode :=\s*\n\s*\[(.*)\]', open(f).read(), re.S)
        idx = int(m.group(1)); body = m.group(2)
        items = []
        for tok in re.finditer(r'\.input (\d+)|\.sum \[([^\]]*)\]|\.assert0 (\d+)', body):
            if tok.group(1) is not None:
                items.append(('input', int(tok.group(1))))
            elif tok.group(2) is not None:
                trip = re.findall(r'\((\d+),\s*(\d+),\s*(\d+)\)', tok.group(2))
                items.append(('sum', [(int(a),int(b),int(c)) for a,b,c in trip]))
            else:
                items.append(('assert0', int(tok.group(3))))
        chunks[idx] = items
    nodes = []
    for i in sorted(chunks): nodes.extend(chunks[i])
    return nodes

def parse_constNat():
    s = open(os.path.join(GEN, f"{NAME}Base.lean")).read()
    body = s.split("def constNat : Nat → Nat")[1]
    d = {}
    for m in re.finditer(r'\|\s*(\d+)\s*=>\s*(0x[0-9a-fA-F]+)', body):
        d[int(m.group(1))] = int(m.group(2), 16)
        if len(d) > 400: break
    return d

def parse_layout():
    s = open(os.path.join(GEN, f"{NAME}Data.lean")).read()
    m = re.search(r'layout := \[(.*?)\]\n', s, re.S)
    return {int(a): b for a, b in re.findall(r'\((\d+),\s*"([^"]*)"\)', m.group(1))}

if __name__ == "__main__":
    nodes = parse_nodes(); consts = parse_constNat(); layout = parse_layout()
    print("nodes:", len(nodes), "consts:", len(consts), "layout:", len(layout))
    print("node 0:", nodes[0], " node 238:", nodes[238])
    print("node 19753 kind:", nodes[19753][0], "terms:", len(nodes[19753][1]))
    print("node 19756:", nodes[19756][0], nodes[19756][1][:3])
