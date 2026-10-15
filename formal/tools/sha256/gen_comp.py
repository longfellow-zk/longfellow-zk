import os as _os, sys as _sys
# Output root, derived from this file rather than hardcoded: these scripts were written
# on a different machine and carried its absolute paths.
_SHAROOT = _os.path.dirname(_os.path.dirname(_os.path.dirname(_os.path.abspath(__file__))))
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
_HERE = _os.path.dirname(_os.path.abspath(__file__))
"""Generate the final composition for the schedule instances."""
import re, sys, pickle
_sys.path.insert(0, _HERE)
from sha_classify import nodes, consts, layout
from sha_parse import P256
insts = pickle.load(open(_os.path.join(_HERE, "insts.pkl"),"rb"))
# `wordtbl.pkl` was loaded here and never read.  Its producer is not in the repo, so the
# dead load was the only thing stopping this stage from running at all.
ONE = {0, 238}
def sg(c):
    v = consts[c]; return v - P256 if v > P256//2 else v
def lname(n):
    k, v = nodes[n]
    return layout.get(v) if k == 'input' else None
def bitpos(n):
    return int(re.match(r'.*_(\d+)$', lname(n)).group(1))
def unwrap(n):
    k, v = nodes[n]
    if k == 'sum' and len(v) == 1:
        c, a, b = v[0]
        return b if a in ONE else a
    return n
def xlegs(n):
    k, v = nodes[n]
    if k == 'sum' and len(v) == 3: return (v[0][2], v[1][2])
    return None
ROTS = {'s0': (7, 18, 3), 's1': (17, 19, 10)}

def detail(d):
    """per sigma group, per bit j: ('3', midTmplIdx, aLeafBit, bLeafBit, cLeafBit) or ('2', aIdx, bIdx, aBit, bBit)"""
    t, ti, L = d['t'], d['ti'], d['L']
    z = d['z']
    pair = {}
    for c, a, b in nodes[z][1]:
        if a in ONE or b in ONE: continue
        W = -sg(c) // 2
        u, other = (a, b) if xlegs(a) else (b, a)
        j = W.bit_length() - 1
        w = re.match(r'(.*)_\d+$', lname(xlegs(u)[0])).group(1)
        pair[(w, j)] = (u, unwrap(other))
    out = {}
    for tag, w, src in (('s0', d['s0w'], d['t']-15), ('s1', d['s1w'], d['t']-2)):
        r1, r2, sh = ROTS[tag]
        bits = {}
        for n in d['leaves'][1:]:
            if re.match(re.escape(w) + r'_\d+$', lname(n)): bits[bitpos(n)] = n
        rows = []
        for j in range(32):
            if (w, j) in pair:
                u, c = pair[(w, j)]
                la, lb = xlegs(u)
                rows.append(('3', ti[u], bitpos(la), bitpos(lb), bitpos(c), ti[la], ti[lb], ti[c]))
            else:
                a, b = bits[(j+r1) % 32], bits[(j+r2) % 32]
                rows.append(('2', ti[a], ti[b], bitpos(a), bitpos(b)))
        out[tag] = (src, rows)
    return out

if __name__ == "__main__":
    d = insts[0]
    det = detail(d)
    print("t =", d['t'])
    for tag, (src, rows) in det.items():
        print(f"  {tag} <- W{src}: 3-way {sum(1 for r in rows if r[0]=='3')}, 2-way {sum(1 for r in rows if r[0]=='2')}")
        print("   j=0:", rows[0], "  j=31:", rows[31])

# --------------------------------------------------------------------------- emission
def compose(d):
    t, L, ti = d['t'], d['L'], d['ti']
    det = detail(d)
    e = t - 16
    ROT = {'s0': ROTS['s0'], 's1': ROTS['s1']}
    out = []
    A = out.append
    lvdef = f"lvS{t}"
    A(f"""/-! #### Composition for `W{t}` -/

/-- The cone's leaf valuation. -/
noncomputable def {lvdef} (inputs : Nat → F) : Nat → F :=
  fun h => interpDag (raw.toDag (cnstw F)) inputs (mpS{t}.getD h 0)
""")
    # v functions, from the already-emitted group lists
    names = {'a': 0, 'b': 1, 'c': 2, 'd': 3}
    for nm, gi in names.items():
        _, g = d['groups'][gi]
        A(f"noncomputable def vS{t}{nm} (lv : Nat → F) : Nat → F")
        for j, (_, expr) in enumerate(g):
            A(f"  | {j} => {expr}")
        A("  | _ => 0\n")
    A(f"noncomputable def vS{t}p (lv : Nat → F) : Nat → F")
    for j, (_, expr) in enumerate(d['ds']):
        A(f"  | {j} => {expr}")
    A("  | _ => 0\n")
    for nm in ('a','b','c','d'):
        A(f"theorem gS{t}{nm}_eq (lv : Nat → F) :\n"
          f"    gS{t}{nm} lv = (List.range 32).map (fun i => ((2 ^ i : Nat), vS{t}{nm} lv i)) := rfl")
    A(f"theorem dsS{t}_eq (lv : Nat → F) :\n"
      f"    dsS{t} lv = (List.range 32).map (fun i => ((2 ^ i : Nat), vS{t}p lv i)) := rfl\n")
    # indexed booleanity
    sig = {'a': 's0', 'c': 's1'}
    for nm, gi in list(names.items()) + [('p', None)]:
        g = d['ds'] if nm == 'p' else d['groups'][gi][1]
        A(f"""theorem vbS{t}{nm} (lv : Nat → F) (hone : lv 0 = 1) (c0 : cnstw F 0 = 1)
    (c1 : cnstw F 1 = -2) (hlv : ∀ i, i < 161 → lv i = 0 ∨ lv i = 1) :
    ∀ j, j < 32 → vS{t}{nm} lv j = 0 ∨ vS{t}{nm} lv j = 1 := by
  intro j hj
  match j, hj with""")
        rows = det[sig[nm]][1] if nm in sig else None
        for j in range(32):
            if rows is None:
                leaf = int(re.match(r'lv (\d+)$', g[j][1]).group(1))
                A(f"  | {j}, _ => exact hlv {leaf} (by norm_num)")
            else:
                r = rows[j]
                if r[0] == '3':
                    _, U, _, _, _, la, lb, lc = r
                    A(f"  | {j}, _ =>\n"
                      f"      rw [show vS{t}{nm} lv {j} = Quadcert.xorVal "
                      f"(midLeafVal (cnstw F) lv {L} mvS{t} {U}) (lv {lc}) from rfl,\n"
                      f"        Quadcert.midLeafVal_xor_at (cnstw F) lv {L} mvS{t} 0 1 c0 c1 hone "
                      f"{U} {U-L} (by norm_num) {la} {lb} (by rfl)]\n"
                      f"      exact Quadcert.xorVal_isBit (Quadcert.xorVal_isBit "
                      f"(hlv {la} (by norm_num)) (hlv {lb} (by norm_num))) (hlv {lc} (by norm_num))")
                else:
                    _, ia, ib, _, _ = r
                    A(f"  | {j}, _ => exact Quadcert.xorVal_isBit (hlv {ia} (by norm_num)) "
                      f"(hlv {ib} (by norm_num))")
        A(f"  | (n + 32), h => exact absurd h (by omega)")
        A("")
    return "\n".join(out)

def wordleaves(d, w):
    """bit position -> template leaf index, for word name w in this cone"""
    ti = d['ti']
    out = {}
    for n in d['leaves'][1:]:
        nm = lname(n)
        if re.match(re.escape(w) + r'_\d+$', nm): out[bitpos(n)] = ti[n]
    assert len(out) == 32, (d['t'], w, len(out))
    return [out[k] for k in range(32)]

import comp2
def compose2(d):
    return comp2.make(d, detail, wordleaves, lname, bitpos)

if __name__ == "__main__":
    import os
    d = insts[0]
    hdr = """import quadcert.Bridge.Sha256.S2SchedA
import quadcert.Bridge.Sha256.S2Words
set_option maxRecDepth 8000000
set_option maxHeartbeats 4000000
namespace Sha256Blk
open Quadcert Quadcert.Gen.Sha256Blk
variable {F : Type} [Field F]

"""
    open(_os.path.join(_SHAROOT, "circuits", "quadcert", "CompT.lean"),"w").write(
        hdr + compose(d) + chr(10) + compose2(d) + chr(10) + comp2.final(d) + "\nend Sha256Blk\n")
    print("emitted CompT.lean")
