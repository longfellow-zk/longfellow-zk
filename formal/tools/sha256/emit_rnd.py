import os as _os, sys as _sys
# Output root, derived from this file rather than hardcoded: these scripts were written
# on a different machine and carried its absolute paths.
_SHAROOT = _os.path.dirname(_os.path.dirname(_os.path.dirname(_os.path.abspath(__file__))))
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
_HERE = _os.path.dirname(_os.path.abspath(__file__))
import re, sys, pickle, os
_sys.path.insert(0, _HERE)
from gen_rnd import *
bit2assert = {}
for (_r,_x,_y) in asserts:
    _k,_v = nodes[_r]
    if _k=='sum' and len(_v)==2:
        (k1,a1,b1),(k2,a2,b2) = _v
        if k1==0 and a1==0 and k2==2 and a2==b2==b1: bit2assert[b1] = _r
NL = chr(10)
OUT = _os.path.join(_SHAROOT, "circuits", "quadcert", "Bridge", "Sha256")
insts = pickle.load(open(_os.path.join(_HERE, "rinsts.pkl"),"rb"))
ROT = {'S1': (6,11,25), 'S0': (2,13,22)}
lst = lambda xs: "[" + ", ".join(xs) + "]"

def cdef(k):
    v = sg(k)
    return (f"  have c{k} : cnstw F {k} = (({v} : Nat) : F) := cnstw_pos {k} {v} (by rfl)" if v > 0
            else f"  have c{k} : cnstw F {k} = -(({-v} : Nat) : F) := cnstw_neg {k} {-v} (by rfl) (by norm_num)")

def sigma_rows(d, w, rots, tag):
    """bit j -> (mid tmpl idx, third-leg tmpl idx)"""
    ti = d['ti']; mids = {}
    for m in d['xormids']:
        l1, l2 = xlegs(m)
        if wname(l1) == w and wname(l2) == w:
            mids[frozenset((bitpos(l1), bitpos(l2)))] = m
    bits = d['words'][w]
    out = []
    for j in range(32):
        idx = [(j+r) % 32 for r in rots]
        hit = [(x,y) for x in range(3) for y in range(3) if x < y and frozenset((idx[x],idx[y])) in mids]
        assert len(hit) == 1, (d['t'], tag, j)
        x, y = hit[0]
        third = [k for k in range(3) if k not in (x, y)][0]
        out.append((ti[mids[frozenset((idx[x], idx[y]))]], ti[bits[idx[third]]],
                    idx[x], idx[y], idx[third]))
    return out

def maj_rows(d):
    ti = d['ti']; t = d['t']
    a, b = statename(t,0), statename(t,1)
    mids = {}
    for m in d['xormids']:
        l1, l2 = xlegs(m)
        if {wname(l1), wname(l2)} == {a, b}: mids[bitpos(l1)] = m
    return [ti[mids[j]] for j in range(32)]

def groups(d):
    t, n, ti, L = d['t'], d['n'], d['ti'], d['L']
    W = d['words']; nm = f"R{n}_{t}"
    a,b,c,dd,e,f,g,h = (statename(t,i) for i in (0,1,2,3,4,5,6,7))
    wt = f"input_block{t}" if t < 16 else f"outw{t-16}"
    lf = lambda w, j: f"lv {ti[W[w][j]]}"
    S1 = [(f"Quadcert.xorVal (midLeafVal (cnstw F) lv {L} mv{nm} {u}) (lv {th})")
          for u, th, *_ in sigma_rows(d, e, ROT['S1'], 'S1')]
    Ch = [f"Quadcert.chVal ({lf(e,j)}) ({lf(f,j)}) ({lf(g,j)})" for j in range(32)]
    if n == 6:
        gs = [(dd, [lf(dd,j) for j in range(32)]), (h, [lf(h,j) for j in range(32)]),
              ('Sigma1', S1), ('Ch', Ch), (wt, [lf(wt,j) for j in range(32)])]
        out = f"oute{t}"
    else:
        S0 = [(f"Quadcert.xorVal (midLeafVal (cnstw F) lv {L} mv{nm} {u}) (lv {th})")
              for u, th, *_ in sigma_rows(d, a, ROT['S0'], 'S0')]
        mj = maj_rows(d)
        def majentry(j):
            u = mj[j]
            la, lb = (ti[x] for x in xlegs([m for m in d['xormids'] if ti[m] == u][0]))
            return (f"Quadcert.majVal (lv {la}) (lv {lb}) ({lf(c,j)}) "
                    f"(midLeafVal (cnstw F) lv {L} mv{nm} {u})")
        Mj = [majentry(j) for j in range(32)]
        gs = [(h, [lf(h,j) for j in range(32)]), ('Sigma1', S1), ('Ch', Ch),
              (wt, [lf(wt,j) for j in range(32)]), ('Sigma0', S0), ('Maj', Mj)]
        out = f"outa{t}"
    ds = [lf(out, j) for j in range(32)]
    return gs, ds, out

def emit(d):
    t, n, L, M, ti = d['t'], d['n'], d['L'], d['M'], d['ti']
    nm = f"R{n}_{t}"
    T = lambda x: ti[x]
    mid_terms = {x: [(k, T(a), T(b)) for k, a, b in nodes[x][1]] for x in d['mids']}
    ts_terms = [(k, T(a), T(b)) for k, a, b in nodes[d['z']][1]]
    ks = sorted({k for k,_,_ in ts_terms} | {k for x in d['mids'] for k,_,_ in mid_terms[x]})
    jm = T(d['merged']) - L
    gs, ds, outw = groups(d)
    o = []; A = o.append
    A(f"/-! ### Round {t}, `n = {n}`: `{outw}`, asserted at node {d['root']} (K = 0x{d['K']:08x}) -/")
    A(f"def merged{nm} : List (Nat × Nat × Nat) :=")
    A("  " + lst(f"({k}, {a}, {b})" for k,a,b in mid_terms[d['merged']]) + NL)
    A(f"def mv{nm} : Nat → List (Nat × Nat × Nat)")
    for x in d['mids']:
        j = T(x) - L
        A(f"  | {j} => " + (f"merged{nm}" if x == d['merged'] else lst(f"({k}, {a}, {b})" for k,a,b in mid_terms[x])))
    A("  | _ => []" + NL)
    A(f"def ts{nm} : List (Nat × Nat × Nat) :=")
    A("  " + lst(f"({k}, {a}, {b})" for k,a,b in ts_terms) + NL)
    A(f"def tn{nm} : List TmplNode :=")
    A(f"  (List.range {L}).map (fun i => (TmplNode.leaf i : TmplNode))")
    A(f"    ++ (List.range {M}).map (fun j => TmplNode.sum (mv{nm} j)) ++ [TmplNode.sum ts{nm}]" + NL)
    A(f"def mp{nm} : List Nat :=")
    A("  " + lst(str(x) for x in (d['leaves'] + d['mids'] + [d['z']])) + NL)
    letters = "abcdef"
    for i, (wn, entries) in enumerate(gs):
        A(f"/-- Addend group `{wn}`. -/")
        A(f"def g{nm}{letters[i]} (lv : Nat → F) : List (Nat × F) :=")
        A("  " + lst(f"({2**j}, {entries[j]})" for j in range(32)) + NL)
    A(f"/-- Output word `{outw}`. -/")
    A(f"def ds{nm} (lv : Nat → F) : List (Nat × F) :=")
    A("  " + lst(f"({2**j}, {ds[j]})" for j in range(32)) + NL)
    gsum = " ++ ".join(f"g{nm}{letters[i]} lv" for i in range(len(gs)))
    A(f"/-- **The regrouping for round {t}.** -/")
    A(f"theorem tmpl_z{nm} [CharP F p256w] (lv : Nat → F) (hone : lv 0 = 1) :")
    A(f"    interpDag (tmplDag (cnstw F) tn{nm}) lv {L+M}")
    A(f"      = (({gsum}).map (fun q => (q.1 : F) * q.2)).sum + (({d['K']} : Nat) : F)")
    A(f"        - ((ds{nm} lv).map (fun q => (q.1 : F) * q.2)).sum := by")
    A(f"  rw [show ({L+M} : Nat) = {L} + {M} from rfl,")
    A(f"    show tn{nm} = (List.range {L}).map (fun i => (TmplNode.leaf i : TmplNode))")
    A(f"      ++ (List.range {M}).map (fun j => TmplNode.sum (mv{nm} j)) ++ [TmplNode.sum ts{nm}] from rfl,")
    A(f"    interpDag_leafMidSum (cnstw F) lv {L} {M} mv{nm} ts{nm} (by decide +kernel) (by decide +kernel)]")
    A("  have c0 : cnstw F 0 = 1 := cnstw_0")
    A(NL.join(cdef(k) for k in ks if k != 0))
    for x in d['copies']:
        idx, k0, a0, b0 = T(x), *nodes[x][1][0]
        leaf = T(b0 if a0 in ONE else a0)
        lem = "midLeafVal_copy_at" if a0 in ONE else "midLeafVal_copyR_at"
        A(f"  have k{idx} : midLeafVal (cnstw F) lv {L} mv{nm} {idx} = lv {leaf} :=")
        A(f"    {lem} (cnstw F) lv {L} mv{nm} 0 c0 hone {idx} {idx-L} (by norm_num) {leaf} (by rfl)")
    A(f"  have mm : midLeafVal (cnstw F) lv {L} mv{nm} {T(d['merged'])}")
    A(f"      = merged{nm}.foldl (fun acc x => acc + cnstw F x.1 * lv x.2.1 * lv x.2.2) 0 := by")
    A(f"    rw [midLeafVal_expand_at (cnstw F) lv {L} mv{nm} {T(d['merged'])} {jm} (by norm_num)]")
    A("    rfl")
    A(f"  simp only [ts{nm}, merged{nm}, " + ", ".join(f"g{nm}{letters[i]}" for i in range(len(gs)))
      + f", ds{nm}, Quadcert.xorVal, Quadcert.chVal, Quadcert.majVal, mm,")
    A("    " + ", ".join('k'+str(T(x)) for x in d['copies']) + ",")
    A("    List.map_cons, List.map_nil, List.map_append, List.sum_cons, List.sum_nil, List.sum_append,")
    A("    List.foldl_cons, List.foldl_nil, hone, c0, " + ", ".join('c'+str(k) for k in ks if k != 0) + "]")
    A("  push_cast")
    A("  ring" + NL)
    # ---- cone match + transfer ----
    gsum2 = " ++ ".join(f"g{nm}{letters[i]} lvv" for i in range(len(gs)))
    A(f"""theorem cone{nm} : coneIs nodeFn tn{nm} (fun i => mp{nm}.getD i 0) = true := by
  decide +kernel

theorem map{nm}_lt : ∀ i, i < tn{nm}.length → mp{nm}.getD i 0 < raw.nodes.length := by
  intro i hi
  have hlen : tn{nm}.length = {L+M+1} := by rfl
  rw [hlen] at hi
  rw [nodes_len]
  have hb : (List.range {L+M+1}).all (fun j => decide (mp{nm}.getD j 0 < 37139)) = true := by
    decide +kernel
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hb
  exact hb i hi

/-- The regrouping, transported to the circuit. -/
theorem zval_{nm} [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1) :
    interpDag (raw.toDag (cnstw F)) inputs {d['z']}
      = (({gsum2}).map (fun q => (q.1 : F) * q.2)).sum + (({d['K']} : Nat) : F)
        - ((ds{nm} lvv).map (fun q => (q.1 : F) * q.2)).sum := by
  have hdaglen : (raw.toDag (cnstw F)).length = raw.nodes.length := by simp [RawCircuit.toDag]
  have htr := coneIs_transfer raw (cnstw F) inputs nodeFn nodefn_ok tn{nm}
    (fun i => mp{nm}.getD i 0) cone{nm} map{nm}_lt {L+M} (by decide)
  have hone : (fun h => interpDag (raw.toDag (cnstw F)) inputs (mp{nm}.getD h 0)) 0 = 1 := by
    show interpDag (raw.toDag (cnstw F)) inputs 0 = 1
    rw [interpDag_input (raw.toDag (cnstw F)) inputs 0 0
      (by rw [hdaglen, nodes_len]; norm_num)
      (by rw [toDag_getD_fn raw (cnstw F) nodeFn nodefn_ok (by rw [nodes_len]; norm_num)]; rfl)]
    exact hin0
  show interpDag (raw.toDag (cnstw F)) inputs (mp{nm}.getD {L+M} 0) = _
  rw [htr, tmpl_z{nm} (fun h => interpDag (raw.toDag (cnstw F)) inputs (mp{nm}.getD h 0)) hone]
""".replace("lvv", "(fun h => interpDag (raw.toDag (cnstw F)) inputs (mp" + nm + ".getD h 0))"))
    # ---- leaf booleanity ----
    nb = L - 1
    bps = [(bit2assert[x], x) for x in d['leaves'][1:]]
    A(f"/-- The {nb} `(booleanity assertion, bit)` pairs of this cone, in leaf order. -/")
    A(f"def bp{nm} : List (Nat × Nat) :=")
    A("  " + lst(f"({a}, {b})" for a, b in bps) + NL)
    A(f"""theorem leafBits{nm} [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hbz : ∀ j, j < {nb} → interpDag (raw.toDag (cnstw F)) inputs (bp{nm}.getD j (0, 0)).1 = 0) :
    ∀ j, j < {nb} → interpDag (raw.toDag (cnstw F)) inputs (bp{nm}.getD j (0, 0)).2 = 0
      ∨ interpDag (raw.toDag (cnstw F)) inputs (bp{nm}.getD j (0, 0)).2 = 1 := by
  have hdaglen : (raw.toDag (cnstw F)).length = raw.nodes.length := by simp [RawCircuit.toDag]
  have hone : interpDag (raw.toDag (cnstw F)) inputs 0 = 1 := by
    rw [interpDag_input (raw.toDag (cnstw F)) inputs 0 0
      (by rw [hdaglen, nodes_len]; norm_num)
      (by rw [toDag_getD_fn raw (cnstw F) nodeFn nodefn_ok (by rw [nodes_len]; norm_num)]; rfl)]
    exact hin0
  have hc2 : cnstw F 2 = -1 := by
    show ((constNat 2 : Nat) : F) = -1
    have h : constNat 2 = p256w - 1 := by rfl
    rw [h, Quadcert.cast_sub_eq_neg p256w 1 (by norm_num), Nat.cast_one]
  have hshape : bp{nm}.all
      (fun q => nodeEq (nodeFn q.1) (.sum [(0, 0, q.2), (2, q.2, q.2)])) = true := by
    decide +kernel
  have hltc : bp{nm}.all
      (fun q => decide (q.2 < q.1) && decide (q.1 < raw.nodes.length)) = true := by
    rw [nodes_len]; decide +kernel
  have hlen : bp{nm}.length = {nb} := by rfl
  exact bits_of_boolNodes_idx raw (cnstw F) inputs nodeFn nodefn_ok cnstw_0 hc2 hone bp{nm}
    hshape hltc (fun j hj => hbz j (by rw [hlen] at hj; exact hj))

/-- Booleanity of every template leaf, index `0` (the constant one) included. -/
theorem lvBits{nm} [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hbz : ∀ j, j < {nb} → interpDag (raw.toDag (cnstw F)) inputs (bp{nm}.getD j (0, 0)).1 = 0) :
    ∀ i, i < {L} → interpDag (raw.toDag (cnstw F)) inputs (mp{nm}.getD i 0) = 0
      ∨ interpDag (raw.toDag (cnstw F)) inputs (mp{nm}.getD i 0) = 1 := by
  have hdaglen : (raw.toDag (cnstw F)).length = raw.nodes.length := by simp [RawCircuit.toDag]
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · refine Or.inr ?_
    show interpDag (raw.toDag (cnstw F)) inputs 0 = 1
    rw [interpDag_input (raw.toDag (cnstw F)) inputs 0 0
      (by rw [hdaglen, nodes_len]; norm_num)
      (by rw [toDag_getD_fn raw (cnstw F) nodeFn nodefn_ok (by rw [nodes_len]; norm_num)]; rfl)]
    exact hin0
  · have hb := leafBits{nm} inputs hin0 hbz (i - 1) (by omega)
    have hall : (List.range {nb}).all
        (fun j => decide ((bp{nm}.getD j (0, 0)).2 = mp{nm}.getD (j + 1) 0)) = true := by
      decide +kernel
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hall
    have heq := hall (i - 1) (by omega)
    rw [show i - 1 + 1 = i from by omega] at heq
    rwa [heq] at hb
""")
    return NL.join(o)

HDR = """/-
# Round assertions: `{title}`

Generated by `tools/gen_rnd.py`. Do not edit.
-/

import quadcert.Core.ConeXor
import quadcert.Bridge.Sha256.S2TmplZ

set_option maxRecDepth 8000000
set_option maxHeartbeats 4000000

namespace Sha256Blk

open Quadcert Quadcert.Gen.Sha256Blk

variable {{F : Type}} [Field F]

"""
if __name__ == "__main__":
    which = sys.argv[1] if len(sys.argv) > 1 else "probe"
    if which == "all":
        LET = "ABCDEFGHIJKLMNOP"
        for i in range(16):
            chunk = insts[i*8:(i+1)*8]
            body = HDR.format(title=f"part {i+1} of 16") + NL.join(emit(x) for x in chunk) + NL + "end Sha256Blk" + NL
            open(os.path.join(OUT, f"S2Rnd{LET[i]}.lean"), "w").write(body)
            print(f"  S2Rnd{LET[i]}.lean  n={chunk[0]['n']} t={chunk[0]['t']}..{chunk[-1]['t']}  {body.count(NL)} lines")
    elif which == "probe":
        d6 = [x for x in insts if x['n'] == 6][0]
        d7 = [x for x in insts if x['n'] == 7][0]
        body = HDR.format(title="probe") + emit(d6) + NL + emit(d7) + NL + "end Sha256Blk" + NL
        open(os.path.join(OUT, "S2RndProbe.lean"), "w").write(body)
        print("emitted S2RndProbe.lean", body.count(NL), "lines")
