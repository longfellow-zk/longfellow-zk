import os as _os, sys as _sys
# Output root, derived from this file rather than hardcoded: these scripts were written
# on a different machine and carried its absolute paths.
_SHAROOT = _os.path.dirname(_os.path.dirname(_os.path.dirname(_os.path.abspath(__file__))))
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
_HERE = _os.path.dirname(_os.path.abspath(__file__))
import re, sys, pickle, os
_sys.path.insert(0, _HERE)
from sha_parse import P256
from sha_classify import nodes, consts, layout, asserts
bit2assert = {}
for (_r,_x,_y) in asserts:
    _k,_v = nodes[_r]
    if _k=='sum' and len(_v)==2:
        (k1,a1,b1),(k2,a2,b2) = _v
        if k1==0 and a1==0 and k2==2 and a2==b2==b1: bit2assert[b1] = _r
OUTDIR = _os.path.join(_SHAROOT, "circuits", "quadcert", "Bridge", "Sha256")
ONE = {0, 238}
def sg(c):
    v = consts[c]; return v - P256 if v > P256//2 else v
insts = pickle.load(open(_os.path.join(_HERE, "insts.pkl"),"rb"))
lst = lambda xs: "[" + ", ".join(xs) + "]"

def cdef(k):
    v = sg(k)
    return (f"  have c{k} : cnstw F {k} = (({v} : Nat) : F) := cnstw_pos {k} {v} (by rfl)" if v > 0
            else f"  have c{k} : cnstw F {k} = -(({-v} : Nat) : F) := cnstw_neg {k} {-v} (by rfl) (by norm_num)")

def emit(d):
    t, L, M, ti = d['t'], d['L'], d['M'], d['ti']
    T = lambda n: ti[n]
    mid_terms = {n: [(k, T(a), T(b)) for k, a, b in nodes[n][1]] for n in d['mids']}
    ts_terms = [(k, T(a), T(b)) for k, a, b in nodes[d['z']][1]]
    ks = sorted({k for k,_,_ in ts_terms} | {k for n in d['mids'] for k,_,_ in mid_terms[n]})
    jm = T(d['merged']) - L
    A = []
    A(f"""/-! ### `W{t} = σ₀(W{t-15}) + W{t-7} + σ₁(W{t-2}) + W{t-16}`, asserted at node {d['root']}

{L} leaves, {len(d['copies'])} copy mids, {len(d['xors'])} xor mids, one merged
{len(nodes[d['merged']][1])}-term linear mid, root at {L+M}. Source words: `{d['s0w']}` (σ₀),
`{d['p7']}`, `{d['s1w']}` (σ₁), `{d['p16']}`; output `{d['outw']}`. -/
""") if False else None
    out = []
    out.append(f"""/-! ### `W{t} = σ₀(W{t-15}) + W{t-7} + σ₁(W{t-2}) + W{t-16}`, asserted at node {d['root']}

Source words `{d['s0w']}` (σ₀), `{d['p7']}`, `{d['s1w']}` (σ₁), `{d['p16']}`; output `{d['outw']}`.
{L} leaves, {len(d['copies'])} copies, {len(d['xors'])} xors, one merged
{len(nodes[d['merged']][1])}-term mid, root at {L+M}. -/

def mergedS{t} : List (Nat × Nat × Nat) :=
  """ + lst(f"({k}, {a}, {b})" for k,a,b in mid_terms[d['merged']]))
    out.append(f"def mvS{t} : Nat → List (Nat × Nat × Nat)")
    for n in d['mids']:
        j = T(n) - L
        out.append(f"  | {j} => " + (f"mergedS{t}" if n == d['merged']
                                     else lst(f"({k}, {a}, {b})" for k,a,b in mid_terms[n])))
    out.append("  | _ => []\n")
    out.append(f"def tsS{t} : List (Nat × Nat × Nat) :=\n  " + lst(f"({k}, {a}, {b})" for k,a,b in ts_terms) + "\n")
    out.append(f"""def tnS{t} : List TmplNode :=
  (List.range {L}).map (fun i => (TmplNode.leaf i : TmplNode))
    ++ (List.range {M}).map (fun j => TmplNode.sum (mvS{t} j)) ++ [TmplNode.sum tsS{t}]

def mpS{t} : List Nat :=
  """ + lst(str(n) for n in (d['leaves'] + d['mids'] + [d['z']])) + "\n")
    for nm, (w, g) in zip("abcd", d['groups']):
        out.append(f"/-- Addend group `{w}`. -/\ndef gS{t}{nm} (lv : Nat → F) : List (Nat × F) :=\n  "
                   + lst(f"({wt}, {e})" for wt, e in g) + "\n")
    out.append(f"/-- Output word `{d['outw']}`. -/\ndef dsS{t} (lv : Nat → F) : List (Nat × F) :=\n  "
               + lst(f"({wt}, {e})" for wt, e in d['ds']) + "\n")
    haves = []
    for n in d['copies']:
        idx, leaf = T(n), T(n if nodes[n][0]=='input' else
                            (nodes[n][1][0][2] if nodes[n][1][0][1] in ONE else nodes[n][1][0][1]))
        k, a, b = nodes[n][1][0]
        lem = "midLeafVal_copy_at" if a in ONE else "midLeafVal_copyR_at"
        haves.append(f"  have k{idx} : midLeafVal (cnstw F) lv {L} mvS{t} {idx} = lv {leaf} :=\n"
                     f"    {lem} (cnstw F) lv {L} mvS{t} 0 c0 hone {idx} {idx-L} (by norm_num) {leaf} (by rfl)")
    out.append(f"""/-- **The regrouping for `W{t}`.** -/
theorem tmpl_zS{t} [CharP F p256w] (lv : Nat → F) (hone : lv 0 = 1) :
    interpDag (tmplDag (cnstw F) tnS{t}) lv {L+M}
      = (((gS{t}a lv ++ gS{t}b lv ++ gS{t}c lv ++ gS{t}d lv)).map (fun q => (q.1 : F) * q.2)).sum
        - ((dsS{t} lv).map (fun q => (q.1 : F) * q.2)).sum := by
  rw [show ({L+M} : Nat) = {L} + {M} from rfl,
    show tnS{t} = (List.range {L}).map (fun i => (TmplNode.leaf i : TmplNode))
      ++ (List.range {M}).map (fun j => TmplNode.sum (mvS{t} j)) ++ [TmplNode.sum tsS{t}] from rfl,
    interpDag_leafMidSum (cnstw F) lv {L} {M} mvS{t} tsS{t} (by decide +kernel) (by decide +kernel)]
  have c0 : cnstw F 0 = 1 := cnstw_0""")
    out.append("\n".join(cdef(k) for k in ks if k != 0))
    out.append("\n".join(haves))
    out.append(f"""  have mm : midLeafVal (cnstw F) lv {L} mvS{t} {T(d['merged'])}
      = mergedS{t}.foldl (fun acc x => acc + cnstw F x.1 * lv x.2.1 * lv x.2.2) 0 := by
    rw [midLeafVal_expand_at (cnstw F) lv {L} mvS{t} {T(d['merged'])} {jm} (by norm_num)]
    rfl
  simp only [tsS{t}, mergedS{t}, gS{t}a, gS{t}b, gS{t}c, gS{t}d, dsS{t}, Quadcert.xorVal, mm,
    {", ".join('k'+str(T(n)) for n in d['copies'])},
    List.map_cons, List.map_nil, List.map_append, List.sum_cons, List.sum_nil, List.sum_append,
    List.foldl_cons, List.foldl_nil, hone, c0, {", ".join('c'+str(k) for k in ks if k != 0)}]
  push_cast
  ring
""")
    bps = [(bit2assert[n], n) for n in d['leaves'][1:]]
    out.append(f"/-- The 160 `(booleanity assertion, bit)` pairs of this cone, in leaf order. -/")
    out.append(f"def bpS{t} : List (Nat × Nat) :=\n  " + lst(f"({a}, {b})" for a, b in bps) + "\n")
    out.append(f"""/-- Booleanity of the 160 input leaves, by index. -/
theorem leafBits{t} [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hbz : ∀ j, j < 160 → interpDag (raw.toDag (cnstw F)) inputs (bpS{t}.getD j (0, 0)).1 = 0) :
    ∀ j, j < 160 → interpDag (raw.toDag (cnstw F)) inputs (bpS{t}.getD j (0, 0)).2 = 0
      ∨ interpDag (raw.toDag (cnstw F)) inputs (bpS{t}.getD j (0, 0)).2 = 1 := by
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
  have hshape : bpS{t}.all
      (fun q => nodeEq (nodeFn q.1) (.sum [(0, 0, q.2), (2, q.2, q.2)])) = true := by
    decide +kernel
  have hltc : bpS{t}.all
      (fun q => decide (q.2 < q.1) && decide (q.1 < raw.nodes.length)) = true := by
    rw [nodes_len]; decide +kernel
  have hlen : bpS{t}.length = 160 := by rfl
  exact bits_of_boolNodes_idx raw (cnstw F) inputs nodeFn nodefn_ok cnstw_0 hc2 hone bpS{t}
    hshape hltc (fun j hj => hbz j (by rw [hlen] at hj; exact hj))

/-- **Booleanity of every template leaf**, including index `0`, the constant-one wire. This is
    the `hb` that `Core/ConeXor.lean`'s mid lemmas and `wrap_four_words` both consume. -/
theorem lvBits{t} [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hbz : ∀ j, j < 160 → interpDag (raw.toDag (cnstw F)) inputs (bpS{t}.getD j (0, 0)).1 = 0) :
    ∀ i, i < 161 → interpDag (raw.toDag (cnstw F)) inputs (mpS{t}.getD i 0) = 0
      ∨ interpDag (raw.toDag (cnstw F)) inputs (mpS{t}.getD i 0) = 1 := by
  have hdaglen : (raw.toDag (cnstw F)).length = raw.nodes.length := by simp [RawCircuit.toDag]
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · refine Or.inr ?_
    show interpDag (raw.toDag (cnstw F)) inputs 0 = 1
    rw [interpDag_input (raw.toDag (cnstw F)) inputs 0 0
      (by rw [hdaglen, nodes_len]; norm_num)
      (by rw [toDag_getD_fn raw (cnstw F) nodeFn nodefn_ok (by rw [nodes_len]; norm_num)]; rfl)]
    exact hin0
  · have hb := leafBits{t} inputs hin0 hbz (i - 1) (by omega)
    have hall : (List.range 160).all
        (fun j => decide ((bpS{t}.getD j (0, 0)).2 = mpS{t}.getD (j + 1) 0)) = true := by
      decide +kernel
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hall
    have heq := hall (i - 1) (by omega)
    rw [show i - 1 + 1 = i from by omega] at heq
    rwa [heq] at hb
""")
    lv = f"(fun h => interpDag (raw.toDag (cnstw F)) inputs (mpS{t}.getD h 0))"
    out.append(f"""/-- The cone of `z` at node {d['z']} matches the template. -/
theorem coneS{t} : coneIs nodeFn tnS{t} (fun i => mpS{t}.getD i 0) = true := by decide +kernel

theorem mapS{t}_lt : ∀ i, i < tnS{t}.length → mpS{t}.getD i 0 < raw.nodes.length := by
  intro i hi
  have hlen : tnS{t}.length = {L+M+1} := by rfl
  rw [hlen] at hi
  rw [nodes_len]
  have hb : (List.range {L+M+1}).all (fun j => decide (mpS{t}.getD j 0 < 37139)) = true := by
    decide +kernel
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hb
  exact hb i hi

/-- **The regrouping, of the circuit.** `tmpl_zS{t}` transported along the cone match: the
    assertion's `z` wire really is `σ₀(W{t-15}) + W{t-7} + σ₁(W{t-2}) + W{t-16}` minus `W{t}`,
    as bit-linear forms over the circuit's own wires. -/
theorem zval_S{t} [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1) :
    interpDag (raw.toDag (cnstw F)) inputs {d['z']}
      = (((gS{t}a {lv} ++ gS{t}b {lv} ++ gS{t}c {lv} ++ gS{t}d {lv})).map
          (fun q => (q.1 : F) * q.2)).sum
        - ((dsS{t} {lv}).map (fun q => (q.1 : F) * q.2)).sum := by
  have hdaglen : (raw.toDag (cnstw F)).length = raw.nodes.length := by simp [RawCircuit.toDag]
  have htr := coneIs_transfer raw (cnstw F) inputs nodeFn nodefn_ok tnS{t}
    (fun i => mpS{t}.getD i 0) coneS{t} mapS{t}_lt {L+M} (by decide)
  have hone : {lv} 0 = 1 := by
    show interpDag (raw.toDag (cnstw F)) inputs 0 = 1
    rw [interpDag_input (raw.toDag (cnstw F)) inputs 0 0
      (by rw [hdaglen, nodes_len]; norm_num)
      (by rw [toDag_getD_fn raw (cnstw F) nodeFn nodefn_ok (by rw [nodes_len]; norm_num)]; rfl)]
    exact hin0
  show interpDag (raw.toDag (cnstw F)) inputs (mpS{t}.getD {L+M} 0) = _
  rw [htr, tmpl_zS{t} {lv} hone]
""")
    return "\n".join(out)

HDR = """/-
# Schedule assertions {lo}-{hi}: `W t = σ₀(W (t-15)) + W (t-7) + σ₁(W (t-2)) + W (t-16)`

Generated by `tools/gen_sched.py`. Do not edit. Part {n} of 8; see `S2SchedA.lean` for the
design notes that apply to all 48.
-/

import quadcert.Core.ConeXor
import quadcert.Bridge.Sha256.S2TmplZ

set_option maxRecDepth 8000000
set_option maxHeartbeats 4000000

namespace Sha256Blk

open Quadcert Quadcert.Gen.Sha256Blk

variable {{F : Type}} [Field F]

"""
LETTERS = "ABCDEFGH"
for n in range(8):
    chunk = insts[n*6:(n+1)*6]
    body = HDR.format(lo=chunk[0]['t'], hi=chunk[-1]['t'], n=n+1)
    body += "\n".join(emit(d) for d in chunk) + "\nend Sha256Blk\n"
    path = os.path.join(OUTDIR, f"S2Sched{LETTERS[n]}.lean")
    open(path, "w").write(body)
    print(f"  S2Sched{LETTERS[n]}.lean  t={chunk[0]['t']}..{chunk[-1]['t']}  {body.count(chr(10))} lines")
