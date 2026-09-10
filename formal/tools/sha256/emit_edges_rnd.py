import sys, pickle, os
SP = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, SP)
from sha_classify import nodes
insts = pickle.load(open(os.path.join(SP, "rinsts.pkl"), "rb"))
i6 = [d for d in insts if d['n']==6]; i7 = [d for d in insts if d['n']==7]
def zdef(name, ds):
    return f"def {name} : Nat -> Nat\n".replace("->", chr(8594)) + \
        "\n".join(f"  | {d['t']} => {d['z']}" for d in ds) + "\n  | _ => 0\n"
H = chr(96)   # backtick
body = f"""/-
# The 128 {H}round_step{H} wrapping sums, as edge lists

The {H}n = 6{H} ({H}e{H} update) and {H}n = 7{H} ({H}a{H} update) analogues of {H}S2EdgesSched{H}.

The product tree above {H}z{H} is contiguous, with one node pulled out by CSE: {H}532{H}, the constant
{H}1{H}, which every tree needs and only one instance owns. That owner is round 18's {H}n = 6{H}
assertion, where {H}532{H} sits inside the tree at {H}z+4{H}; its map is contiguous where the other 63
have a gap.

Round 5's {H}n = 7{H} assertion is the one instance of 128 whose tree the compiler emitted with the
operands the other way round, so it goes through {H}tnWrap7b{H} on its own. The other 63 share an
edge list, indexed through {H}skip5{H}.
-/

import quadcert.Core.ConeEdges
import quadcert.Bridge.Sha256.S2TmplWrap

set_option maxRecDepth 4000000
set_option maxHeartbeats 1000000

namespace Sha256Blk

open Quadcert Quadcert.Gen.Sha256Blk

{zdef("zOf6", i6)}
{zdef("zOf7", i7)}
def rootOf6 : Nat → Nat := fun e => zOf6 e + (if e = 18 then 14 else 13)
def rootOf7 : Nat → Nat := fun e => zOf7 e + 14

def mapOf6 : Nat → Nat → Nat := fun e i =>
  if i < 3 then (if i < 1 then 0 else if i < 2 then 238 else 239)
  else if i < 7 then zOf6 e + (i - 3)
  else if i = 7 then (if e = 18 then zOf6 e + 4 else 532)
  else zOf6 e + (if e = 18 then i - 3 else i - 4)

def mapOf7 : Nat → Nat → Nat := fun e i =>
  if i < 3 then (if i < 1 then 0 else if i < 2 then 238 else 239)
  else if i < 14 then zOf7 e + (i - 3)
  else if i = 14 then 532
  else zOf7 e + (i - 4)

/-- The 63 rounds whose `n = 7` tree has the standard operand order. -/
def skip5 : Nat → Nat := fun k => if k < 5 then k else k + 1

theorem rndEdges6 : edgesMatch nodeFn tnWrap6 mapOf6 64 = true := by decide +kernel
theorem rndEdges7 : edgesMatch nodeFn tnWrap7 (fun k i => mapOf7 (skip5 k) i) 63 = true := by
  decide +kernel
theorem cone7at5 : coneIs nodeFn tnWrap7b (mapOf7 5) = true := by decide +kernel

theorem mapOf6_lt : ∀ e, e < 64 → ∀ i, i < tnWrap6.length → mapOf6 e i < raw.nodes.length := by
  have hb : (List.range 64).all
      (fun e => (List.range 18).all (fun i => decide (mapOf6 e i < 37139))) = true := by
    decide +kernel
  intro e he i hi
  rw [nodes_len]
  have h18 : tnWrap6.length = 18 := rfl
  rw [h18] at hi
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hb
  exact hb e he i hi

theorem mapOf7s_lt : ∀ k, k < 63 → ∀ i, i < tnWrap7.length →
    mapOf7 (skip5 k) i < raw.nodes.length := by
  have hb : (List.range 63).all
      (fun k => (List.range 19).all (fun i => decide (mapOf7 (skip5 k) i < 37139))) = true := by
    decide +kernel
  intro k hk i hi
  rw [nodes_len]
  have h19 : tnWrap7.length = 19 := rfl
  rw [h19] at hi
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hb
  exact hb k hk i hi

theorem map7at5_lt : ∀ i, i < tnWrap7b.length → mapOf7 5 i < raw.nodes.length := by
  have hb : (List.range 19).all (fun i => decide (mapOf7 5 i < 37139)) = true := by decide +kernel
  intro i hi
  rw [nodes_len]
  have h19 : tnWrap7b.length = 19 := rfl
  rw [h19] at hi
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hb
  exact hb i hi

variable {{F : Type}} [Field F]

private theorem one_val (inputs : Nat → F) (hin0 : inputs 0 = 1) :
    interpDag (raw.toDag (cnstw F)) inputs 0 = 1 := by
  have hdl : (raw.toDag (cnstw F)).length = raw.nodes.length := by simp [RawCircuit.toDag]
  rw [interpDag_input (raw.toDag (cnstw F)) inputs 0 0
    (by rw [hdl, nodes_len]; norm_num)
    (by rw [toDag_getD_fn raw (cnstw F) nodeFn nodefn_ok (by rw [nodes_len]; norm_num)]; rfl)]
  exact hin0

/-- **All 64 `n = 6` wrapping sums.** -/
theorem allWrap6 [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hz : ∀ e, e < 64 → interpDag (raw.toDag (cnstw F)) inputs (rootOf6 e) = 0) :
    ∀ e, e < 64 → SHA256F.wrapPoly 6 ((2 ^ 32 : Nat) : F)
      (interpDag (raw.toDag (cnstw F)) inputs (zOf6 e)) = 0 := by
  intro e he
  have htr := edges_transfer raw (cnstw F) inputs nodeFn nodefn_ok tnWrap6 mapOf6 64
    rndEdges6 mapOf6_lt e he
  have hone : (fun h => interpDag (raw.toDag (cnstw F)) inputs (mapOf6 e h)) 0 = 1 :=
    one_val inputs hin0
  have hroot : interpDag (tmplDag (cnstw F) tnWrap6)
      (fun h => interpDag (raw.toDag (cnstw F)) inputs (mapOf6 e h)) 17 = 0 := by
    rw [← htr 17 (by decide)]
    show interpDag (raw.toDag (cnstw F)) inputs (rootOf6 e) = 0
    exact hz e he
  exact tmpl_wrap6 (cnstw F) (fun h => interpDag (raw.toDag (cnstw F)) inputs (mapOf6 e h))
    cnstw_0 cnstw_65 cnstw_66 cnstw_67 cnstw_68 cnstw_69 hone hroot

/-- Round 5, through the mirrored template. -/
theorem wrap7at5 [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hz : interpDag (raw.toDag (cnstw F)) inputs (rootOf7 5) = 0) :
    SHA256F.wrapPoly 7 ((2 ^ 32 : Nat) : F)
      (interpDag (raw.toDag (cnstw F)) inputs (zOf7 5)) = 0 := by
  have htr := coneIs_transfer raw (cnstw F) inputs nodeFn nodefn_ok tnWrap7b (mapOf7 5)
    cone7at5 map7at5_lt
  have hone : (fun h => interpDag (raw.toDag (cnstw F)) inputs (mapOf7 5 h)) 0 = 1 :=
    one_val inputs hin0
  have hroot : interpDag (tmplDag (cnstw F) tnWrap7b)
      (fun h => interpDag (raw.toDag (cnstw F)) inputs (mapOf7 5 h)) 18 = 0 := by
    rw [← htr 18 (by decide)]
    show interpDag (raw.toDag (cnstw F)) inputs (rootOf7 5) = 0
    exact hz
  exact tmpl_wrap7b (cnstw F) (fun h => interpDag (raw.toDag (cnstw F)) inputs (mapOf7 5 h))
    cnstw_0 cnstw_65 cnstw_66 cnstw_67 cnstw_68 cnstw_69 cnstw_70 hone hroot

/-- **All 64 `n = 7` wrapping sums.** -/
theorem allWrap7 [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hz : ∀ e, e < 64 → interpDag (raw.toDag (cnstw F)) inputs (rootOf7 e) = 0) :
    ∀ e, e < 64 → SHA256F.wrapPoly 7 ((2 ^ 32 : Nat) : F)
      (interpDag (raw.toDag (cnstw F)) inputs (zOf7 e)) = 0 := by
  intro e he
  by_cases h5 : e = 5
  · subst h5; exact wrap7at5 inputs hin0 (hz 5 (by norm_num))
  · have hk : skip5 (if e < 5 then e else e - 1) = e := by
      simp only [skip5]; split <;> split <;> omega
    have hlt : (if e < 5 then e else e - 1) < 63 := by split <;> omega
    set k := if e < 5 then e else e - 1 with hkdef
    have htr := edges_transfer raw (cnstw F) inputs nodeFn nodefn_ok tnWrap7
      (fun k i => mapOf7 (skip5 k) i) 63 rndEdges7 mapOf7s_lt k hlt
    have hone : (fun h => interpDag (raw.toDag (cnstw F)) inputs (mapOf7 (skip5 k) h)) 0 = 1 :=
      one_val inputs hin0
    have hroot : interpDag (tmplDag (cnstw F) tnWrap7)
        (fun h => interpDag (raw.toDag (cnstw F)) inputs (mapOf7 (skip5 k) h)) 18 = 0 := by
      rw [← htr 18 (by decide)]
      show interpDag (raw.toDag (cnstw F)) inputs (mapOf7 (skip5 k) 18) = 0
      rw [hk]
      exact hz e he
    have hw := tmpl_wrap7 (cnstw F)
      (fun h => interpDag (raw.toDag (cnstw F)) inputs (mapOf7 (skip5 k) h))
      cnstw_0 cnstw_65 cnstw_66 cnstw_67 cnstw_68 cnstw_69 cnstw_70 hone hroot
    show SHA256F.wrapPoly 7 ((2 ^ 32 : Nat) : F)
      (interpDag (raw.toDag (cnstw F)) inputs (zOf7 e)) = 0
    rw [← hk]
    exact hw

end Sha256Blk
"""
open("/Users/abhi/Projects/longfellow-zk/formal/circuits/quadcert/Bridge/Sha256/S2EdgesRnd.lean","w").write(body)
print("emitted S2EdgesRnd.lean")
