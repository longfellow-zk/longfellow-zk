import re, sys, os, pickle
# Output root, derived from this file rather than hardcoded: these scripts were written
# on a different machine and carried its absolute paths.
_SHAROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
SP = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, SP)
import gen_final_bridge as G
from sha_classify import nodes, layout
NL = chr(10)
OUT = os.path.join(_SHAROOT, "circuits", "quadcert", "Bridge", "Sha256")
insts = G.instances
o = []; A = o.append
A("""/-
# The eight `final` assertions, composed

`S2Final` proves each of the eight outgoing chaining words is the wrapped sum of the incoming one
and a round-64 state word, as three linear forms over the circuit's bits. This file names those
three `Nat`s: `hWord`, `stateWord … 64`, `outWord`, the same vocabulary the schedule and round
bridges speak. What comes out is `SHA256.sha256_soundness`'s `hout`.
-/

import quadcert.Bridge.Sha256.S2Final
import quadcert.Bridge.Sha256.S2State

set_option maxRecDepth 8000000
set_option maxHeartbeats 4000000

namespace Sha256Blk

open Quadcert Quadcert.Gen.Sha256Blk

variable {F : Type} [Field F]
""")
for d in insts:
    i = d['i']
    A(f"/-! #### Output word {i} -/" + NL)
    A(f"noncomputable def lvF{i} (inputs : Nat → F) : Nat → F :=")
    A(f"  fun k => interpDag (raw.toDag (cnstw F)) inputs (mpF{i}.getD k 0)" + NL)
    A(f"""theorem leafBitsF{i} [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hbz : ∀ j, j < 96 → interpDag (raw.toDag (cnstw F)) inputs (bpLF{i}.getD j (0, 0)).1 = 0) :
    ∀ j, j < 96 → interpDag (raw.toDag (cnstw F)) inputs (bpLF{i}.getD j (0, 0)).2 = 0
      ∨ interpDag (raw.toDag (cnstw F)) inputs (bpLF{i}.getD j (0, 0)).2 = 1 := by
  have hdaglen : (raw.toDag (cnstw F)).length = raw.nodes.length := by simp [RawCircuit.toDag]
  have hone : interpDag (raw.toDag (cnstw F)) inputs 0 = 1 := by
    rw [interpDag_input (raw.toDag (cnstw F)) inputs 0 0
      (by rw [hdaglen, nodes_len]; norm_num)
      (by rw [toDag_getD_fn raw (cnstw F) nodeFn nodefn_ok (by rw [nodes_len]; norm_num)]; rfl)]
    exact hin0
  have hc2 : cnstw F 2 = -1 := by
    show ((constNat 2 : Nat) : F) = -1
    have hq : constNat 2 = p256w - 1 := by rfl
    rw [hq, Quadcert.cast_sub_eq_neg p256w 1 (by norm_num), Nat.cast_one]
  have hshape : bpLF{i}.all
      (fun q => nodeEq (nodeFn q.1) (.sum [(0, 0, q.2), (2, q.2, q.2)])) = true := by decide +kernel
  have hltc : bpLF{i}.all
      (fun q => decide (q.2 < q.1) && decide (q.1 < raw.nodes.length)) = true := by
    rw [nodes_len]; decide +kernel
  have hlen : bpLF{i}.length = 96 := by rfl
  exact bits_of_boolNodes_idx raw (cnstw F) inputs nodeFn nodefn_ok cnstw_0 hc2 hone bpLF{i}
    hshape hltc (fun j hj => hbz j (by rw [hlen] at hj; exact hj))

theorem lvBitsF{i} [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hbz : ∀ j, j < 96 → interpDag (raw.toDag (cnstw F)) inputs (bpLF{i}.getD j (0, 0)).1 = 0) :
    ∀ k, k < 97 → lvF{i} inputs k = 0 ∨ lvF{i} inputs k = 1 := by
  have hdaglen : (raw.toDag (cnstw F)).length = raw.nodes.length := by simp [RawCircuit.toDag]
  intro k hk
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · refine Or.inr ?_
    show interpDag (raw.toDag (cnstw F)) inputs 0 = 1
    rw [interpDag_input (raw.toDag (cnstw F)) inputs 0 0
      (by rw [hdaglen, nodes_len]; norm_num)
      (by rw [toDag_getD_fn raw (cnstw F) nodeFn nodefn_ok (by rw [nodes_len]; norm_num)]; rfl)]
    exact hin0
  · have hb := leafBitsF{i} inputs hin0 hbz (k - 1) (by omega)
    have hall : (List.range 96).all
        (fun j => decide ((bpLF{i}.getD j (0, 0)).2 = mpF{i}.getD (j + 1) 0)) = true := by
      decide +kernel
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hall
    have heq := hall (k - 1) (by omega)
    rw [show k - 1 + 1 = k from by omega] at heq
    rwa [heq] at hb
""")
    for nm, xs, tgt in (("a", d['csA'], f"bitsOf inputs (hinBits {i})"),
                        ("b", d['csB'], f"bitsOf inputs (stateBits 64 {i})"),
                        ("p", d['ds'],  f"bitsOf inputs (h1Bits {i})")):
        A(f"noncomputable def vF{i}{nm} (lv : Nat → F) : Nat → F")
        for j, (_, leaf, _) in enumerate(xs): A(f"  | {j} => lv {leaf}")
        A("  | _ => 0" + NL)
        src = {"a": f"csA{i}", "b": f"csB{i}", "p": f"dsF{i}"}[nm]
        A(f"theorem {src}_eq (lv : Nat → F) :")
        A(f"    {src} lv = (List.range 32).map (fun j => ((2 ^ j : Nat), vF{i}{nm} lv j)) := rfl" + NL)
        A(f"theorem vbF{i}{nm} (lv : Nat → F) (hlv : ∀ k, k < 97 → lv k = 0 ∨ lv k = 1) :")
        A(f"    ∀ j, j < 32 → vF{i}{nm} lv j = 0 ∨ vF{i}{nm} lv j = 1 := by")
        A("  intro j hj")
        A("  match j, hj with")
        for j, (_, leaf, _) in enumerate(xs):
            A(f"  | {j}, _ => exact hlv {leaf} (by norm_num)")
        A("  | (n + 32), hx => exact absurd hx (by omega)" + NL)
        A(f"noncomputable def bwF{i}{nm} (inputs : Nat → F) : List Nat :=")
        A("  [" + ", ".join(f"SHA256F.natBit (lvF{i} inputs {leaf})" for _, leaf, _ in xs) + "]" + NL)
        A(f"theorem bwF{i}{nm}_eq (inputs : Nat → F) : bwF{i}{nm} inputs = {tgt} := rfl" + NL)
    lv = f"(lvF{i} inputs)"
    A(f"""/-- **Output word {i}.** -/
theorem finalW{i} [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hbz : ∀ j, j < 96 → interpDag (raw.toDag (cnstw F)) inputs (bpF{i}.getD j (0, 0)).1 = 0)
    (hbzl : ∀ j, j < 96 → interpDag (raw.toDag (cnstw F)) inputs (bpLF{i}.getD j (0, 0)).1 = 0)
    (hroot : ∀ e, e < 8 → interpDag (raw.toDag (cnstw F)) inputs (rootOfW e) = 0) :
    outWord inputs {i} = SHA256.w32 (hWord inputs {i} + stateWord inputs 64 {i}) := by
  have hlv : ∀ k, k < 97 → lvF{i} inputs k = 0 ∨ lvF{i} inputs k = 1 := lvBitsF{i} inputs hin0 hbzl
  obtain ⟨A, B, P, hA, hB, hP, hAlt, hBlt, hPlt, hres⟩ :=
    final{i} inputs hin0 hbz (allWrap2 inputs hin0 hroot {i} (by norm_num))
  rw [csA{i}_eq] at hA
  rw [csB{i}_eq] at hB
  rw [dsF{i}_eq] at hP
  have hvA : A = SHA256.ofBits ((List.range 32).map (fun j => SHA256F.natBit (vF{i}a {lv} j))) :=
    SHA256F.group_val_eq' (p := p256w) _ 32 A (fun j hj => vbF{i}a {lv} hlv j hj) hA
      (by simp only [p256w]; omega) (by norm_num)
  have hvB : B = SHA256.ofBits ((List.range 32).map (fun j => SHA256F.natBit (vF{i}b {lv} j))) :=
    SHA256F.group_val_eq' (p := p256w) _ 32 B (fun j hj => vbF{i}b {lv} hlv j hj) hB
      (by simp only [p256w]; omega) (by norm_num)
  have hvP : P = SHA256.ofBits ((List.range 32).map (fun j => SHA256F.natBit (vF{i}p {lv} j))) :=
    SHA256F.group_val_eq' (p := p256w) _ 32 P (fun j hj => vbF{i}p {lv} hlv j hj) hP
      (by simp only [p256w]; omega) (by norm_num)
  have heA : A = hWord inputs {i} := by rw [hvA, hWord, ← bwF{i}a_eq]; rfl
  have heB : B = stateWord inputs 64 {i} := by rw [hvB, stateWord, ← bwF{i}b_eq]; rfl
  have heP : P = outWord inputs {i} := by rw [hvP, outWord, ← bwF{i}p_eq]; rfl
  rw [← heP, ← heA, ← heB]
  exact hres
""")
A("""/-- **`hout`.** -/
theorem hout [CharP F p256w] (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hbz : ∀ i, i < 8 → ∀ j, j < 96 →
      interpDag (raw.toDag (cnstw F)) inputs ((bpAt i).getD j (0, 0)).1 = 0)
    (hbzl : ∀ i, i < 8 → ∀ j, j < 96 →
      interpDag (raw.toDag (cnstw F)) inputs ((bpLAt i).getD j (0, 0)).1 = 0)
    (hroot : ∀ e, e < 8 → interpDag (raw.toDag (cnstw F)) inputs (rootOfW e) = 0) :
    ∀ i, i < 8 → outWord inputs i = SHA256.w32 (hWord inputs i + stateWord inputs 64 i) := by
  intro i hi
  match i, hi with""")
for d in insts:
    A(f"  | {d['i']}, _ => exact finalW{d['i']} inputs hin0 (hbz {d['i']} (by norm_num)) "
      f"(hbzl {d['i']} (by norm_num)) hroot")
A("  | (n + 8), hx => exact absurd hx (by omega)" + NL)
A("end Sha256Blk")
open(os.path.join(OUT, "S2FinalComp.lean"), "w").write(NL.join(o) + NL)
print("emitted S2FinalComp.lean")
