import Lfzk.NizkDeployedHashAdaptive

/-!
# Two-field Longfellow against one re-committing prover, with Fiat–Shamir hash inputs as deployed

`Lfzk.NizkAdaptiveTwoField` and the two-field part of `Lfzk.CompiledLongfellowAdaptive` bound one
prover program that builds both sides' Merkle trees and grinds both sides' transcripts, with the
MAC-key share hashed from the two roots, at hash inputs that carry the raw earlier answers.  Here the
hash inputs are the deployed ones and the challenge oracle is the total random oracle on them
(`Bcs.TotalOracleCommit`), so `N` counts deployed hash queries over all three roles.

## The deployed transcript (`rust/applications/mdoc_zk/runtime/src/prover.rs`)

One running transcript: the first side's commitment and the second side's are absorbed, the
MAC-key share `av` is drawn (`tp.u128()`), the first side is proved — its public inputs, which
contain `av` and the MACs, are absorbed (`write_sumcheck_statement`), then its sumcheck messages,
each challenge drawn from the digest and not re-absorbed — and then the second side is proved on the
same transcript.  So (`hash2`):

* round `0`, **the key point**, is the pair of roots;
* side 1's round `k` hashes the roots, the public inputs (`av` and the public data `pub`) and side 1's
  messages through round `k` — an `MPoint (SideCtx D C X) Msg₁` with context `(roots, av, pub)`;
* side 2's round `k` hashes all of that, **all of side 1's messages**, and side 2's messages through
  round `k` — an `MPoint (SideCtx D C X × (Fin L₁ → Msg₁)) Msg₂`.

`av` enters a hash input only as a public input that the proof carries (`avOf out`), and the
verifier checks it against its own recomputation `ro (key point)` — that equation is part of the
acceptance event.  Hash inputs are then functions of the proof alone, which is what
`Bcs.TotalOracle` needs.  In the deployed mdoc pairing, side 1 is the `GF(2^128)` hash circuit and
side 2 the `P-256` signature circuit (`p256sha_adaptive_compiled_ratio_le` instantiates it so).

## What is proved

* `twofield_adaptive_ratio_le` — `NizkAdaptiveTwoField.twofield_adaptive_ratio_le`'s right-hand side
  for an abstract pair of compiled verifiers:

```text
Pr[ both verifiers accept ∧ av is the key answer ∧ no two good witnesses agree ]
    ≤  R₁.bound + R₂.bound + 1/|Fmac|  +  N · max(κ₁, κ₂, 1/|Fmac|)
       +  2 · tape · (1 + L₁ + L₂ + N) / 2^digestBits
```

* `twofield_adaptive_compiled_ratio_le` — the same at the compiled Longfellow verifiers
  (`CompiledLongfellowAdaptive.CompiledSide`), `hlig` and `hright` theorems;
* `p256sha_adaptive_compiled_ratio_le` (`≤ 2^-114 + N · 2^-115`) and `twofield_rhs_swap`, which lets
  any certified pair (whose numerals are stated ECDSA-first) be instantiated hash-first.

## What is still a hypothesis

Those of `CompiledLongfellowAdaptive.twofield_adaptive_compiled_ratio_le`: per side a `CompiledSide`
(verifier data, LayerStep data with `hexact`, `MD`, `Matches`, Ligero's extractor `hfalse`, `|F|`),
`|Cand|`, `|D|`, the MAC data `aP`, `decode`, `hbal`, `hmac`, the MAC rows `hrow₁`, `hrow₂` (now at
the `av` the proof carries), fuels; plus finiteness of `X`, `Msg₁`, `Msg₂`.  The idealisation of the
SHA-256 transcript as a random oracle on prefixes is `Lfzk.NizkDeployedHash`'s.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.NizkDeployedHashTwoField

open Finset Bcs Bcs.TotalOracleCommit Merkle Merkle.MH Merkle.RandomOracle
  Merkle.RandomOracle.TwoOracleTree RbrLongfellow Lfzk.NizkGrinding Lfzk.NizkDeployedHash
  Lfzk.NizkDeployedHashAdaptive Lfzk.CertifiedV1 Lfzk.Mac
open Lfzk.NizkAdaptiveTwoField (SideCtx Side check2 len2 sum_roleAt)
open scoped Classical

/-! ## 1. The two-field transcript, as deployed -/

/-- **A deployed two-field hash input**: the key point (the two roots), a point of side 1 (context
roots, `av`, public data), or a point of side 2 (that context and all of side 1's messages). -/
abbrev Pt2 (D C X Msg₁ Msg₂ : Type) (nl₁ nl₂ : ℕ) (w₁ w₂ : ℕ → ℕ) :=
  (D × D) ⊕ (MPoint (SideCtx D C X) Msg₁ nl₁ w₁ ⊕
    MPoint (SideCtx D C X × (Fin (Rounds.Role.length nl₁ w₁) → Msg₁)) Msg₂ nl₂ w₂)

section Transcript

variable {D C X Msg₁ Msg₂ Out : Type} {nl₁ nl₂ : ℕ} {w₁ w₂ : ℕ → ℕ}

/-- The pair of roots a point names. -/
def key2 : Pt2 D C X Msg₁ Msg₂ nl₁ nl₂ w₁ w₂ → D × D :=
  Sum.elim id (Sum.elim (fun p => p.ctx.1) (fun p => p.ctx.1.1))

/-- The side context a proof carries: both roots, the MAC-key share it claims, and the public
data. -/
def ctxOf (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X) (out : Out) :
    SideCtx D C X :=
  ((rootOf₁ out, rootOf₂ out), avOf out, pubOf out)

variable [Inhabited Msg₁] [Inhabited Msg₂]

/-- **The verifier's round-`k` hash input.**  Round `0` is the key point, rounds `1 + k₁` side 1's,
the rest side 2's (whose prefix contains all of side 1's messages). -/
noncomputable def hash2 (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂) (out : Out) (k : ℕ) :
    Pt2 D C X Msg₁ Msg₂ nl₁ nl₂ w₁ w₂ :=
  if k = 0 then Sum.inl (rootOf₁ out, rootOf₂ out)
  else if k < 1 + Rounds.Role.length nl₁ w₁ then
    Sum.inr (Sum.inl (msgPoint (nl := nl₁) (w := w₁) (ctxOf rootOf₁ rootOf₂ avOf pubOf out)
      msgOf₁ out (k - 1)))
  else
    Sum.inr (Sum.inr (msgPoint (nl := nl₂) (w := w₂)
      (ctxOf rootOf₁ rootOf₂ avOf pubOf out,
        fun i : Fin (Rounds.Role.length nl₁ w₁) => msgOf₁ out i.val)
      msgOf₂ out (k - 1 - Rounds.Role.length nl₁ w₁)))

theorem key2_hash2 (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂) (out : Out) (k : ℕ) :
    key2 (hash2 (nl₁ := nl₁) (nl₂ := nl₂) (w₁ := w₁) (w₂ := w₂) rootOf₁ rootOf₂ avOf pubOf msgOf₁
      msgOf₂ out k) = (rootOf₁ out, rootOf₂ out) := by
  unfold hash2
  split_ifs <;> rfl

theorem hash2_zero (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂) (out : Out) :
    hash2 (nl₁ := nl₁) (nl₂ := nl₂) (w₁ := w₁) (w₂ := w₂) rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      out 0 = Sum.inl (rootOf₁ out, rootOf₂ out) := by
  unfold hash2; rw [if_pos rfl]

theorem hash2_side1 (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂) (out : Out) {k₁ : ℕ}
    (hk : k₁ < Rounds.Role.length nl₁ w₁) :
    hash2 (nl₁ := nl₁) (nl₂ := nl₂) (w₁ := w₁) (w₂ := w₂) rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      out (1 + k₁)
      = Sum.inr (Sum.inl (msgPoint (nl := nl₁) (w := w₁) (ctxOf rootOf₁ rootOf₂ avOf pubOf out)
          msgOf₁ out k₁)) := by
  unfold hash2
  rw [if_neg (by omega), if_pos (by omega), show 1 + k₁ - 1 = k₁ by omega]

theorem hash2_side2 (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂) (out : Out) (k₂ : ℕ) :
    hash2 (nl₁ := nl₁) (nl₂ := nl₂) (w₁ := w₁) (w₂ := w₂) rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      out (1 + Rounds.Role.length nl₁ w₁ + k₂)
      = Sum.inr (Sum.inr (msgPoint (nl := nl₂) (w := w₂)
          (ctxOf rootOf₁ rootOf₂ avOf pubOf out,
            fun i : Fin (Rounds.Role.length nl₁ w₁) => msgOf₁ out i.val) msgOf₂ out k₂)) := by
  unfold hash2
  rw [if_neg (by omega), if_neg (by omega),
    show 1 + Rounds.Role.length nl₁ w₁ + k₂ - 1 - Rounds.Role.length nl₁ w₁ = k₂ by omega]

/-- A sum over the actual deployed verifier hash inputs consists of the
key point followed by each side's own complete role sequence.  This exact
identity is used when a graded side path pays a unit across several slots. -/
theorem sum_hash2 {A : Type} [AddCommMonoid A]
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (out : Out) (f : Pt2 D C X Msg₁ Msg₂ nl₁ nl₂ w₁ w₂ → A) :
    (∑ i : Fin (1 + Rounds.Role.length nl₁ w₁ + Rounds.Role.length nl₂ w₂),
      f (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out i.val)) =
      f (Sum.inl (rootOf₁ out, rootOf₂ out)) +
      (∑ i : Fin (Rounds.Role.length nl₁ w₁),
        f (Sum.inr (Sum.inl
          (msgPoint (ctxOf rootOf₁ rootOf₂ avOf pubOf out) msgOf₁ out i.val)))) +
      (∑ i : Fin (Rounds.Role.length nl₂ w₂),
        f (Sum.inr (Sum.inr
          (msgPoint (ctxOf rootOf₁ rootOf₂ avOf pubOf out,
            fun j : Fin (Rounds.Role.length nl₁ w₁) => msgOf₁ out j.val)
              msgOf₂ out i.val)))) := by
  classical
  let g : ℕ → A := fun i => f (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out i)
  change (∑ i : Fin (1 + Rounds.Role.length nl₁ w₁ + Rounds.Role.length nl₂ w₂),
    g i.val) = _
  rw [Fin.sum_univ_eq_sum_range g,
    Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_one]
  have g0 : g 0 = f (Sum.inl (rootOf₁ out, rootOf₂ out)) := by
    exact congrArg f (hash2_zero rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out)
  rw [g0]
  congr 1
  · congr 1
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg f (hash2_side1 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out
      i.isLt)
  · rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg f (hash2_side2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out i)

/-- The round a point is drawn for, on the merged schedule. -/
def slot2 : Pt2 D C X Msg₁ Msg₂ nl₁ nl₂ w₁ w₂ → ℕ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl p) => 1 + p.role.slot
  | Sum.inr (Sum.inr p) => 1 + Rounds.Role.length nl₁ w₁ + p.role.slot

/-- Each deployed verifier hash input records its exact round in its point
type.  Consequently a transcript cannot count one oracle answer twice at
two different verifier slots in a graded-potential sum. -/
theorem slot2_hash2 (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂) (out : Out)
    (i : Fin (1 + Rounds.Role.length nl₁ w₁ + Rounds.Role.length nl₂ w₂)) :
    slot2 (nl₁ := nl₁) (nl₂ := nl₂) (w₁ := w₁) (w₂ := w₂)
      (hash2 (nl₁ := nl₁) (nl₂ := nl₂) (w₁ := w₁) (w₂ := w₂)
        rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out i.val) = i.val := by
  unfold hash2
  split_ifs with h0 h1
  · simp [slot2, h0]
  · change 1 + (roleAt (nl := nl₁) (w := w₁) (i.val - 1)).slot = i.val
    rw [slot_roleAt (by omega)]
    omega
  · change 1 + Rounds.Role.length nl₁ w₁ +
        (roleAt (nl := nl₂) (w := w₂)
          (i.val - 1 - Rounds.Role.length nl₁ w₁)).slot = i.val
    rw [slot_roleAt (by omega)]
    omega

/-- The actual two-field verifier's hash inputs are pairwise distinct. -/
theorem hash2_injective (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂) (out : Out) :
    Function.Injective (fun i : Fin (1 + Rounds.Role.length nl₁ w₁ +
      Rounds.Role.length nl₂ w₂) =>
        hash2 (nl₁ := nl₁) (nl₂ := nl₂) (w₁ := w₁) (w₂ := w₂)
          rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out i.val) := by
  intro i j hij
  apply Fin.ext
  have h := congrArg (slot2 (nl₁ := nl₁) (nl₂ := nl₂) (w₁ := w₁) (w₂ := w₂)) hij
  simpa only [slot2_hash2] using h

/-- A point's ancestors on the merged schedule: the key point, then the earlier rounds of the same
prefix (for side 2, side 1's rounds come first). -/
noncomputable def anc2 : Pt2 D C X Msg₁ Msg₂ nl₁ nl₂ w₁ w₂ → ℕ → Pt2 D C X Msg₁ Msg₂ nl₁ nl₂ w₁ w₂
  | Sum.inl r, _ => Sum.inl r
  | Sum.inr (Sum.inl p), j =>
      if j = 0 then Sum.inl p.ctx.1 else Sum.inr (Sum.inl (mpoints.anc p (j - 1)))
  | Sum.inr (Sum.inr p), j =>
      if j = 0 then Sum.inl p.ctx.1.1
      else if j < 1 + Rounds.Role.length nl₁ w₁ then
        Sum.inr (Sum.inl ⟨p.ctx.1, roleAt (j - 1),
          padMsgs (fun i => if h : i < Rounds.Role.length nl₁ w₁ then p.ctx.2 ⟨i, h⟩ else default)
            (j - 1)⟩)
      else Sum.inr (Sum.inr (mpoints.anc p (j - 1 - Rounds.Role.length nl₁ w₁)))

/-- **The ancestor structure of the merged schedule.** -/
noncomputable def pts2 : TotalOracle.PrefixPoints (Pt2 D C X Msg₁ Msg₂ nl₁ nl₂ w₁ w₂) where
  slot := slot2
  anc := anc2
  anc_ne q j hj := by
    rcases q with r | p | p
    · simp [slot2] at hj
    · simp only [slot2] at hj
      simp only [anc2]
      split_ifs with h0
      · exact Sum.inl_ne_inr
      · intro h
        exact mpoints.anc_ne p (j - 1) (by show j - 1 < p.role.slot; omega)
          (Sum.inl.inj (Sum.inr.inj h))
    · simp only [slot2] at hj
      simp only [anc2]
      split_ifs with h0 h1
      · exact Sum.inl_ne_inr
      · intro h
        exact Sum.inl_ne_inr (Sum.inr.inj h)
      · intro h
        exact mpoints.anc_ne p (j - 1 - Rounds.Role.length nl₁ w₁)
          (by show j - 1 - Rounds.Role.length nl₁ w₁ < p.role.slot; omega)
          (Sum.inr.inj (Sum.inr.inj h))

/-- A prefix, read as a total function. -/
def pget {m : ℕ} (dflt : C) (pref : Fin m → C) (j : ℕ) : C :=
  if h : j < m then pref ⟨j, h⟩ else dflt

/-- At a side-1 point, round `j` of side 1 is read at the ancestor `1 + j`. -/
theorem pget_side1 (dflt : C) (ro : Pt2 D C X Msg₁ Msg₂ nl₁ nl₂ w₁ w₂ → C)
    (p : MPoint (SideCtx D C X) Msg₁ nl₁ w₁) (j : Fin p.role.slot) :
    pget dflt (pts2.chal ro (Sum.inr (Sum.inl p))) (1 + j.val)
      = ro (Sum.inr (Sum.inl (mpoints.anc p j.val))) := by
  have hlt : 1 + j.val < (pts2 : TotalOracle.PrefixPoints (Pt2 D C X Msg₁ Msg₂ nl₁ nl₂ w₁ w₂)).slot
      (Sum.inr (Sum.inl p)) := by
    show 1 + j.val < 1 + p.role.slot
    omega
  unfold pget
  rw [dif_pos hlt]
  show ro (anc2 (Sum.inr (Sum.inl p)) (1 + j.val)) = _
  simp only [anc2]
  rw [if_neg (by omega), show 1 + j.val - 1 = j.val by omega]

/-- The whole side-1 ancestor prefix, not merely one coordinate. -/
theorem pget_side1_prefix (dflt : C)
    (ro : Pt2 D C X Msg₁ Msg₂ nl₁ nl₂ w₁ w₂ → C)
    (p : MPoint (SideCtx D C X) Msg₁ nl₁ w₁) :
    (fun j : Fin p.role.slot =>
      pget dflt (pts2.chal ro (Sum.inr (Sum.inl p))) (1 + j.val)) =
      mpoints.chal (fun q => ro (Sum.inr (Sum.inl q))) p := by
  funext j
  exact pget_side1 dflt ro p j

/-- At a side-2 point, round `j` of side 2 is read at the ancestor `1 + L₁ + j`. -/
theorem pget_side2 (dflt : C) (ro : Pt2 D C X Msg₁ Msg₂ nl₁ nl₂ w₁ w₂ → C)
    (p : MPoint (SideCtx D C X × (Fin (Rounds.Role.length nl₁ w₁) → Msg₁)) Msg₂ nl₂ w₂)
    (j : Fin p.role.slot) :
    pget dflt (pts2.chal ro (Sum.inr (Sum.inr p))) (1 + Rounds.Role.length nl₁ w₁ + j.val)
      = ro (Sum.inr (Sum.inr (mpoints.anc p j.val))) := by
  have hlt : 1 + Rounds.Role.length nl₁ w₁ + j.val
      < (pts2 : TotalOracle.PrefixPoints (Pt2 D C X Msg₁ Msg₂ nl₁ nl₂ w₁ w₂)).slot
        (Sum.inr (Sum.inr p)) := by
    show 1 + Rounds.Role.length nl₁ w₁ + j.val < 1 + Rounds.Role.length nl₁ w₁ + p.role.slot
    omega
  unfold pget
  rw [dif_pos hlt]
  show ro (anc2 (Sum.inr (Sum.inr p)) (1 + Rounds.Role.length nl₁ w₁ + j.val)) = _
  simp only [anc2]
  rw [if_neg (by omega), if_neg (by omega),
    show 1 + Rounds.Role.length nl₁ w₁ + j.val - 1 - Rounds.Role.length nl₁ w₁ = j.val by omega]

/-- The whole side-2 ancestor prefix. -/
theorem pget_side2_prefix (dflt : C)
    (ro : Pt2 D C X Msg₁ Msg₂ nl₁ nl₂ w₁ w₂ → C)
    (p : MPoint (SideCtx D C X ×
      (Fin (Rounds.Role.length nl₁ w₁) → Msg₁)) Msg₂ nl₂ w₂) :
    (fun j : Fin p.role.slot =>
      pget dflt (pts2.chal ro (Sum.inr (Sum.inr p)))
        (1 + Rounds.Role.length nl₁ w₁ + j.val)) =
      mpoints.chal (fun q => ro (Sum.inr (Sum.inr q))) p := by
  funext j
  exact pget_side2 dflt ro p j

/-- **The deployed two-field reading of a re-committing prover.** -/
noncomputable def setup2 [Nonempty C] {Enc : Type} {tA N : ℕ}
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ nl₁ nl₂ w₁ w₂) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂) :
    TotalOracleCommit.Setup Enc D (Pt2 D C X Msg₁ Msg₂ nl₁ nl₂ w₁ w₂) C Out (D × D) tA N
      (1 + Rounds.Role.length nl₁ w₁ + Rounds.Role.length nl₂ w₂) where
  body := body
  hashInput := hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
  dflt := Classical.arbitrary C
  key := key2
  keyOut out := (rootOf₁ out, rootOf₂ out)
  hkey := key2_hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂

/-- The concrete two-field setup satisfies the injective-schedule premise
of the graded potential compiler. -/
theorem setup2_hashInput_injective [Nonempty C] {Enc : Type} {tA N : ℕ}
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ nl₁ nl₂ w₁ w₂) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂) :
    ∀ out, Function.Injective (fun i : Fin (1 + Rounds.Role.length nl₁ w₁ +
      Rounds.Role.length nl₂ w₂) =>
        (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).hashInput out i.val) := by
  intro out
  exact hash2_injective rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out

end Transcript

/-! ## 2. Two sides, one prover, one hashed MAC key -/

section Compose

variable {R₁ R₂ : Row}
variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {D : Type} [Fintype D] [DecidableEq D] [Inhabited D]
variable {Enc X Out : Type} [DecidableEq Enc] [Fintype X]
variable {Fmac : Type} [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {nblk : ℕ}
variable {Cand₁ F₁ Equations₁ Witness₁ Msg₁ : Type} [Fintype Cand₁] [Nonempty Cand₁] [Field F₁]
  [Fintype F₁] [DecidableEq F₁] [SumcheckInterp F₁] [Fintype Equations₁] [DecidableEq Equations₁]
  [Inhabited Msg₁] [Fintype Msg₁] {nc₁ nv₁ logw₁ logc₁ : ℕ}
variable {Cand₂ F₂ Equations₂ Witness₂ Msg₂ : Type} [Fintype Cand₂] [Nonempty Cand₂] [Field F₂]
  [Fintype F₂] [DecidableEq F₂] [SumcheckInterp F₂] [Fintype Equations₂] [DecidableEq Equations₂]
  [Inhabited Msg₂] [Fintype Msg₂] {nc₂ nv₂ logw₂ logc₂ : ℕ}
variable {Statement₁ Oracle₁ Challenge₁ Response₁ Query₁ : Type} {Opening₁ : Query₁ → Type}
variable {Statement₂ Oracle₂ Challenge₂ Response₂ Query₂ : Type} {Opening₂ : Query₂ → Type}
variable {Salt₁ M₁ Salt₂ M₂ : Type} [Inhabited Salt₁] [Inhabited M₁] [Inhabited Salt₂]
  [Inhabited M₂] {n₁ n₂ : ℕ}

/--
**Two-field Longfellow against one re-committing prefix-only Fiat–Shamir prover, with a hashed MAC
key.**

Over one Merkle tape (`R₁.tape` slots, shared by both sides' trees) and the random oracle on the
deployed hash inputs `Pt2`, against one program `body` with at most `tA` Merkle-oracle and `N`
challenge-oracle queries over all three roles:

```text
Pr[ both verifiers accept ∧ av = ro(key point) ∧ no two good witnesses agree on the common value ]
    ≤  R₁.bound + R₂.bound + 1/|Fmac|  +  N · max(κ₁, κ₂, 1/|Fmac|)
       +  2 · R₁.tape · (1 + L₁ + L₂ + N) / 2^digestBits
```

The side context is `σ = (κ, avOf out, pubOf out)`: the commitment context of the pair of roots and
the public inputs the proof carries.  The premises are `NizkAdaptiveTwoField.twofield_adaptive_ratio_le`'s,
with the MAC rows at the proof's `av`.
-/
theorem twofield_adaptive_ratio_le (h₁ : R₁.Valid) {tA N : ℕ}
    {codec₁ : Codec Salt₁ M₁ D Enc} (dec₁ : RoleDecoders codec₁)
    {codec₂ : Codec Salt₂ M₂ D Enc} (dec₂ : RoleDecoders codec₂)
    (K₁ : Compiler Statement₁ Oracle₁ Challenge₁ Response₁ Query₁ Opening₁ M₁ n₁)
    (K₂ : Compiler Statement₂ Oracle₂ Challenge₂ Response₂ Query₂ Opening₂ M₂ n₂)
    -- the prover, and the verifier's reading of its proof
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds
      R₂.params.rounds) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim n₁ Salt₁ M₁ D) (claimOf₂ : Out → OpeningClaim n₂ Salt₂ M₂ D)
    (statementOf₁ : Out → (Fin (len2 R₁ R₂) → C) → Statement₁) (responseOf₁ : Out → Response₁)
    (challengeOf₁ : Out → (Fin (len2 R₁ R₂) → C) → Challenge₁)
    (queryOf₁ : Out → (Fin (len2 R₁ R₂) → C) → Query₁)
    (statementOf₂ : Out → (Fin (len2 R₁ R₂) → C) → Statement₂) (responseOf₂ : Out → Response₂)
    (challengeOf₂ : Out → (Fin (len2 R₁ R₂) → C) → Challenge₂)
    (queryOf₂ : Out → (Fin (len2 R₁ R₂) → C) → Query₂)
    -- the two sides, per side context
    (S₁ : Side R₁ (((D × D) × List (Enc × D)) × C × X) C Cand₁ F₁ Equations₁ Witness₁ Msg₁
      nc₁ nv₁ logw₁ logc₁)
    (S₂ : Side R₂ (((D × D) × List (Enc × D)) × C × X) C Cand₂ F₂ Equations₂ Witness₂ Msg₂
      nc₂ nv₂ logw₂ logc₂)
    (hF₁ : Fintype.card F₁ = R₁.params.row.fieldSize)
    (hF₂ : Fintype.card F₂ = R₂.params.row.fieldSize)
    (hcand₁ : Fintype.card Cand₁ = R₁.cardCand) (hcand₂ : Fintype.card Cand₂ = R₂.cardCand)
    (hD₁ : Fintype.card D = 2 ^ R₁.params.digestBits)
    (hD₂ : Fintype.card D = 2 ^ R₂.params.digestBits)
    -- the MAC
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : Witness₁ → Fin nblk → Fmac) (common₂ : Witness₂ → Fin nblk → Fmac)
    -- acceptance, transliteration, and the MAC rows
    (hright₁ : ∀ (mt : Fin R₁.tape → D)
        (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      let σ := (S.context mt ro, avOf (S.proof mt ro), pubOf (S.proof mt ro))
      (∀ cand, ¬ S₁.Sat σ cand) →
      JointAccepts K₁ codec₁ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ claimOf₁
        statementOf₁ responseOf₁ challengeOf₁ queryOf₁ mt ro →
      S.Explains dec₁ Prod.fst claimOf₁ mt ro →
      RbrSplit.LayerStepAccepts
        (RbrSplit.stepsOf (nl := R₁.params.nl) (w := R₁.params.rounds)
          (withMsgs (S₁.field σ) (S₁.MD σ) (msgOf₁ (S.proof mt ro)))
          (fun m pref => S₁.accR σ m pref (msgOf₁ (S.proof mt ro) m)))
        (fun i => S.challenges mt ro ⟨1 + i.val, by omega⟩))
    (hright₂ : ∀ (mt : Fin R₁.tape → D)
        (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      let σ := (S.context mt ro, avOf (S.proof mt ro), pubOf (S.proof mt ro))
      (∀ cand, ¬ S₂.Sat σ cand) →
      JointAccepts K₂ codec₂ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂
        statementOf₂ responseOf₂ challengeOf₂ queryOf₂ mt ro →
      S.Explains dec₂ Prod.snd claimOf₂ mt ro →
      RbrSplit.LayerStepAccepts
        (RbrSplit.stepsOf (nl := R₂.params.nl) (w := R₂.params.rounds)
          (withMsgs (S₂.field σ) (S₂.MD σ) (msgOf₂ (S.proof mt ro)))
          (fun m pref => S₂.accR σ m pref (msgOf₂ (S.proof mt ro) m)))
        (fun i => S.challenges mt ro
          ⟨1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + i.val, by omega⟩))
    (hrow₁ : ∀ (mt : Fin R₁.tape → D)
        (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C)
        (a : Witness₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      JointAccepts K₁ codec₁ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ claimOf₁
        statementOf₁ responseOf₁ challengeOf₁ queryOf₁ mt ro →
      S₁.Good (S.context mt ro, avOf (S.proof mt ro), pubOf (S.proof mt ro)) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin R₁.tape → D)
        (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C)
        (a : Witness₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      JointAccepts K₂ codec₂ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂
        statementOf₂ responseOf₂ challengeOf₂ queryOf₂ mt ro →
      S₂.Good (S.context mt ro, avOf (S.proof mt ro), pubOf (S.proof mt ro)) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₂ a) = tagOf (S.proof mt ro))
    -- the prover's Merkle budget and the shared Merkle tape
    (htA₁ : tA ≤ R₁.commitFuel) (htA₂ : tA ≤ R₂.commitFuel)
    (htape : 2 * n₂ + 2 * n₁ + tA ≤ R₁.tape) (htape₂ : R₁.tape = R₂.tape) :
    ((univ.filter fun ω : (Fin R₁.tape → D) ×
          (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C) =>
        JointAccepts K₁ codec₁ (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ claimOf₁ statementOf₁ responseOf₁
            challengeOf₁ queryOf₁ ω.1 ω.2 ∧
          JointAccepts K₂ codec₂ (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂ statementOf₂ responseOf₂
            challengeOf₂ queryOf₂ ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2 ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            S₁.Good ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).context ω.1 ω.2,
              avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2),
              pubOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2)) a₁ ∧
            S₂.Good ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).context ω.1 ω.2,
              avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2),
              pubOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2)) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ R₁.tape * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds))
      ≤ R₁.bound + R₂.bound + 1 / (Fintype.card Fmac : ℚ)
        + N * max (max R₁.fsCoefficient R₂.fsCoefficient) (1 / (Fintype.card Fmac : ℚ))
        + 2 * (((R₁.tape * (len2 R₁ R₂ + N) : ℕ) : ℚ) / 2 ^ R₁.params.digestBits) := by
  set S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ with hS
  set dflt : C := Classical.arbitrary C with hdflt
  -- the Ligero halves, in each failing side context
  choose LigD₁ ML₁ hacc₁ hesc₁ hbq₁ using S₁.hlig
  choose LigD₂ ML₂ hacc₂ hesc₂ hbq₂ using S₂.hlig
  have hCpos : 0 < Fintype.card C := Fintype.card_pos
  have hFpos₁ : 0 < R₁.params.row.fieldSize := by rw [← hF₁]; exact Fintype.card_pos
  have hFpos₂ : 0 < R₂.params.row.fieldSize := by rw [← hF₂]; exact Fintype.card_pos
  set bp₁ := pairBudget (Fintype.card C) R₁.params.row.fieldSize
  set bi₁ := inBudget (Fintype.card C) R₁.params.row.fieldSize
  set bl₁ := ligBudget R₁.params.row (Fintype.card C)
  set bq₁ := queryBudget R₁.params.row (Fintype.card C)
  set bp₂ := pairBudget (Fintype.card C) R₂.params.row.fieldSize
  set bi₂ := inBudget (Fintype.card C) R₂.params.row.fieldSize
  set bl₂ := ligBudget R₂.params.row (Fintype.card C)
  set bq₂ := queryBudget R₂.params.row (Fintype.card C)
  have hB₁ : ∀ σ (hσ : ∀ cand, ¬ S₁.Sat σ cand),
      MsgBudgets (S₁.field σ) (ML₁ σ hσ) bp₁ bp₁ bi₁ bl₁ bq₁ := by
    intro σ hσ
    have ep : 2 * Fintype.card C / Fintype.card F₁ = bp₁ := by rw [hF₁]; rfl
    have ei : Fintype.card C / Fintype.card F₁ = bi₁ := by rw [hF₁]; rfl
    obtain ⟨hp0, hp1, hr, hi⟩ := (S₁.hexact σ).field_budgets
    obtain ⟨-, -, hchal, hqq⟩ := S₁.hexact σ
    refine ⟨hp0.trans_eq ep, hp1.trans_eq ep, hr.trans_eq ep, hi.trans_eq ei,
      LigeroV1LayerStep.mul_le_floor (add_nonneg (LigeroV1LayerStep.fail_nonneg _)
        (LigeroV1LayerStep.arith_nonneg _)) (hesc₁ σ hσ) hchal, ?_⟩
    rw [hbq₁ σ hσ]
    exact LigeroV1LayerStep.queryBudget_le hqq
  have hB₂ : ∀ σ (hσ : ∀ cand, ¬ S₂.Sat σ cand),
      MsgBudgets (S₂.field σ) (ML₂ σ hσ) bp₂ bp₂ bi₂ bl₂ bq₂ := by
    intro σ hσ
    have ep : 2 * Fintype.card C / Fintype.card F₂ = bp₂ := by rw [hF₂]; rfl
    have ei : Fintype.card C / Fintype.card F₂ = bi₂ := by rw [hF₂]; rfl
    obtain ⟨hp0, hp1, hr, hi⟩ := (S₂.hexact σ).field_budgets
    obtain ⟨-, -, hchal, hqq⟩ := S₂.hexact σ
    refine ⟨hp0.trans_eq ep, hp1.trans_eq ep, hr.trans_eq ep, hi.trans_eq ei,
      LigeroV1LayerStep.mul_le_floor (add_nonneg (LigeroV1LayerStep.fail_nonneg _)
        (LigeroV1LayerStep.arith_nonneg _)) (hesc₂ σ hσ) hchal, ?_⟩
    rw [hbq₂ σ hσ]
    exact LigeroV1LayerStep.queryBudget_le hqq
  -- the bad event at a point, by role, reading the ancestors' answers as a total function
  let L₁ := Rounds.Role.length R₁.params.nl R₁.params.rounds
  obtain ⟨Bad', hBad'⟩ : ∃ Bad' : (D × D) × List (Enc × D) →
      Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds →
        (ℕ → C) → C → Prop,
      Bad' = fun κ q g c => Sum.elim (fun _ => aP κ + decode c = 0)
        (Sum.elim
          (fun p => ∃ hσ : (∀ cand, ¬ S₁.Sat (κ, p.ctx.2.1, p.ctx.2.2) cand),
            (layerStep (nl := R₁.params.nl) (w := R₁.params.rounds) (S₁.field (κ, p.ctx.2.1, p.ctx.2.2))
                (S₁.MD (κ, p.ctx.2.1, p.ctx.2.2)) (ML₁ (κ, p.ctx.2.1, p.ctx.2.2) hσ) p.msgFn).doomed
                p.role.slot (fun j => g (1 + j.val)) ∧
              ¬ (layerStep (nl := R₁.params.nl) (w := R₁.params.rounds)
                (S₁.field (κ, p.ctx.2.1, p.ctx.2.2)) (S₁.MD (κ, p.ctx.2.1, p.ctx.2.2))
                (ML₁ (κ, p.ctx.2.1, p.ctx.2.2) hσ) p.msgFn).doomed (p.role.slot + 1)
                (Bcs.extend (fun j => g (1 + j.val)) c))
          (fun p => ∃ hσ : (∀ cand, ¬ S₂.Sat (κ, p.ctx.1.2.1, p.ctx.1.2.2) cand),
            (layerStep (nl := R₂.params.nl) (w := R₂.params.rounds)
                (S₂.field (κ, p.ctx.1.2.1, p.ctx.1.2.2)) (S₂.MD (κ, p.ctx.1.2.1, p.ctx.1.2.2))
                (ML₂ (κ, p.ctx.1.2.1, p.ctx.1.2.2) hσ) p.msgFn).doomed
                p.role.slot (fun j => g (1 + L₁ + j.val)) ∧
              ¬ (layerStep (nl := R₂.params.nl) (w := R₂.params.rounds)
                (S₂.field (κ, p.ctx.1.2.1, p.ctx.1.2.2)) (S₂.MD (κ, p.ctx.1.2.1, p.ctx.1.2.2))
                (ML₂ (κ, p.ctx.1.2.1, p.ctx.1.2.2) hσ) p.msgFn).doomed (p.role.slot + 1)
                (Bcs.extend (fun j => g (1 + L₁ + j.val)) c))) q := ⟨_, rfl⟩
  let Bad : (D × D) × List (Enc × D) →
      (x : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds) →
        (Fin (pts2.slot x) → C) → C → Prop :=
    fun κ x pref c => Bad' κ x (pget dflt pref) c
  let beta : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds →
      ℕ := Sum.elim (fun _ => kmac) (Sum.elim
    (fun p => Fintype.card Cand₁ * RbrLayerStep.classBudget (nl := R₁.params.nl)
      (w := R₁.params.rounds) bp₁ bp₁ bi₁ bl₁ bq₁ p.role)
    (fun p => Fintype.card Cand₂ * RbrLayerStep.classBudget (nl := R₂.params.nl)
      (w := R₂.params.rounds) bp₂ bp₂ bi₂ bl₂ bq₂ p.role))
  have hbad : ∀ κ x pref, (univ.filter fun c : C => Bad κ x pref c).card ≤ beta x := by
    intro κ x pref
    rcases x with r | p | p
    · refine le_trans (Finset.card_le_card ?_) (hbal (-aP κ))
      intro c hc
      simp only [mem_filter, mem_univ, true_and, Bad, hBad', Sum.elim_inl] at hc ⊢
      linear_combination hc
    · set σ := (κ, p.ctx.2.1, p.ctx.2.2) with hσdef
      set g := pget dflt pref
      by_cases hσ : ∀ cand, ¬ S₁.Sat σ cand
      · by_cases hd : (layerStep (nl := R₁.params.nl) (w := R₁.params.rounds) (S₁.field σ)
            (S₁.MD σ) (ML₁ σ hσ) p.msgFn).doomed p.role.slot (fun j => g (1 + j.val))
        · have hpres := (layerStepRbr (nl := R₁.params.nl) (w := R₁.params.rounds) (S₁.field σ)
            (S₁.MD σ) (ML₁ σ hσ) (hB₁ σ hσ) (Fails := False) False.elim p.msgFn).doom_preserved
            p.role.index (fun j => g (1 + j.val)) hd
          rw [show (layerStepRbr (nl := R₁.params.nl) (w := R₁.params.rounds) (S₁.field σ)
              (S₁.MD σ) (ML₁ σ hσ) (hB₁ σ hσ) (Fails := False) False.elim p.msgFn).beta
                p.role.index
              = Fintype.card Cand₁ * RbrLayerStep.classBudget (nl := R₁.params.nl)
                  (w := R₁.params.rounds) bp₁ bp₁ bi₁ bl₁ bq₁
                  (Rounds.Role.indexEquiv.symm p.role.index) from rfl,
            indexEquiv_symm_index] at hpres
          refine le_trans (Finset.card_le_card ?_) hpres
          intro c hc
          simp only [mem_filter, mem_univ, true_and, Bad, hBad', Sum.elim_inr, Sum.elim_inl]
            at hc ⊢
          obtain ⟨_, _, he⟩ := hc
          exact he
        · refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
          intro c hc
          simp only [mem_filter, mem_univ, true_and, Bad, hBad', Sum.elim_inr, Sum.elim_inl]
            at hc
          obtain ⟨_, hd', _⟩ := hc
          exact absurd hd' hd
      · refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
        intro c hc
        simp only [mem_filter, mem_univ, true_and, Bad, hBad', Sum.elim_inr, Sum.elim_inl] at hc
        obtain ⟨hσ', _⟩ := hc
        exact absurd hσ' hσ
    · set σ := (κ, p.ctx.1.2.1, p.ctx.1.2.2) with hσdef
      set g := pget dflt pref
      by_cases hσ : ∀ cand, ¬ S₂.Sat σ cand
      · by_cases hd : (layerStep (nl := R₂.params.nl) (w := R₂.params.rounds) (S₂.field σ)
            (S₂.MD σ) (ML₂ σ hσ) p.msgFn).doomed p.role.slot (fun j => g (1 + L₁ + j.val))
        · have hpres := (layerStepRbr (nl := R₂.params.nl) (w := R₂.params.rounds) (S₂.field σ)
            (S₂.MD σ) (ML₂ σ hσ) (hB₂ σ hσ) (Fails := False) False.elim p.msgFn).doom_preserved
            p.role.index (fun j => g (1 + L₁ + j.val)) hd
          rw [show (layerStepRbr (nl := R₂.params.nl) (w := R₂.params.rounds) (S₂.field σ)
              (S₂.MD σ) (ML₂ σ hσ) (hB₂ σ hσ) (Fails := False) False.elim p.msgFn).beta
                p.role.index
              = Fintype.card Cand₂ * RbrLayerStep.classBudget (nl := R₂.params.nl)
                  (w := R₂.params.rounds) bp₂ bp₂ bi₂ bl₂ bq₂
                  (Rounds.Role.indexEquiv.symm p.role.index) from rfl,
            indexEquiv_symm_index] at hpres
          refine le_trans (Finset.card_le_card ?_) hpres
          intro c hc
          simp only [mem_filter, mem_univ, true_and, Bad, hBad', Sum.elim_inr] at hc ⊢
          obtain ⟨_, _, he⟩ := hc
          exact he
        · refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
          intro c hc
          simp only [mem_filter, mem_univ, true_and, Bad, hBad', Sum.elim_inr] at hc
          obtain ⟨_, hd', _⟩ := hc
          exact absurd hd' hd
      · refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
        intro c hc
        simp only [mem_filter, mem_univ, true_and, Bad, hBad', Sum.elim_inr] at hc
        obtain ⟨hσ', _⟩ := hc
        exact absurd hσ' hσ
  -- the worst point, and each verifier round's point
  set βmax := max kmac (max (Fintype.card Cand₁ * NizkGrinding.maxBudget bp₁ bp₁ bi₁ bl₁ bq₁)
    (Fintype.card Cand₂ * NizkGrinding.maxBudget bp₂ bp₂ bi₂ bl₂ bq₂)) with hβmax
  have hmax : ∀ q, beta q ≤ βmax := by
    intro q
    rcases q with r | p | p
    · exact le_max_left _ _
    · exact le_trans (Nat.mul_le_mul_left _ (classBudget_le_max p.role))
        (le_trans (le_max_left _ _) (le_max_right _ _))
    · exact le_trans (Nat.mul_le_mul_left _ (classBudget_le_max p.role))
        (le_trans (le_max_right _ _) (le_max_right _ _))
  let g : ℕ → ℕ := fun k =>
    if k = 0 then kmac
    else if k < 1 + Rounds.Role.length R₁.params.nl R₁.params.rounds then
      Fintype.card Cand₁ * RbrLayerStep.classBudget (nl := R₁.params.nl) (w := R₁.params.rounds)
        bp₁ bp₁ bi₁ bl₁ bq₁ (roleAt (k - 1))
    else
      Fintype.card Cand₂ * RbrLayerStep.classBudget (nl := R₂.params.nl) (w := R₂.params.rounds)
        bp₂ bp₂ bi₂ bl₂ bq₂ (roleAt (k - 1 - Rounds.Role.length R₁.params.nl R₁.params.rounds))
  let slotBeta : Fin (len2 R₁ R₂) → ℕ := fun i => g i.val
  have hslot : ∀ (out : Out) (i : Fin (len2 R₁ R₂)),
      beta (S.hashInput out i.val) ≤ slotBeta i := by
    intro out i
    show beta (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out i.val) ≤ g i.val
    unfold hash2
    simp only [g]
    split_ifs <;> exact le_rfl
  have hsum : ∑ i, slotBeta i
      = kmac + Fintype.card Cand₁ * (R₁.params.nl * bp₁
          + (∑ i ∈ Finset.range R₁.params.nl, R₁.params.rounds i) * bp₁ + bi₁ + bl₁ + bq₁)
        + Fintype.card Cand₂ * (R₂.params.nl * bp₂
          + (∑ i ∈ Finset.range R₂.params.nl, R₂.params.rounds i) * bp₂ + bi₂ + bl₂ + bq₂) := by
    rw [show (∑ i, slotBeta i) = ∑ i : Fin (len2 R₁ R₂), g i.val from rfl,
      Fin.sum_univ_eq_sum_range g, len2, Finset.sum_range_add, Finset.sum_range_add,
      Finset.sum_range_one]
    have e0 : g 0 = kmac := by simp only [g, if_pos rfl]
    have e1 : ∑ x ∈ range (Rounds.Role.length R₁.params.nl R₁.params.rounds), g (1 + x)
        = Fintype.card Cand₁ * ∑ x ∈ range (Rounds.Role.length R₁.params.nl R₁.params.rounds),
          RbrLayerStep.classBudget (nl := R₁.params.nl) (w := R₁.params.rounds)
            bp₁ bp₁ bi₁ bl₁ bq₁ (roleAt x) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x hx => ?_
      have hx' := Finset.mem_range.mp hx
      simp only [g]
      rw [if_neg (by omega), if_pos (by omega), show 1 + x - 1 = x by omega]
    have e2 : ∑ x ∈ range (Rounds.Role.length R₂.params.nl R₂.params.rounds),
          g (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + x)
        = Fintype.card Cand₂ * ∑ x ∈ range (Rounds.Role.length R₂.params.nl R₂.params.rounds),
          RbrLayerStep.classBudget (nl := R₂.params.nl) (w := R₂.params.rounds)
            bp₂ bp₂ bi₂ bl₂ bq₂ (roleAt x) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x hx => ?_
      simp only [g]
      rw [if_neg (by omega), if_neg (by omega),
        show 1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + x - 1
          - Rounds.Role.length R₁.params.nl R₁.params.rounds = x by omega]
    rw [e0, e1, e2, sum_roleAt, sum_roleAt, RbrLayerStep.layerStep_budget_sum,
      RbrLayerStep.layerStep_budget_sum]
  -- the chain: the three-way split of the composed failure, at the verifier's rounds
  have hchain : ∀ (mt : Fin R₁.tape → D)
      (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C),
      (JointAccepts K₁ codec₁ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ claimOf₁
          statementOf₁ responseOf₁ challengeOf₁ queryOf₁ mt ro ∧
        JointAccepts K₂ codec₂ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂
          statementOf₂ responseOf₂ challengeOf₂ queryOf₂ mt ro ∧
        S.challenges mt ro ⟨0, by omega⟩ = avOf (S.proof mt ro)) →
      S.Explains dec₁ Prod.fst claimOf₁ mt ro → S.Explains dec₂ Prod.snd claimOf₂ mt ro →
      (¬ ∃ a₁ a₂,
        S₁.Good (S.context mt ro, avOf (S.proof mt ro), pubOf (S.proof mt ro)) a₁ ∧
        S₂.Good (S.context mt ro, avOf (S.proof mt ro), pubOf (S.proof mt ro)) a₂ ∧
        common₁ a₁ = common₂ a₂) →
      (S.grinding mt pts2 Bad beta hbad).RoundBad ro := by
    intro mt ro hacc hex₁ hex₂ hcomp
    set out := S.proof mt ro with hout
    set σ := (S.context mt ro, avOf out, pubOf out) with hσdef
    set ctx₁ := ctxOf rootOf₁ rootOf₂ avOf pubOf out with hctx₁
    by_cases hσ₁ : ∀ cand, ¬ S₁.Sat σ cand
    · -- side 1 has no good witness: its LayerStep sheds doom at some side-1 round
      have hlayerStep := hright₁ mt ro hσ₁ hacc.1 hex₁
      rw [← hacc₁ σ hσ₁] at hlayerStep
      let ro₁ : MPoint (SideCtx D C X) Msg₁ R₁.params.nl R₁.params.rounds → C :=
        fun p => ro (Sum.inr (Sum.inl p))
      have hch : (fun i : Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) =>
          S.challenges mt ro ⟨1 + i.val, by omega⟩)
          = fun i => ro₁ (msgPoint ctx₁ msgOf₁ out i.val) := by
        funext i
        show ro (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out (1 + i.val)) = _
        rw [hash2_side1 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out i.isLt]
      rw [hch] at hlayerStep
      let hR := layerStepRbr (nl := R₁.params.nl) (w := R₁.params.rounds) (S₁.field σ) (S₁.MD σ)
        (ML₁ σ hσ₁) (hB₁ σ hσ₁) (Fails := ∀ cand, ¬ S₁.Sat σ cand) (fun h => h) (msgOf₁ out)
      obtain ⟨k₁, hd, he⟩ := hR.exists_escape _ (hR.doomed_start hσ₁ _)
        (hR.accepts_undoomed _ hlayerStep)
      have hsh := shed_at_msgPoint (S₁.field σ) (S₁.MD σ) (ML₁ σ hσ₁) ctx₁ msgOf₁ out ro₁ k₁ hd he
      refine ⟨⟨1 + k₁.val, by omega⟩, ?_⟩
      rw [S.grinding_ctx_point mt pts2 Bad beta hbad ro _,
        S.grinding_point mt pts2 Bad beta hbad ro _]
      show Bad' (S.context mt ro) (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out (1 + k₁.val))
        (pget dflt (pts2.chal ro (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out (1 + k₁.val))))
        (ro (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out (1 + k₁.val)))
      rw [hash2_side1 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out k₁.isLt, hBad']
      simp only [Sum.elim_inr, Sum.elim_inl]
      refine ⟨hσ₁, ?_⟩
      have hpre : (fun j : Fin (msgPoint (nl := R₁.params.nl) (w := R₁.params.rounds) ctx₁ msgOf₁
            out k₁.val).role.slot =>
          pget dflt (pts2.chal ro (Sum.inr (Sum.inl (msgPoint ctx₁ msgOf₁ out k₁.val))))
            (1 + j.val))
          = mpoints.chal ro₁ (msgPoint ctx₁ msgOf₁ out k₁.val) := by
        funext j
        rw [pget_side1]
        rfl
      rw [hpre]
      exact hsh
    by_cases hσ₂ : ∀ cand, ¬ S₂.Sat σ cand
    · -- side 2 has no good witness
      have hlayerStep := hright₂ mt ro hσ₂ hacc.2.1 hex₂
      rw [← hacc₂ σ hσ₂] at hlayerStep
      set ctx₂ := (ctx₁, fun i : Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) =>
        msgOf₁ out i.val) with hctx₂
      let ro₂ : MPoint (SideCtx D C X × (Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds)
          → Msg₁)) Msg₂ R₂.params.nl R₂.params.rounds → C :=
        fun p => ro (Sum.inr (Sum.inr p))
      have hch : (fun i : Fin (Rounds.Role.length R₂.params.nl R₂.params.rounds) =>
          S.challenges mt ro
            ⟨1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + i.val, by omega⟩)
          = fun i => ro₂ (msgPoint ctx₂ msgOf₂ out i.val) := by
        funext i
        show ro (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out
          (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + i.val)) = _
        rw [hash2_side2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out i.val]
      rw [hch] at hlayerStep
      let hR := layerStepRbr (nl := R₂.params.nl) (w := R₂.params.rounds) (S₂.field σ) (S₂.MD σ)
        (ML₂ σ hσ₂) (hB₂ σ hσ₂) (Fails := ∀ cand, ¬ S₂.Sat σ cand) (fun h => h) (msgOf₂ out)
      obtain ⟨k₂, hd, he⟩ := hR.exists_escape _ (hR.doomed_start hσ₂ _)
        (hR.accepts_undoomed _ hlayerStep)
      have hsh := shed_at_msgPoint (S₂.field σ) (S₂.MD σ) (ML₂ σ hσ₂) ctx₂ msgOf₂ out ro₂ k₂ hd he
      refine ⟨⟨1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + k₂.val, by omega⟩, ?_⟩
      rw [S.grinding_ctx_point mt pts2 Bad beta hbad ro _,
        S.grinding_point mt pts2 Bad beta hbad ro _]
      show Bad' (S.context mt ro) (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out
          (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + k₂.val))
        (pget dflt (pts2.chal ro (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out
          (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + k₂.val))))
        (ro (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out
          (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + k₂.val)))
      rw [hash2_side2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out k₂.val, hBad']
      simp only [Sum.elim_inr]
      refine ⟨hσ₂, ?_⟩
      have hpre : (fun j : Fin (msgPoint (nl := R₂.params.nl) (w := R₂.params.rounds) ctx₂ msgOf₂
            out k₂.val).role.slot =>
          pget dflt (pts2.chal ro (Sum.inr (Sum.inr (msgPoint ctx₂ msgOf₂ out k₂.val))))
            (1 + L₁ + j.val))
          = mpoints.chal ro₂ (msgPoint ctx₂ msgOf₂ out k₂.val) := by
        funext j
        rw [pget_side2]
        rfl
      rw [hpre]
      exact hsh
    -- both sides have good witnesses, which disagree: the MAC rows kill the multiplier
    push Not at hσ₁ hσ₂
    obtain ⟨cand₁, hs₁⟩ := hσ₁
    obtain ⟨cand₂, hs₂⟩ := hσ₂
    have hne : common₁ ((S₁.field σ).wOf cand₁) ≠ common₂ ((S₂.field σ).wOf cand₂) :=
      fun heq => hcomp ⟨_, _, ⟨cand₁, hs₁, rfl⟩, ⟨cand₂, hs₂, rfl⟩, heq⟩
    have hm₁ := hrow₁ mt ro _ hacc.1 ⟨cand₁, hs₁, rfl⟩
    have hm₂ := hrow₂ mt ro _ hacc.2.1 ⟨cand₂, hs₂, rfl⟩
    have hzero := macTag_collision hne (hm₁.trans hm₂.symm)
    refine ⟨⟨0, by omega⟩, ?_⟩
    rw [S.grinding_ctx_point mt pts2 Bad beta hbad ro _,
      S.grinding_point mt pts2 Bad beta hbad ro _]
    show Bad' (S.context mt ro) (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out 0)
      (pget dflt (pts2.chal ro (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out 0)))
      (ro (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out 0))
    have hav : ro (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out 0) = avOf out := hacc.2.2
    rw [hav, hash2_zero rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out, hBad']
    simp only [Sum.elim_inl]
    exact hzero
  -- the generic two-root count
  have hcheck₁ : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec₁ n₁ (claimOf₁ out).I (claimOf₁ out).a (claimOf₁ out).pf (2 * n₁)
          fun _ => default).run H).2,
        qa ∈ ((check2 codec₁ claimOf₁ codec₂ claimOf₂ out).run H).2 := by
    intro H out qa hqa
    rw [check2, Tree.run_bind]
    exact List.mem_append_left _ (NizkAdaptive.lfCheck_trace codec₁ claimOf₁ H out qa hqa)
  have hcheck₂ : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec₂ n₂ (claimOf₂ out).I (claimOf₂ out).a (claimOf₂ out).pf (2 * n₂)
          fun _ => default).run H).2,
        qa ∈ ((check2 codec₁ claimOf₁ codec₂ claimOf₂ out).run H).2 := by
    intro H out qa hqa
    rw [check2, Tree.run_bind]
    exact List.mem_append_right _ (NizkAdaptive.lfCheck_trace codec₂ claimOf₂ H out qa hqa)
  have hroom := Row.fuel_room h₁
  have hgen := S.ratio_le_two codec₁ dec₁ codec₂ dec₂ (check2 codec₁ claimOf₁ codec₂ claimOf₂)
    Prod.fst Prod.snd claimOf₁ claimOf₂ hcheck₁ hcheck₂ pts2 Bad beta hbad βmax hmax slotBeta hslot
    (by omega) (by omega) htape (by omega)
    (fun mt ro => JointAccepts K₁ codec₁ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁
        claimOf₁ statementOf₁ responseOf₁ challengeOf₁ queryOf₁ mt ro ∧
      JointAccepts K₂ codec₂ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂
        statementOf₂ responseOf₂ challengeOf₂ queryOf₂ mt ro ∧
      S.challenges mt ro ⟨0, by omega⟩ = avOf (S.proof mt ro))
    (fun mt ro => ¬ ∃ a₁ a₂,
      S₁.Good (S.context mt ro, avOf (S.proof mt ro), pubOf (S.proof mt ro)) a₁ ∧
      S₂.Good (S.context mt ro, avOf (S.proof mt ro), pubOf (S.proof mt ro)) a₂ ∧
      common₁ a₁ = common₂ a₂)
    (fun mt ro h => h.1.2.1) (fun mt ro h => h.2.1.2.1) hchain
  refine le_trans (div_le_div_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card ?_))
    (by positivity)) (le_trans hgen ?_)
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    exact ⟨⟨hω.1, hω.2.1, hω.2.2.1⟩, hω.2.2.2⟩
  -- the densities
  rw [hsum]
  have hc : (0 : ℚ) < (Fintype.card C : ℚ) := by exact_mod_cast hCpos
  have hDpos : (0 : ℚ) < (Fintype.card D : ℚ) := by exact_mod_cast Fintype.card_pos
  have hseq₁ := budgets_le_bound R₁ hCpos hFpos₁ (cardCand := Fintype.card Cand₁) hD₁
  have hseq₂ := budgets_le_bound R₂ hCpos hFpos₂ (cardCand := Fintype.card Cand₂) hD₂
  have hb₁ : R₁.bound = R₁.params.nizkBound (Fintype.card Cand₁) R₁.commitFuel R₁.tape := by
    rw [hcand₁]; rfl
  have hb₂ : R₂.bound = R₂.params.nizkBound (Fintype.card Cand₂) R₂.commitFuel R₂.tape := by
    rw [hcand₂]; rfl
  have hmacq := Lfzk.TwoFieldV1.mac_term_le (C := C) hmac
  set M := max (max R₁.fsCoefficient R₂.fsCoefficient) (1 / (Fintype.card Fmac : ℚ)) with hM
  have hβ : (βmax : ℚ) / (Fintype.card C : ℚ) ≤ M := by
    rw [div_le_iff₀ hc, hβmax]
    push_cast
    have hk : (kmac : ℚ) ≤ M * Fintype.card C := by
      have h := (div_le_iff₀ hc).mp hmacq
      have hle : 1 / (Fintype.card Fmac : ℚ) ≤ M := le_max_right _ _
      nlinarith
    have h1 : (Fintype.card Cand₁ : ℚ) * (NizkGrinding.maxBudget bp₁ bp₁ bi₁ bl₁ bq₁ : ℚ)
        ≤ M * Fintype.card C := by
      have hmd := maxBudget_le_density R₁ hCpos hFpos₁
      have hκ : R₁.fsCoefficient = (Fintype.card Cand₁ : ℚ) * R₁.maxDensity := by
        unfold Row.fsCoefficient; rw [hcand₁]
      have hle : R₁.fsCoefficient ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
      calc (Fintype.card Cand₁ : ℚ) * (NizkGrinding.maxBudget bp₁ bp₁ bi₁ bl₁ bq₁ : ℚ)
          ≤ (Fintype.card Cand₁ : ℚ) * ((Fintype.card C : ℚ) * R₁.maxDensity) :=
            mul_le_mul_of_nonneg_left hmd (by positivity)
        _ = R₁.fsCoefficient * Fintype.card C := by rw [hκ]; ring
        _ ≤ M * Fintype.card C := mul_le_mul_of_nonneg_right hle hc.le
    have h2 : (Fintype.card Cand₂ : ℚ) * (NizkGrinding.maxBudget bp₂ bp₂ bi₂ bl₂ bq₂ : ℚ)
        ≤ M * Fintype.card C := by
      have hmd := maxBudget_le_density R₂ hCpos hFpos₂
      have hκ : R₂.fsCoefficient = (Fintype.card Cand₂ : ℚ) * R₂.maxDensity := by
        unfold Row.fsCoefficient; rw [hcand₂]
      have hle : R₂.fsCoefficient ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
      calc (Fintype.card Cand₂ : ℚ) * (NizkGrinding.maxBudget bp₂ bp₂ bi₂ bl₂ bq₂ : ℚ)
          ≤ (Fintype.card Cand₂ : ℚ) * ((Fintype.card C : ℚ) * R₂.maxDensity) :=
            mul_le_mul_of_nonneg_left hmd (by positivity)
        _ = R₂.fsCoefficient * Fintype.card C := by rw [hκ]; ring
        _ ≤ M * Fintype.card C := mul_le_mul_of_nonneg_right hle hc.le
    exact max_le hk (max_le h1 h2)
  have hDq : (Fintype.card D : ℚ) = 2 ^ R₁.params.digestBits := by rw [hD₁]; push_cast; rfl
  have hnum₁ := NizkAdaptive.adaptiveNumerator_le (Lfs := len2 R₁ R₂ + N) htA₁ htape
  have hnum₂ := NizkAdaptive.adaptiveNumerator_le (Lfs := len2 R₁ R₂ + N) htA₂ (htape₂ ▸ htape)
  have hnumq₁ : (AdaptiveCommit.adaptiveNumerator (2 * n₂ + 2 * n₁) tA (len2 R₁ R₂ + N) : ℚ)
        / (Fintype.card D : ℚ)
      ≤ (merkleNumerator R₁.commitFuel R₁.tape : ℚ) / (Fintype.card D : ℚ)
        + ((R₁.tape * (len2 R₁ R₂ + N) : ℕ) : ℚ) / 2 ^ R₁.params.digestBits := by
    rw [← hDq, ← add_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hnum₁) hDpos.le
  have hnumq₂ : (AdaptiveCommit.adaptiveNumerator (2 * n₂ + 2 * n₁) tA (len2 R₁ R₂ + N) : ℚ)
        / (Fintype.card D : ℚ)
      ≤ (merkleNumerator R₂.commitFuel R₂.tape : ℚ) / (Fintype.card D : ℚ)
        + ((R₁.tape * (len2 R₁ R₂ + N) : ℕ) : ℚ) / 2 ^ R₁.params.digestBits := by
    rw [← hDq, ← add_div, htape₂]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hnum₂) hDpos.le
  have hsplit : ((N * βmax + (kmac + Fintype.card Cand₁ * (R₁.params.nl * bp₁
          + (∑ i ∈ Finset.range R₁.params.nl, R₁.params.rounds i) * bp₁ + bi₁ + bl₁ + bq₁)
        + Fintype.card Cand₂ * (R₂.params.nl * bp₂
          + (∑ i ∈ Finset.range R₂.params.nl, R₂.params.rounds i) * bp₂ + bi₂ + bl₂ + bq₂)) : ℕ)
          : ℚ) / (Fintype.card C : ℚ)
      = N * ((βmax : ℚ) / (Fintype.card C : ℚ)) + (kmac : ℚ) / (Fintype.card C : ℚ)
        + ((Fintype.card Cand₁ * (R₁.params.nl * bp₁
          + (∑ i ∈ Finset.range R₁.params.nl, R₁.params.rounds i) * bp₁ + bi₁ + bl₁ + bq₁) : ℕ)
            : ℚ) / (Fintype.card C : ℚ)
        + ((Fintype.card Cand₂ * (R₂.params.nl * bp₂
          + (∑ i ∈ Finset.range R₂.params.nl, R₂.params.rounds i) * bp₂ + bi₂ + bl₂ + bq₂) : ℕ)
            : ℚ) / (Fintype.card C : ℚ) := by
    push_cast
    ring
  rw [hsplit, hb₁, hb₂]
  have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg N
  have := mul_le_mul_of_nonneg_left hβ hN
  linarith

end Compose

/-! ## 3. At the compiled Longfellow verifiers -/

section CompiledTwoField

open Lfzk.CompiledLongfellow (Code Col guarded v1K Matches stepsOf_withMsgs_eq layerStepAccepts_iff)
open Lfzk.CompiledLongfellowAdaptive (CompiledSide Sig statementOfAt challengeOfAt queryOfAt
  responseOfAt accepts_guarded mem_acceptingR_of_accepts slice1 slice2)

variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {D : Type} [Fintype D] [DecidableEq D] [Inhabited D]
variable {Enc X Out : Type} [DecidableEq Enc]

/-- **The side context on `(mt, ro)`**: the commitment context of the pair of roots, and the
public inputs the proof carries (the MAC-key share and the public data). -/
def sideCtx {Pt : Type} [DecidableEq Pt] {tA N Lsch TM : ℕ}
    (S : TotalOracleCommit.Setup Enc D Pt C Out (D × D) tA N Lsch) (avOf : Out → C)
    (pubOf : Out → X) (mt : Fin TM → D) (ro : Pt → C) : Sig D C X Enc :=
  (S.context mt ro, avOf (S.proof mt ro), pubOf (S.proof mt ro))

namespace CompiledSide

variable {R : Row} {hR : R.Valid} {hr : 0 < R.params.row.openings}
variable {Cand F Equations Witness Msg : Type} [Fintype Cand] [Field F] [Fintype F] [DecidableEq F]
  [SumcheckInterp F] [Fintype Equations] [DecidableEq Equations] {nc nv logw logc : ℕ}
variable {Salt : Type} [Inhabited Salt]
variable {codec : Codec Salt (Col F R.params.nw R.params.nq) D Enc} {dec : RoleDecoders codec}
  {rootOfKey : D × D → D}
variable (L : CompiledSide R hR hr C Cand F Equations Witness Msg nc nv logw logc X dec rootOfKey)

/-- The side's statement map: at the side's root and the public inputs the proof carries. -/
def stmtOf {Lsch : ℕ} (rootOf : Out → D) (avOf : Out → C) (pubOf : Out → X) (out : Out)
    (_chals : Fin Lsch → C) :
    LigeroFamily.ConstraintSystem F R.params.nw R.params.nq R.params.q Equations :=
  L.stmt (rootOf out) (avOf out) (pubOf out)

variable {Pt : Type} [DecidableEq Pt] {tA N Lsch fc TM : ℕ}

/-- **The side's compiled verifier on `(mt, ro)`**, at its slice `sl` of the verifier's
challenges. -/
def accepts (S : TotalOracleCommit.Setup Enc D Pt C Out (D × D) tA N Lsch)
    (check : Out → Tree Enc D Unit fc) (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim R.params.row.n Salt (Col F R.params.nw R.params.nq) D)
    (avOf : Out → C) (pubOf : Out → X)
    (sl : (Fin Lsch → C) → Fin (Rounds.Role.length R.params.nl R.params.rounds) → C)
    (mt : Fin TM → D) (ro : Pt → C) : Prop :=
  AcceptsAt (v1K (Row.rowValid hR) L.dom (Row.hkrow hR) hr) L.V codec S check rootOf msgOf claimOf
    (stmtOf L rootOf avOf pubOf) L.respOf sl mt ro

omit [DecidableEq C] [Nonempty C] [Fintype D] in
/-- The side's compiled verifier is `guarded (v1K …)`'s joint acceptance at the side's maps. -/
theorem accepts_iff_joint (S : TotalOracleCommit.Setup Enc D Pt C Out (D × D) tA N Lsch)
    (check : Out → Tree Enc D Unit fc) (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim R.params.row.n Salt (Col F R.params.nw R.params.nq) D)
    (avOf : Out → C) (pubOf : Out → X)
    (sl : (Fin Lsch → C) → Fin (Rounds.Role.length R.params.nl R.params.rounds) → C)
    (mt : Fin TM → D) (ro : Pt → C) :
    accepts L S check rootOf msgOf claimOf avOf pubOf sl mt ro ↔
      JointAccepts (guarded (v1K (Row.rowValid hR) L.dom (Row.hkrow hR) hr)) codec S check
        rootOf claimOf (statementOfAt L.V msgOf (stmtOf L rootOf avOf pubOf) sl)
        (responseOfAt R.params.nl R.params.rounds L.respOf msgOf) (challengeOfAt L.V sl)
        (queryOfAt L.V sl) mt ro :=
  acceptsAt_iff_joint _ _ _ _ _ _ _ _ _ _ _ _ _

omit [DecidableEq C] [Nonempty C] [Fintype D] in
/-- **`hright`, proved for one side**: from the guarded joint acceptance at the side's maps and the
cut-trace extraction at the side's root, the side's LayerStep accepts at its slice of the verifier's
challenges, with the response-reading test of the extracted instance. -/
theorem hright [DecidableEq Msg] [Inhabited Msg]
    (S : TotalOracleCommit.Setup Enc D Pt C Out (D × D) tA N Lsch)
    (check : Out → Tree Enc D Unit fc)
    (rootOf : Out → D) (hroot : ∀ out, rootOfKey (S.keyOut out) = rootOf out)
    (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim R.params.row.n Salt (Col F R.params.nw R.params.nq) D)
    (avOf : Out → C) (pubOf : Out → X)
    (sl : (Fin Lsch → C) → Fin (Rounds.Role.length R.params.nl R.params.rounds) → C)
    (mt : Fin TM → D) (ro : Pt → C)
    (hacc : JointAccepts (guarded (v1K (Row.rowValid hR) L.dom (Row.hkrow hR) hr)) codec S check
      rootOf claimOf (statementOfAt L.V msgOf (stmtOf L rootOf avOf pubOf) sl)
      (responseOfAt R.params.nl R.params.rounds L.respOf msgOf) (challengeOfAt L.V sl)
      (queryOfAt L.V sl) mt ro)
    (hexp : S.Explains dec rootOfKey claimOf mt ro) :
    RbrSplit.LayerStepAccepts
      (RbrSplit.stepsOf (nl := R.params.nl) (w := R.params.rounds)
        (withMsgs (L.field (sideCtx S avOf pubOf mt ro)) (L.MD (sideCtx S avOf pubOf mt ro))
          (msgOf (S.proof mt ro)))
        (fun m pref => L.toSide.accR (sideCtx S avOf pubOf mt ro) m pref
          (msgOf (S.proof mt ro) m)))
      (sl (S.challenges mt ro)) := by
  unfold JointAccepts statementOfAt at hacc
  rw [accepts_guarded, decide_eq_true_iff] at hacc
  obtain ⟨hfield, hv1⟩ := hacc
  obtain ⟨e, hext, hagree, -⟩ := hexp
  rw [stepsOf_withMsgs_eq (L.hmatch _), layerStepAccepts_iff]
  refine ⟨hfield, ?_⟩
  unfold stmtOf at hv1
  rw [← hroot (S.proof mt ro)] at hv1
  exact mem_acceptingR_of_accepts (Row.rowValid hR) L.dom (Row.hkrow hR) hr dec _ _ _ _ _ _ _ _
    e hext hagree hv1

end CompiledSide

variable {Fmac : Type} [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {nblk : ℕ}
variable [Fintype X]
variable {Cand₁ F₁ Equations₁ Witness₁ Msg₁ : Type} [Fintype Cand₁] [Nonempty Cand₁] [Field F₁]
  [Fintype F₁] [DecidableEq F₁] [SumcheckInterp F₁] [Fintype Equations₁] [DecidableEq Equations₁]
  [DecidableEq Msg₁] [Inhabited Msg₁] [Fintype Msg₁] {nc₁ nv₁ logw₁ logc₁ : ℕ}
variable {Cand₂ F₂ Equations₂ Witness₂ Msg₂ : Type} [Fintype Cand₂] [Nonempty Cand₂] [Field F₂]
  [Fintype F₂] [DecidableEq F₂] [SumcheckInterp F₂] [Fintype Equations₂] [DecidableEq Equations₂]
  [DecidableEq Msg₂] [Inhabited Msg₂] [Fintype Msg₂] {nc₂ nv₂ logw₂ logc₂ : ℕ}
variable {Salt₁ Salt₂ : Type} [Inhabited Salt₁] [Inhabited Salt₂]

/--
**Two-field Longfellow at the compiled verifiers, against one re-committing prefix-only Fiat–Shamir
prover with a hashed MAC key.**

`twofield_adaptive_ratio_le` at two compiled sides, `hlig` and `hright` discharged.  The verifier
accepts when both sides' compiled verifiers accept (`CompiledSide.accepts`: field rounds, Merkle
opening and V1 policy, on the statement at the side's root and the public inputs the proof carries)
and the proof's MAC-key share is the oracle's answer at the key point.

```text
Pr[ both accept ∧ av = ro(key point) ∧ no two good witnesses agree on the common value ]
    ≤  R₁.bound + R₂.bound + 1/|Fmac|  +  N · max(κ₁, κ₂, 1/|Fmac|)
       +  2 · R₁.tape · (1 + L₁ + L₂ + N) / 2^digestBits
```

`N` counts deployed hash queries over all three roles.  **Every premise:** per side a
`CompiledSide`, `|Cand|`, `|D|`, the MAC data `aP`, `decode`, `hbal`, `hmac`, the MAC rows
`hrow₁`, `hrow₂` (a good witness of an accepting side satisfies the MAC at `aP κ + decode av` and the
proof's tag), and the fuels.
-/
theorem twofield_adaptive_compiled_ratio_le {R₁ R₂ : Row} (h₁ : R₁.Valid) (h₂ : R₂.Valid)
    (hr₁ : 0 < R₁.params.row.openings) (hr₂ : 0 < R₂.params.row.openings) {tA N : ℕ}
    {codec₁ : Codec Salt₁ (Col F₁ R₁.params.nw R₁.params.nq) D Enc} {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ R₂.params.nw R₂.params.nq) D Enc} {dec₂ : RoleDecoders codec₂}
    (L₁ : CompiledSide R₁ h₁ hr₁ C Cand₁ F₁ Equations₁ Witness₁ Msg₁ nc₁ nv₁ logw₁ logc₁ X dec₁
      Prod.fst)
    (L₂ : CompiledSide R₂ h₂ hr₂ C Cand₂ F₂ Equations₂ Witness₂ Msg₂ nc₂ nv₂ logw₂ logc₂ X dec₂
      Prod.snd)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds
      R₂.params.rounds) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim R₁.params.row.n Salt₁ (Col F₁ R₁.params.nw R₁.params.nq) D)
    (claimOf₂ : Out → OpeningClaim R₂.params.row.n Salt₂ (Col F₂ R₂.params.nw R₂.params.nq) D)
    (hcand₁ : Fintype.card Cand₁ = R₁.cardCand) (hcand₂ : Fintype.card Cand₂ = R₂.cardCand)
    (hD₁ : Fintype.card D = 2 ^ R₁.params.digestBits)
    (hD₂ : Fintype.card D = 2 ^ R₂.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : Witness₁ → Fin nblk → Fmac) (common₂ : Witness₂ → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin R₁.tape → D)
        (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C)
        (a : Witness₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      CompiledSide.accepts L₁ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁
        avOf pubOf (slice1 R₁ R₂) mt ro →
      L₁.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin R₁.tape → D)
        (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C)
        (a : Witness₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      CompiledSide.accepts L₂ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂
        avOf pubOf (slice2 R₁ R₂) mt ro →
      L₂.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₂ a) = tagOf (S.proof mt ro))
    (htA₁ : tA ≤ R₁.commitFuel) (htA₂ : tA ≤ R₂.commitFuel)
    (htape : 2 * R₂.params.row.n + 2 * R₁.params.row.n + tA ≤ R₁.tape)
    (htape₂ : R₁.tape = R₂.tape) :
    ((univ.filter fun ω : (Fin R₁.tape → D) ×
          (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C) =>
        CompiledSide.accepts L₁ (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 R₁ R₂) ω.1 ω.2 ∧
          CompiledSide.accepts L₂ (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 R₁ R₂) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            L₁.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf pubOf
              ω.1 ω.2) a₁ ∧
            L₂.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf pubOf
              ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ R₁.tape * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds))
      ≤ R₁.bound + R₂.bound + 1 / (Fintype.card Fmac : ℚ)
        + N * max (max R₁.fsCoefficient R₂.fsCoefficient) (1 / (Fintype.card Fmac : ℚ))
        + 2 * (((R₁.tape * (len2 R₁ R₂ + N) : ℕ) : ℚ) / 2 ^ R₁.params.digestBits) := by
  have hroot₁ : ∀ out, Prod.fst ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).keyOut out)
      = rootOf₁ out := fun _ => rfl
  have hroot₂ : ∀ out, Prod.snd ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).keyOut out)
      = rootOf₂ out := fun _ => rfl
  refine le_trans (le_of_eq ?_)
    (twofield_adaptive_ratio_le h₁ dec₁ dec₂
      (guarded (v1K (Row.rowValid h₁) L₁.dom (Row.hkrow h₁) hr₁))
      (guarded (v1K (Row.rowValid h₂) L₂.dom (Row.hkrow h₂) hr₂))
      body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂
      (statementOfAt L₁.V msgOf₁ (CompiledSide.stmtOf L₁ rootOf₁ avOf pubOf) (slice1 R₁ R₂))
      (responseOfAt R₁.params.nl R₁.params.rounds L₁.respOf msgOf₁)
      (challengeOfAt L₁.V (slice1 R₁ R₂)) (queryOfAt L₁.V (slice1 R₁ R₂))
      (statementOfAt L₂.V msgOf₂ (CompiledSide.stmtOf L₂ rootOf₂ avOf pubOf) (slice2 R₁ R₂))
      (responseOfAt R₂.params.nl R₂.params.rounds L₂.respOf msgOf₂)
      (challengeOfAt L₂.V (slice2 R₁ R₂)) (queryOfAt L₂.V (slice2 R₁ R₂))
      L₁.toSide L₂.toSide L₁.hF L₂.hF hcand₁ hcand₂ hD₁ hD₂ aP decode kmac hbal hmac keyB tagOf
      common₁ common₂
      (fun mt ro _ hacc hexp => CompiledSide.hright L₁ _ _ rootOf₁ hroot₁ msgOf₁ claimOf₁ avOf
        pubOf (slice1 R₁ R₂) mt ro hacc hexp)
      (fun mt ro _ hacc hexp => CompiledSide.hright L₂ _ _ rootOf₂ hroot₂ msgOf₂ claimOf₂ avOf
        pubOf (slice2 R₁ R₂) mt ro hacc hexp)
      (fun mt ro a hacc hgood => hrow₁ mt ro a
        ((CompiledSide.accepts_iff_joint L₁ _ _ rootOf₁ msgOf₁ claimOf₁ avOf pubOf (slice1 R₁ R₂)
          mt ro).mpr hacc) hgood)
      (fun mt ro a hacc hgood => hrow₂ mt ro a
        ((CompiledSide.accepts_iff_joint L₂ _ _ rootOf₂ msgOf₂ claimOf₂ avOf pubOf (slice2 R₁ R₂)
          mt ro).mpr hacc) hgood)
      htA₁ htA₂ htape htape₂)
  congr 3
  refine Finset.filter_congr fun ω _ => ?_
  rw [CompiledSide.accepts_iff_joint, CompiledSide.accepts_iff_joint]
  exact Iff.rfl

end CompiledTwoField

/-! ## 4. The deployed pair, hash side first -/

/-- **The two-field right-hand side is symmetric in the two rows** (at a shared tape and digest), so a
pair certified ECDSA-first instantiates the hash-first transcript. -/
theorem twofield_rhs_swap (R₁ R₂ : Row) (m : ℚ) (N : ℕ) (ht : R₁.tape = R₂.tape)
    (hd : R₁.params.digestBits = R₂.params.digestBits) :
    R₁.bound + R₂.bound + m + N * max (max R₁.fsCoefficient R₂.fsCoefficient) m
        + 2 * (((R₁.tape * (len2 R₁ R₂ + N) : ℕ) : ℚ) / 2 ^ R₁.params.digestBits)
      = R₂.bound + R₁.bound + m + N * max (max R₂.fsCoefficient R₁.fsCoefficient) m
        + 2 * (((R₂.tape * (len2 R₂ R₁ + N) : ℕ) : ℚ) / 2 ^ R₂.params.digestBits) := by
  have hl : len2 R₁ R₂ = len2 R₂ R₁ := by unfold len2; omega
  rw [max_comm R₁.fsCoefficient, ht, hd, hl]
  ring

section Headline

open Lfzk.CompiledLongfellow (Col)
open Lfzk.CompiledLongfellowAdaptive (CompiledSide slice1 slice2 p256sha_ecdsa_openings_pos
  p256sha_sha_openings_pos p256sha_adaptive_rhs_le)
open Lfzk.TwoFieldV1Rows

variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {D : Type} [Fintype D] [DecidableEq D] [Inhabited D]
variable {Enc X Out : Type} [DecidableEq Enc] [Fintype X]
variable {Fmac : Type} [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {nblk : ℕ}
variable {Cand₁ F₁ Equations₁ Witness₁ Msg₁ : Type} [Fintype Cand₁] [Nonempty Cand₁] [Field F₁]
  [Fintype F₁] [DecidableEq F₁] [SumcheckInterp F₁] [Fintype Equations₁] [DecidableEq Equations₁]
  [DecidableEq Msg₁] [Inhabited Msg₁] [Fintype Msg₁] {nc₁ nv₁ logw₁ logc₁ : ℕ}
variable {Cand₂ F₂ Equations₂ Witness₂ Msg₂ : Type} [Fintype Cand₂] [Nonempty Cand₂] [Field F₂]
  [Fintype F₂] [DecidableEq F₂] [SumcheckInterp F₂] [Fintype Equations₂] [DecidableEq Equations₂]
  [DecidableEq Msg₂] [Inhabited Msg₂] [Fintype Msg₂] {nc₂ nv₂ logw₂ logc₂ : ℕ}
variable {Salt₁ Salt₂ : Type} [Inhabited Salt₁] [Inhabited Salt₂]

/--
**Two-field Longfellow at `p256sha`, at the compiled verifiers, with Fiat–Shamir hash inputs as
deployed.**

`twofield_adaptive_compiled_ratio_le` with side 1 the `GF(2^128)` hash component
(`p256sha.sha`) and side 2 the `P-256` signature component (`p256sha.ecdsa`) — the order of the
deployed transcript — composed through the MAC over a field of `2^128` elements, against one
adaptive program making at most `tA ≤ 2^60` Merkle-oracle and `N` deployed hash queries:

```text
Pr [ both compiled verifiers accept ∧ av = ro(key point) ∧ no two good witnesses agree ]
    ≤  2^-114  +  N · 2^-115
```

the numerals of `CompiledLongfellowAdaptive.p256sha_adaptive_compiled_ratio_le` (via
`twofield_rhs_swap`), where `N` counted raw-answer points.
-/
theorem p256sha_adaptive_compiled_ratio_le {tA N : ℕ} (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ p256sha.sha.params.nw p256sha.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ p256sha.ecdsa.params.nw p256sha.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (L₁ : CompiledSide p256sha.sha (TwoFieldRowV1.sha_valid p256sha_valid)
      p256sha_sha_openings_pos C Cand₁ F₁ Equations₁ Witness₁ Msg₁ nc₁ nv₁ logw₁ logc₁ X dec₁
      Prod.fst)
    (L₂ : CompiledSide p256sha.ecdsa (TwoFieldRowV1.ecdsa_valid p256sha_valid)
      p256sha_ecdsa_openings_pos C Cand₂ F₂ Equations₂ Witness₂ Msg₂ nc₂ nv₂ logw₂ logc₂ X dec₂
      Prod.snd)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ p256sha.sha.params.nl
      p256sha.ecdsa.params.nl p256sha.sha.params.rounds p256sha.ecdsa.params.rounds) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim p256sha.sha.params.row.n Salt₁
      (Col F₁ p256sha.sha.params.nw p256sha.sha.params.nq) D)
    (claimOf₂ : Out → OpeningClaim p256sha.ecdsa.params.row.n Salt₂
      (Col F₂ p256sha.ecdsa.params.nw p256sha.ecdsa.params.nq) D)
    (hcand₁ : Fintype.card Cand₁ = p256sha.sha.cardCand)
    (hcand₂ : Fintype.card Cand₂ = p256sha.ecdsa.cardCand)
    (hD : Fintype.card D = 2 ^ p256sha.ecdsa.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : Witness₁ → Fin nblk → Fmac) (common₂ : Witness₂ → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin p256sha.sha.tape → D)
        (ro : Pt2 D C X Msg₁ Msg₂ p256sha.sha.params.nl p256sha.ecdsa.params.nl
          p256sha.sha.params.rounds p256sha.ecdsa.params.rounds → C) (a : Witness₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      CompiledSide.accepts L₁ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁
        avOf pubOf (slice1 p256sha.sha p256sha.ecdsa) mt ro →
      L₁.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin p256sha.sha.tape → D)
        (ro : Pt2 D C X Msg₁ Msg₂ p256sha.sha.params.nl p256sha.ecdsa.params.nl
          p256sha.sha.params.rounds p256sha.ecdsa.params.rounds → C) (a : Witness₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      CompiledSide.accepts L₂ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂
        avOf pubOf (slice2 p256sha.sha p256sha.ecdsa) mt ro →
      L₂.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₂ a) = tagOf (S.proof mt ro))
    (htA : tA ≤ 2 ^ 60)
    (htape : 2 * p256sha.ecdsa.params.row.n + 2 * p256sha.sha.params.row.n + tA ≤ 2 ^ 62) :
    ((univ.filter fun ω : (Fin p256sha.sha.tape → D) ×
          (Pt2 D C X Msg₁ Msg₂ p256sha.sha.params.nl p256sha.ecdsa.params.nl
            p256sha.sha.params.rounds p256sha.ecdsa.params.rounds → C) =>
        CompiledSide.accepts L₁ (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 p256sha.sha p256sha.ecdsa) ω.1 ω.2 ∧
          CompiledSide.accepts L₂ (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 p256sha.sha p256sha.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            L₁.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf pubOf
              ω.1 ω.2) a₁ ∧
            L₂.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf pubOf
              ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ p256sha.sha.tape * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ p256sha.sha.params.nl p256sha.ecdsa.params.nl
              p256sha.sha.params.rounds p256sha.ecdsa.params.rounds))
      ≤ (1 : ℚ) / 2 ^ 114 + N * ((1 : ℚ) / 2 ^ 115) := by
  have hv := p256sha_valid
  refine le_trans
    (twofield_adaptive_compiled_ratio_le (TwoFieldRowV1.sha_valid hv)
      (TwoFieldRowV1.ecdsa_valid hv) p256sha_sha_openings_pos p256sha_ecdsa_openings_pos
      L₁ L₂ body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂ hcand₁ hcand₂
      (hD.trans (by rw [TwoFieldRowV1.digest_eq hv])) hD aP decode kmac hbal hmac keyB tagOf
      common₁ common₂ hrow₁ hrow₂ htA htA htape (TwoFieldRowV1.tape_eq hv).symm) ?_
  rw [twofield_rhs_swap _ _ _ N (TwoFieldRowV1.tape_eq hv).symm (TwoFieldRowV1.digest_eq hv).symm]
  exact p256sha_adaptive_rhs_le N hFmac

end Headline

end Lfzk.NizkDeployedHashTwoField
