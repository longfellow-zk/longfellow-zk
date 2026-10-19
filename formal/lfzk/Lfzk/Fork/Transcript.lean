import Lfzk.NizkDeployedHashTwoField

/-! Forked schedule in the existing ambient point type. The unused side-1
vector in side-2 contexts is fixed padding. The adversary may query the entire
ambient namespace; no restriction to well-formed fork points is imposed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.Fork.Transcript

open Lfzk.NizkDeployedHashTwoField

open Finset Bcs Bcs.TotalOracleCommit Merkle Merkle.MH Merkle.RandomOracle
  Merkle.RandomOracle.TwoOracleTree RbrLongfellow Lfzk.NizkGrinding Lfzk.NizkDeployedHash
  Lfzk.NizkDeployedHashAdaptive Lfzk.CertifiedV1 Lfzk.Mac
open Lfzk.NizkAdaptiveTwoField (SideCtx Side check2 len2 sum_roleAt)
open scoped Classical

section Transcript

variable {D C X Msg₁ Msg₂ Out : Type} {nl₁ nl₂ : ℕ} {w₁ w₂ : ℕ → ℕ}

variable [Inhabited Msg₁] [Inhabited Msg₂]

/-- **The verifier's round-`k` hash input.**  Round `0` is the key point, rounds `1 + k₁` side 1's,
the rest side 2's (with a fixed padding vector, independent of side 1). -/
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
        fun _ : Fin (Rounds.Role.length nl₁ w₁) => (default : Msg₁))
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
            fun _ : Fin (Rounds.Role.length nl₁ w₁) => (default : Msg₁)) msgOf₂ out k₂)) := by
  unfold hash2
  rw [if_neg (by omega), if_neg (by omega),
    show 1 + Rounds.Role.length nl₁ w₁ + k₂ - 1 - Rounds.Role.length nl₁ w₁ = k₂ by omega]

/-- A sum over the actual forked verifier hash inputs consists of the
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
            fun _ : Fin (Rounds.Role.length nl₁ w₁) => (default : Msg₁))
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

/-- Each forked verifier hash input records its exact round in its point
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

/-- A second-side hash input does not depend on any first-side message.
The shared roots and public inputs are fixed in this comparison. -/
theorem hash2_side2_independent
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ msgOf₁' : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (out : Out) (k : ℕ) :
    hash2 (nl₁ := nl₁) (nl₂ := nl₂) (w₁ := w₁) (w₂ := w₂)
      rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out (1 + Rounds.Role.length nl₁ w₁ + k) =
    hash2 (nl₁ := nl₁) (nl₂ := nl₂) (w₁ := w₁) (w₂ := w₂)
      rootOf₁ rootOf₂ avOf pubOf msgOf₁' msgOf₂ out (1 + Rounds.Role.length nl₁ w₁ + k) := by
  rw [hash2_side2, hash2_side2]

/-- First-side hash inputs likewise do not depend on second-side messages. -/
theorem hash2_side1_independent
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ msgOf₂' : Out → ℕ → Msg₂)
    (out : Out) {k : ℕ} (hk : k < Rounds.Role.length nl₁ w₁) :
    hash2 (nl₁ := nl₁) (nl₂ := nl₂) (w₁ := w₁) (w₂ := w₂)
      rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out (1 + k) =
    hash2 (nl₁ := nl₁) (nl₂ := nl₂) (w₁ := w₁) (w₂ := w₂)
      rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂' out (1 + k) := by
  rw [hash2_side1 _ _ _ _ _ _ _ hk, hash2_side1 _ _ _ _ _ _ _ hk]

end Transcript

end Lfzk.Fork.Transcript
