import Lfzk.RbrZkPotentialHybrid
import Lfzk.Fork.JointBound

/-! Schedule-dependent bridge for the forked verifier. Generic local
counts, cut-context lemmas, and numerical certificates are reused. -/

/-!
The first (hash) side's terminal V1 event is bounded directly.  This charge
keeps its field escapes and all charges on the signature side and MAC key.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 300000

namespace Lfzk.Fork.HybridCharge

open Lfzk.NizkZkDeployedHash

open Finset Lfzk.NizkDeployedHash Lfzk.NizkDeployedHashTwoField
  Lfzk.RbrZkFlat
  Lfzk.NizkZkTwoField Lfzk.NizkZk
open scoped Classical

variable {R₁ R₂ : Lfzk.CertifiedV1.Row} {logv₁ logv₂ : ℕ}
variable {C : Type} [Fintype C] [DecidableEq C]
variable {D Enc X : Type} [Fintype X] [DecidableEq X]
variable {F₁ X₁ Q₁ Msg₁ Witness₁ : Type} [Field F₁] [Fintype F₁]
  [DecidableEq F₁] [SumcheckInterp F₁] [Fintype X₁] [DecidableEq X₁]
  [Fintype Q₁] [DecidableEq Q₁] [Inhabited Msg₁]
  {M₁ ninp₁ logw₁ logc₁ : ℕ}
variable {F₂ X₂ Q₂ Msg₂ Witness₂ : Type} [Field F₂] [Fintype F₂]
  [DecidableEq F₂] [SumcheckInterp F₂] [Fintype X₂] [DecidableEq X₂]
  [Fintype Q₂] [DecidableEq Q₂] [Inhabited Msg₂]
  {M₂ ninp₂ logw₂ logc₂ : ℕ}

private abbrev HKey (D Enc : Type) := (D × D) × List (Enc × D)
private abbrev HSig (D C X Enc : Type) := HKey D Enc × C × X

variable (S₁ : ZkSide R₁ logv₁ (HSig D C X Enc) C F₁ X₁ Q₁ Msg₁ Witness₁
  M₁ ninp₁ logw₁ logc₁)
variable (S₂ : ZkSide R₂ logv₂ (HSig D C X Enc) C F₂ X₂ Q₂ Msg₂ Witness₂
  M₂ ninp₂ logw₂ logc₂)

omit [Fintype C] [DecidableEq C] [Fintype X] [DecidableEq X] in
/-- Any nonnegative charge on the merged forked schedule pays if its key,
first side, or second side component pays. -/
theorem twoField_nonneg_component_path
    {Out : Type} (rootOf₁ rootOf₂ : Out → D)
    (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (out : Out)
    (f : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl
      R₁.params.rounds R₂.params.rounds → ℚ)
    (hnonneg : ∀ p, 0 ≤ f p)
    (A B : Prop)
    (hkey : ¬ A → ¬ B → 1 ≤ f (Sum.inl (rootOf₁ out, rootOf₂ out)))
    (hside₁ : A → 1 ≤ ∑ i : Fin
        (Rounds.Role.length R₁.params.nl R₁.params.rounds),
      f (Sum.inr (Sum.inl
        (msgPoint (ctxOf rootOf₁ rootOf₂ avOf pubOf out)
          msgOf₁ out i.val))))
    (hside₂ : B → 1 ≤ ∑ i : Fin
        (Rounds.Role.length R₂.params.nl R₂.params.rounds),
      f (Sum.inr (Sum.inr (msgPoint
        (ctxOf rootOf₁ rootOf₂ avOf pubOf out,
          fun _ : Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) => (default : Msg₁)) msgOf₂ out i.val)))) :
    1 ≤ ∑ i : Fin (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds +
        Rounds.Role.length R₂.params.nl R₂.params.rounds),
      f (Lfzk.Fork.Transcript.hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out i.val) := by
  rw [Lfzk.Fork.Transcript.sum_hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out f]
  have hk : 0 ≤ f (Sum.inl (rootOf₁ out, rootOf₂ out)) := hnonneg _
  have hs₁ : 0 ≤ ∑ i : Fin
      (Rounds.Role.length R₁.params.nl R₁.params.rounds),
      f (Sum.inr (Sum.inl (msgPoint
        (ctxOf rootOf₁ rootOf₂ avOf pubOf out) msgOf₁ out i.val))) :=
    Finset.sum_nonneg fun i _ => hnonneg _
  have hs₂ : 0 ≤ ∑ i : Fin
      (Rounds.Role.length R₂.params.nl R₂.params.rounds),
      f (Sum.inr (Sum.inr (msgPoint
        (ctxOf rootOf₁ rootOf₂ avOf pubOf out,
          fun _ : Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) => (default : Msg₁)) msgOf₂ out i.val))) :=
    Finset.sum_nonneg fun i _ => hnonneg _
  by_cases ha : A
  · linarith [hside₁ ha]
  by_cases hb : B
  · linarith [hside₂ hb]
  linarith [hkey ha hb]

omit [DecidableEq C] [Fintype X] [DecidableEq X] in
/-- The reduced merged charge pays on any path with a hash-side field
escape, a failing signature-side extractor, or a MAC key collision. -/
theorem twoFieldHybridCharge_verifier_path
    (P₁ : ∀ σ, TerminalPotential (S₁.LD σ))
    (P₂ : ∀ σ, TerminalPotential (S₂.LD σ))
    (keyBad : HKey D Enc → C → Prop) (dflt : C)
    {Out : Type} (rootOf₁ rootOf₂ : Out → D)
    (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (out : Out) (cut : List (Enc × D))
    (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl
      R₁.params.rounds R₂.params.rounds → C)
    (hkey : ¬ ZkFails S₁.Sat
        (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out) →
      ¬ ZkFails S₂.Sat
        (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out) →
      keyBad ((rootOf₁ out, rootOf₂ out), cut)
        (ro (Sum.inl (rootOf₁ out, rootOf₂ out))))
    (hside₁ : ZkFails S₁.Sat
        (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out) →
      1 ≤ ∑ i : Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds),
        sideFieldTraceCharge
          (H := S₁.H (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
          (Sat := S₁.Sat (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
          (S₁.LD (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
          (P₁ (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
          (ctxOf rootOf₁ rootOf₂ avOf pubOf out) msgOf₁ out
          (fun p => ro (Sum.inr (Sum.inl p))) i)
    (hside₂ : ZkFails S₂.Sat
        (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out) →
      1 ≤ ∑ i : Fin (Rounds.Role.length R₂.params.nl R₂.params.rounds),
        sideTraceCharge
          (H := S₂.H (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
          (Sat := S₂.Sat (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
          (S₂.LD (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
          (P₂ (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
          (ctxOf rootOf₁ rootOf₂ avOf pubOf out,
            fun _ : Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) => (default : Msg₁)) msgOf₂ out
          (fun p => ro (Sum.inr (Sum.inr p))) i) :
    1 ≤ ∑ i : Fin (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds +
        Rounds.Role.length R₂.params.nl R₂.params.rounds),
      twoFieldHybridCharge S₁ S₂ P₁ P₂ keyBad dflt
        ((rootOf₁ out, rootOf₂ out), cut)
        (Lfzk.Fork.Transcript.hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out i.val)
        (pts2.chal ro
          (Lfzk.Fork.Transcript.hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out i.val))
        (ro (Lfzk.Fork.Transcript.hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out i.val)) := by
  let κ : HKey D Enc := ((rootOf₁ out, rootOf₂ out), cut)
  let σ : HSig D C X Enc := (κ, avOf out, pubOf out)
  let f : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl
      R₁.params.rounds R₂.params.rounds → ℚ :=
    fun p => twoFieldHybridCharge S₁ S₂ P₁ P₂ keyBad dflt κ p
      (pts2.chal ro p) (ro p)
  change 1 ≤ ∑ i : Fin (1 + Rounds.Role.length R₁.params.nl
      R₁.params.rounds + Rounds.Role.length R₂.params.nl R₂.params.rounds),
    f (Lfzk.Fork.Transcript.hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out i.val)
  apply Lfzk.Fork.HybridCharge.twoField_nonneg_component_path rootOf₁ rootOf₂ avOf pubOf
    msgOf₁ msgOf₂ out f
    (fun p => twoFieldHybridCharge_nonneg S₁ S₂ P₁ P₂
      keyBad dflt κ p _ _) (ZkFails S₁.Sat σ) (ZkFails S₂.Sat σ)
  · intro hf₁ hf₂
    have hb := hkey hf₁ hf₂
    simp [f, twoFieldHybridCharge, twoFieldPotentialCharge, κ, hb]
  · intro hf₁
    have hp := hside₁ hf₁
    calc
      1 ≤ ∑ i : Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds),
          sideFieldTraceCharge (H := S₁.H σ) (Sat := S₁.Sat σ)
            (S₁.LD σ) (P₁ σ)
            (ctxOf rootOf₁ rootOf₂ avOf pubOf out) msgOf₁ out
            (fun p => ro (Sum.inr (Sum.inl p))) i := hp
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [sideFieldTraceCharge_eq_point]
        exact (twoFieldHybridCharge_side1_at S₁ S₂ P₁ P₂
          keyBad dflt κ _ ro hf₁).symm
  · intro hf₂
    have hp := hside₂ hf₂
    calc
      1 ≤ ∑ i : Fin (Rounds.Role.length R₂.params.nl R₂.params.rounds),
          sideTraceCharge (H := S₂.H σ) (Sat := S₂.Sat σ)
            (S₂.LD σ) (P₂ σ)
            (ctxOf rootOf₁ rootOf₂ avOf pubOf out,
              fun _ : Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) => (default : Msg₁)) msgOf₂ out
            (fun p => ro (Sum.inr (Sum.inr p))) i := hp
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        exact (twoFieldHybridCharge_side2_at S₁ S₂ P₁ P₂
          keyBad dflt κ _ ro hf₂).symm

omit [DecidableEq C] [Fintype X] [DecidableEq X] in
/-- Accepted signature side plus a hash-side field escape imply payment on
the forked merged path; the hash terminal is outside this charge. -/
theorem twoFieldHybridCharge_accepted_path_of_field
    (P₁ : ∀ σ, TerminalPotential (S₁.LD σ))
    (P₂ : ∀ σ, TerminalPotential (S₂.LD σ))
    (keyBad : HKey D Enc → C → Prop) (dflt : C)
    {Out : Type} (rootOf₁ rootOf₂ : Out → D)
    (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (out : Out) (cut : List (Enc × D))
    (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl
      R₁.params.rounds R₂.params.rounds → C)
    (hkey : ¬ ZkFails S₁.Sat
        (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out) →
      ¬ ZkFails S₂.Sat
        (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out) →
      keyBad ((rootOf₁ out, rootOf₂ out), cut)
        (ro (Sum.inl (rootOf₁ out, rootOf₂ out))))
    (hfield : ZkFails S₁.Sat
        (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out) →
      let tape : Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) → C :=
        fun i => ro (Sum.inr (Sum.inl (msgPoint
          (ctxOf rootOf₁ rootOf₂ avOf pubOf out) msgOf₁ out i.val)))
      fieldPrefixEscape
        (H := S₁.H (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
        (Sat := S₁.Sat (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
        (S₁.LD (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
        (msgOf₁ out)
        (Bcs.trunc tape
          (Rounds.Role.layerBase R₁.params.rounds R₁.params.nl + 1)
          (by dsimp [Rounds.Role.length]; omega)))
    (hacc₂ : Lfzk.RbrZkSplit.ZkLayerStepAccepts .accepted .start
      (Lfzk.RbrZkSplit.steps (nl := R₂.params.nl)
        (w := R₂.params.rounds)
        (S₂.V (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
        (S₂.LD (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
        (msgOf₂ out))
      (fun i => ro (Sum.inr (Sum.inr (msgPoint
        (ctxOf rootOf₁ rootOf₂ avOf pubOf out,
          fun _ : Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) => (default : Msg₁)) msgOf₂ out i.val))))) :
    1 ≤ ∑ i : Fin (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds +
        Rounds.Role.length R₂.params.nl R₂.params.rounds),
      twoFieldHybridCharge S₁ S₂ P₁ P₂ keyBad dflt
        ((rootOf₁ out, rootOf₂ out), cut)
        (Lfzk.Fork.Transcript.hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out i.val)
        (pts2.chal ro
          (Lfzk.Fork.Transcript.hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out i.val))
        (ro (Lfzk.Fork.Transcript.hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out i.val)) := by
  apply Lfzk.Fork.HybridCharge.twoFieldHybridCharge_verifier_path S₁ S₂ P₁ P₂ keyBad dflt
    rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out cut ro hkey
  · intro hf
    exact fieldPrefixEscape_sideFieldTrace_pays
      (H := S₁.H (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
      (Sat := S₁.Sat (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
      (S₁.LD (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
      (P₁ (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
      (ctxOf rootOf₁ rootOf₂ avOf pubOf out) msgOf₁ out
      (fun p => ro (Sum.inr (Sum.inl p))) (hfield hf)
  · intro hf
    exact accepted_noSat_sideTrace_pays
      (H := S₂.H (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
      (Sat := S₂.Sat (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
      (S₂.LD (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
      (P₂ (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
      (ctxOf rootOf₁ rootOf₂ avOf pubOf out,
        fun _ : Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) => (default : Msg₁)) msgOf₂ out
      (fun p => ro (Sum.inr (Sum.inr p))) hf hacc₂

end Lfzk.Fork.HybridCharge
