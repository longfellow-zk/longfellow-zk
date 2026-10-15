import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Abel

-- Ported verbatim from `proofs/ligero/LigeroFamily/ZeroKnowledge/Distribution.lean` (only the import paths are rewritten);
-- `formal/ligero/` must not change, so the module lives under `Lfzk.LigeroZk`.
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Exact finite distributions for LigeroFamily

This is the small self-contained distribution layer needed by the V2 masking
proof.  It is independent of the protocol-specific masking construction.
-/

namespace LigeroFamily

/-- Number of random tapes producing one target value. -/
def viewCount {Randomness View : Type*}
    [Fintype Randomness] [DecidableEq View]
    (view : Randomness → View) (target : View) : ℕ :=
  (Finset.univ.filter fun randomness ↦ view randomness = target).card

/-- Equality of two exact finite output distributions, allowing different
randomness spaces. -/
def SameDistribution
    {R₁ R₂ View : Type*}
    [Fintype R₁] [Fintype R₂] [DecidableEq View]
    (view₁ : R₁ → View) (view₂ : R₂ → View) : Prop :=
  ∀ target, Fintype.card R₂ * viewCount view₁ target =
    Fintype.card R₁ * viewCount view₂ target

/-- Reindexing a finite random tape by an equivalence preserves its exact
output distribution. -/
theorem sameDistribution_of_equiv
    {R₁ R₂ View : Type*}
    [Fintype R₁] [Fintype R₂] [DecidableEq View]
    (equivalence : R₁ ≃ R₂)
    (view₁ : R₁ → View) (view₂ : R₂ → View)
    (hview : ∀ randomness, view₁ randomness = view₂ (equivalence randomness)) :
    SameDistribution view₁ view₂ := by
  classical
  intro target
  have hcard : Fintype.card R₁ = Fintype.card R₂ :=
    Fintype.card_congr equivalence
  have hfiber : viewCount view₁ target = viewCount view₂ target := by
    unfold viewCount
    apply Finset.card_bij (fun randomness _ ↦ equivalence randomness)
    · intro randomness hrandomness
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, by
        rw [← hview randomness]
        exact (Finset.mem_filter.mp hrandomness).2⟩
    · intro first _ second _ hequal
      exact equivalence.injective hequal
    · intro randomness hrandomness
      refine ⟨equivalence.symm randomness, ?_, equivalence.apply_symm_apply _⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, by
        rw [hview, equivalence.apply_symm_apply]
        exact (Finset.mem_filter.mp hrandomness).2⟩
  rw [hcard, hfiber]

/-- Translation by an element in an additive observation's range preserves
its exact output distribution. -/
theorem additive_map_one_time_pad_of_lift
    {Source Target : Type*}
    [AddCommGroup Source] [Fintype Source] [DecidableEq Source]
    [AddCommGroup Target] [DecidableEq Target]
    (observation : Source → Target)
    (observation_add : ∀ first second,
      observation (first + second) = observation first + observation second)
    (observation_neg : ∀ source, observation (-source) = -observation source)
    (secret : Target) (lift : Source) (hlift : observation lift = secret) :
    SameDistribution
      (fun source ↦ secret + observation source) observation := by
  classical
  intro target
  let RealFiber := { source : Source //
    secret + observation source = target }
  let SimFiber := { source : Source // observation source = target }
  let translate : RealFiber ≃ SimFiber :=
    { toFun := fun source ↦ ⟨lift + source.1, by
        rw [observation_add, hlift]
        exact source.2⟩
      invFun := fun source ↦ ⟨source.1 - lift, by
        rw [sub_eq_add_neg, observation_add, observation_neg, hlift]
        simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using source.2⟩
      left_inv := by
        intro source
        apply Subtype.ext
        simp
      right_inv := by
        intro source
        apply Subtype.ext
        simp }
  have hfibers : Fintype.card RealFiber = Fintype.card SimFiber :=
    Fintype.card_congr translate
  unfold viewCount
  rw [show (Finset.univ.filter fun source : Source ↦
      secret + observation source = target).card = Fintype.card RealFiber by
        exact (Fintype.card_subtype fun source : Source ↦
          secret + observation source = target).symm]
  rw [show (Finset.univ.filter fun source : Source ↦
      observation source = target).card = Fintype.card SimFiber by
        exact (Fintype.card_subtype fun source : Source ↦
          observation source = target).symm]
  rw [hfibers]

/-- A surjective additive observation of uniform source randomness is an exact
one-time pad on its target. -/
theorem surjective_additive_map_one_time_pad
    {Source Target : Type*}
    [AddCommGroup Source] [Fintype Source] [DecidableEq Source]
    [AddCommGroup Target] [DecidableEq Target]
    (observation : Source → Target)
    (observation_add : ∀ first second,
      observation (first + second) = observation first + observation second)
    (observation_neg : ∀ source, observation (-source) = -observation source)
    (hsurjective : Function.Surjective observation)
    (secret : Target) :
    SameDistribution
      (fun source ↦ secret + observation source) observation := by
  obtain ⟨lift, hlift⟩ := hsurjective secret
  exact additive_map_one_time_pad_of_lift observation observation_add
    observation_neg secret lift hlift

end LigeroFamily
