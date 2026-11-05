import LfzkV2.Native.Soundness
import LfzkV2.Budgets

/-!
# Native frontend challenge budget

The native reconstruction produces the existing `ChallengeTest` values, so
their finite-field root bounds are shared. Constants and linear terms introduce
no extra challenge slots or degree. This does not identify Rust's byte transcript
with a random oracle; that remains a separate composition obligation.
-/

namespace LfzkV2.Native

open SumcheckV2 Classical

variable {F Pad Slot : Type} [Field F]

noncomputable def assertionIndices {n : ℕ} (residuals : Fin n → F) : Finset (Fin n) :=
  Finset.univ.filter fun i => residuals i ≠ 0 ∧ ∀ j, i < j → residuals j = 0

theorem assertionIndices_card_le {n : ℕ} (residuals : Fin n → F) :
    (assertionIndices residuals).card ≤ min 1 n := by
  apply Nat.le_min.mpr
  constructor
  · apply Finset.card_le_one.mpr
    intro i hi j hj
    obtain ⟨hi, hilast⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨hj, hjlast⟩ := (Finset.mem_filter.mp hj).2
    rcases lt_trichotomy i j with hij | hij | hij
    · exact (hj (hilast j hij)).elim
    · exact hij
    · exact (hi (hjlast i hij)).elim
  · exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_fin _)

noncomputable def assertionTests {n : ℕ}
    (incoming claim : F) (beta residuals : Fin n → F) : Tests F :=
  (assertionIndices residuals).toList.map fun i =>
    (.linear (assertionOffset incoming claim beta residuals i) (residuals i), beta i)

theorem assertionTests_bad {n : ℕ} (incoming claim : F) (beta residuals : Fin n → F)
    (hbad : AssertionBad incoming claim beta residuals) :
    (assertionTests incoming claim beta residuals).Bad := by
  obtain ⟨i, hlast, hi⟩ := hbad
  refine ⟨_, List.mem_map.mpr ⟨i, ?_, rfl⟩, hi⟩
  exact Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi.1, hlast⟩)

theorem assertionTests_budget_le {n : ℕ} (incoming claim : F) (beta residuals : Fin n → F) :
    (assertionTests incoming claim beta residuals).budget ≤ min 1 n := by
  simpa [assertionTests, Tests.budget, ChallengeTest.budget, Function.comp_def] using
    assertionIndices_card_le residuals

noncomputable def layerTests {n : ℕ} (q w : Cube n → F) (point : Fin n → F)
    (t : LfzkV2.LayerTranscript Pad Slot F) (pads : Pad → F) (claim K : F) : Tests F :=
  roundTests (claim - K) (truePolys q w point) (t.clearRounds pads) (List.ofFn point) ++
    [(.combine ⟨evaluate w point, evaluate q point, t.clearA pads, t.clearB pads⟩, t.alpha)]

theorem layerTests_bad {n : ℕ} (q w : Cube n → F) (point : Fin n → F)
    (t : LfzkV2.LayerTranscript Pad Slot F) (pads : Pad → F) (claim K : F) :
    (layerTests q w point t pads claim K).Bad ↔
      multi_round_bad_event (claim - K) (truePolys q w point) (t.clearRounds pads)
          (List.ofFn point) ∨
        BadCombineEvent (evaluate w point) (evaluate q point)
          (t.clearA pads) (t.clearB pads) t.alpha := by
  rw [layerTests, Tests.bad_append, roundTests_bad]
  simp [Tests.Bad, ChallengeTest.Bad]

theorem layerTests_valid {n : ℕ} (q w : Cube n → F) (point : Fin n → F)
    (t : LfzkV2.LayerTranscript Pad Slot F) (pads : Pad → F) (claim K : F) :
    (layerTests q w point t pads claim K).Valid := by
  rw [layerTests, Tests.valid_append]
  exact ⟨roundTests_valid _ _ _ _ (truePolys_degree _ _ _), by
    simp [Tests.Valid, ChallengeTest.Valid]⟩

theorem layerTests_budget_le {n : ℕ} (q w : Cube n → F) (point : Fin n → F)
    (t : LfzkV2.LayerTranscript Pad Slot F) (pads : Pad → F) (claim K : F) :
    (layerTests q w point t pads claim K).budget ≤ 2 * n + 1 := by
  rw [layerTests, Tests.budget_append]
  change (roundTests _ _ _ _).budget + 1 ≤ _
  have h := roundTests_budget_le (claim - K) (truePolys q w point)
    (t.clearRounds pads) (List.ofFn point)
  rw [truePolys_length] at h
  omega

namespace Circuit

noncomputable def layerTests : {out input : ℕ} → (circuit : Circuit F out input) →
    circuit.Messages Pad Slot → (Cube input → F) → (Cube out → F) → (Pad → F) → F → Tests F
  | _, _, .input, _, _, _, _, _ => []
  | _, _, .layer _ body rest, m, w, weights, pads, claim =>
      let Q := body.effectiveQuadratic weights m.1.beta
      let L := body.effectiveLinear weights m.1.beta
      let K := body.effectiveConstant weights
      let wires := rest.eval w
      assertionTests (dot weights (body.outputs wires)) claim m.1.beta (body.residuals wires) ++
        Native.layerTests (bindRightAffine Q L wires) wires m.1.point m.1.transcript pads claim K ++
        layerTests rest m.2 w (nextWeights Q (monomialWeights m.1.point) m.1.alpha) pads
          ((body.transcript weights m.1).nextValue pads)

theorem layerTests_bad {out input : ℕ} (circuit : Circuit F out input)
    (m : circuit.Messages Pad Slot) (w : Cube input → F) (weights : Cube out → F)
    (pads : Pad → F) (claim : F) (hbad : circuit.Bad m w weights pads claim) :
    (circuit.layerTests m w weights pads claim).Bad := by
  induction circuit generalizing claim with
  | input => exact hbad.elim
  | layer a body rest ih =>
      rcases m with ⟨ml, mr⟩
      simp only [layerTests, Tests.bad_append, Native.layerTests_bad]
      rcases hbad with hassert | hlayer | hrest
      · exact Or.inl (Or.inl (assertionTests_bad _ _ _ _ hassert))
      · exact Or.inl (Or.inr hlayer)
      · exact Or.inr (ih mr w _ _ hrest)

theorem layerTests_valid {out input : ℕ} (circuit : Circuit F out input)
    (m : circuit.Messages Pad Slot) (w : Cube input → F) (weights : Cube out → F)
    (pads : Pad → F) (claim : F) : (circuit.layerTests m w weights pads claim).Valid := by
  induction circuit generalizing claim with
  | input => simp [layerTests, Tests.Valid]
  | layer a body rest ih =>
      rcases m with ⟨ml, mr⟩
      simp only [layerTests, Tests.valid_append]
      exact ⟨⟨by simp [assertionTests, Tests.Valid, ChallengeTest.Valid],
        Native.layerTests_valid _ _ _ _ _ _ _⟩, ih mr w _ _⟩

def sharpLayerBudget : {out input : ℕ} → Circuit F out input → ℕ
  | _, _, .input => 0
  | _, _, .layer (mid := mid) a _ rest => min 1 a + 2 * mid + 1 + rest.sharpLayerBudget

theorem layerTests_budget_le {out input : ℕ} (circuit : Circuit F out input)
    (m : circuit.Messages Pad Slot) (w : Cube input → F) (weights : Cube out → F)
    (pads : Pad → F) (claim : F) :
    (circuit.layerTests m w weights pads claim).budget ≤ circuit.sharpLayerBudget := by
  induction circuit generalizing claim with
  | input => rfl
  | layer a body rest ih =>
      rcases m with ⟨ml, mr⟩
      simp only [layerTests, Tests.budget_append]
      have ha := assertionTests_budget_le (dot weights (body.outputs (rest.eval w))) claim
        ml.beta (body.residuals (rest.eval w))
      have hl := Native.layerTests_budget_le
        (bindRightAffine (body.effectiveQuadratic weights ml.beta)
          (body.effectiveLinear weights ml.beta) (rest.eval w))
        (rest.eval w) ml.point ml.transcript pads claim (body.effectiveConstant weights)
      have hr := ih mr w
        (nextWeights (body.effectiveQuadratic weights ml.beta) (monomialWeights ml.point) ml.alpha)
        ((body.transcript weights ml).nextValue pads)
      change _ ≤ min 1 a + 2 * _ + 1 + rest.sharpLayerBudget
      omega

noncomputable def tests {out input : ℕ} (circuit : Circuit F out input)
    (m : circuit.Messages Pad Slot) (w : Cube input → F) (point : Fin out → F)
    (pads : Pad → F) : Tests F :=
  outputTests (circuit.eval w) point ++ circuit.layerTests m w (monomialWeights point) pads 0

theorem tests_valid {out input : ℕ} (circuit : Circuit F out input)
    (m : circuit.Messages Pad Slot) (w : Cube input → F) (point : Fin out → F)
    (pads : Pad → F) : (circuit.tests m w point pads).Valid :=
  (Tests.valid_append _ _).mpr ⟨outputTests_valid _ _, circuit.layerTests_valid m w _ pads 0⟩

theorem tests_soundness {out input : ℕ} (circuit : Circuit F out input)
    (m : circuit.Messages Pad Slot) (w : Cube input → F) (point : Fin out → F)
    (pads : Pad → F) (hfalse : ¬ circuit.Satisfies w)
    (haccept : ClearAccepts pads 0 (circuit.proof m (monomialWeights point))
      (dot (circuit.inputWeights m (monomialWeights point)) w)) :
    (circuit.tests m w point pads).Bad := by
  rcases circuit.soundness_reduction m w point pads hfalse haccept with houtput | hlayer
  · exact (Tests.bad_append _ _).mpr (Or.inl ((outputTests_bad _ _).mpr houtput))
  · exact (Tests.bad_append _ _).mpr (Or.inr (circuit.layerTests_bad m w _ pads 0 hlayer))

/-- Backend composition can supply authenticated layer equations and the source
input equation directly, without materializing an unpacked committed vector. -/
theorem constraints_tests_soundness {out input : ℕ} (circuit : Circuit F out input)
    (m : circuit.Messages Pad Slot) (w : Cube input → F) (point : Fin out → F)
    (pads : Pad → F) (cs : Constraints Pad Slot F)
    (hbuild : Native.buildConstraints (circuit.proof m (monomialWeights point)) = some cs)
    (hholds : cs.Holds pads (dot (circuit.inputWeights m (monomialWeights point)) w))
    (hfalse : ¬ circuit.Satisfies w) : (circuit.tests m w point pads).Bad := by
  apply circuit.tests_soundness m w point pads hfalse
  exact (Native.buildConstraints_correct _ _ _).mp ⟨cs, hbuild, hholds⟩

theorem tests_budget_le_sharp {out input : ℕ} (circuit : Circuit F out input)
    (m : circuit.Messages Pad Slot) (w : Cube input → F) (point : Fin out → F)
    (pads : Pad → F) :
    (circuit.tests m w point pads).budget ≤ out + circuit.sharpLayerBudget := by
  rw [tests, Tests.budget_append, outputTests_budget]
  exact Nat.add_le_add_left (circuit.layerTests_budget_le m w _ pads 0) out

end Circuit

end LfzkV2.Native
