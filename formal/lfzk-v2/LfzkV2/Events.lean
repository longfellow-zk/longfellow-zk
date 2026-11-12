import LfzkV2.ChallengeTests
import LfzkV2.Inputs

/-!
# Concrete challenge tests for a reconstructed V2 execution

These lists expose the exact data needed at each challenge. The Fiat--Shamir
interface links these values to prefix-only oracle points; it does not assume
that accepted false statements imply an oracle bad event.
-/

namespace LfzkV2

open SumcheckV2 Classical

variable {F Pad Slot : Type} [Field F]

/-- Only the last nonzero residual can be needed by assertion reduction. Its
index is fixed by the witness before the assertion challenges are sampled. -/
noncomputable def assertionIndices (m : AssertedModel F) : Finset (Fin m.assertions) :=
  Finset.univ.filter fun i => m.residuals i ≠ 0 ∧ ∀ j, i < j → m.residuals j = 0

theorem assertionIndices_card_le_one (m : AssertedModel F) : (assertionIndices m).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  obtain ⟨hi, hilast⟩ := (Finset.mem_filter.mp hi).2
  obtain ⟨hj, hjlast⟩ := (Finset.mem_filter.mp hj).2
  rcases lt_trichotomy i j with hij | hij | hij
  · exact (hj (hilast j hij)).elim
  · exact hij
  · exact (hi (hjlast i hij)).elim

noncomputable def assertionTests (m : AssertedModel F) (claim : F) : Tests F :=
  (assertionIndices m).toList.map fun i =>
    (.linear (assertionOffset m.incoming claim m.beta m.residuals i) (m.residuals i), m.beta i)

theorem assertionTests_bad (m : AssertedModel F) (claim : F)
    (hbad : AssertionBad m.incoming claim m.beta m.residuals) :
    (assertionTests m claim).Bad := by
  obtain ⟨i, hlast, hi⟩ := hbad
  refine ⟨_, List.mem_map.mpr ⟨i, ?_, rfl⟩, hi⟩
  exact Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi.1, hlast⟩)

noncomputable def layerTests (m : LayerModel F) (t : LayerTranscript Pad Slot F)
    (pads : Pad → F) (claim : F) : Tests F :=
  roundTests claim (truePolys (bindRight m.kernel m.wires) m.wires m.point)
    (t.clearRounds pads) t.challenges ++
  [(.combine ⟨evaluate m.wires m.point, evaluate (bindRight m.kernel m.wires) m.point,
      t.clearA pads, t.clearB pads⟩, t.alpha)]

theorem layerTests_bad (m : LayerModel F) (t : LayerTranscript Pad Slot F)
    (pads : Pad → F) (claim : F) :
    (layerTests m t pads claim).Bad ↔ m.Bad t pads claim := by
  rw [layerTests, Tests.bad_append, roundTests_bad]
  simp [Tests.Bad, ChallengeTest.Bad, LayerModel.Bad]

theorem layerTests_valid (m : LayerModel F) (t : LayerTranscript Pad Slot F)
    (pads : Pad → F) (claim : F) : (layerTests m t pads claim).Valid := by
  rw [layerTests, Tests.valid_append]
  exact ⟨roundTests_valid _ _ _ _ (truePolys_degree _ _ _), by
    simp [Tests.Valid, ChallengeTest.Valid]⟩

noncomputable def traceTests (pads : Pad → F) (claim : F) : AssertedTrace Pad Slot F → Tests F
  | [] => []
  | (t, m) :: rest => assertionTests m claim ++ layerTests m.toLayerModel t pads claim ++
      traceTests pads (t.clearA pads + t.alpha * t.clearB pads) rest

theorem traceTests_bad (pads : Pad → F) (claim : F) (trace : AssertedTrace Pad Slot F)
    (hbad : AssertedBad pads claim trace) : (traceTests pads claim trace).Bad := by
  induction trace generalizing claim with
  | nil => exact hbad.elim
  | cons entry rest ih =>
      rcases entry with ⟨t, m⟩
      simp only [traceTests, Tests.bad_append, layerTests_bad]
      rcases hbad with hassert | hlayer | hrest
      · exact Or.inl (Or.inl (assertionTests_bad m claim hassert))
      · exact Or.inl (Or.inr hlayer)
      · exact Or.inr (ih _ hrest)

theorem traceTests_valid (pads : Pad → F) (claim : F) (trace : AssertedTrace Pad Slot F) :
    (traceTests pads claim trace).Valid := by
  induction trace generalizing claim with
  | nil => simp [traceTests, Tests.Valid]
  | cons entry rest ih =>
      rcases entry with ⟨t, m⟩
      simp only [traceTests, Tests.valid_append]
      exact ⟨⟨by simp [assertionTests, Tests.Valid, ChallengeTest.Valid],
        layerTests_valid _ _ _ _⟩, ih _⟩

noncomputable def Circuit.tests {out input : ℕ} (circuit : Circuit F out input)
    (messages : circuit.Messages Pad Slot) (w : Cube input → F) (point : Fin out → F)
    (pads : Pad → F) : Tests F :=
  outputTests (circuit.eval w) point ++
    traceTests pads 0 (circuit.execution messages w (monomialWeights point))

theorem Circuit.tests_valid {out input : ℕ} (circuit : Circuit F out input)
    (messages : circuit.Messages Pad Slot) (w : Cube input → F) (point : Fin out → F)
    (pads : Pad → F) : (circuit.tests messages w point pads).Valid := by
  exact (Tests.valid_append _ _).mpr ⟨outputTests_valid _ _, traceTests_valid _ _ _⟩

theorem Circuit.tests_soundness {out input : ℕ} (circuit : Circuit F out input)
    (messages : circuit.Messages Pad Slot) (w : Cube input → F) (point : Fin out → F)
    (pads : Pad → F) (hfalse : ¬ circuit.Satisfies w)
    (haccept : ClearAccepts pads 0 (circuit.proof messages)
      (dot (circuit.inputWeights messages (monomialWeights point)) w)) :
    (circuit.tests messages w point pads).Bad := by
  rcases circuit.soundness_reduction messages w point pads hfalse haccept with houtput | htrace
  · exact (Tests.bad_append _ _).mpr (Or.inl ((outputTests_bad _ _).mpr houtput))
  · exact (Tests.bad_append _ _).mpr (Or.inr (traceTests_bad _ _ _ htrace))

end LfzkV2
