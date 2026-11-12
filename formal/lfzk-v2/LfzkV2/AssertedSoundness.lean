import LfzkV2.Circuit
import LfzkV2.Constraints
import LfzkV2.Challenges

/-!
# Soundness including intermediate assertions

A false witness need not have nonzero outputs. The invariant below retains
violations of assertions in layers not yet visited. Each layer either preserves
a false scalar claim, encounters a sumcheck/combine bad event, or hides a
nonzero assertion vector at its independently sampled assertion coefficients.
-/

namespace LfzkV2

open SumcheckV2 Classical

variable {F Pad Slot : Type} [Field F]

abbrev AssertedTrace (Pad Slot F : Type) [Field F] :=
  List (LayerTranscript Pad Slot F × AssertedModel F)

def assertedTranscripts (trace : AssertedTrace Pad Slot F) : List (LayerTranscript Pad Slot F) :=
  trace.map Prod.fst

def TraceConsistent (incoming : F) : AssertedTrace Pad Slot F → F → Prop
  | [], inputSum => incoming = inputSum
  | (t, m) :: rest, inputSum =>
      m.toLayerModel.Matches t ∧ incoming = m.incoming ∧
        TraceConsistent (m.toLayerModel.nextTruth t.alpha) rest inputSum

def HasViolation (trace : AssertedTrace Pad Slot F) : Prop :=
  ∃ entry ∈ trace, ∃ i, entry.2.residuals i ≠ 0

theorem hasViolation_cons (t : LayerTranscript Pad Slot F) (m : AssertedModel F)
    (rest : AssertedTrace Pad Slot F) :
    HasViolation ((t, m) :: rest) ↔ (∃ i, m.residuals i ≠ 0) ∨ HasViolation rest := by
  constructor
  · rintro ⟨entry, hentry, i, hi⟩
    rcases List.mem_cons.mp hentry with heq | hentry
    · subst entry
      exact Or.inl ⟨i, hi⟩
    · exact Or.inr ⟨entry, hentry, i, hi⟩
  · rintro (⟨i, hi⟩ | ⟨entry, hentry, i, hi⟩)
    · exact ⟨(t, m), List.mem_cons_self, i, hi⟩
    · exact ⟨entry, List.mem_cons_of_mem _ hentry, i, hi⟩

def AssertedBad (pads : Pad → F) (claim : F) : AssertedTrace Pad Slot F → Prop
  | [] => False
  | (t, m) :: rest =>
      AssertionBad m.incoming claim m.beta m.residuals ∨
        m.toLayerModel.Bad t pads claim ∨
          AssertedBad pads (t.clearA pads + t.alpha * t.clearB pads) rest

/-- Doom is a false current scalar claim or any still-unvisited assertion violation. -/
theorem asserted_chain_reduction (trace : AssertedTrace Pad Slot F) (pads : Pad → F)
    (claim incoming inputSum : F) (hconsistent : TraceConsistent incoming trace inputSum)
    (haccept : ClearAccepts pads claim (assertedTranscripts trace) inputSum)
    (hdoom : claim ≠ incoming ∨ HasViolation trace) : AssertedBad pads claim trace := by
  induction trace generalizing claim incoming with
  | nil =>
      rcases hdoom with hfalse | hviolation
      · exact (hfalse (haccept.trans hconsistent.symm)).elim
      · simp [HasViolation] at hviolation
  | cons entry rest ih =>
      rcases entry with ⟨t, m⟩
      rcases hconsistent with ⟨hshape, hincoming, hrest⟩
      rcases haccept with ⟨hterminal, htail⟩
      by_cases hclaim : claim = m.toLayerModel.truth
      · by_cases hbad : ∃ i, m.residuals i ≠ 0
        · exact Or.inl (assertion_reduction m.incoming claim m.beta m.residuals hbad
            (hclaim.trans m.mixed_truth))
        · have hvalid : ∀ i, m.residuals i = 0 := by simpa using hbad
          have hcurrent : claim = incoming := by
            rw [hclaim, m.mixed_truth, hincoming]
            simp [dot, hvalid]
          have hremaining : HasViolation rest := by
            rcases hdoom with hfalse | ⟨entry, hentry, i, hi⟩
            · exact (hfalse hcurrent).elim
            · rcases List.mem_cons.mp hentry with heq | hentry
              · subst entry
                exact (hi (hvalid i)).elim
              · exact ⟨entry, hentry, i, hi⟩
          exact Or.inr (Or.inr (ih _ _ hrest htail (Or.inr hremaining)))
      · by_cases hnext : t.clearA pads + t.alpha * t.clearB pads =
            m.toLayerModel.nextTruth t.alpha
        · exact Or.inr (Or.inl (m.toLayerModel.reduction t pads claim hshape hclaim
            hterminal hnext))
        · exact Or.inr (Or.inr (ih _ _ hrest htail (Or.inl hnext)))

/-- Accepted constraints on a false witness imply an actual output, assertion,
round, or combination bad event. No nonzero-output assumption is made. -/
theorem circuit_reduction {n : ℕ} (outputs : Cube n → F) (point : Fin n → F)
    (trace : AssertedTrace Pad Slot F) (pads : Pad → F) (inputSum : F)
    (hconsistent : TraceConsistent (evaluate outputs point) trace inputSum)
    (haccept : ClearAccepts pads 0 (assertedTranscripts trace) inputSum)
    (hfalse : outputs ≠ 0 ∨ HasViolation trace) :
    OutputBad outputs point ∨ AssertedBad pads 0 trace := by
  by_cases hzero : evaluate outputs point = 0
  · rcases hfalse with houtputs | hassertions
    · exact Or.inl (output_reduction outputs point houtputs hzero)
    · exact Or.inr (asserted_chain_reduction trace pads 0 _ inputSum hconsistent haccept
        (Or.inr hassertions))
  · exact Or.inr (asserted_chain_reduction trace pads 0 _ inputSum hconsistent haccept
      (Or.inl (Ne.symm hzero)))

theorem asserted_chain_completeness (trace : AssertedTrace Pad Slot F) (pads : Pad → F)
    (incoming inputSum : F) (hconsistent : TraceConsistent incoming trace inputSum)
    (hvalid : ¬ HasViolation trace)
    (hhonest : ∀ entry ∈ trace, entry.2.toLayerModel.Honest entry.1 pads) :
    ClearAccepts pads incoming (assertedTranscripts trace) inputSum := by
  induction trace generalizing incoming with
  | nil => exact hconsistent
  | cons entry rest ih =>
      rcases entry with ⟨t, m⟩
      rcases hconsistent with ⟨hshape, hincoming, hrest⟩
      have hzero (i : Fin m.assertions) : m.residuals i = 0 := by
        by_cases hz : m.residuals i = 0
        · exact hz
        · exact (hvalid ⟨(t, m), List.mem_cons_self, i, hz⟩).elim
      have htruth : m.toLayerModel.truth = incoming := by
        rw [m.mixed_truth, hincoming]
        simp [dot, hzero]
      have hlayer := m.toLayerModel.completeness t pads hshape
        (hhonest (t, m) List.mem_cons_self)
      constructor
      · simpa only [htruth] using hlayer.1
      · rw [hlayer.2]
        apply ih _ hrest
        · rintro ⟨entry, hentry, i, hi⟩
          exact hvalid ⟨entry, List.mem_cons_of_mem _ hentry, i, hi⟩
        · exact fun entry h => hhonest entry (List.mem_cons_of_mem _ h)

end LfzkV2
