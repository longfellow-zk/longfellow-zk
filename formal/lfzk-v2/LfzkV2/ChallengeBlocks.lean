import LfzkV2.ChallengePrefix
import Bcs.TotalOracle
import LigeroFamily.Protocol.Finite

/-!
# Whole-answer bounds for the V2 challenge blocks

The initial output point and each layer's assertion coefficients are decoded
from one oracle answer each. They are not charged as separate oracle queries
for each field coordinate. V1's finite-tape count handles the output block;
its affine-equation count handles assertion batching with one root budget.
-/

namespace LfzkV2.ChallengeBlocks

open SumcheckV2 Finset LigeroFamily
open scoped Classical

variable {F : Type} [Field F]

theorem output_bad_card [Fintype F] [DecidableEq F] {n : ℕ} (table : Cube n → F) :
    (univ.filter fun point : Fin n → F => OutputBad table point).card ≤
      n * Fintype.card F ^ (n-1) := by
  have hsub : (univ.filter fun point : Fin n → F => OutputBad table point) ⊆
      univ.filter (fun point => ∃ i : Fin n,
        (OutputReplay.dataAt table i (SumcheckV1.extract_prefix point i)).Bad (point i)) := by
    intro point hp
    have hbad := (outputTests_bad table point).2 (mem_filter.mp hp).2
    rw [OutputReplay.outputTests_eq] at hbad
    obtain ⟨test, hmem, htest⟩ := hbad
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hmem
    exact mem_filter.mpr ⟨mem_univ _, i, htest⟩
  apply (card_le_card hsub).trans
  simpa using SumcheckV1.tape_bad_card_le (fun _ : Fin n => 1)
    (fun i pref z => (OutputReplay.dataAt table i pref).Bad z)
    (fun i pref => by
      simpa only [OutputReplay.dataAt_budget] using
        (OutputReplay.dataAt table i pref).card_bad_le (OutputReplay.dataAt_valid table i pref))

theorem assertion_bad_equation {n : ℕ} (incoming claim : F) (beta values : Fin n → F)
    (hbad : AssertionBad incoming claim beta values) : dot beta values = claim-incoming := by
  obtain ⟨i, hlast, _, heq⟩ := hbad
  have hsum := assertion_dot_eq_prefix beta values i hlast
  unfold assertionOffset at heq
  rw [hsum]
  linear_combination heq

theorem assertion_bad_card [Fintype F] [DecidableEq F] {n : ℕ}
    (incoming claim : F) (values : Fin n → F) :
    (univ.filter fun beta : Fin n → F => AssertionBad incoming claim beta values).card ≤
      min 1 n * Fintype.card F ^ (n-1) := by
  cases n with
  | zero => simp [AssertionBad]
  | succ n =>
      by_cases hz : values = 0
      · subst values
        simp [AssertionBad, AssertionSlotBad, BadLinear]
      · have hsub : (univ.filter fun beta : Fin (n+1) → F => AssertionBad incoming claim beta values) ⊆
          affineEquationSolutions values (claim-incoming) := by
          intro beta hb
          apply mem_filter.mpr
          refine ⟨mem_univ _, ?_⟩
          exact assertion_bad_equation incoming claim beta values (mem_filter.mp hb).2
        simpa using (card_le_card hsub).trans
          (card_affineEquationSolutions_le values (claim-incoming) hz)

inductive Kind where
  | output (coordinates : ℕ)
  | assertions (occurrences : ℕ)
  | round
  | combine
  deriving DecidableEq

abbrev Kind.dimension : Kind → ℕ
  | .output n | .assertions n => n
  | .round | .combine => 1

def Kind.budget : Kind → ℕ
  | .output n => n
  | .assertions n => min 1 n
  | .round => 2
  | .combine => 1

abbrev Kind.Sample (F : Type) (kind : Kind) := Fin kind.dimension → F

omit [Field F] in
theorem Kind.sample_card [Fintype F] (kind : Kind) :
    Fintype.card (kind.Sample F) = Fintype.card F ^ kind.dimension := by
  simp [Sample]

omit [Field F] in
theorem scalar_bad_card [Fintype F] (event : F → Prop) :
    (univ.filter fun sample : Fin 1 → F => event (sample 0)).card ≤
      (univ.filter event).card := by
  apply card_le_card_of_injOn (fun sample : Fin 1 → F => sample 0)
  · intro sample hs
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hs).2⟩
  · intro first _ second _ heq
    funext j
    simpa only [Subsingleton.elim j (0 : Fin 1)] using heq

abbrev Data (F : Type) [Field F] : Kind → Type
  | .output n => Cube n → F
  | .assertions n => F × F × (Fin n → F)
  | .round => RoundData F
  | .combine => CombineData F

def Data.Valid {kind : Kind} : Data F kind → Prop :=
  match kind with
  | .round => fun d => d.truth.natDegree ≤ 2
  | _ => fun _ => True

def Data.Bad {kind : Kind} : Data F kind → kind.Sample F → Prop :=
  match kind with
  | .output _ => fun table point => OutputBad table point
  | .assertions _ => fun d beta => AssertionBad d.1 d.2.1 beta d.2.2
  | .round => fun d z => BadRoundEvent d.truth d.message d.claim (z 0)
  | .combine => fun d z => BadCombineEvent d.trueA d.trueB d.claimA d.claimB (z 0)

theorem Data.card_bad_le [Fintype F] [DecidableEq F] {kind : Kind}
    (data : Data F kind) (hvalid : Data.Valid data) :
    (univ.filter (Data.Bad data)).card ≤ kind.budget * Fintype.card F ^ (kind.dimension-1) := by
  cases kind with
  | output n => exact output_bad_card data
  | assertions n => exact assertion_bad_card data.1 data.2.1 data.2.2
  | round =>
      change (univ.filter fun sample : Fin 1 → F =>
        BadRoundEvent data.truth data.message data.claim (sample 0)).card ≤ 2
      exact (scalar_bad_card (fun z => BadRoundEvent data.truth data.message data.claim z)).trans
        (bad_round_roots data.truth data.message data.claim hvalid)
  | combine =>
      change (univ.filter fun sample : Fin 1 → F =>
        BadCombineEvent data.trueA data.trueB data.claimA data.claimB (sample 0)).card ≤ 1
      exact (scalar_bad_card (fun z => BadCombineEvent data.trueA data.trueB data.claimA data.claimB z)).trans
        (bad_combine_roots data.trueA data.trueB data.claimA data.claimB)

/-- A balanced projection of the full oracle answer onto one whole block.
The adversary continues to see the full answer. -/
structure Sampler (F C : Type) [Field F] [Fintype F] [DecidableEq F] [Fintype C] (kind : Kind) where
  decode : C → kind.Sample F
  fiber : ℕ
  fiber_bound : ∀ sample, (univ.filter fun c => decode c = sample).card ≤ fiber
  balanced : fiber * Fintype.card F ^ kind.dimension = Fintype.card C

theorem Sampler.raw_bad_card {C : Type} [Fintype F] [DecidableEq F] [Fintype C] {kind : Kind}
    (sampler : Sampler F C kind) (unitFiber : ℕ)
    (hunit : unitFiber * Fintype.card F = Fintype.card C)
    (data : Data F kind) (hvalid : Data.Valid data) :
    (univ.filter fun c : C => Data.Bad data (sampler.decode c)).card ≤ unitFiber * kind.budget := by
  have hcard := Bcs.card_decode_le sampler.decode sampler.fiber sampler.fiber_bound
    (Data.Bad data) _ (Data.card_bad_le data hvalid)
  by_cases hb : kind.budget = 0
  · simpa only [hb, zero_mul, mul_zero] using hcard
  · have hdim : 1 ≤ kind.dimension := by
      cases kind <;> simp_all [Kind.dimension, Kind.budget] <;> omega
    have hpow : Fintype.card F ^ (kind.dimension-1) * Fintype.card F =
        Fintype.card F ^ kind.dimension := by
      rw [← pow_succ, Nat.sub_add_cancel hdim]
    have hfiber : sampler.fiber * Fintype.card F ^ (kind.dimension-1) = unitFiber := by
      apply mul_right_cancel₀ (Nat.ne_of_gt (Fintype.card_pos (α := F)))
      rw [mul_assoc, hpow, sampler.balanced, hunit]
    calc
      _ ≤ sampler.fiber * (kind.budget * Fintype.card F ^ (kind.dimension-1)) := hcard
      _ = (sampler.fiber * Fintype.card F ^ (kind.dimension-1)) * kind.budget := by ring
      _ = _ := by rw [hfiber]

end LfzkV2.ChallengeBlocks
