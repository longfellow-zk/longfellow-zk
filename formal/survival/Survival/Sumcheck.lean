import Survival.Basic
import SumcheckV2.Round

/-! Use the actual Longfellow v2 projective round/root theorem. The query's
context includes the truthful residual polynomial and incoming claim. Its
construction from a strand prefix is an integration obligation.
-/
noncomputable section
namespace Survival.Sumcheck
open Finset Merkle.RandomOracle Bcs.FiniteProbability
open scoped Classical

variable {P F Out : Type} [Field F] [Fintype F] [DecidableEq F]

structure Context (F : Type) [Field F] where
  polynomial : Polynomial F
  message : SumcheckV2.RoundPoly F
  claim : F
  degree : polynomial.natDegree ≤ 2

def safe (context : Context F) (answer : F) : Prop :=
  ¬SumcheckV2.BadRoundEvent context.polynomial context.message context.claim answer

theorem round_hazard (context : Context F) :
    density (fun answer => ¬safe context answer) ≤ 2/(Fintype.card F : ℚ) := by
  have roots := SumcheckV2.bad_round_roots context.polynomial context.message context.claim context.degree
  simp only [safe, not_not, density]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast roots

/-- Sumcheck saturation for arbitrary adaptive context choices, once they
are chronological and oracle queries have been memoized. -/
theorem escape_le [Fintype P] [DecidableEq P]
    (contexts : P → Context F) (cardinality : 2 ≤ Fintype.card F)
    {fuel : ℕ} (tree : Tree P F Out fuel)
    (fresh : TranscriptV2.FreshOracle.FreshFrom (fun _ => False) tree) :
    density (fun H => ¬((Survival.monitor (fun _ point => safe (contexts point)) 0 tree).run H).1 = true) ≤
      1-(1-2/(Fintype.card F : ℚ))^fuel := by
  apply Survival.escape_le (fun point => safe (contexts point)) (2/(Fintype.card F : ℚ))
    (by positivity) ?_ (fun point => round_hazard (contexts point)) tree fresh
  apply (div_le_one₀ (by positivity)).mpr
  exact_mod_cast cardinality

end Survival.Sumcheck
