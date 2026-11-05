import SumcheckV2.LinearTerminal
import Bcs.RoundByRound

/-!
# Nonzero terminal challenges and committed candidate families

Uniform sampling after rejection of zero has denominator `q - 1`, not `q`.
The balanced decoder below states that ideal-sampler boundary explicitly.
The local bad event uses only data fixed before the scale: committed cells,
the round claim, the true evaluations, and the cross message. In particular,
it does not enumerate the later pair of masked claims.
-/

namespace LfzkV2.Linear.TerminalSampling

open SumcheckV2 Finset
open scoped Classical

variable {F C Candidate : Type} [Field F] [Fintype F] [DecidableEq F]

abbrev Nonzero (F : Type) [Zero F] := {z : F // z ≠ 0}

theorem nonzero_card : Fintype.card (Nonzero F) = Fintype.card F - 1 := by
  simp [Nonzero, Fintype.card_subtype_compl]

/-- Count the union over the one committed candidate family. -/
theorem candidates_card_le [Fintype Candidate] (data : Candidate → LinearTerminal.Data F) :
    (univ.filter fun scale : Nonzero F => ∃ candidate, (data candidate).Bad scale.val).card ≤
      2 * Fintype.card Candidate := by
  have he : (univ.filter fun scale : Nonzero F => ∃ candidate, (data candidate).Bad scale.val) =
      univ.biUnion (fun candidate => univ.filter fun scale : Nonzero F =>
        (data candidate).Bad scale.val) := by
    ext scale
    simp
  rw [he]
  exact card_biUnion_le.trans ((sum_le_sum fun candidate _ =>
    (data candidate).bad_nonzero_roots).trans_eq (by simp [mul_comm]))

theorem candidate_probability_le [Fintype Candidate] (data : Candidate → LinearTerminal.Data F) :
    ((univ.filter fun scale : Nonzero F => ∃ candidate, (data candidate).Bad scale.val).card : ℚ) /
        Fintype.card (Nonzero F) ≤
      2 * Fintype.card Candidate / (Fintype.card F - 1 : ℕ) := by
  rw [nonzero_card]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast candidates_card_le data

structure Sampler (F C : Type) [Field F] [Fintype F] [DecidableEq F] [Fintype C] where
  decode : C → Nonzero F
  fiber : ℕ
  fiber_bound : ∀ scale, (univ.filter fun answer => decode answer = scale).card ≤ fiber
  balanced : fiber * Fintype.card (Nonzero F) = Fintype.card C

theorem Sampler.bad_card_le [Fintype C] [Fintype Candidate]
    (sampler : Sampler F C) (data : Candidate → LinearTerminal.Data F) :
    (univ.filter fun answer => ∃ candidate, (data candidate).Bad (sampler.decode answer).val).card ≤
      sampler.fiber * (2 * Fintype.card Candidate) := by
  have h := Bcs.card_decode_le sampler.decode sampler.fiber sampler.fiber_bound
    (fun scale : Nonzero F => ∃ candidate, (data candidate).Bad scale.val)
    (2 * Fintype.card Candidate) (by
      convert! candidates_card_le data using 1
      congr 1
      ext scale
      simp only [mem_filter])
  convert! h using 1
  congr 1
  ext answer
  simp only [mem_filter]

end LfzkV2.Linear.TerminalSampling
