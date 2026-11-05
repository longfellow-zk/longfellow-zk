import LfzkV2.Linear.Budgets

/-! Field-normalized frontend bounds, including committed candidate families,
adaptive search, and the nonzero terminal denominator. -/

namespace LfzkV2.Linear.Replay

open Challenges

variable {F C : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype C] [Nonempty C]
variable {out input : ℕ} {circuit : Native.Circuit F out input}

private theorem normalized_fiber (fiber size : ℕ) (h : fiber * size = Fintype.card C) (x : ℕ) :
    ((fiber * x : ℕ) : ℚ) / Fintype.card C = (x : ℚ) / size := by
  have hf : (0 : ℚ) < fiber := by
    have hc := Fintype.card_pos (α := C)
    exact_mod_cast (show 0 < fiber by nlinarith)
  have hc : (Fintype.card C : ℚ) = fiber * size := by exact_mod_cast h.symm
  rw [hc]
  push_cast
  field_simp [hf.ne']

theorem Sampling.field_rate (sampling : Sampling (C := C) circuit) (x : ℕ) :
    ((sampling.fieldFiber * x : ℕ) : ℚ) / Fintype.card C = (x : ℚ) / Fintype.card F :=
  normalized_fiber _ _ sampling.balanced x

theorem Sampling.terminal_rate (sampling : Sampling (C := C) circuit) (x : ℕ) :
    ((sampling.terminal.fiber * x : ℕ) : ℚ) / Fintype.card C =
      (x : ℚ) / (Fintype.card F - 1 : ℕ) :=
  normalized_fiber _ _ (by simpa only [TerminalSampling.nonzero_card] using sampling.terminal.balanced) x

theorem Sampling.max_rate (sampling : Sampling (C := C) circuit) :
    ((max (sampling.fieldFiber * max out 2) (sampling.terminal.fiber * 2) : ℕ) : ℚ) /
        Fintype.card C =
      max ((max out 2 : ℕ) / (Fintype.card F : ℚ)) (2 / ((Fintype.card F - 1 : ℕ) : ℚ)) := by
  rw [Nat.cast_max, ← max_div_div_right (Nat.cast_nonneg _), sampling.field_rate, sampling.terminal_rate]
  rfl

theorem Sampling.path_rate (sampling : Sampling (C := C) circuit) :
    ((∑ i : Fin (slots circuit), (roleKind circuit ((roleEquiv circuit).symm i)).rawBudget
      sampling.fieldFiber sampling.terminal.fiber : ℕ) : ℚ) / Fintype.card C =
      (out + circuit.sharpLayerBudget : ℕ) / (Fintype.card F : ℚ) +
        (2 * circuit.layers : ℕ) / ((Fintype.card F - 1 : ℕ) : ℚ) := by
  rw [budget_sum, Nat.cast_add, add_div, sampling.field_rate, sampling.terminal_rate]

end LfzkV2.Linear.Replay

namespace LfzkV2.Linear.FiatShamir.Setup

open SumcheckV2 Challenges Replay Finset
open scoped Classical

variable {F C Key Context Candidate Pad Out : Type}
variable [Field F] [Fintype F] [DecidableEq F] [Fintype C] [Nonempty C]
variable [DecidableEq Key] [Fintype Key] [Fintype Candidate]
variable {out input N : ℕ}

/-- The complete frontend bound for the reconstructed native circuit. The
right side distinguishes ordinary full-field challenges from terminal scales. -/
theorem normalized_soundness_le (circuit : Native.Circuit F out input)
    (S : Setup circuit C Key Context Candidate Pad Out N) :
    ((univ.filter (S.FalseAccepted circuit)).card : ℚ) /
        (Fintype.card C : ℚ) ^ Fintype.card (Point Key F circuit) ≤
      Fintype.card Candidate *
        (N * max ((max out 2 : ℕ) / (Fintype.card F : ℚ))
            (2 / ((Fintype.card F - 1 : ℕ) : ℚ)) +
          (out + circuit.sharpLayerBudget : ℕ) / (Fintype.card F : ℚ) +
          (2 * circuit.layers : ℕ) / ((Fintype.card F - 1 : ℕ) : ℚ)) := by
  have h := S.soundness_le circuit
    (Fintype.card Candidate * max (S.sampling.fieldFiber * max out 2) (S.sampling.terminal.fiber * 2))
    (fun x => Nat.mul_le_mul_left _ (pointKind_budget_le _ _ circuit x))
  refine h.trans_eq ?_
  have hmax := S.sampling.max_rate
  have hpath := S.sampling.path_rate
  push_cast at hmax hpath ⊢
  linear_combination (norm := ring_nf)
    (Fintype.card Candidate : ℚ) * (N : ℚ) * hmax + (Fintype.card Candidate : ℚ) * hpath

end LfzkV2.Linear.FiatShamir.Setup
