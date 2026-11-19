import LfzkV2.Current.PrimeClaim
import DualPacking.Counting

/-! Row batching of a pure-foreign participant (`rust/src/runtime/v2/zk/batching.rs`).
Such a participant commits no cell, so its `L` layer rows and its input
equation are not authenticated as rows. After the frontend's last message,
row weights `rho_0..rho_L` are drawn uniformly from the full field and batch
the `L+1` rows into one dense claim `<weights, v> = target` over every value,
which the foreign adapter proves. A false row survives one uniform
combination with probability at most `1/#F`. -/
noncomputable section
namespace LfzkV2.Current.RowBatching
open Finset SumcheckV2
open scoped Classical

variable {F Value : Type} [Field F] {n : ℕ}

/-- The participant's rows before batching, all of which must hold. -/
def Holds (rows : Fin n → LinearRow Value F) (values : Value → F) : Prop :=
  ∀ i, (rows i).eval values = 0

theorem holds_get_iff (rows : List (LinearRow Value F)) (values : Value → F) :
    Holds rows.get values ↔ RowsHold rows values := by
  constructor
  · intro h row hrow
    obtain ⟨i, rfl⟩ := List.get_of_mem hrow
    exact h i
  · intro h i
    exact h _ (List.get_mem rows i)

/-- The dense modular claim `<weights, v> = target` over every value, with a
public target: `ModularClaim` of `zk::split::pure::PureSplit::claim` before its terms
are mapped to bit groups. -/
structure Claim (Value F : Type) where
  weights : Value → F
  target : F

def Claim.residual [Fintype Value] (c : Claim Value F) (values : Value → F) : F :=
  (∑ v, c.weights v * values v) - c.target

/-- `batching::batch`: `weights = sum_i rho_i * A_i` and
`target = -sum_i rho_i * b_i` for the rows `A_i*v + b_i = 0`. -/
def batch (rows : Fin n → LinearRow Value F) (rho : Fin n → F) : Claim Value F where
  weights v := ∑ i, rho i * Prime.coefficients (rows i) v
  target := -∑ i, rho i * (rows i).constant

/-- The batched claim's residual is the weighted sum of the row values. -/
theorem batch_residual [Fintype Value] (rows : Fin n → LinearRow Value F) (rho : Fin n → F)
    (values : Value → F) :
    (batch rows rho).residual values = ∑ i, rho i * (rows i).eval values := by
  simp only [Claim.residual, batch, Prime.eval_coefficients, mul_add, sum_add_distrib, sum_mul,
    mul_sum, sub_neg_eq_add]
  rw [sum_comm, add_comm]
  simp only [mul_assoc]

/-- Completeness: rows that hold give a true batched claim for every weight. -/
theorem batch_of_holds [Fintype Value] (rows : Fin n → LinearRow Value F) (rho : Fin n → F)
    (values : Value → F) (h : Holds rows values) : (batch rows rho).residual values = 0 := by
  simp [batch_residual, h _]

/-- The runtime's row order: the `L` layer rows `A_c*v + b_c = 0`, then the
input equation. -/
def ofLayers {L : ℕ} (layers : Fin L → LinearRow Value F) (input : LinearRow Value F) :
    Fin (L+1) → LinearRow Value F :=
  Fin.lastCases input layers

/-- The design's coefficients: `sum_c rho_c*A_c` from the layer rows and
`rho_L` times the input row, whose coefficients are `-w_priv` on the inputs
and `+k` on the pads (`Linear.compileInput`). -/
theorem batch_ofLayers_weights {L : ℕ} (layers : Fin L → LinearRow Value F)
    (input : LinearRow Value F) (rho : Fin (L+1) → F) (v : Value) :
    (batch (ofLayers layers input) rho).weights v =
      (∑ c, rho c.castSucc * Prime.coefficients (layers c) v) +
        rho (Fin.last L) * Prime.coefficients input v := by
  simp [batch, ofLayers, Fin.sum_univ_castSucc]

/-- The design's target `-(sum_c rho_c*b_c + rho_L*t)`, with `t` the input
row's constant. -/
theorem batch_ofLayers_target {L : ℕ} (layers : Fin L → LinearRow Value F)
    (input : LinearRow Value F) (rho : Fin (L+1) → F) :
    (batch (ofLayers layers input) rho).target =
      -((∑ c, rho c.castSucc * (layers c).constant) + rho (Fin.last L) * input.constant) := by
  simp [batch, ofLayers, Fin.sum_univ_castSucc]

/-- The batching event: some row is false, yet the batched claim holds. -/
def Bad [Fintype Value] (rows : Fin n → LinearRow Value F) (values : Value → F)
    (rho : Fin n → F) : Prop :=
  ¬ Holds rows values ∧ (batch rows rho).residual values = 0

/-- A true batched claim means every row holds, or the batching event. -/
theorem holds_or_bad [Fintype Value] (rows : Fin n → LinearRow Value F) (values : Value → F)
    (rho : Fin n → F) (h : (batch rows rho).residual values = 0) :
    Holds rows values ∨ Bad rows values rho := by
  by_cases hrows : Holds rows values
  · exact Or.inl hrows
  · exact Or.inr ⟨hrows, h⟩

variable [Fintype F] [DecidableEq F] [Fintype Value]

/-- For fixed rows and values, at most `#F^(n-1)` of the `#F^n` weight
vectors are bad (`DualPacking.affine_batch_card_le`); here `n = L+1`. -/
theorem bad_card_mul_le (rows : Fin n → LinearRow Value F) (values : Value → F) :
    (univ.filter (Bad rows values)).card * Fintype.card F ≤ Fintype.card F ^ n := by
  by_cases hrows : Holds rows values
  · simp [Bad, hrows]
  · have hn : 0 < n := by
      rcases n with _ | n
      · exact absurd (fun i => i.elim0) hrows
      · exact Nat.succ_pos n
    obtain ⟨k, hk⟩ := not_forall.mp hrows
    have hsub : univ.filter (Bad rows values) ⊆
        univ.filter fun rho : Fin n → F => ∑ i, (rows i).eval values * rho i = 0 := by
      intro rho h
      have h := (mem_filter.mp h).2.2
      rw [batch_residual] at h
      exact mem_filter.mpr ⟨mem_univ _, by simpa only [mul_comm] using h⟩
    have hcard := (card_le_card hsub).trans
      (DualPacking.affine_batch_card_le (fun i => (rows i).eval values) ⟨k, hk⟩ 0)
    rw [Fintype.card_fin] at hcard
    calc _ ≤ Fintype.card F ^ (n-1) * Fintype.card F := Nat.mul_le_mul_right _ hcard
      _ = Fintype.card F ^ n := by rw [← pow_succ, Nat.sub_add_cancel hn]

/-- One uniform combination of the rows: a false row survives with
probability at most `1/#F`. -/
theorem bad_probability_le (rows : Fin n → LinearRow Value F) (values : Value → F) :
    ((univ.filter (Bad rows values)).card : ℚ) / Fintype.card (Fin n → F) ≤
      1 / Fintype.card F := by
  have hF : (0 : ℚ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hc : ((univ.filter (Bad rows values)).card : ℚ) * Fintype.card F ≤
      (Fintype.card F : ℚ) ^ n := by exact_mod_cast bad_card_mul_le rows values
  rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow,
    div_le_div_iff₀ (pow_pos hF n) hF, one_mul]
  exact hc

end LfzkV2.Current.RowBatching
