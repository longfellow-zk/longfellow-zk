import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Tactic.ComputeDegree
import GF128.Field

/-!
# `IsGen.indep` is not an extra assumption

`IsGen` bundles two facts about `α`: that it is a root of `P = X^128 + X^7 + X^2 + X + 1`, and
that `eval α` is injective on bit patterns — equivalently that `1, α, …, α^127` are independent
over `F₂`. The second was carried as a hypothesis. It is not independent of the first: it is
exactly the statement that `α` has degree 128, which follows from `P` being irreducible.

Nothing weaker will do. If `P` factored, a root of a proper factor would satisfy `root` while
generating a smaller field, and `indep` would be false for it — so `root` alone cannot imply
`indep`, and irreducibility is the precise missing input.

The argument here needs no linear-algebra machinery. A bit pattern `n < 2^128` names a polynomial
`q` over `F₂` of degree below 128; if `eval α n = 0` then `minpoly α ∣ q`, and `minpoly α = P`
has degree 128, so `q = 0`.
-/

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

namespace GF128

open Polynomial



/-! ## `eval` as a polynomial evaluation -/

variable {F : Type*} [CommRing F] [CharP F 2]

/-- `eval α n` is the `F₂`-combination of `1, α, …` picked out by the bits of `n`. -/
theorem eval_eq_sum (α : F) :
    ∀ (k n : Nat), n < 2 ^ k →
      eval α n = ∑ i ∈ Finset.range k, (if n.testBit i then (1 : F) else 0) * α ^ i
  | 0, n, hn => by
      have : n = 0 := by omega
      subst this
      simp
  | k + 1, n, hn => by
      have hhalf : n / 2 < 2 ^ k := by
        have : n < 2 ^ k * 2 := by rw [← pow_succ]; exact hn
        omega
      rw [eval_step' α n, eval_eq_sum α k (n / 2) hhalf, Finset.mul_sum,
        Finset.sum_range_succ' (fun i => (if n.testBit i then (1 : F) else 0) * α ^ i) k]
      simp only [Nat.testBit_div_two, pow_zero, mul_one]
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [pow_succ]
      ring

/-! ## The polynomial, and the reduction -/

/-- `P(X) = X^128 + X^7 + X^2 + X + 1` over `F₂`, the reduction polynomial of
    `core/algebra/src/gf2_128.rs:24`. -/
noncomputable def Pgf : (ZMod 2)[X] := X ^ 128 + X ^ 7 + X ^ 2 + X + 1

theorem Pgf_monic : Pgf.Monic := by
  unfold Pgf
  monicity!

theorem Pgf_natDegree : Pgf.natDegree = 128 := by
  unfold Pgf
  compute_degree!

variable [Algebra (ZMod 2) F]

/-- Being a root of `P`, in `aeval` form. -/
theorem aeval_Pgf (α : F) (hroot : α ^ 128 = α ^ 7 + α ^ 2 + α + 1) :
    aeval α Pgf = 0 := by
  simp only [Pgf, map_add, map_pow, map_one, aeval_X]
  rw [hroot]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  linear_combination (α ^ 7 + α ^ 2 + α + 1) * h2

/-- The polynomial a bit pattern names. -/
noncomputable def bitsPoly (n : Nat) : (ZMod 2)[X] :=
  ∑ i ∈ Finset.range 128, C (if n.testBit i then (1 : ZMod 2) else 0) * X ^ i

theorem bitsPoly_natDegree_lt (n : Nat) : (bitsPoly n).natDegree < 128 := by
  have h : (bitsPoly n).natDegree ≤ 127 := by
    refine natDegree_sum_le_of_forall_le _ _ (fun i hi => ?_)
    refine le_trans (natDegree_C_mul_le _ _) ?_
    have hlt := Finset.mem_range.mp hi
    exact le_trans (natDegree_X_pow_le i) (by omega)
  omega

theorem bitsPoly_coeff (n i : Nat) (hi : i < 128) :
    (bitsPoly n).coeff i = if n.testBit i then (1 : ZMod 2) else 0 := by
  unfold bitsPoly
  rw [finsetSum_coeff, Finset.sum_eq_single i]
  · by_cases h : n.testBit i <;> simp [h, coeff_C_mul, coeff_X_pow]
  · intro j _ hj
    by_cases h : n.testBit j <;> simp [h, coeff_C_mul, coeff_X_pow, Ne.symm hj]
  · intro h
    exact absurd (Finset.mem_range.mpr hi) h

theorem aeval_bitsPoly (α : F) {n : Nat} (hn : n < 2 ^ 128) :
    aeval α (bitsPoly n) = eval α n := by
  rw [eval_eq_sum α 128 n hn]
  unfold bitsPoly
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : n.testBit i <;> simp [h]

/-- **The degree argument.** Whatever supplies `deg (minpoly α) = 128` — irreducibility of `P`,
    or a power basis — this is the step that turns it into injectivity of `eval α`. -/
theorem indep_of_minpoly_degree [Nontrivial F] (α : F)
    (hdeg : (minpoly (ZMod 2) α).natDegree = 128) :
    ∀ n, n < 2 ^ 128 → eval α n = 0 → n = 0 := by
  intro n hn hz
  by_contra hne

  have hq0 : bitsPoly n ≠ 0 := by
    obtain ⟨i, hi, hbit⟩ : ∃ i, i < 128 ∧ n.testBit i = true := by
      by_contra hc
      push_neg at hc
      refine hne (Nat.eq_of_testBit_eq (fun i => ?_))
      rw [Nat.zero_testBit]
      rcases Nat.lt_or_ge i 128 with h | h
      · simpa using hc i h
      · exact Nat.testBit_eq_false_of_lt
          (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) h))
    intro h0
    have := bitsPoly_coeff n i hi
    rw [h0, hbit] at this
    simp at this
  have hdvd := minpoly.dvd (ZMod 2) α (p := bitsPoly n) (by rw [aeval_bitsPoly α hn, hz])
  have hle := Polynomial.natDegree_le_of_dvd hdvd hq0
  rw [hdeg] at hle
  exact absurd (lt_of_le_of_lt hle (bitsPoly_natDegree_lt n)) (lt_irrefl 128)

/-- **`indep` follows from irreducibility.** -/
theorem indep_of_irreducible [Nontrivial F] (hirr : Irreducible Pgf) (α : F)
    (hroot : α ^ 128 = α ^ 7 + α ^ 2 + α + 1) :
    ∀ n, n < 2 ^ 128 → eval α n = 0 → n = 0 := by
  refine indep_of_minpoly_degree α ?_
  have hmin := minpoly.eq_of_irreducible_of_monic (B := F) hirr (aeval_Pgf α hroot) Pgf_monic
  rw [← hmin, Pgf_natDegree]

/-- **`IsGen` from one closed fact.** With irreducibility in hand, presenting `F` as GF(2^128)
    needs only that `α` is a root of `P`; nothing else about `F` or `α` is assumed. -/
theorem isGen_of_irreducible [Nontrivial F] (hirr : Irreducible Pgf) (α : F)
    (hroot : α ^ 128 = α ^ 7 + α ^ 2 + α + 1) : IsGen α :=
  ⟨hroot, indep_of_irreducible hirr α hroot⟩

/-! ## Discharged

`Irreducible Pgf` is proved in `GF128/Irred.lean`, from the order certificate of `Poly.lean`
rather than from a factorisation search: in `AdjoinRoot Pgf` the power basis gives
`|R| = 2^128` and injectivity of `eval`, injectivity carries `ord x = 2^128 − 1` across, and a
commutative ring with `|R| − 1` units is a field. So `indep_of_irreducible` is not the end of the
chain — `Irred.isGen_of_root` is, and it assumes only `P(α) = 0`.
-/

end GF128
