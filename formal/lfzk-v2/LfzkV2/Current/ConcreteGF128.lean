import LfzkV2.Current.GeneratorChecks
import LfzkV2.Current.MdocRuntime
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.ZMod.Basic

/-! Kernel-checked primitive-order proof for the concrete GF(2^128) field
`F_2[X] / (X^128 + X^7 + X^2 + X + 1)` used by Longfellow.

Using `orderFactors` and `orderFactors_prime` from `GeneratorChecks`, we verify
by `decide +kernel` (with no `native_decide`) that `X^(2^128 - 1) = 1` and
`X^((2^128 - 1) / q) ≠ 1` for every prime factor `q` of `2^128 - 1` in the
quotient ring `AdjoinRoot gfPoly`. This implies `orderOf X = 2^128 - 1`, which
forces every nonzero element of the `2^128`-element ring to be a unit, yielding
both the `Field` instance and `Adapter.Mdoc.generatorCheck = true` for the
concrete polynomial basis. -/

namespace LfzkV2.Current.ConcreteGF128

open Polynomial

/-- The irreducible (and primitive) AES-GCM modulus `X^128 + X^7 + X^2 + X + 1` over `GF(2)`. -/
noncomputable def gfPoly : Polynomial (ZMod 2) :=
  monomial 128 1 + monomial 7 1 + monomial 2 1 + monomial 1 1 + 1

private theorem gfPoly_tail_natDegree_lt :
    (monomial 7 1 + monomial 2 1 + monomial 1 1 + 1 : Polynomial (ZMod 2)).natDegree <
      (monomial 128 1 : Polynomial (ZMod 2)).natDegree := by
  rw [natDegree_monomial_eq 128 (by decide : (1 : ZMod 2) ≠ 0)]
  compute_degree!

private theorem gfPoly_eq_add :
    gfPoly = monomial 128 1 + (monomial 7 1 + monomial 2 1 + monomial 1 1 + 1) := by
  unfold gfPoly
  ring

private theorem gfPoly_natDegree : gfPoly.natDegree = 128 := by
  rw [gfPoly_eq_add, natDegree_add_eq_left_of_natDegree_lt gfPoly_tail_natDegree_lt,
    natDegree_monomial_eq 128 (by decide : (1 : ZMod 2) ≠ 0)]

private theorem gfPoly_monic : gfPoly.Monic := by
  rw [gfPoly_eq_add]
  have hm : (monomial 128 (1 : ZMod 2)).Monic := by
    rw [← X_pow_eq_monomial]
    exact monic_X_pow 128
  exact hm.add_of_left (degree_lt_degree gfPoly_tail_natDegree_lt)

/-- The concrete quotient ring `F_2[X] / (X^128 + X^7 + X^2 + X + 1)`. -/
abbrev GF128 : Type := AdjoinRoot gfPoly

/-- The polynomial-basis generator `X` in `GF128`. -/
noncomputable def alpha : GF128 := AdjoinRoot.root gfPoly

private theorem char_two_add (x : GF128) : x + x = 0 := by
  have h2z : (2 : ZMod 2) = 0 := rfl
  have h2 : (2 : GF128) = 0 := by
    rw [← map_ofNat (AdjoinRoot.of gfPoly) 2, h2z, map_zero]
  calc x + x = 2 * x := (two_mul x).symm
    _ = 0 * x := by rw [h2]
    _ = 0 := zero_mul x

private theorem alpha_pow_128 : alpha ^ 128 = alpha ^ 7 + alpha ^ 2 + alpha + 1 := by
  have h0 : eval₂ (AdjoinRoot.of gfPoly) alpha
      (monomial 128 1 + monomial 7 1 + monomial 2 1 + monomial 1 1 + 1) = 0 :=
    AdjoinRoot.eval₂_root gfPoly
  simp only [eval₂_add, eval₂_monomial, eval₂_one, map_one, one_mul, pow_one] at h0
  calc alpha ^ 128 = alpha ^ 128 + (alpha ^ 7 + alpha ^ 2 + alpha + 1) +
        (alpha ^ 7 + alpha ^ 2 + alpha + 1) := by
          rw [add_assoc, char_two_add, add_zero]
    _ = (alpha ^ 128 + alpha ^ 7 + alpha ^ 2 + alpha + 1) +
        (alpha ^ 7 + alpha ^ 2 + alpha + 1) := by ring
    _ = 0 + (alpha ^ 7 + alpha ^ 2 + alpha + 1) := by rw [h0]
    _ = alpha ^ 7 + alpha ^ 2 + alpha + 1 := zero_add _

/-! ### Fast `Nat` model for kernel evaluation -/

/-- Multiply by `X` modulo `X^128 + X^7 + X^2 + X + 1` on 128-bit polynomials encoded as `Nat`. -/
def xtime (a : ℕ) : ℕ :=
  let lo := (a % 2 ^ 127) * 2
  if a / 2 ^ 127 % 2 = 1 then lo ^^^ 135 else lo

def gfMulLoop : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, acc => acc
  | fuel + 1, a, b, acc =>
      if b = 0 then acc
      else
        let acc' := if b % 2 = 1 then acc ^^^ a else acc
        gfMulLoop fuel (xtime a) (b / 2) acc'

/-- Multiplication in `GF(2^128)` on `Nat` bit-encodings. -/
def gfMul (a b : ℕ) : ℕ := gfMulLoop 128 a b 0

def gfPowLoop : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, acc => acc
  | fuel + 1, base, exp, acc =>
      if exp = 0 then acc
      else
        let acc' := if exp % 2 = 1 then gfMul acc base else acc
        gfPowLoop fuel (gfMul base base) (exp / 2) acc'

/-- Binary exponentiation in `GF(2^128)` on `Nat` bit-encodings (for `exp < 2^128`). -/
def gfPow (base exp : ℕ) : ℕ := gfPowLoop 128 base exp 1

private theorem xtime_lt {a : ℕ} : xtime a < 2 ^ 128 := by
  unfold xtime
  have hlo : (a % 2 ^ 127) * 2 < 2 ^ 128 := by
    have := Nat.mod_lt a (by positivity : 0 < 2 ^ 127)
    omega
  split_ifs
  · exact Nat.xor_lt_two_pow hlo (by norm_num)
  · exact hlo

private theorem gfMulLoop_lt : ∀ fuel a b acc, a < 2 ^ 128 → acc < 2 ^ 128 →
    gfMulLoop fuel a b acc < 2 ^ 128
  | 0, _, _, _, _, hacc => hacc
  | fuel + 1, a, b, acc, ha, hacc => by
      unfold gfMulLoop
      split_ifs with hb hodd
      · exact hacc
      · exact gfMulLoop_lt fuel (xtime a) (b / 2) (acc ^^^ a) xtime_lt
          (Nat.xor_lt_two_pow hacc ha)
      · exact gfMulLoop_lt fuel (xtime a) (b / 2) acc xtime_lt hacc

private theorem gfMul_lt {a b : ℕ} (ha : a < 2 ^ 128) : gfMul a b < 2 ^ 128 :=
  gfMulLoop_lt 128 a b 0 ha (by norm_num)

private theorem gfPowLoop_lt : ∀ fuel base exp acc, base < 2 ^ 128 → acc < 2 ^ 128 →
    gfPowLoop fuel base exp acc < 2 ^ 128
  | 0, _, _, _, _, hacc => hacc
  | fuel + 1, base, exp, acc, hb, hacc => by
      unfold gfPowLoop
      split_ifs with he hodd
      · exact hacc
      · exact gfPowLoop_lt fuel (gfMul base base) (exp / 2) (gfMul acc base)
          (gfMul_lt hb) (gfMul_lt hacc)
      · exact gfPowLoop_lt fuel (gfMul base base) (exp / 2) acc
          (gfMul_lt hb) hacc

private theorem gfPow_lt {base exp : ℕ} (hb : base < 2 ^ 128) : gfPow base exp < 2 ^ 128 :=
  gfPowLoop_lt 128 base exp 1 hb (by norm_num)

/-! ### Link between the `Nat` model and `AdjoinRoot gfPoly` -/

/-- Interpret the low 128 bits of `n` as a polynomial in `alpha`. -/
noncomputable def toRoot (n : ℕ) : GF128 :=
  ∑ i : Fin 128, (if n.testBit i.val then (1 : GF128) else 0) * alpha ^ i.val

private theorem toRoot_zero : toRoot 0 = 0 := by
  simp [toRoot]

private theorem toRoot_one : toRoot 1 = 1 := by
  unfold toRoot
  rw [Finset.sum_eq_single ⟨0, by omega⟩]
  · simp
  · intro i _ hi
    have hne : i.val ≠ 0 := fun h => hi (Fin.ext h)
    have htb : Nat.testBit 1 i.val = false := by
      rw [Nat.testBit_eq_false_of_lt]
      calc 1 < 2 ^ 1 := by norm_num
        _ ≤ 2 ^ i.val := Nat.pow_le_pow_right (by norm_num) (by omega)
    simp [htb]
  · intro h; exact (h (Finset.mem_univ _)).elim

private theorem toRoot_two : toRoot 2 = alpha := by
  unfold toRoot
  rw [Finset.sum_eq_single ⟨1, by omega⟩]
  · have h21 : Nat.testBit 2 1 = true := by decide
    simp [h21]
  · intro i _ hi
    have hne : i.val ≠ 1 := fun h => hi (Fin.ext h)
    have htb : Nat.testBit 2 i.val = false := by
      by_cases h0 : i.val = 0
      · rw [h0]; decide
      · rw [Nat.testBit_eq_false_of_lt]
        calc 2 < 2 ^ 2 := by norm_num
          _ ≤ 2 ^ i.val := Nat.pow_le_pow_right (by norm_num) (by omega)
    simp [htb]
  · intro h; exact (h (Finset.mem_univ _)).elim

private theorem toRoot_135 : toRoot 135 = alpha ^ 7 + alpha ^ 2 + alpha + 1 := by
  unfold toRoot
  let S : Finset (Fin 128) := {⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨7, by omega⟩}
  have hsub : ∀ i : Fin 128, i ∉ S →
      (if (135 : ℕ).testBit i.val then (1 : GF128) else 0) * alpha ^ i.val = 0 := by
    intro i hi
    have htb : (135 : ℕ).testBit i.val = false := by
      by_cases hlt : i.val < 8
      · have h0 : i.val ≠ 0 := fun h => hi (by simp [S, Fin.ext_iff, h])
        have h1 : i.val ≠ 1 := fun h => hi (by simp [S, Fin.ext_iff, h])
        have h2 : i.val ≠ 2 := fun h => hi (by simp [S, Fin.ext_iff, h])
        have h7 : i.val ≠ 7 := fun h => hi (by simp [S, Fin.ext_iff, h])
        interval_cases hvi : i.val
        · exact (h0 rfl).elim
        · exact (h1 rfl).elim
        · exact (h2 rfl).elim
        · decide
        · decide
        · decide
        · decide
        · exact (h7 rfl).elim
      · rw [Nat.testBit_eq_false_of_lt]
        calc 135 < 2 ^ 8 := by norm_num
          _ ≤ 2 ^ i.val := Nat.pow_le_pow_right (by norm_num) (by omega)
    simp only [htb, Bool.false_eq_true, ↓reduceIte, zero_mul]
  rw [← Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => hsub i hi)]
  have h01 : (⟨0, by omega⟩ : Fin 128) ∉ ({⟨1, by omega⟩, ⟨2, by omega⟩, ⟨7, by omega⟩} : Finset (Fin 128)) := by decide
  have h12 : (⟨1, by omega⟩ : Fin 128) ∉ ({⟨2, by omega⟩, ⟨7, by omega⟩} : Finset (Fin 128)) := by decide
  have h27 : (⟨2, by omega⟩ : Fin 128) ∉ ({⟨7, by omega⟩} : Finset (Fin 128)) := by decide
  dsimp only [S]
  rw [Finset.sum_insert h01, Finset.sum_insert h12, Finset.sum_insert h27, Finset.sum_singleton]
  have b0 : (135 : ℕ).testBit 0 = true := by decide
  have b1 : (135 : ℕ).testBit 1 = true := by decide
  have b2 : (135 : ℕ).testBit 2 = true := by decide
  have b7 : (135 : ℕ).testBit 7 = true := by decide
  simp only [b0, b1, b2, b7, ↓reduceIte, one_mul, pow_zero, pow_one]
  ring

private theorem toRoot_xor (a b : ℕ) : toRoot (a ^^^ b) = toRoot a + toRoot b := by
  unfold toRoot
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.testBit_xor]
  cases a.testBit i.val <;> cases b.testBit i.val <;> simp [char_two_add]

private theorem toRoot_xtime (a : ℕ) : toRoot (xtime a) = toRoot a * alpha := by
  unfold xtime
  have hlo : toRoot ((a % 2 ^ 127) * 2) =
      ∑ i : Fin 127, (if a.testBit i.val then (1 : GF128) else 0) * alpha ^ (i.val + 1) := by
    unfold toRoot
    rw [Fin.sum_univ_succ]
    have h0 : ((a % 2 ^ 127) * 2).testBit 0 = false := by
      simp [Nat.testBit_zero]
    simp only [Fin.val_zero, Fin.val_succ, h0, Bool.false_eq_true, ↓reduceIte, zero_mul, zero_add]
    refine Finset.sum_congr rfl fun i _ => ?_
    have htb : ((a % 2 ^ 127) * 2).testBit (i.val + 1) = a.testBit i.val := by
      have hsh : (a % 2 ^ 127) * 2 = (a % 2 ^ 127) <<< 1 := by simp [Nat.shiftLeft_eq]
      rw [hsh]
      simp only [Nat.testBit_shiftLeft, ge_iff_le, Nat.le_add_left, decide_true, Bool.true_and,
        Nat.add_sub_cancel, Nat.testBit_mod_two_pow, decide_eq_true i.isLt]
    simp only [htb]
  have hrhs : toRoot a * alpha =
      (∑ i : Fin 127, (if a.testBit i.val then (1 : GF128) else 0) * alpha ^ (i.val + 1)) +
      (if a.testBit 127 then (1 : GF128) else 0) * alpha ^ 128 := by
    unfold toRoot
    rw [Fin.sum_univ_castSucc, add_mul, Finset.sum_mul]
    simp only [Fin.val_castSucc, Fin.val_last]
    refine congrArg₂ (· + ·) ?_ (by rw [mul_assoc, ← pow_succ]; rfl)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, ← pow_succ]
    rfl
  have htop : (a / 2 ^ 127 % 2 = 1) ↔ a.testBit 127 = true := by
    rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
    simp
  split_ifs with h
  · rw [toRoot_xor, hlo, toRoot_135, hrhs, htop.mp h, if_pos rfl, one_mul, alpha_pow_128]
  · have hf : a.testBit 127 = false := by
      cases hb : a.testBit 127
      · rfl
      · exact (h (htop.mpr hb)).elim
    rw [hlo, hrhs, hf, if_neg Bool.false_ne_true, zero_mul, add_zero]

private theorem toRoot_div_two (b : ℕ) (hb : b < 2 ^ 128) :
    toRoot b = (if b % 2 = 1 then (1 : GF128) else 0) + alpha * toRoot (b / 2) := by
  have h1 : toRoot b =
      (if b.testBit 0 then (1 : GF128) else 0) +
      ∑ i : Fin 127, (if b.testBit (i.val + 1) then (1 : GF128) else 0) * alpha ^ (i.val + 1) := by
    unfold toRoot
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, pow_zero, mul_one]
    rfl
  have h2 : alpha * toRoot (b / 2) =
      ∑ i : Fin 127, (if (b / 2).testBit i.val then (1 : GF128) else 0) * alpha ^ (i.val + 1) := by
    unfold toRoot
    rw [Fin.sum_univ_castSucc, mul_add, Finset.mul_sum]
    have hhi : (b / 2).testBit 127 = false := by
      rw [Nat.testBit_eq_false_of_lt]
      omega
    simp only [Fin.val_castSucc, Fin.val_last, hhi, Bool.false_eq_true, ↓reduceIte,
      zero_mul, mul_zero, add_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc, mul_comm alpha, mul_assoc, ← pow_succ']
    rfl
  rw [h1, h2]
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [Nat.testBit_zero]
    by_cases hm : b % 2 = 1 <;> simp [hm]
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Nat.testBit_succ]

private theorem toRoot_mulLoop : ∀ fuel a b acc, fuel ≤ 128 → b < 2 ^ fuel →
    toRoot (gfMulLoop fuel a b acc) = toRoot acc + toRoot a * toRoot b
  | 0, a, b, acc, _, hb => by
      have hb0 : b = 0 := by omega
      subst hb0
      simp [gfMulLoop, toRoot_zero]
  | fuel + 1, a, b, acc, hf, hb => by
      unfold gfMulLoop
      have hb128 : b < 2 ^ 128 := lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) hf)
      have hdiv : b / 2 < 2 ^ fuel := by
        rw [Nat.pow_succ] at hb
        omega
      split_ifs with hb0 hodd
      · subst hb0; simp [toRoot_zero]
      · rw [toRoot_mulLoop fuel (xtime a) (b / 2) (acc ^^^ a) (by omega) hdiv,
          toRoot_xor, toRoot_xtime, toRoot_div_two b hb128, if_pos hodd]
        ring
      · rw [toRoot_mulLoop fuel (xtime a) (b / 2) acc (by omega) hdiv,
          toRoot_xtime, toRoot_div_two b hb128, if_neg hodd]
        ring

private theorem toRoot_mul (a b : ℕ) (hb : b < 2 ^ 128) :
    toRoot (gfMul a b) = toRoot a * toRoot b := by
  unfold gfMul
  rw [toRoot_mulLoop 128 a b 0 le_rfl hb, toRoot_zero, zero_add]

private theorem toRoot_powLoop : ∀ fuel base exp acc,
    base < 2 ^ 128 → acc < 2 ^ 128 → exp < 2 ^ fuel →
    toRoot (gfPowLoop fuel base exp acc) = toRoot acc * (toRoot base) ^ exp
  | 0, base, exp, acc, _, _, he => by
      have he0 : exp = 0 := by omega
      subst he0
      simp [gfPowLoop]
  | fuel + 1, base, exp, acc, hb, hacc, he => by
      unfold gfPowLoop
      have hdiv : exp / 2 < 2 ^ fuel := by
        rw [Nat.pow_succ] at he
        omega
      split_ifs with he0 hodd
      · subst he0; simp
      · rw [toRoot_powLoop fuel (gfMul base base) (exp / 2) (gfMul acc base)
          (gfMul_lt hb) (gfMul_lt hacc) hdiv,
          toRoot_mul acc base hb, toRoot_mul base base hb]
        have hdecomp : exp = 2 * (exp / 2) + 1 := by omega
        conv_rhs => rw [hdecomp, pow_succ, pow_mul]
        ring
      · rw [toRoot_powLoop fuel (gfMul base base) (exp / 2) acc
          (gfMul_lt hb) hacc hdiv,
          toRoot_mul base base hb]
        have hdecomp : exp = 2 * (exp / 2) := by omega
        conv_rhs => rw [hdecomp, pow_mul]
        ring

private theorem toRoot_pow (base exp : ℕ) (hb : base < 2 ^ 128) (he : exp < 2 ^ 128) :
    toRoot (gfPow base exp) = (toRoot base) ^ exp := by
  unfold gfPow
  rw [toRoot_powLoop 128 base exp 1 hb (by norm_num) he, toRoot_one, one_mul]

/-! ### Polynomial basis and injectivity of `toRoot` -/

/-- The canonical polynomial basis `1, alpha, alpha^2, ..., alpha^127` of `GF128` over `GF(2)`. -/
noncomputable def basis : Module.Basis (Fin 128) (ZMod 2) GF128 :=
  (AdjoinRoot.powerBasis gfPoly_monic.ne_zero).basis.reindex (finCongr gfPoly_natDegree)

private theorem basis_apply (i : Fin 128) : basis i = alpha ^ i.val := by
  simp only [basis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow,
    AdjoinRoot.powerBasis_gen, alpha, finCongr_symm, finCongr_apply, Fin.val_cast]

private theorem basis_zero : basis 0 = 1 := by
  rw [basis_apply]; simp

private theorem basis_one : basis 1 = alpha := by
  rw [basis_apply]; simp

private theorem toRoot_eq_sum_basis (n : ℕ) :
    toRoot n = ∑ i : Fin 128, (if n.testBit i.val then (1 : ZMod 2) else 0) • basis i := by
  unfold toRoot
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [basis_apply]
  cases n.testBit i.val <;> simp

private theorem toRoot_injective_lt {a b : ℕ} (ha : a < 2 ^ 128) (hb : b < 2 ^ 128)
    (h : toRoot a = toRoot b) : a = b := by
  rw [toRoot_eq_sum_basis a, toRoot_eq_sum_basis b] at h
  have hrepr : ∀ (f : Fin 128 → ZMod 2) (i : Fin 128),
      basis.repr (∑ j : Fin 128, f j • basis j) i = f i := by
    intro f i
    rw [map_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single i]
    · rw [map_smul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
        smul_eq_mul, mul_one]
    · intro j _ hji
      rw [map_smul, Finsupp.smul_apply, Module.Basis.repr_self,
        Finsupp.single_eq_of_ne (Ne.symm hji), smul_eq_mul, mul_zero]
    · intro hi; exact (hi (Finset.mem_univ i)).elim
  have hcoeff : ∀ i : Fin 128,
      (if a.testBit i.val then (1 : ZMod 2) else 0) =
      (if b.testBit i.val then (1 : ZMod 2) else 0) := by
    intro i
    have hi := congrArg (fun x => basis.repr x i) h
    rw [hrepr, hrepr] at hi
    exact hi
  refine Nat.eq_of_testBit_eq fun k => ?_
  by_cases hk : k < 128
  · have hc := hcoeff ⟨k, hk⟩
    cases hka : a.testBit k <;> cases hkb : b.testBit k <;> simp_all
  · have hka : a.testBit k = false := Nat.testBit_eq_false_of_lt
      (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega)))
    have hkb : b.testBit k = false := Nat.testBit_eq_false_of_lt
      (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [hka, hkb]

/-! ### Kernel evaluation of the primitive-order check -/

private theorem kernel_pow_groupOrder :
    gfPow 2 Adapter.Mdoc.groupOrder = 1 := by
  decide +kernel

private theorem kernel_pow_div_factors :
    Adapter.Mdoc.orderFactors.all (fun q => decide (gfPow 2 (Adapter.Mdoc.groupOrder / q) ≠ 1)) = true := by
  decide +kernel

private theorem alpha_pow_groupOrder : alpha ^ Adapter.Mdoc.groupOrder = 1 := by
  have h := congrArg toRoot kernel_pow_groupOrder
  rw [toRoot_pow 2 Adapter.Mdoc.groupOrder (by norm_num)
    (by unfold Adapter.Mdoc.groupOrder Adapter.Mdoc.binaryOrder; omega),
    toRoot_two, toRoot_one] at h
  exact h

private theorem alpha_pow_div_factor_ne_one {q : ℕ} (hq : q ∈ Adapter.Mdoc.orderFactors) :
    alpha ^ (Adapter.Mdoc.groupOrder / q) ≠ 1 := by
  have hne : gfPow 2 (Adapter.Mdoc.groupOrder / q) ≠ 1 :=
    of_decide_eq_true ((List.all_eq_true.mp kernel_pow_div_factors) q hq)
  intro heq
  apply hne
  apply toRoot_injective_lt (gfPow_lt (by norm_num)) (by norm_num)
  rw [toRoot_pow 2 (Adapter.Mdoc.groupOrder / q) (by norm_num)
    (lt_of_le_of_lt (Nat.div_le_self _ _)
      (by unfold Adapter.Mdoc.groupOrder Adapter.Mdoc.binaryOrder; omega)),
    toRoot_two, toRoot_one]
  exact heq

/-! ### Field structure and `generatorCheck` -/

private noncomputable def alphaUnit : GF128ˣ where
  val := alpha
  inv := alpha ^ (Adapter.Mdoc.groupOrder - 1)
  val_inv := by
    rw [← pow_succ', show Adapter.Mdoc.groupOrder - 1 + 1 = Adapter.Mdoc.groupOrder by
      unfold Adapter.Mdoc.groupOrder Adapter.Mdoc.binaryOrder; omega]
    exact alpha_pow_groupOrder
  inv_val := by
    rw [← pow_succ, show Adapter.Mdoc.groupOrder - 1 + 1 = Adapter.Mdoc.groupOrder by
      unfold Adapter.Mdoc.groupOrder Adapter.Mdoc.binaryOrder; omega]
    exact alpha_pow_groupOrder

private theorem alphaUnit_order : orderOf alphaUnit = Adapter.Mdoc.groupOrder := by
  apply orderOf_eq_of_pow_and_pow_div_prime
    (by unfold Adapter.Mdoc.groupOrder Adapter.Mdoc.binaryOrder; omega)
  · ext; simpa [alphaUnit] using alpha_pow_groupOrder
  · intro q hq hd
    have hm := ECDSA.mem_of_prime_dvd_prod Adapter.Mdoc.orderFactors_prime hq
      (Adapter.Mdoc.orderFactors_product ▸ hd)
    intro heq
    exact alpha_pow_div_factor_ne_one hm (by simpa [alphaUnit] using congrArg Units.val heq)

noncomputable instance instFintypeGF128 : Fintype GF128 :=
  Fintype.ofEquiv (Fin 128 → ZMod 2) basis.equivFun.symm

private theorem card_GF128 : Fintype.card GF128 = Adapter.Mdoc.binaryOrder := by
  simpa [Adapter.Mdoc.binaryOrder] using Fintype.card_congr basis.equivFun.toEquiv

private theorem one_ne_zero_GF128 : (1 : GF128) ≠ 0 := by
  intro h
  have h10 : (1 : ℕ) = 0 := toRoot_injective_lt (by norm_num) (by norm_num)
    (by rw [toRoot_one, toRoot_zero, h])
  omega

private theorem isField_GF128 : IsField GF128 := by
  classical
  haveI : Nontrivial GF128 := ⟨⟨1, 0, one_ne_zero_GF128⟩⟩
  refine ⟨⟨1, 0, one_ne_zero_GF128⟩, mul_comm, ?_⟩
  intro x hx
  -- Every nonzero element is a unit since `|GF128ˣ| ≥ orderOf alphaUnit = 2^128 - 1 = |GF128 \ {0}|`.
  let f : GF128ˣ → {y : GF128 // y ≠ 0} := fun u => ⟨u.val, u.ne_zero⟩
  have hf_inj : Function.Injective f := fun u v huv => Units.ext (congrArg Subtype.val huv)
  have hcard_nz : Fintype.card {y : GF128 // y ≠ 0} = Adapter.Mdoc.groupOrder := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, card_GF128]
    rfl
  have hcard_le : Fintype.card GF128ˣ ≤ Adapter.Mdoc.groupOrder := by
    rw [← hcard_nz]
    exact Fintype.card_le_of_injective f hf_inj
  have hcard_ge : Adapter.Mdoc.groupOrder ≤ Fintype.card GF128ˣ := by
    rw [← alphaUnit_order]
    exact Nat.le_of_dvd Fintype.card_pos orderOf_dvd_card
  have hcard_eq : Fintype.card GF128ˣ = Fintype.card {y : GF128 // y ≠ 0} := by
    omega
  have hf_surj : Function.Surjective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf_inj, hcard_eq⟩ |>.2
  obtain ⟨u, hu⟩ := hf_surj ⟨x, hx⟩
  exact ⟨u.inv, by simpa [f, Subtype.ext_iff] using congrArg (· * u.inv) (congrArg Subtype.val hu) |>.symm.trans u.val_inv⟩

/-- `GF128 = F_2[X] / (X^128 + X^7 + X^2 + X + 1)` is a field, proved in the kernel. -/
noncomputable instance instFieldGF128 : Field GF128 :=
  isField_GF128.toField

/-- The concrete polynomial basis has coordinate 0 equal to `1`. -/
theorem pivot_zero : basis 0 = 1 := basis_zero

/-- The concrete polynomial generator `X` passes `Adapter.Mdoc.generatorCheck`, proved
in the Lean kernel without `native_decide`. -/
theorem generatorCheck_true [DecidableEq GF128] :
    Adapter.Mdoc.generatorCheck (MdocRuntime.polynomialX basis) = true := by
  rw [Adapter.Mdoc.generatorCheck, List.all_eq_true]
  intro q hq
  rw [decide_eq_true_iff]
  intro heq
  apply alpha_pow_div_factor_ne_one hq
  have hval := congrArg Units.val heq
  simpa [MdocRuntime.polynomialX, basis_one] using hval

/-- The concrete polynomial generator `X` has exact multiplicative order `2^128 - 1`. -/
theorem polynomialX_order [DecidableEq GF128] :
    orderOf (MdocRuntime.polynomialX basis) = Adapter.Mdoc.groupOrder :=
  Adapter.Mdoc.primitive_order_of_check (MdocRuntime.field_card basis)
    (MdocRuntime.polynomialX basis) generatorCheck_true

end LfzkV2.Current.ConcreteGF128
