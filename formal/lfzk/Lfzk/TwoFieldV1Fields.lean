import Lfzk.WPoly
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime
import Mathlib.FieldTheory.Finite.GaloisField
import Lfzk.LigeroV1Rows

/-!
# The two fields exist

A two-field V1 row quantifies over a field `F₁` with `Fintype.card F₁ = p` (`P-256`'s base field,
`LigeroV1Rows.p256Order`) and a field `F₂` with `Fintype.card F₂ = 2^128`, each with a
`SumcheckInterp` instance.  If no such field existed, every theorem at the row would hold vacuously.
This file exhibits both:

* `p256Order_prime`: `p` is prime, by a **Pratt certificate** checked by the kernel (`decide`, no
  `native_decide`).  `prime_of_pratt` is Mathlib's `lucas_primality` with the modular powers computed
  by `powModAux`, a square-and-multiply evaluator whose correctness is `powModAux_eq`.  The
  certificate is seven nested primes, from 256 bits down to 23 bits; primes below `2^20` are
  `norm_num`'s.
* `ZMod p256Order` is then a field of cardinality `p` with interpolation points `0, 1, 2`
  (`p256_card`, `instSumcheckInterpP256`);
* `GaloisField 2 128` is a field of cardinality `2^128` (`gf128_card`), with interpolation points
  `0, 1, x` for some `x ∉ {0, 1}` (`instSumcheckInterpGF128`).

The Reed–Solomon domains then exist at both fields by `LigeroFamily.ReedSolomon.Domain.ofCardLE`
(`Lfzk.TwoFieldV1Rows.domain_exists_ecdsa`, `domain_exists_sha`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.TwoFieldV1Fields

open Lfzk.LigeroV1Rows (p256Order)

/-! ## Modular exponentiation the kernel can evaluate -/

/-- `a ^ b % n` by square-and-multiply, with explicit fuel so that it is structurally recursive. -/
def powModAux : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, n => 1 % n
  | fuel + 1, a, b, n =>
      if b = 0 then 1 % n
      else if b % 2 = 0 then powModAux fuel (a * a % n) (b / 2) n
      else a * powModAux fuel (a * a % n) (b / 2) n % n

/-- **`powModAux` is modular exponentiation**, whenever the exponent fits in the fuel's bits. -/
theorem powModAux_eq : ∀ (fuel a b n : ℕ), b < 2 ^ fuel → powModAux fuel a b n = a ^ b % n
  | 0, a, b, n, hb => by
      have : b = 0 := by simpa using hb
      subst this
      simp [powModAux]
  | fuel + 1, a, b, n, hb => by
      have hb2 : b / 2 < 2 ^ fuel := by
        rw [pow_succ] at hb
        omega
      have ih := powModAux_eq fuel (a * a % n) (b / 2) n hb2
      have hsq : (a * a % n) ^ (b / 2) % n = (a * a) ^ (b / 2) % n := by
        rw [← Nat.pow_mod]
      by_cases h0 : b = 0
      · subst h0
        simp [powModAux]
      · by_cases he : b % 2 = 0
        · simp only [powModAux, if_neg h0, if_pos he, ih, hsq]
          congr 1
          rw [← sq, ← pow_mul]
          congr 1
          omega
        · simp only [powModAux, if_neg h0, if_neg he, ih, hsq]
          have hb' : b = 2 * (b / 2) + 1 := by omega
          rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
          congr 1
          conv_rhs => rw [hb']
          rw [pow_succ, pow_mul, sq, mul_comm]

/-! ## Pratt certificates -/

/--
**A Pratt certificate proves primality.**  `lucas_primality` at `a`, with `p - 1` factored as
`∏ qᵢ ^ eᵢ` over primes `qᵢ`, and the modular powers checked by `powModAux`.
-/
theorem prime_of_pratt (p a : ℕ) (fs : List (ℕ × ℕ)) (hp : 2 ≤ p) (hlt : p < 2 ^ 512)
    (hprod : (fs.map fun f => f.1 ^ f.2).prod = p - 1)
    (hprimes : ∀ f ∈ fs, f.1.Prime)
    (hfermat : powModAux 512 a (p - 1) p = 1)
    (hwit : ∀ f ∈ fs, powModAux 512 a ((p - 1) / f.1) p ≠ 1) : p.Prime := by
  have key : ∀ k, k < 2 ^ 512 →
      (((a : ℕ) : ZMod p) ^ k = 1 ↔ powModAux 512 a k p = 1) := by
    intro k hk
    rw [powModAux_eq 512 a k p hk, ← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff',
      Nat.one_mod_eq_one.mpr (by omega)]
  refine lucas_primality p (a : ZMod p) ((key _ (by omega)).mpr hfermat) ?_
  intro q hq hdvd
  rw [← hprod] at hdvd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hdvd
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hx
  have hqf : q = f.1 :=
    (Nat.prime_dvd_prime_iff_eq hq (hprimes f hf)).mp (hq.dvd_of_dvd_pow hqx)
  subst hqf
  intro h1
  exact hwit f hf ((key _ (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))).mp h1)

/-! ## The certificate for `p` -/

theorem prime_6700417 : Nat.Prime 6700417 := by
  refine prime_of_pratt 6700417 5 [(2, 7), (3, 1), (17449, 1)] (by norm_num) (by decide +kernel)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl <;> norm_num

theorem prime_204061199 : Nat.Prime 204061199 := by
  refine prime_of_pratt 204061199 11 [(2, 1), (11, 1), (23, 1), (107, 1), (3769, 1)]
    (by norm_num) (by decide +kernel)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem prime_34282281433 : Nat.Prime 34282281433 := by
  refine prime_of_pratt 34282281433 17 [(2, 3), (3, 1), (7, 1), (204061199, 1)]
    (by norm_num) (by decide +kernel)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · exact prime_204061199

theorem prime_66417393611 : Nat.Prime 66417393611 := by
  refine prime_of_pratt 66417393611 6 [(2, 1), (5, 1), (53, 1), (173, 1), (197, 1), (3677, 1)]
    (by norm_num) (by decide +kernel)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem prime_11290956913871 : Nat.Prime 11290956913871 := by
  refine prime_of_pratt 11290956913871 13 [(2, 1), (5, 1), (17, 1), (66417393611, 1)]
    (by norm_num) (by decide +kernel)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · exact prime_66417393611

theorem prime_46076956964474543 : Nat.Prime 46076956964474543 := by
  refine prime_of_pratt 46076956964474543 5
    [(2, 1), (23, 1), (18169, 1), (78283, 1), (704251, 1)]
    (by norm_num) (by decide +kernel)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem prime_q150 : Nat.Prime 774023187263532362759620327192479577272145303 := by
  refine prime_of_pratt 774023187263532362759620327192479577272145303 3
    [(2, 1), (3, 2), (2411, 1), (34282281433, 1), (11290956913871, 1), (46076956964474543, 1)]
    (by norm_num) (by decide +kernel)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · exact prime_34282281433
  · exact prime_11290956913871
  · exact prime_46076956964474543

theorem prime_q160 : Nat.Prime 835945042244614951780389953367877943453916927241 := by
  refine prime_of_pratt 835945042244614951780389953367877943453916927241 11
    [(2, 3), (3, 3), (5, 1), (774023187263532362759620327192479577272145303, 1)]
    (by norm_num) (by decide +kernel)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · exact prime_q150

/-- **`P-256`'s base field order is prime.** -/
theorem p256Order_prime : Nat.Prime p256Order := by
  unfold p256Order
  refine prime_of_pratt
    115792089210356248762697446949407573530086143415290314195533631308867097853951 6
    [(2, 1), (3, 1), (5, 2), (17, 1), (257, 1), (641, 1), (1531, 1), (65537, 1), (490463, 1),
      (6700417, 1), (835945042244614951780389953367877943453916927241, 1)]
    (by norm_num) (by decide +kernel)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact prime_6700417
  · exact prime_q160

/-! ## The ECDSA side's field: `ZMod p` -/

instance factP256 : Fact (Nat.Prime p256Order) := ⟨p256Order_prime⟩

/-- `F₁`: `P-256`'s base field. -/
abbrev FP256 := ZMod p256Order

theorem p256_card : Fintype.card FP256 = p256Order := ZMod.card p256Order

theorem p256_two_lt : 2 < p256Order := by unfold p256Order; norm_num

/-- The third interpolation point of a prime field is `2` (`Field::poly_evaluation_point(2)`). -/
instance instSumcheckInterpP256 : SumcheckInterp FP256 where
  pts := ![0, 1, 2]
  pts_inj := by
    have h2 : (2 : FP256) ≠ 0 := by
      intro h
      have := (ZMod.natCast_eq_zero_iff 2 p256Order).mp (by exact_mod_cast h)
      exact absurd (Nat.le_of_dvd (by norm_num) this) (by have := p256_two_lt; omega)
    have h21 : (2 : FP256) ≠ 1 := by
      intro h
      have h' : ((1 : ℕ) : FP256) = 0 := by
        have : (2 : FP256) - 1 = 0 := by rw [h, sub_self]
        rw [show (2 : FP256) - 1 = 1 by norm_num] at this
        exact_mod_cast this
      exact one_ne_zero (by exact_mod_cast h')
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  pts_zero := rfl
  pts_one := rfl

/-! ## The SHA side's field: `GF(2^128)` -/

/-- `F₂`: the binary field of `2^128` elements. -/
abbrev GF128 := GaloisField 2 128

noncomputable instance : Fintype GF128 := Fintype.ofFinite _

noncomputable instance : DecidableEq GF128 := Classical.decEq _

theorem gf128_card : Fintype.card GF128 = 2 ^ 128 := by
  rw [Fintype.card_eq_nat_card]
  exact GaloisField.card 2 128 (by norm_num)

/-- Some element of `GF(2^128)` is neither `0` nor `1`. -/
theorem gf128_exists_third : ∃ x : GF128, x ≠ 0 ∧ x ≠ 1 := by
  by_contra h
  have hsub : (Finset.univ : Finset GF128) ⊆ {0, 1} := fun x _ => by
    by_cases hx : x = 0
    · simp [hx]
    · by_cases hx1 : x = 1
      · simp [hx1]
      · exact absurd ⟨x, hx, hx1⟩ h
  have := Finset.card_le_card hsub
  rw [Finset.card_univ, gf128_card] at this
  have h2 : ({0, 1} : Finset GF128).card ≤ 2 := Finset.card_le_two
  omega

/-- Interpolation points `0, 1, x` for a chosen `x ∉ {0, 1}`. -/
noncomputable instance instSumcheckInterpGF128 : SumcheckInterp GF128 where
  pts := ![0, 1, gf128_exists_third.choose]
  pts_inj := by
    obtain ⟨h0, h1⟩ := gf128_exists_third.choose_spec
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  pts_zero := rfl
  pts_one := rfl

end Lfzk.TwoFieldV1Fields
