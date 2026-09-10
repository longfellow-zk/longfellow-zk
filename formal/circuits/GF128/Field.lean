import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import GF128.Poly

/-!
# The Nat model computes the field

`GF128/Poly.lean` is arithmetic on bit patterns: `add` is xor, `mul` is the shift-and-add ladder
of `gf2_128.rs`. This file says those operations *are* field operations, by exhibiting the map
that reads a bit pattern as a polynomial in a designated element α and showing it is a ring
homomorphism.

The point is to import the kernel-checked facts of `Poly.lean` — `ord α = 2^128 − 1` above all —
into an abstract `[Field F] [CharP F 2]`, which is where the meaning lemmas have to live. That is
the same shape as the p256 bridges, which never construct their field either; the difference is
that in characteristic 2 a `Nat` cast reaches only `0` and `1`, so the constant map has to be
`eval` rather than `Nat.cast`.

That this is the right map is not a guess. The emitted constant table for the GF(2^128) SHA-256
artifact opens

```
0x1, 0x0, 0x3, 0x5, 0x11, 0x101, 0x10001, 0x100000001, 0x10000000000000001, 0x86, 0x4014, …
```

which is `1, 0`, then `α^(2^i) + 1` for `i = 0 … 7` — the adder's `basis_minus_one`
(`analog_adder/src/circuit.rs:158`). `0x86` is `α^128 + 1` already reduced through `P`, so the
table only makes sense under `eval`.
-/

namespace GF128

variable {F : Type*} [CommRing F] [CharP F 2]

/-- `eval α n`: the polynomial whose coefficient bits are `n`, evaluated at `α`, by Horner from
    the low bit. Never computed — `F` is abstract — so well-founded recursion is harmless here. -/
noncomputable def eval (α : F) (n : Nat) : F :=
  if h : n = 0 then 0
  else (if n.testBit 0 then (1 : F) else 0) + α * eval α (n / 2)
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) Nat.one_lt_two

@[simp] theorem eval_zero (α : F) : eval α 0 = 0 := by rw [eval]; simp

theorem eval_step (α : F) {n : Nat} (h : n ≠ 0) :
    eval α n = (if n.testBit 0 then (1 : F) else 0) + α * eval α (n / 2) := by
  rw [eval]; simp [h]

@[simp] theorem eval_one (α : F) : eval α 1 = 1 := by
  rw [eval_step α Nat.one_ne_zero]
  norm_num

/-! ### `eval` is additive

Xor is addition because in characteristic 2 a repeated coefficient cancels. -/

private theorem xor_div_two (a b : Nat) : (a ^^^ b) / 2 = a / 2 ^^^ b / 2 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp [Nat.testBit_div_two, Nat.testBit_xor]

private theorem xor_eq_zero_iff (a b : Nat) : a ^^^ b = 0 ↔ a = b := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    have hb := congrArg (fun n => Nat.testBit n i) h
    simp only [Nat.testBit_xor, Nat.zero_testBit] at hb
    revert hb
    cases Nat.testBit a i <;> cases Nat.testBit b i <;> simp
  · rintro rfl
    simp

theorem eval_add (α : F) (a b : Nat) : eval α (a ^^^ b) = eval α a + eval α b := by
  induction a using Nat.strong_induction_on generalizing b with
  | _ a ih =>
    rcases Nat.eq_zero_or_pos a with rfl | hapos
    · simp
    rcases Nat.eq_zero_or_pos b with rfl | hbpos
    · simp
    have ha : a ≠ 0 := Nat.pos_iff_ne_zero.mp hapos
    have hb : b ≠ 0 := Nat.pos_iff_ne_zero.mp hbpos
    have hlt : a / 2 < a := Nat.div_lt_self hapos Nat.one_lt_two
    by_cases hz : a ^^^ b = 0
    · have hab : a = b := (xor_eq_zero_iff a b).mp hz
      subst hab
      simp [hz, CharTwo.add_self_eq_zero]
    · rw [eval_step α hz, eval_step α ha, eval_step α hb, xor_div_two,
        ih (a / 2) hlt (b / 2), Nat.testBit_xor]
      cases hta : Nat.testBit a 0 <;> cases htb : Nat.testBit b 0 <;>
        simp [mul_add] <;>
        first
          | ring1
          | linear_combination (CharTwo.add_self_eq_zero (1 : F))
          | linear_combination -(CharTwo.add_self_eq_zero (1 : F))

/-! ### `eval` on the pieces the reduction uses -/

theorem eval_two_pow (α : F) : ∀ k, eval α (2 ^ k) = α ^ k
  | 0 => by simpa using eval_one α
  | k + 1 => by
      have hne : (2 : Nat) ^ (k + 1) ≠ 0 := (Nat.two_pow_pos (k + 1)).ne'
      have hbit : Nat.testBit (2 ^ (k + 1)) 0 = false := by
        simp [Nat.testBit_two_pow]
      have hd : (2 : Nat) ^ (k + 1) / 2 = 2 ^ k := by
        rw [pow_succ]; omega
      rw [eval_step α hne, hbit, hd, eval_two_pow α k]
      simp only [Bool.false_eq_true, if_false, zero_add, pow_succ]
      ring

@[simp] theorem eval_alpha (α : F) : eval α 2 = α := by
  simpa using eval_two_pow α 1

/-- The Horner step, with no side condition: at `n = 0` both sides are `0`. -/
theorem eval_step' (α : F) (n : Nat) :
    eval α n = (if n.testBit 0 then (1 : F) else 0) + α * eval α (n / 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · simp
  · exact eval_step α (Nat.pos_iff_ne_zero.mp h)

theorem eval_double (α : F) (a : Nat) : eval α (a * 2) = α * eval α a := by
  rw [eval_step' α (a * 2)]
  have hb : (a * 2).testBit 0 = false := by
    simp [Nat.testBit_zero, Nat.mul_mod_left]
  have hd : a * 2 / 2 = a := by omega
  rw [hb, hd]
  simp

/-- `P(α) = 0`, in the `+`-only form characteristic 2 gives. -/
theorem eval_rp (α : F) : eval α rp = α ^ 7 + α ^ 2 + α + 1 := by
  have h : rp = 2 ^ 7 ^^^ (2 ^ 2 ^^^ (2 ^ 1 ^^^ 2 ^ 0)) := by decide
  rw [h]
  simp only [eval_add, eval_two_pow]
  ring

/-! ### The reduction step

`xtime` is multiplication by `α`, provided the argument is in range: doubling can set bit 128 and
nothing above it, and `P(α) = 0` lets that bit be traded for `rp`. -/

private theorem xor_lt (n : Nat) {a b : Nat} (ha : a < 2 ^ n) (hb : b < 2 ^ n) :
    a ^^^ b < 2 ^ n := Nat.xor_lt_two_pow ha hb

private theorem shiftRight_xor (a b n : Nat) : (a ^^^ b) >>> n = (a >>> n) ^^^ (b >>> n) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp [Nat.testBit_shiftRight, Nat.testBit_xor]

private theorem shiftLeft_one (a : Nat) : a <<< 1 = a * 2 := by simp [Nat.shiftLeft_eq]

private theorem one_shiftLeft_w : (1 : Nat) <<< w = 2 ^ 128 := by simp [Nat.shiftLeft_eq, w]

/-- Clearing the one bit above the field: the top bit of a doubled in-range element. -/
private theorem xor_high_bit_lt {x : Nat} (h1 : 2 ^ 128 ≤ x) (h2 : x < 2 ^ 129) :
    x ^^^ 2 ^ 128 < 2 ^ 128 := by
  have hx : x >>> 128 = 1 := by
    rw [Nat.shiftRight_eq_div_pow]
    omega
  have hp : (2 : Nat) ^ 128 >>> 128 = 1 := by
    rw [Nat.shiftRight_eq_div_pow]
    omega
  have hz : (x ^^^ 2 ^ 128) >>> 128 = 0 := by
    rw [shiftRight_xor, hx, hp]
    decide
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff] at hz
  omega

/-- `xtime` below the reduction threshold. -/
theorem xtime_eq_of_lt {a : Nat} (h : a * 2 < 2 ^ 128) : xtime a = a * 2 := by
  have hc : a <<< 1 >>> w = 0 := by
    rw [shiftLeft_one, Nat.shiftRight_eq_div_pow]
    simp only [w]
    omega
  unfold xtime
  rw [if_pos hc, shiftLeft_one]

/-- `xtime` at or above it: the `x^128` term is traded for `P`'s tail. -/
theorem xtime_eq_of_ge {a : Nat} (ha : a < 2 ^ 128) (h : 2 ^ 128 ≤ a * 2) :
    xtime a = (a * 2 ^^^ 2 ^ 128) ^^^ rp := by
  have hc : a <<< 1 >>> w ≠ 0 := by
    rw [shiftLeft_one, Nat.shiftRight_eq_div_pow]
    simp only [w]
    omega
  unfold xtime
  rw [if_neg hc, shiftLeft_one, one_shiftLeft_w]

theorem xtime_lt {a : Nat} (ha : a < 2 ^ 128) : xtime a < 2 ^ 128 := by
  by_cases h : a * 2 < 2 ^ 128
  · rw [xtime_eq_of_lt h]; exact h
  · rw [xtime_eq_of_ge ha (by omega)]
    exact xor_lt 128 (xor_high_bit_lt (by omega) (by omega)) (by decide)

theorem eval_xtime (α : F) (hroot : α ^ 128 = α ^ 7 + α ^ 2 + α + 1)
    {a : Nat} (ha : a < 2 ^ 128) : eval α (xtime a) = α * eval α a := by
  by_cases h : a * 2 < 2 ^ 128
  · rw [xtime_eq_of_lt h, eval_double]
  · rw [xtime_eq_of_ge ha (by omega), eval_add, eval_add, eval_two_pow, eval_rp, eval_double,
      hroot]
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination (α ^ 7 + α ^ 2 + α + 1) * h2

/-! ### The ladder is multiplication -/

private theorem and_one (b : Nat) : b &&& 1 = if b.testBit 0 then 1 else 0 := by
  rw [Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one b with h | h <;> simp [Nat.testBit_zero, h]

private theorem mod_two_pow_succ_div (b n : Nat) : b % 2 ^ (n + 1) / 2 = b / 2 % 2 ^ n := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp [Nat.testBit_div_two, Nat.testBit_mod_two_pow, Nat.succ_lt_succ_iff]

private theorem mod_two_pow_testBit_zero (b n : Nat) :
    (b % 2 ^ (n + 1)).testBit 0 = b.testBit 0 := by
  simp [Nat.testBit_mod_two_pow]

theorem mulAux_lt : ∀ (n a b acc : Nat), a < 2 ^ 128 → acc < 2 ^ 128 →
    mulAux n a b acc < 2 ^ 128
  | 0, _, _, _, _, hacc => hacc
  | n + 1, a, b, acc, ha, hacc => by
      refine mulAux_lt n (xtime a) (b >>> 1) _ (xtime_lt ha) ?_
      split
      · exact xor_lt 128 hacc ha
      · exact hacc

theorem eval_mulAux (α : F) (hroot : α ^ 128 = α ^ 7 + α ^ 2 + α + 1) :
    ∀ (n a b acc : Nat), a < 2 ^ 128 →
      eval α (mulAux n a b acc) = eval α acc + eval α a * eval α (b % 2 ^ n)
  | 0, a, b, acc, _ => by
      simp only [mulAux, pow_zero, Nat.mod_one, eval_zero, mul_zero, add_zero]
  | n + 1, a, b, acc, ha => by
      rw [show mulAux (n + 1) a b acc
            = mulAux n (xtime a) (b >>> 1) (if b &&& 1 = 1 then acc ^^^ a else acc) from rfl,
        eval_mulAux α hroot n (xtime a) (b >>> 1) _ (xtime_lt ha),
        eval_xtime α hroot ha]
      have hshift : b >>> 1 = b / 2 := by simp [Nat.shiftRight_eq_div_pow]
      have hstep : eval α (b % 2 ^ (n + 1))
          = (if b.testBit 0 then (1 : F) else 0) + α * eval α (b / 2 % 2 ^ n) := by
        rw [eval_step' α (b % 2 ^ (n + 1)), mod_two_pow_testBit_zero, mod_two_pow_succ_div]
      rw [hshift, hstep, and_one]
      cases hb0 : b.testBit 0 <;> simp [eval_add] <;> ring

theorem mul_lt {a : Nat} (ha : a < 2 ^ 128) (b : Nat) : mul a b < 2 ^ 128 :=
  mulAux_lt 128 a b 0 ha (by decide)

/-- **The Nat ladder computes the field product.** -/
theorem eval_mul (α : F) (hroot : α ^ 128 = α ^ 7 + α ^ 2 + α + 1)
    {a b : Nat} (ha : a < 2 ^ 128) (hb : b < 2 ^ 128) :
    eval α (mul a b) = eval α a * eval α b := by
  rw [show mul a b = mulAux 128 a b 0 from rfl, eval_mulAux α hroot 128 a b 0 ha,
    Nat.mod_eq_of_lt hb]
  simp

theorem eval_sq (α : F) (hroot : α ^ 128 = α ^ 7 + α ^ 2 + α + 1)
    {a : Nat} (ha : a < 2 ^ 128) : eval α (sq a) = eval α a * eval α a :=
  eval_mul α hroot ha ha

/-! ### Powers -/

theorem powAux_lt : ∀ (n a e acc : Nat), a < 2 ^ 128 → acc < 2 ^ 128 →
    powAux n a e acc < 2 ^ 128
  | 0, _, _, _, _, hacc => hacc
  | n + 1, a, e, acc, ha, hacc => by
      rw [show powAux (n + 1) a e acc = if e = 0 then acc else
        powAux n (mul a a) (e >>> 1) (if e &&& 1 = 1 then mul acc a else acc) from rfl]
      split
      · exact hacc
      · refine powAux_lt n (mul a a) (e >>> 1) _ (mul_lt ha a) ?_
        split
        · exact mul_lt hacc a
        · exact hacc

theorem pow_lt {a : Nat} (ha : a < 2 ^ 128) (e : Nat) : pow a e < 2 ^ 128 :=
  powAux_lt 160 a e 1 ha (by decide)

theorem eval_powAux (α : F) (hroot : α ^ 128 = α ^ 7 + α ^ 2 + α + 1) :
    ∀ (n a e acc : Nat), a < 2 ^ 128 → acc < 2 ^ 128 → e < 2 ^ n →
      eval α (powAux n a e acc) = eval α acc * eval α a ^ e
  | 0, a, e, acc, _, _, he => by
      have h0 : e = 0 := by simpa using he
      subst h0
      simp [powAux]
  | n + 1, a, e, acc, ha, hacc, he => by
      rw [show powAux (n + 1) a e acc = if e = 0 then acc else
        powAux n (mul a a) (e >>> 1) (if e &&& 1 = 1 then mul acc a else acc) from rfl]
      split
      · next h => subst h; simp
      · have hshift : e >>> 1 = e / 2 := by simp [Nat.shiftRight_eq_div_pow]
        have hlt : e / 2 < 2 ^ n := by
          have h2 : e < 2 ^ n * 2 := by rw [← pow_succ]; exact he
          omega
        have hacc' : (if e &&& 1 = 1 then mul acc a else acc) < 2 ^ 128 := by
          split
          · exact mul_lt hacc a
          · exact hacc
        rw [hshift, eval_powAux α hroot n (mul a a) (e / 2) _ (mul_lt ha a) hacc' hlt,
          eval_mul α hroot ha ha, and_one]
        have he2 : 2 * (e / 2) + (if e.testBit 0 then 1 else 0) = e := by
          rcases Nat.mod_two_eq_zero_or_one e with h | h <;>
            simp only [Nat.testBit_zero, h] <;> simp <;> omega
        have hx : eval α a ^ e
            = (eval α a * eval α a) ^ (e / 2) * eval α a ^ (if e.testBit 0 then 1 else 0) := by
          rw [← pow_two, ← pow_mul, ← pow_add, he2]
        rw [hx]
        cases h0 : e.testBit 0 <;>
          (try simp only [h0, Bool.false_eq_true, reduceIte, pow_zero, pow_one, mul_one]) <;>
          (try norm_num) <;>
          first
            | ring1
            | (rw [eval_mul α hroot hacc ha]; ring1)

/-- **The Nat ladder computes field powers.** Every exponent used anywhere is below `2^160`. -/
theorem eval_pow (α : F) (hroot : α ^ 128 = α ^ 7 + α ^ 2 + α + 1)
    {a : Nat} (ha : a < 2 ^ 128) {e : Nat} (he : e < 2 ^ 160) :
    eval α (pow a e) = eval α a ^ e := by
  rw [show pow a e = powAux 160 a e 1 from rfl,
    eval_powAux α hroot 160 a e 1 ha (by decide) he]
  simp

/-! ## What it takes for `α` to present `F` as GF(2^128)

Two facts, both true of `Gf2_128(2)` in the deployed code. `root` is `P(α) = 0`, written without
a minus because the characteristic is 2. `indep` says the 128 powers of α are linearly independent
over F₂ — equivalently, that `eval α` is injective on bit patterns — which is what makes the
kernel-checked computations of `Poly.lean` say anything about `F`.

Both are **theorems**, not assumptions: `GF128/Irred.lean` proves `P` irreducible and derives
`indep` from `root` alone, so `isGen_of_root` builds an `IsGen` from `P(α) = 0` over any
nontrivial commutative ring of characteristic 2. `IsGen` survives as a convenient bundle; use
that constructor rather than supplying the fields by hand. -/

structure IsGen (α : F) : Prop where
  root : α ^ 128 = α ^ 7 + α ^ 2 + α + 1
  indep : ∀ n, n < 2 ^ 128 → eval α n = 0 → n = 0

theorem eval_injOn (α : F) (h : IsGen α) {m n : Nat} (hm : m < 2 ^ 128) (hn : n < 2 ^ 128)
    (heq : eval α m = eval α n) : m = n := by
  have hz : eval α (m ^^^ n) = 0 := by
    rw [eval_add, heq]
    exact CharTwo.add_self_eq_zero _
  exact (xor_eq_zero_iff m n).mp (h.indep _ (xor_lt 128 hm hn) hz)

/-! ### The order certificate, transferred

`Poly.alpha_pow_N` and `Poly.alpha_pow_cofactor_ne_one` are `decide +kernel` facts about bit
patterns. Through `eval_pow` and `eval_injOn` they become facts about `α` in `F`. -/

/-- `eval` sends the bit pattern `2` — the generator `Gf2_128(2)` — to `α`. -/
theorem eval_alpha' (α : F) : eval α alpha = α := eval_alpha α

theorem alpha_pow_N_eq_one (α : F) (h : IsGen α) : α ^ N = 1 := by
  have hp := eval_pow α h.root (a := alpha) (by decide) (e := N) (by decide)
  rw [alpha_pow_N, eval_alpha'] at hp
  simpa using hp.symm

theorem alpha_pow_div_ne_one (α : F) (h : IsGen α) {q : Nat} (hq : q ∈ NFactors) :
    α ^ (N / q) ≠ 1 := by
  intro hc
  have hne : pow alpha (N / q) ≠ 1 := by
    have hall := alpha_pow_cofactor_ne_one
    rw [List.all_eq_true] at hall
    have := hall q hq
    simpa using this
  refine hne (eval_injOn α h (pow_lt (by decide) _) (by decide) ?_)
  have hp := eval_pow α h.root (a := alpha) (by decide) (e := N / q)
    (by have : N / q ≤ N := Nat.div_le_self _ _
        have : N < 2 ^ 160 := by decide
        omega)
  rw [hp, eval_alpha']
  simpa using hc

end GF128
