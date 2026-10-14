module

public import Mathlib

/-!
# Kernel-reducible modular exponentiation

`lucas_primality` needs `a ^ (p - 1)` in `ZMod p`, but `Monoid.npow` is `npowRec` — linear in
the exponent, so hopeless at 2^256.  Binary exponentiation recursing on `e / 2` would be
*well-founded*, and well-founded recursion is opaque to kernel reduction (the same trap that
killed the `List.mergeSort` route earlier in this project).  Recursing structurally on a `fuel`
argument keeps it reducible by `decide`, and `Nat` multiplication and `%` are GMP-accelerated,
so a 256-bit exponentiation is a few hundred fast operations.
-/

@[expose] public section

namespace ECDSA

/-- `powMod n fuel b e = b ^ e % n`, provided `e < 2 ^ fuel`. -/
def powMod (n : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 1 % n
  | fuel + 1, b, e =>
      if e = 0 then 1 % n
      else
        let half := powMod n fuel (b * b % n) (e / 2)
        if e % 2 = 0 then half else half * b % n

theorem powMod_eq (n : Nat) :
    ∀ (fuel b e : Nat), e < 2 ^ fuel → powMod n fuel b e = b ^ e % n := by
  intro fuel
  induction fuel with
  | zero =>
      intro b e he
      simp only [pow_zero, Nat.lt_one_iff] at he
      subst he
      simp [powMod]
  | succ fuel ih =>
      intro b e he
      rw [powMod]
      by_cases h0 : e = 0
      · simp [h0]
      · rw [if_neg h0]
        have hhalf : e / 2 < 2 ^ fuel := by
          have : e < 2 ^ (fuel + 1) := he
          omega
        rw [ih (b * b % n) (e / 2) hhalf]
        have hsq : (b * b % n) ^ (e / 2) % n = (b ^ 2) ^ (e / 2) % n := by
          conv_rhs => rw [Nat.pow_mod]
          rw [pow_two]
        by_cases hpar : e % 2 = 0
        · rw [if_pos hpar, hsq, ← pow_mul]
          congr 2
          omega
        · rw [if_neg hpar, hsq]
          have hb : (b ^ 2) ^ (e / 2) % n * b % n = (b ^ 2) ^ (e / 2) * b % n := by
            conv_lhs => rw [Nat.mul_mod]
            conv_rhs => rw [Nat.mul_mod]
            simp
          have h2 : 2 * (e / 2) + 1 = e := by omega
          rw [hb, ← pow_mul, ← pow_succ, h2]

/-! ## Bridging `powMod` to `ZMod`, and the Lucas side conditions -/

theorem cast_pow_eq_iff {p a k : ℕ} (hp : 1 < p) :
    ((a : ZMod p)) ^ k = 1 ↔ a ^ k % p = 1 := by
  rw [← Nat.cast_pow]
  constructor
  · intro h
    have : ((a ^ k : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by simpa using h
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mp this
    simpa [Nat.ModEq, Nat.mod_eq_of_lt hp] using this
  · intro h
    have : (a ^ k) % p = 1 % p := by rw [h, Nat.mod_eq_of_lt hp]
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr this
    simpa using this

theorem cast_pow_eq_one {p a k fuel : ℕ} (hp : 1 < p) (hk : k < 2 ^ fuel)
    (h : powMod p fuel a k = 1) : ((a : ZMod p)) ^ k = 1 :=
  (cast_pow_eq_iff hp).mpr (by rwa [powMod_eq p fuel a k hk] at h)

theorem cast_pow_ne_one {p a k fuel : ℕ} (hp : 1 < p) (hk : k < 2 ^ fuel)
    (h : powMod p fuel a k ≠ 1) : ((a : ZMod p)) ^ k ≠ 1 := fun hc =>
  h (by rw [powMod_eq p fuel a k hk]; exact (cast_pow_eq_iff hp).mp hc)

/-- Every prime dividing a product of primes is one of them.  This is what turns
    `lucas_primality`'s quantifier over *all* prime divisors of `p - 1` into a finite check
    against an explicit factorisation. -/
theorem mem_of_prime_dvd_prod : ∀ {qs : List ℕ}, (∀ q ∈ qs, Nat.Prime q) →
    ∀ {q : ℕ}, Nat.Prime q → q ∣ qs.prod → q ∈ qs
  | [], _, q, hq, hd => absurd (Nat.eq_one_of_dvd_one (by simpa using hd)) hq.one_lt.ne'
  | r :: rs, hall, q, hq, hd => by
      rcases (Nat.Prime.dvd_mul hq).mp (by simpa using hd) with h | h
      · have : q = r := (Nat.prime_dvd_prime_iff_eq hq (hall r (by simp))).mp h
        subst this
        exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _
          (mem_of_prime_dvd_prod (fun x hx => hall x (by simp [hx])) hq h)

end ECDSA

end
