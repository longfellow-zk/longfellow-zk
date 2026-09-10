import GF128.Order

/-!
# The GF(2^128) wrapping sum

`SHA/Wrap.lean` does this for a prime field, where `assert_wrapping_sum` embeds a 32-bit word
*positionally* — `p = Σ 2^i·bᵢ` — and asserts `Π_j (C − P − j·2^32) = 0`. Over GF(2^128) the
compiler emits a different assertion entirely (`analog_adder/src/circuit.rs:117` rather than
`:58`): the word goes into the **exponent** of the generator,

```
inject(v) = Π_{i<32} (1 + (α^(2^i) − 1)·bᵢ)        -- = α^v
assert     Π_{j<n} (got − (α^(2^32))^j · want) = 0
```

so none of the positional theory applies. This file is its replacement, laid out to match
`SHA/Wrap.lean` clause for clause: a recursive product, the "a product vanishes only at a factor"
lemma, and the `Nat` reading of what that factor says.

The two ingredients that make the exponent readable are `inject_eq` — which is just booleanity
plus a telescoping induction, and holds in any field — and `alpha_pow_injOn` from
`GF128/Order.lean`, which is where `ord α = 2^128 − 1` is spent. The adder's own overflow guard
caps `n` at `2^(128−32)`, so the `hbound` hypothesis below is never tight in practice: the
deployed circuit's largest wrapping sum has `n = 7`.
-/

set_option maxRecDepth 100000

namespace GF128

variable {F : Type*} [Field F] [CharP F 2]

/-! ## Step 1: the injection is `α` to the word

Nothing here needs the characteristic or the order — only that the wires are bits. -/

/-- One factor of the adder's injection: `1 + (α^(2^i) − 1)·bᵢ`. -/
def injFactor (α : F) (i : Nat) (b : F) : F := 1 + (α ^ 2 ^ i - 1) * b

/-- The injection of the low `n` bits, by recursion so the induction peels one factor. -/
def injectF (α : F) (b : Nat → F) : Nat → F
  | 0 => 1
  | n + 1 => injFactor α n (b n) * injectF α b n

private theorem mod_two_pow_succ (v n : Nat) :
    v % 2 ^ (n + 1) = v % 2 ^ n + (if v.testBit n then 2 ^ n else 0) := by
  have h : v % (2 ^ n * 2) = v % 2 ^ n + 2 ^ n * (v / 2 ^ n % 2) := Nat.mod_mul
  rw [pow_succ, h, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ n) with hm | hm <;> simp [hm]

/-- **Step 1.** With boolean wires spelling `v`, the injection is `α ^ v`. -/
theorem inject_eq (α : F) (b : Nat → F) (v : Nat) :
    ∀ n, (∀ i, i < n → b i = if v.testBit i then 1 else 0) →
      injectF α b n = α ^ (v % 2 ^ n)
  | 0, _ => by simp [injectF, Nat.mod_one]
  | n + 1, hb => by
      rw [injectF, inject_eq α b v n (fun i hi => hb i (Nat.lt_succ_of_lt hi)),
        hb n (Nat.lt_succ_self n), mod_two_pow_succ]
      cases hbit : v.testBit n
      · simp [injFactor]
      · simp only [injFactor, if_true, if_pos, mul_one, ite_true]
        rw [pow_add]
        ring

/-- **Each factor is a power of α.** For a boolean wire, `1 + (α^(2^i) − 1)·b` is `α^(2^i)` when
    the bit is set and `1` when it is not.

    This is the fact that makes templating an injection cone unnecessary. A product of powers of
    α is a power of α whatever the association *and whatever the order*, so the compiler's tree
    shape and its leaf ordering both stop mattering — which they otherwise do: the artifact's 428
    injection cones have only 7 distinct leaf-kind mixes but **204** distinct templates, because
    the 2-, 3- and 4-term factors sit at different positions in each. -/
theorem injFactor_eq_pow (α : F) (i n : Nat) (b : F) (hb : b = (n : F)) (hn : n = 0 ∨ n = 1) :
    injFactor α i b = α ^ (2 ^ i * n) := by
  rcases hn with rfl | rfl
  · rw [hb]; simp [injFactor]
  · rw [hb]; simp only [injFactor, Nat.cast_one, mul_one, pow_one]
    ring

/-- `injectF` re-associated, the counterpart of `wrapPolyM_eq_prod`. The compiler builds each
    injection as a binary tree of its 32 factors; this is what makes the tree shape irrelevant. -/
theorem injectF_eq_prod (α : F) (b : Nat → F) :
    ∀ n, injectF α b n = ∏ i ∈ Finset.range n, injFactor α i (b i)
  | 0 => by simp [injectF]
  | n + 1 => by
      rw [injectF, Finset.prod_range_succ, injectF_eq_prod α b n]
      ring

/-! ## Step 2: a vanishing product, and what the surviving factor says -/

/-- `Π_{j < n} (g − t^j · z)`, mirroring `SHA256F.wrapPoly`. -/
def wrapPolyM : Nat → F → F → F → F
  | 0, _, _, _ => 1
  | n + 1, t, z, g => (g - t ^ n * z) * wrapPolyM n t z g

/-- The whole content of the assertion, in a field: a product vanishes only at a factor. -/
theorem wrapM_of_prod_zero :
    ∀ (n : Nat) (t z g : F), wrapPolyM n t z g = 0 → ∃ j, j < n ∧ g = t ^ j * z
  | 0, _, _, _, h => absurd h one_ne_zero
  | n + 1, t, z, g, h => by
      rw [wrapPolyM] at h
      rcases mul_eq_zero.mp h with h' | h'
      · exact ⟨n, Nat.lt_succ_self n, by linear_combination h'⟩
      · obtain ⟨j, hj, hg⟩ := wrapM_of_prod_zero n t z g h'
        exact ⟨j, Nat.lt_succ_of_lt hj, hg⟩

/-- **Step 2.** The `Nat` reading: the expected word is the addends' sum reduced mod `2^32`.

    This is where `ord α = 2^128 − 1` is spent, through `alpha_pow_injOn`. `hbound` is what the
    adder's own `max_terms` guard enforces on the Rust side. -/
theorem wrap_nat_gf (α : F) (h : IsGen α) (n C P : Nat)
    (hC : C < n * 2 ^ 32) (hP : P < 2 ^ 32) (hbound : n * 2 ^ 32 ≤ N)
    (hass : ∃ j, j < n ∧ α ^ C = (α ^ 2 ^ 32) ^ j * α ^ P) :
    P = C % 2 ^ 32 := by
  obtain ⟨j, hj, hg⟩ := hass
  have hlt : j * 2 ^ 32 + P < n * 2 ^ 32 := by
    have hstep : (j + 1) * 2 ^ 32 ≤ n * 2 ^ 32 := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul] at hstep
    omega
  have hpow : (α ^ 2 ^ 32) ^ j * α ^ P = α ^ (j * 2 ^ 32 + P) := by
    rw [← pow_mul, ← pow_add]
    ring_nf
  rw [hpow] at hg
  have := alpha_pow_injOn α h (by omega) (by omega) hg
  omega

/-! ## The two steps composed

The statement an emitted meaning lemma discharges. `bs k` are the 32 wires of addend `k` and
`be` those of the expected word; the values `vs k` and `e` are what the booleanity assertions
let the bridge name. -/

theorem wrap_gf (α : F) (h : IsGen α)
    (n : Nat) (hbound : n * 2 ^ 32 ≤ N)
    (bs : Nat → Nat → F) (vs : Nat → Nat) (be : Nat → F) (e : Nat)
    (hbs : ∀ k, k < n → ∀ i, i < 32 → bs k i = if (vs k).testBit i then 1 else 0)
    (hbe : ∀ i, i < 32 → be i = if e.testBit i then 1 else 0)
    (hv : ∀ k, k < n → vs k < 2 ^ 32) (he : e < 2 ^ 32)
    (hass : wrapPolyM n (α ^ 2 ^ 32) (injectF α be 32)
              (∏ k ∈ Finset.range n, injectF α (bs k) 32) = 0) :
    e = (∑ k ∈ Finset.range n, vs k) % 2 ^ 32 := by
  have hgot : (∏ k ∈ Finset.range n, injectF α (bs k) 32)
      = α ^ (∑ k ∈ Finset.range n, vs k) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl ?_
    intro k hk
    rw [inject_eq α (bs k) (vs k) 32 (hbs k (Finset.mem_range.mp hk)),
      Nat.mod_eq_of_lt (hv k (Finset.mem_range.mp hk))]
  have hwant : injectF α be 32 = α ^ e := by
    rw [inject_eq α be e 32 hbe, Nat.mod_eq_of_lt he]
  rw [hgot, hwant] at hass
  refine wrap_nat_gf α h n _ e ?_ he hbound (wrapM_of_prod_zero n _ _ _ hass)
  have : ∑ k ∈ Finset.range n, vs k < ∑ _k ∈ Finset.range n, 2 ^ 32 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp at hass
      exact absurd hass one_ne_zero
    · refine Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_range.mpr hn⟩ ?_
      intro k hk
      exact hv k (Finset.mem_range.mp hk)
  simpa [Finset.sum_const, mul_comm] using this

/-- The bound `wrap_nat_gf` needs, discharged once for every addend count that can occur.
    `analog_adder`'s own guard is `n < 2^(128−32)`; the four SHA-256 classes are `n = 2, 4, 6, 7`,
    so in practice this is slack by about `2^93`. -/
theorem bound_of_le (n : Nat) (hn : n ≤ 2 ^ 90) : n * 2 ^ 32 ≤ N := by
  have h1 : n * 2 ^ 32 ≤ 2 ^ 90 * 2 ^ 32 := Nat.mul_le_mul_right _ hn
  have h2 : (2 : Nat) ^ 90 * 2 ^ 32 ≤ N := by decide +kernel
  exact le_trans h1 h2

/-- The largest wrapping sum in the deployed SHA-256 circuit has seven addends. -/
example : (7 : Nat) * 2 ^ 32 ≤ N := bound_of_le 7 (by norm_num)

end GF128
