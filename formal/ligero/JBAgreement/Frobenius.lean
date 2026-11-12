import Mathlib.Algebra.Polynomial.Expand

/-!
# §6.6: the inseparable case, by separable extraction and pointwise untwisting

In positive characteristic an irreducible factor `P` of the interpolant can be
inseparable in `Y`: `∂_Y P = 0`, which kills the simple-root value `ξ` and with it the
whole jet recursion.  The classical remedy extracts the separable core,

  `P = S(X, Y^{p^f}, Z)`,   `∂_Y S ≠ 0`,   `S` irreducible,

and this file provides that extraction (`exists_expand_eq`) together with the two facts
that make the extracted data usable downstream:

* **root transfer** — a `Y`-root `π` of a specialisation of `P` becomes the root
  `π^{p^f}` of the same specialisation of `S` (`expand`/`eval` commutation); and

* **pointwise untwisting** — over the *finite* field `F` the map `c ↦ c^{p^f}` is
  injective, so any identity between `p^f`-th powers of field elements descends.

The second point is what keeps the quantitative side intact.  Running the machinery on
`S` uses the conservative jet order `κ = k·p^f` (the proximates become
`q_z = p_z^{p^f}`), but the final interpolation happens *after* untwisting each
coordinate value, so it still uses exactly `k` coordinates; and the column bound is

  `(2κ+1)·deg_Y S·D_Z = (2k·p^f+1)·(deg_Y P/p^f)·D_Z ≈ 2k·deg_Y P·D_Z` —

the factor `p^f` cancels.  The `η³` exponent is therefore unaffected by inseparability;
no separability hypothesis survives into the final theorem.
-/

namespace JBAgreement

open Polynomial

/-! ### Separable extraction -/

section Extract

variable {R : Type*} [CommRing R] [IsDomain R]

/-- `expand` preserves and reflects invertibility. -/
theorem isUnit_expand_iff {n : ℕ} (hn : 0 < n) {f : R[X]} :
    IsUnit (expand R n f) ↔ IsUnit f := by
  constructor
  · intro h
    have hdeg : (expand R n f).natDegree = 0 := natDegree_eq_zero_of_isUnit h
    rw [natDegree_expand] at hdeg
    have hf0 : f.natDegree = 0 := by
      rcases Nat.mul_eq_zero.mp hdeg with h' | h'
      · exact h'
      · omega
    have hfC : f = C (f.coeff 0) := eq_C_of_natDegree_eq_zero hf0
    have : expand R n f = f := by rw [hfC, expand_C]
    rwa [this] at h
  · intro h
    have hdeg : f.natDegree = 0 := natDegree_eq_zero_of_isUnit h
    have hfC : f = C (f.coeff 0) := eq_C_of_natDegree_eq_zero hdeg
    rw [hfC, expand_C]
    rwa [hfC] at h

/-- Irreducibility descends along `expand`. -/
theorem irreducible_of_irreducible_expand {n : ℕ} (hn : 0 < n) {f : R[X]}
    (h : Irreducible (expand R n f)) : Irreducible f := by
  constructor
  · exact fun hu => h.not_isUnit ((isUnit_expand_iff hn).mpr hu)
  · intro a b hab
    have hexp : expand R n f = expand R n a * expand R n b := by
      rw [hab, map_mul]
    rcases h.isUnit_or_isUnit hexp with hu | hu
    · exact Or.inl ((isUnit_expand_iff hn).mp hu)
    · exact Or.inr ((isUnit_expand_iff hn).mp hu)

variable (p : ℕ) [hp : Fact p.Prime] [CharP R p]

/-- **Separable extraction.**  An irreducible polynomial of positive degree over a
domain of characteristic `p` is `expand (p^f)` of an irreducible *separable* polynomial
(nonzero derivative), of positive degree, with the degrees related by `p^f`. -/
theorem exists_expand_eq :
    ∀ (n : ℕ) (P : R[X]), P.natDegree ≤ n → Irreducible P → 1 ≤ P.natDegree →
    ∃ (f : ℕ) (S : R[X]), P = expand R (p ^ f) S ∧ S.derivative ≠ 0 ∧
      Irreducible S ∧ 1 ≤ S.natDegree ∧ S.natDegree * p ^ f = P.natDegree := by
  intro n
  induction n with
  | zero => intro P hPn _ hPdeg; omega
  | succ n ih =>
      intro P hPn hPirr hPdeg
      rcases eq_or_ne P.derivative 0 with hder | hder
      · -- Inseparable: contract one factor of `p` and recurse.
        set S₀ := contract p P with hS₀
        have hPS₀ : expand R p S₀ = P := expand_contract p hder hp.out.ne_zero
        have hdegS₀ : S₀.natDegree * p = P.natDegree := by
          rw [← hPS₀, natDegree_expand]
        have hS₀deg : 1 ≤ S₀.natDegree := by
          rw [← hdegS₀] at hPdeg
          exact Nat.pos_of_mul_pos_right hPdeg
        have hp2 : 2 ≤ p := hp.out.two_le
        have hS₀lt : S₀.natDegree ≤ n := by nlinarith
        have hS₀irr : Irreducible S₀ :=
          irreducible_of_irreducible_expand hp.out.pos (hPS₀ ▸ hPirr)
        obtain ⟨f, S, hSeq, hSder, hSirr, hSdeg, hSdegeq⟩ :=
          ih S₀ hS₀lt hS₀irr hS₀deg
        refine ⟨f + 1, S, ?_, hSder, hSirr, hSdeg, ?_⟩
        · rw [← hPS₀, hSeq, expand_expand]
          congr 1
          simp [pow_succ, mul_comm]
        · rw [pow_succ, ← mul_assoc, hSdegeq, hdegS₀]
      · -- Already separable.
        exact ⟨0, P, by rw [pow_zero, expand_one], hder, hPirr, hPdeg, by
          rw [pow_zero, mul_one]⟩

end Extract

/-! ### Root transfer -/

section Roots

variable {A B : Type*} [CommRing A] [CommRing B]

/-- A root of a mapped `expand` is a power-root of the mapped base: if
`P = expand N S` and `π` annihilates `P` under the coefficient map `φ`, then `π^N`
annihilates `S` under `φ`. -/
theorem eval_map_expand_eq (φ : A →+* B) (S : A[X]) (N : ℕ) (π : B) :
    ((expand A N S).map φ).eval π = (S.map φ).eval (π ^ N) := by
  rw [map_expand, expand_eval]

end Roots

/-! ### Pointwise untwisting over a field of characteristic `p` -/

section Untwist

variable {F : Type*} [Field F] (p : ℕ) [hp : Fact p.Prime] [CharP F p]

/-- Frobenius powers are injective on a field. -/
theorem pow_char_pow_injective (f : ℕ) :
    Function.Injective (fun c : F => c ^ p ^ f) := by
  intro x y h
  have hsub : (x - y) ^ p ^ f = 0 := by
    rw [sub_pow_char_pow x y f]
    simpa using sub_eq_zero.mpr h
  have := pow_eq_zero_iff (pow_ne_zero f hp.out.ne_zero) |>.mp hsub
  exact sub_eq_zero.mp this

/-- The twisted affine value: `(a + z·b)^{p^f} = a^{p^f} + z^{p^f}·b^{p^f}`. -/
theorem add_mul_pow_char_pow (f : ℕ) (a b z : F) :
    (a + z * b) ^ p ^ f = a ^ p ^ f + z ^ p ^ f * b ^ p ^ f := by
  rw [add_pow_char_pow (a) (z * b) p f, mul_pow]

end Untwist

end JBAgreement
