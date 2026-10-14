module

public import ECDSA.PowMod

/-!
# Certifying that a depressed cubic has no root in `ZMod p`

`CurveHasNoPointsOfOrder2 params` is exactly `∀ x, x^3 + a*x + b ≠ 0`.  Routing it through the
group order needs the point count, which is out of reach; this instead uses the classical
criterion `gcd(f, X^p - X) = 1`, in a form that is *checked* rather than searched.

Suppose `α` is a root.  Then working modulo `f` is legitimate at `α`, so `α^p` equals the
evaluation of `X^p mod f`, a polynomial `r` of degree < 3 computed here by kernel-reducible
binary exponentiation on coefficient triples.  Fermat gives `α^p = α`, so `α` is also a root of
`g = r - X`.  A Bézout pair `u·f + v·g = 1` then evaluates to `1 = 0` at `α`.

Both `r` and `(u, v)` are untrusted advice: wrong values simply fail their `decide` checks.
-/

@[expose] public section

namespace ECDSA

/-- Coefficients of `c0 + c1·X + c2·X²`, as naturals below `p`. -/
abbrev Tri := ℕ × ℕ × ℕ

/-- `x - y` in `ZMod p`, on representatives. -/
def subM (p x y : ℕ) : ℕ := (x + p - y % p) % p

/-- Multiply two triples modulo `X^3 + a·X + b` and `p`. -/
def mulTri (p a b : ℕ) (u v : Tri) : Tri :=
  let (u0, u1, u2) := u
  let (v0, v1, v2) := v
  let w0 := u0 * v0 % p
  let w1 := (u0 * v1 + u1 * v0) % p
  let w2 := (u0 * v2 + u1 * v1 + u2 * v0) % p
  let w3 := (u1 * v2 + u2 * v1) % p
  let w4 := u2 * v2 % p
  -- X^3 = -a·X - b,  X^4 = -a·X^2 - b·X
  (subM p w0 (b * w3),
   subM p (subM p w1 (a * w3)) (b * w4),
   subM p w2 (a * w4))

/-- `X^e mod (X^3 + a·X + b)` over `ZMod p`, structural in `fuel` so the kernel reduces it. -/
def powTri (p a b : ℕ) : ℕ → Tri → ℕ → Tri
  | 0, _, _ => (1 % p, 0, 0)
  | fuel + 1, base, e =>
      if e = 0 then (1 % p, 0, 0)
      else if e % 2 = 0 then powTri p a b fuel (mulTri p a b base base) (e / 2)
      else mulTri p a b (powTri p a b fuel (mulTri p a b base base) (e / 2)) base


/-- Evaluate a triple at `α`. -/
def evalTri {F : Type} [CommRing F] (t : Tri) (α : F) : F :=
  (t.1 : F) + (t.2.1 : F) * α + (t.2.2 : F) * α ^ 2

/-! ## Correctness at a root -/

theorem cast_subM (p x y : ℕ) [NeZero p] :
    ((subM p x y : ℕ) : ZMod p) = (x : ZMod p) - (y : ZMod p) := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hlt : y % p < p := Nat.mod_lt _ hp
  unfold subM
  rw [ZMod.natCast_mod, Nat.cast_sub (by omega)]
  push_cast
  simp [ZMod.natCast_mod]

/-- At a root of the cubic, reduction modulo it is invisible: `mulTri` computes the product. -/
theorem evalTri_mulTri (p a b : ℕ) [NeZero p] (α : ZMod p)
    (hα : α ^ 3 + (a : ZMod p) * α + (b : ZMod p) = 0) (u v : Tri) :
    evalTri (mulTri p a b u v) α = evalTri u α * evalTri v α := by
  obtain ⟨u0, u1, u2⟩ := u
  obtain ⟨v0, v1, v2⟩ := v
  simp only [mulTri, evalTri, cast_subM]
  push_cast [ZMod.natCast_mod]
  linear_combination
    (-((u1 : ZMod p) * v2 + (u2 : ZMod p) * v1 + (u2 : ZMod p) * v2 * α)) * hα


/-- `powTri` really computes the power, at any root of the cubic. -/
theorem evalTri_powTri (p a b : ℕ) [NeZero p] (α : ZMod p)
    (hα : α ^ 3 + (a : ZMod p) * α + (b : ZMod p) = 0) :
    ∀ (fuel : ℕ) (base : Tri) (e : ℕ), e < 2 ^ fuel →
      evalTri (powTri p a b fuel base e) α = (evalTri base α) ^ e := by
  intro fuel
  induction fuel with
  | zero =>
      intro base e he
      simp only [pow_zero, Nat.lt_one_iff] at he
      subst he
      simp [powTri, evalTri, ZMod.natCast_mod]
  | succ fuel ih =>
      intro base e he
      rw [powTri]
      by_cases h0 : e = 0
      · simp [h0, evalTri, ZMod.natCast_mod]
      · rw [if_neg h0]
        have hhalf : e / 2 < 2 ^ fuel := by omega
        by_cases hpar : e % 2 = 0
        · rw [if_pos hpar, ih _ (e / 2) hhalf, evalTri_mulTri p a b α hα,
            ← pow_two, ← pow_mul]
          congr 1
          omega
        · rw [if_neg hpar, evalTri_mulTri p a b α hα, ih _ (e / 2) hhalf,
            evalTri_mulTri p a b α hα, ← pow_two, ← pow_mul]
          have h2 : 2 * (e / 2) + 1 = e := by omega
          rw [← pow_succ, h2]

end ECDSA

end
