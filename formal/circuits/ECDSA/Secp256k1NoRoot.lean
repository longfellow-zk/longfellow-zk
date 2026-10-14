module

public import ECDSA.NoRoot
public import ECDSA.Pratt

/-!
# The secp256k1 cubic has no root in `F_p`

`x^3 + a*x + b` is the secp256k1 curve equation, so this is exactly
`CurveHasNoPointsOfOrder2 secp256k1_params`.  Everything below is a *checked certificate*:

* `srTri` is `X^p mod f`, verified by reducing `powTri` in the kernel;
* `U, V` are Bezout polynomials with `U*f + V*g = 1` where `g = srTri - X`;
* `W` witnesses that identity integrally, `U*f + V*g - 1 = p*W` over `ZZ`, which is what lets
  `linear_combination` discharge it with `ring` -- `ring` cannot reduce modulo `p`, but it can
  verify an identity that holds over `ZZ`, and `(p : ZMod p) = 0` removes the remainder.
-/

@[expose] public section

set_option maxRecDepth 100000
set_option exponentiation.threshold 400

namespace ECDSA

abbrev sp : ℕ := 115792089237316195423570985008687907853269984665640564039457584007908834671663
abbrev sa : ℕ := 0
abbrev sb : ℕ := 7

/-- `X^p mod (X^3 + sa*X + sb)`, as advice. -/
def srTri : Tri := (0, 55594575648329892869085402983802832744385952214688224221778511981742606582254, 0)

theorem srTri_ok : powTri sp sa sb 300 (0, 1, 0) sp = srTri := by decide

instance : Fact (Nat.Prime sp) := ⟨prime_115792089237316195423570985008687907853269984665640564039457584007908834671663⟩

theorem secp256k1_cubic_no_root (x : ZMod sp) :
    x ^ 3 + (sa : ZMod sp) * x + (sb : ZMod sp) ≠ 0 := by
  intro h1
  -- `x` is also a root of `g = srTri - X`, because `x^p = x`.
  have hx : evalTri srTri x = x := by
    have h := evalTri_powTri sp sa sb x h1 300 (0, 1, 0) sp (by decide)
    rw [srTri_ok] at h
    simpa [evalTri, ZMod.pow_card] using h
  have h2 : (0 : ZMod sp) + (55594575648329892869085402983802832744385952214688224221778511981742606582254 : ZMod sp) * x + (0 : ZMod sp) * x ^ 2 - x = 0 := by
    simp only [evalTri, srTri] at hx
    push_cast at hx
    linear_combination hx
  have hp : (115792089237316195423570985008687907853269984665640564039457584007908834671663 : ZMod sp) = 0 := by exact_mod_cast ZMod.natCast_self sp
  push_cast at h1
  have : (1 : ZMod sp) = 0 := by
    linear_combination ((99250362203413881791632272864589635302802843999120483462392214863921858289997 : ZMod sp)) * h1 + ((46758632835564736012269203954919337884311706168562511263687580192619680188360 : ZMod sp) * x^2) * h2 - ((6 : ZMod sp) + (22449947725371373332185929779931479592985265144132311030846271179023097389979 : ZMod sp) * x^3) * hp
  exact one_ne_zero this

end ECDSA

end
