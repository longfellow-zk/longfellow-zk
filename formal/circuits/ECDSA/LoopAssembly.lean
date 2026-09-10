import ECDSA.EcdsaV2

/-!
# Introduction rules for `LoopFull`

The generated bridge has to build a 256-step `LoopFull` out of 768 round lemmas and 256 mux
lemmas. Two shapes make that a chain of term applications rather than 256 rounds of `simp only
[LoopFull]` on a literal list, which is the difference between a bridge that elaborates and one
that does not: unfolding a recursive definition against a 256-element literal rebuilds the whole
remaining list at every step.

The two rules differ only in `is_first`. Keeping them separate means the hypothesis is stated
with the `if` already decided, so a round lemma — whose conclusion is always
`addE (doubleE acc) mux` — matches it syntactically, with no reliance on `Bool`'s `if`
reducing during unification.

`cons_first` also absorbs `doubleE_infinity`: the first round's lemma doubles the literal
`⟨0, 1, 0⟩` because that is what the circuit computes, while `LoopFull` at `is_first = true`
does not double at all. Those agree because doubling the point at infinity returns it.
-/

namespace ECDSA2

variable {F : Type} [Field F]

theorem LoopFull.nil (acc : ProjectivePoint F) (is_first : Bool) (pk : AffinePoint F) (rx ry : F)
    (pre : List F) (params : CurveParameters F) :
    LoopFull acc is_first [] [] [] [] pk rx ry pre params := by
  simp only [LoopFull]

theorem LoopFull.cons_step (acc : ProjectivePoint F) (u : F) (us : List F)
    (wx wy wz : F) (wxs wys wzs : List F) (pk : AffinePoint F) (rx ry : F)
    (pre : List F) (params : CurveParameters F)
    (hx : (addE (doubleE acc params) (optPoint u pk rx ry pre params) params).X = wx)
    (hy : (addE (doubleE acc params) (optPoint u pk rx ry pre params) params).Y = wy)
    (hz : (addE (doubleE acc params) (optPoint u pk rx ry pre params) params).Z = wz)
    (ht : LoopFull ⟨wx, wy, wz⟩ false us wxs wys wzs pk rx ry pre params) :
    LoopFull acc false (u :: us) (wx :: wxs) (wy :: wys) (wz :: wzs) pk rx ry pre params := by
  simp only [LoopFull, if_false, Bool.false_eq_true]
  exact ⟨hx, hy, hz, ht⟩

theorem LoopFull.cons_first (u : F) (us : List F)
    (wx wy wz : F) (wxs wys wzs : List F) (pk : AffinePoint F) (rx ry : F)
    (pre : List F) (params : CurveParameters F)
    (hx : (addE (doubleE infinityPoint params) (optPoint u pk rx ry pre params) params).X = wx)
    (hy : (addE (doubleE infinityPoint params) (optPoint u pk rx ry pre params) params).Y = wy)
    (hz : (addE (doubleE infinityPoint params) (optPoint u pk rx ry pre params) params).Z = wz)
    (ht : LoopFull ⟨wx, wy, wz⟩ false us wxs wys wzs pk rx ry pre params) :
    LoopFull infinityPoint true (u :: us) (wx :: wxs) (wy :: wys) (wz :: wzs)
      pk rx ry pre params := by
  rw [doubleE_infinity] at hx hy hz
  simp only [LoopFull, if_true]
  exact ⟨hx, hy, hz, ht⟩

end ECDSA2
