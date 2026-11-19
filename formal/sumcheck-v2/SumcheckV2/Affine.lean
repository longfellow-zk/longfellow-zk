import SumcheckV2.Layer

/-!
# Native affine layers

The Rust layer has three independent streams: quadratic `Q`, linear `L`, and
constant `K`. The dot-product rounds use `q = Q W + L` and incoming claim `C-K`.
Afterwards `B = q(u)` includes the public value `L(u)`, so the next claim is
`A + alpha * (B-L(u))`. These corrections leave every round quadratic and the
final combination linear. No distinguished constant-one wire is introduced.
-/

namespace SumcheckV2

variable {F : Type} [Field F]

def bindRightAffine {ι : Type} [Fintype ι]
    (Q : ι → ι → F) (L w : ι → F) : ι → F :=
  fun l => bindRight Q w l + L l

theorem affine_rebinding {ι : Type} [Fintype ι]
    (Q : ι → ι → F) (L m w : ι → F) :
    dot m (bindRightAffine Q L w) = dot (bindLeft Q m) w + dot m L := by
  rw [← tensor_rebinding]
  simp [dot, bindRightAffine, mul_add, Finset.sum_add_distrib]

theorem affine_nextWeights_correct {ι : Type} [Fintype ι]
    (Q : ι → ι → F) (L m w : ι → F) (alpha : F) :
    dot (nextWeights Q m alpha) w =
      dot m w + alpha * (dot m (bindRightAffine Q L w) - dot m L) := by
  rw [affine_rebinding, add_sub_cancel_right, nextWeights_correct, tensor_rebinding]

theorem affine_layer_completeness {n : ℕ}
    (Q : Cube n → Cube n → F) (L w : Cube n → F)
    (K : F) (u : Fin n → F) (alpha : F) :
    verify_multi_round ((dot (bindRightAffine Q L w) w + K) - K)
        (honestMessages (bindRightAffine Q L w) w u) (List.ofFn u) =
      some (evaluate w u * evaluate (bindRightAffine Q L w) u) ∧
    evaluate w u + alpha * (evaluate (bindRightAffine Q L w) u - evaluate L u) =
      dot (nextWeights Q (monomialWeights u) alpha) w := by
  constructor
  · simpa [mul_comm] using honest_completeness (bindRightAffine Q L w) w u
  · rw [affine_nextWeights_correct Q L (monomialWeights u) w alpha,
      evaluate_eq_dot, evaluate_eq_dot, evaluate_eq_dot]

/-- Both public corrections cancel in the comparison with the true claims.
The bad events are the original degree-two round and degree-one combination. -/
theorem affine_layer_reduction {n : ℕ}
    (Q : Cube n → Cube n → F) (L w : Cube n → F)
    (K : F) (u : Fin n → F) (claim a b alpha : F) (messages : List (RoundPoly F))
    (hfalse : claim ≠ dot (bindRightAffine Q L w) w + K)
    (hterminal : verify_multi_round (claim - K) messages (List.ofFn u) = some (a * b))
    (hnext : a + alpha * (b - evaluate L u) =
      dot (nextWeights Q (monomialWeights u) alpha) w) :
    multi_round_bad_event (claim - K) (truePolys (bindRightAffine Q L w) w u)
        messages (List.ofFn u) ∨
      BadCombineEvent (evaluate w u) (evaluate (bindRightAffine Q L w) u) a b alpha := by
  by_cases hpair : a = evaluate w u ∧ b = evaluate (bindRightAffine Q L w) u
  · left
    apply dot_product_reduction (bindRightAffine Q L w) w u (claim - K) messages
    · intro h
      exact hfalse (sub_eq_iff_eq_add.mp h)
    · simpa [hpair.1, hpair.2, mul_comm] using hterminal
  · right
    refine ⟨by tauto, ?_⟩
    rw [affine_nextWeights_correct Q L (monomialWeights u) w alpha] at hnext
    simp only [← evaluate_eq_dot] at hnext
    linear_combination hnext

end SumcheckV2
