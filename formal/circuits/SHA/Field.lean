import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import SHA.Spec

/-!
# Field-side support for the generated SHA-256 meaning lemmas

`meaning_gen` emits one lemma per `is_boolean` assertion — 6,656 of them for the one-block
circuit — each of the shape

```
theorem m14940 (inputs : Nat → F) (hone : inputs 0 = 1)
    (h : interpDag (raw.toDag (Sha.consts F)) inputs 14940 = 0) :
    inputs 1 = 0 ∨ inputs 1 = 1 := by
  refine SHA256F.isBit_of_zero_raw (inputs 1) ?_
  …cone chain…
  linear_combination h
```

The assertion polynomial is `x - x * x`. Factoring it and using that a field has no zero
divisors is done **once**, here, rather than in every one of the 6,656 proofs — the same reason
`ECDSA2.RangeCert.isDigit_of_zero_raw` exists for the digit range checks. Everything after the
`refine` is then a `linear_combination`, which is what the generator already knows how to emit.
-/

namespace SHA256F

variable {F : Type} [Field F]

/-- The circuit's booleanity constraint, factored. -/
theorem isBit_of_zero_raw (x : F) (h : x - x * x = 0) : x = 0 ∨ x = 1 := by
  have hfac : x * (1 - x) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hfac with h' | h'
  · exact Or.inl h'
  · exact Or.inr (by linear_combination -h')

/-- The `Nat` predicate the specification uses, for a field element known to be a bit. Stated
    separately because the bridge from field to `Nat` happens once per word, not once per bit. -/
theorem isBit_cast (x : F) (h : x = 0 ∨ x = 1) :
    ∃ n : Nat, SHA256.IsBit n ∧ x = (n : F) := by
  rcases h with rfl | rfl
  · exact ⟨0, Or.inl rfl, by norm_num⟩
  · exact ⟨1, Or.inr rfl, by norm_num⟩

end SHA256F
