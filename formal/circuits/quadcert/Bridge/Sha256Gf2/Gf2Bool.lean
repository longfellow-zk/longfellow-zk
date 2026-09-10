import quadcert.Core.ConeEdges
import quadcert.Bridge.Sha256Gf2.Gf2Bits
import quadcert.Bridge.Sha256Gf2.Gf2Sound

/-!
# The `is_boolean` template, over GF(2^128)

6,656 of the artifact's 6,840 assertions have the same three-node cone:

```
  node 0      input 0                               -- the constant-1 input
  node x      input k                               -- the bit
  node r      sum [(0, 0, x), (0, x, x)]            -- consts 0 · 1 · x + consts 0 · x · x
```

Both coefficients are the *unit* constant — index 0 — because in characteristic 2 the prime
field's `-1` is `1`. That is the only difference from `Bridge/Sha256/S2TmplBool.lean`, and it
makes the cone one constant lighter: there is no `p - 1` entry to identify.

Proven once. An individual assertion is discharged by matching its cone against `tnBool` and
transporting through `coneIs_transfer`; `Gf2BoolEdges.lean` does all 6,656 at once as an edge
list, which is the unit that actually scales.

The bit nodes these assertions name sum to 88,685,843 — exactly `Gf2Words.allBits_sum`, computed
independently from the word layer. So the circuit asserts booleanity of precisely the bits the
word layer names, no more and no fewer.
-/

namespace Sha256Gf2

open Quadcert Quadcert.Gen.Sha256Gf2

variable {F : Type} [Field F] [CharP F 2]

/-- **The `is_boolean` cone template.** Index 0 is the constant-1 input, index 1 the bit,
    index 2 the asserted node. -/
def tnBool : List TmplNode :=
  [.leaf 0, .leaf 1, .sum [(0, 0, 1), (0, 1, 1)]]

/-- **The template lemma.** Proven once; every `is_boolean` assertion instantiates it. -/
theorem tmpl_isBool (cs lv : Nat → F) (h0 : cs 0 = 1) (hone : lv 0 = 1)
    (hroot : interpDag (tmplDag cs tnBool) lv 2 = 0) :
    lv 1 = 0 ∨ lv 1 = 1 := by
  refine isBit_of_zero (b := lv 1) ?_
  have hval : interpDag (tmplDag cs tnBool) lv 2
      = cs 0 * lv 0 * lv 1 + cs 0 * lv 1 * lv 1 := by
    simp [interpDag, interpDagAux, nodeValue, tmplDag, tnBool, List.getD]
  rw [hval, h0, hone] at hroot
  linear_combination hroot

end Sha256Gf2
