import SHA.Sigma
import quadcert.Bridge.Sha256Gf2.Gf2Spec
import quadcert.Bridge.Sha256Gf2.Gf2Wrap

/-!
# Words, from the node indices of their bits

`Gf2Words.lean` gives, for every 32-bit quantity the specification names, the DAG node indices of
its 32 bits (LSB first). This file reads such a list as a number: `nb` is one node's value as a
bit, `wv` packs 32 of them with `SHA256.ofBits`.

That is the whole interface the word layer needs. Everything above it —
`bitAt` inverting `ofBits`, and `σ₀ σ₁ Σ₀ Σ₁ Ch Maj` each reduced to one identity per output
bit — is `SHA/Bits.lean` and `SHA/Sigma.lean`, which mention no field and so serve both bridges.
-/

namespace Sha256Gf2

open Quadcert Quadcert.Gen.Sha256Gf2 GF128 SHA256

variable {F : Type} [Field F] [CharP F 2]

/-- A DAG node's value, read as a bit. -/
noncomputable def nb (α : F) (inputs : Nat → F) (nd : Nat) : Nat :=
  bitOf (interpDag (raw.toDag (consts α)) inputs nd)

/-- A 32-bit word, from the node indices of its bits, least significant first. -/
noncomputable def wv (α : F) (inputs : Nat → F) (l : List Nat) : Nat :=
  ofBits (l.map (nb α inputs))

theorem nb_isBit (α : F) (inputs : Nat → F) (nd : Nat) : IsBit (nb α inputs nd) :=
  bitOf_isBit _

theorem wv_isBits (α : F) (inputs : Nat → F) (l : List Nat) :
    ∀ b ∈ l.map (nb α inputs), IsBit b := by
  intro b hb
  obtain ⟨nd, _, rfl⟩ := List.mem_map.mp hb
  exact nb_isBit α inputs nd

/-- **A missing shift leg.** `sigma0_bits`/`sigma1_bits` model `x ≫ d` by reading `bs.getD (j+d)`,
    which falls off the end of a 32-bit list at the top `d` positions and yields the default `0`.
    The compiler drops the leg there instead, emitting a two-leg row; this is why the two agree. -/
theorem xb_zero (x : Nat) : xb x 0 = x := by simp [xb]

/-- **`ofBits` of a 32-element `List.range` map, as a weighted sum.** Proved once; every group
    lemma uses it to turn `SHA/Sigma.lean`'s per-bit conclusion into the shape an injection
    cone's flat exponent has. -/
theorem ofBits_range32 (f : Nat → Nat) :
    ofBits ((List.range 32).map f) = 2 ^ 0 * f 0 + 2 ^ 1 * f 1 + 2 ^ 2 * f 2 + 2 ^ 3 * f 3 + 2 ^ 4 * f 4 + 2 ^ 5 * f 5 + 2 ^ 6 * f 6 + 2 ^ 7 * f 7 + 2 ^ 8 * f 8 + 2 ^ 9 * f 9 + 2 ^ 10 * f 10 + 2 ^ 11 * f 11 + 2 ^ 12 * f 12 + 2 ^ 13 * f 13 + 2 ^ 14 * f 14 + 2 ^ 15 * f 15 + 2 ^ 16 * f 16 + 2 ^ 17 * f 17 + 2 ^ 18 * f 18 + 2 ^ 19 * f 19 + 2 ^ 20 * f 20 + 2 ^ 21 * f 21 + 2 ^ 22 * f 22 + 2 ^ 23 * f 23 + 2 ^ 24 * f 24 + 2 ^ 25 * f 25 + 2 ^ 26 * f 26 + 2 ^ 27 * f 27 + 2 ^ 28 * f 28 + 2 ^ 29 * f 29 + 2 ^ 30 * f 30 + 2 ^ 31 * f 31 := by
  rw [show (List.range 32) = ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31] : List Nat) from by decide]
  simp only [List.map_cons, List.map_nil, ofBits]
  ring

/-- `nb` is what a template leaf's `bitOf` is, so a cone's `spec<o>` lemma lands here. -/
theorem nb_lvAt (α : F) (inputs : Nat → F) (mp : Nat → Nat) (i : Nat) :
    bitOf (lvAt α inputs mp i) = nb α inputs (mp i) := rfl

end Sha256Gf2
