import Mathlib.Tactic.Ring
import SHA.Sigma
import SHA.Field
import SHA.Wrap

/-!
# Packing an addend group back into a word

Step 4 of the schedule bridge. `SHA256F.sum_of_bits` turns a group of weighted bit-valued field
elements into *some* `Nat`; this file says **which** `Nat`, so that `sigma0_bits` can be applied
to it.

The chain is:

* a group is `(List.range 32).map (fun i => (2 ^ i, v i))` with `v i` the cast of a bit;
* `cast_ofBits_range` says its weighted sum is `ofBits` of the bit list;
* `sum_of_bits` independently says the sum is `(A : F)` for some `A`;
* both `A` and `ofBits …` are below `2 ^ 32 ≤ p`, so `cast_inj_of_lt` identifies them.

Only then is `A` a thing `SHA/Sigma.lean` can talk about. Note the group must be **least
significant first** — `ofBits` is LSB-first and `List.range` counts up, so a group emitted
MSB-first silently reverses every word.
-/

namespace SHA256

/-- `ofBits` extends on the right by a new most significant bit. `ofBits` recurses on the left,
    so this is the direction every `List.range` induction needs. -/
theorem ofBits_append_single (l : List Nat) (x : Nat) :
    ofBits (l ++ [x]) = ofBits l + 2 ^ l.length * x := by
  induction l with
  | nil => simp [ofBits]
  | cons b bs ih =>
      simp only [List.cons_append, ofBits, ih, List.length_cons, Nat.pow_succ]
      ring

theorem ofBits_range_lt (g : Nat → Nat) (m : Nat) (hg : ∀ i, i < m → IsBit (g i)) :
    ofBits ((List.range m).map g) < 2 ^ m := by
  have hb : ∀ b ∈ (List.range m).map g, IsBit b := by
    intro b hb
    simp only [List.mem_map, List.mem_range] at hb
    obtain ⟨i, hi, rfl⟩ := hb
    exact hg i hi
  have := ofBits_lt _ hb
  simpa using this

end SHA256

namespace SHA256F

variable {F : Type} [Field F]

/-- The weighted sum of a bit list, in the field, is the cast of `ofBits`. -/
theorem cast_ofBits_range (g : Nat → Nat) : ∀ m : Nat,
    (((List.range m).map (fun i => ((2 ^ i : Nat), ((g i : Nat) : F)))).map
        (fun q => ((q.1 : Nat) : F) * q.2)).sum
      = ((SHA256.ofBits ((List.range m).map g) : Nat) : F)
  | 0 => by simp [SHA256.ofBits]
  | m + 1 => by
      rw [List.range_succ]
      simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
        List.sum_nil]
      rw [cast_ofBits_range g m, SHA256.ofBits_append_single]
      simp only [List.length_map, List.length_range]
      push_cast
      ring

/-- **The identification.** A group's `sum_of_bits` witness *is* `ofBits` of its bits. -/
theorem group_val_eq {p : Nat} [CharP F p] (g : Nat → Nat) (m A : Nat)
    (hg : ∀ i, i < m → SHA256.IsBit (g i))
    (hA : (((List.range m).map (fun i => ((2 ^ i : Nat), ((g i : Nat) : F)))).map
        (fun q => ((q.1 : Nat) : F) * q.2)).sum = (A : F))
    (hAp : A < p) (hmp : 2 ^ m ≤ p) :
    A = SHA256.ofBits ((List.range m).map g) := by
  have hlt : SHA256.ofBits ((List.range m).map g) < 2 ^ m := SHA256.ofBits_range_lt g m hg
  have hcast : ((A : Nat) : F) = ((SHA256.ofBits ((List.range m).map g) : Nat) : F) := by
    rw [← hA, cast_ofBits_range g m]
  exact cast_inj_of_lt (p := p) hAp (by omega) hcast

/-! ### Naming the bit

`sum_of_bits` and `group_val_eq` both want a `Nat → Nat` giving each position's bit, but what a
bridge has is a *field* element known to satisfy `x = 0 ∨ x = 1`. `isBit_cast` produces the `Nat`
existentially, which is no use for building a function. `natBit` names it. It is noncomputable —
`x = 1` is not decidable in an abstract field — which costs nothing here, since the whole chain
already depends on `Classical.choice`. -/

open scoped Classical in
/-- The `Nat` bit behind a field element that is one. -/
noncomputable def natBit (x : F) : Nat := if x = 1 then 1 else 0

theorem natBit_isBit (x : F) : SHA256.IsBit (natBit x) := by
  unfold natBit
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem natBit_cast {x : F} (h : x = 0 ∨ x = 1) : x = ((natBit x : Nat) : F) := by
  unfold natBit
  rcases h with rfl | rfl
  · rw [if_neg (zero_ne_one)]; simp
  · rw [if_pos rfl]; simp

theorem natBit_one : natBit (1 : F) = 1 := by unfold natBit; rw [if_pos rfl]

theorem natBit_zero : natBit (0 : F) = 0 := by unfold natBit; rw [if_neg zero_ne_one]

/-- **The convenient form.** A group given as `(2^i, v i)` with each `v i` a bit: its
    `sum_of_bits` witness is `ofBits` of the `natBit`s. This is what a schedule bridge calls. -/
theorem group_val_eq' {p : Nat} [CharP F p] (v : Nat → F) (m A : Nat)
    (hv : ∀ i, i < m → v i = 0 ∨ v i = 1)
    (hA : (((List.range m).map (fun i => ((2 ^ i : Nat), v i))).map
        (fun q => ((q.1 : Nat) : F) * q.2)).sum = (A : F))
    (hAp : A < p) (hmp : 2 ^ m ≤ p) :
    A = SHA256.ofBits ((List.range m).map (fun i => natBit (v i))) := by
  refine group_val_eq (F := F) (p := p) (fun i => natBit (v i)) m A (fun i _ => natBit_isBit _) ?_ hAp hmp
  rw [← hA, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left ?_
  intro i hi
  have h32 : i < m := List.mem_range.mp hi
  simp only [Function.comp_apply]
  rw [← natBit_cast (hv i h32)]

/-! ### Sanity check on the bit order

`cast_ofBits_range` is exactly the lemma an MSB-first group would satisfy with every word
reversed, and nothing else in the chain would notice. This pins the direction: bits 0, 3 and 6 of
an 8-bit word give `1 + 8 + 64 = 73`, not `2^7 + 2^4 + 2^1`. -/

section Sanity

private def gT : Nat → Nat := fun i => if i % 3 == 0 then 1 else 0

private theorem gT_ofBits : SHA256.ofBits ((List.range 8).map gT) = 73 := by decide

example : (((List.range 8).map (fun i => ((2 ^ i : Nat), ((gT i : Nat) : ℚ)))).map
    (fun q => ((q.1 : Nat) : ℚ) * q.2)).sum = ((73 : Nat) : ℚ) := by
  rw [cast_ofBits_range gT 8, gT_ofBits]

end Sanity

end SHA256F
