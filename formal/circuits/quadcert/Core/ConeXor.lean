/-
# Xor mids are bit-valued

Step 2 of the schedule bridge. `ConeMid` evaluates a two-level template; this module says what
the mid layer *is*.

51 of each schedule cone's 104 mids have the same three-term shape

    consts k₁ · 1 · a  +  consts k₁ · 1 · b  +  consts k₂ · a · b        (k₁ ↦ 1, k₂ ↦ -2)

which is `a + b - 2ab`, the compiler's xor. On bits that is a bit, so those mids may be used as
addend entries in `sum_of_bits` exactly like an asserted input bit.

The distinction that matters: an input bit is a bit **because the circuit asserts it**
(`is_boolean`, discharged by `bits_of_boolNodes_idx`), whereas a mid is a bit **because its
operands are** — nothing in the circuit constrains it, and nothing needs to. So this cannot go
through the booleanity edge list; it is a derivation, and `xorVal_isBit` is where it happens.

Measured over all 48 cones, the mid layer is 51 xor nodes, 52 one-term copies and exactly one
merged 173-term linear node. `midBits_of_copyList` covers the copies; the merged node is not
bit-valued and is not covered here — it carries the linear part of all four addends, and is
regrouped in step 3.
-/

import quadcert.Core.ConeMid
import quadcert.Core.BackedIdx

namespace Quadcert

variable {F : Type} [Field F]

/-- The compiler's xor, in the field. -/
def xorVal (x y : F) : F := x + y - 2 * x * y

theorem xorVal_isBit {x y : F} (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) :
    xorVal x y = 0 ∨ xorVal x y = 1 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact Or.inl (by rw [xorVal]; ring)
  · exact Or.inr (by rw [xorVal]; ring)
  · exact Or.inr (by rw [xorVal]; ring)
  · exact Or.inl (by rw [xorVal]; ring)

/-- `Ch`'s output bit, as the compiler emits it: one linear and two quadratic terms over the
    `e`, `f`, `g` bits. Measured on the artifact — the merged node of every `n = 6` round cone
    carries exactly the 64 quadratics `2^j·e_j·f_j` and `-2^j·e_j·g_j`. -/
def chVal (x y z : F) : F := z + x * y - x * z

/-- `Maj`'s output bit, as the compiler emits it: `a·b + c·(a ⊕ b)`, where `a ⊕ b` is a xor mid
    of the cone. The two summands are never both `1`, so no xor is needed at the top. -/
def majVal (x y z u : F) : F := x * y + z * u

theorem chVal_isBit {x y z : F} (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) (hz : z = 0 ∨ z = 1) :
    chVal x y z = 0 ∨ chVal x y z = 1 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl
  · exact Or.inl (by rw [chVal]; ring)
  · exact Or.inr (by rw [chVal]; ring)
  · exact Or.inl (by rw [chVal]; ring)
  · exact Or.inr (by rw [chVal]; ring)
  · exact Or.inl (by rw [chVal]; ring)
  · exact Or.inl (by rw [chVal]; ring)
  · exact Or.inr (by rw [chVal]; ring)
  · exact Or.inr (by rw [chVal]; ring)

theorem majVal_isBit {x y z : F} (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) (hz : z = 0 ∨ z = 1) :
    majVal x y z (xorVal x y) = 0 ∨ majVal x y z (xorVal x y) = 1 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl
  · exact Or.inl (by rw [majVal, xorVal]; ring)
  · exact Or.inl (by rw [majVal, xorVal]; ring)
  · exact Or.inl (by rw [majVal, xorVal]; ring)
  · exact Or.inr (by rw [majVal, xorVal]; ring)
  · exact Or.inl (by rw [majVal, xorVal]; ring)
  · exact Or.inr (by rw [majVal, xorVal]; ring)
  · exact Or.inr (by rw [majVal, xorVal]; ring)
  · exact Or.inr (by rw [majVal, xorVal]; ring)

/-- A mid of xor shape evaluates to `xorVal` of its two operands. -/
theorem midLeafVal_xor (consts lv : Nat → F) (L : Nat) (mv : Nat → List (Nat × Nat × Nat))
    (k₁ k₂ : Nat) (hc₁ : consts k₁ = 1) (hc₂ : consts k₂ = -2) (hone : lv 0 = 1)
    (j a b : Nat) (hj : mv j = [(k₁, 0, a), (k₁, 0, b), (k₂, a, b)]) :
    midLeafVal consts lv L mv (L + j) = xorVal (lv a) (lv b) := by
  rw [midLeafVal, if_neg (by omega : ¬ (L + j < L)), show L + j - L = j from by omega, hj]
  simp only [List.foldl_cons, List.foldl_nil, hc₁, hc₂, hone]
  rw [xorVal]; ring

/-- A mid that merely copies a wire. 52 of each cone's 104 mids have this shape: 51 are a single
    input bit re-exported so the root can multiply it, and one is the circuit's constant `1`
    (`a = 0`), which `hone` makes a bit too. -/
theorem midLeafVal_copy (consts lv : Nat → F) (L : Nat) (mv : Nat → List (Nat × Nat × Nat))
    (k₁ : Nat) (hc₁ : consts k₁ = 1) (hone : lv 0 = 1)
    (j a : Nat) (hj : mv j = [(k₁, 0, a)]) :
    midLeafVal consts lv L mv (L + j) = lv a := by
  rw [midLeafVal, if_neg (by omega : ¬ (L + j < L)), show L + j - L = j from by omega, hj]
  simp only [List.foldl_cons, List.foldl_nil, hc₁, hone]
  ring

/-- `midLeafVal_copy` at an absolute template index. The root's operands are literals like `200`,
    not `L + j`, so this is the form a generated rewrite actually uses. -/
theorem midLeafVal_copy' (consts lv : Nat → F) (L : Nat) (mv : Nat → List (Nat × Nat × Nat))
    (k₁ : Nat) (hc₁ : consts k₁ = 1) (hone : lv 0 = 1)
    (i : Nat) (hi : L ≤ i) (a : Nat) (hj : mv (i - L) = [(k₁, 0, a)]) :
    midLeafVal consts lv L mv i = lv a := by
  rw [midLeafVal, if_neg (by omega), hj]
  simp only [List.foldl_cons, List.foldl_nil, hc₁, hone]; ring

/-- The form a generator emits: the absolute index and the mid index side by side, so neither
    `i - L` nor a numeral subtraction has to reduce definitionally. -/
theorem midLeafVal_copy_at (consts lv : Nat → F) (L : Nat) (mv : Nat → List (Nat × Nat × Nat))
    (k₁ : Nat) (hc₁ : consts k₁ = 1) (hone : lv 0 = 1)
    (i j : Nat) (hij : i = L + j) (a : Nat) (hj : mv j = [(k₁, 0, a)]) :
    midLeafVal consts lv L mv i = lv a := by
  subst hij; exact midLeafVal_copy consts lv L mv k₁ hc₁ hone j a hj

/-- `midLeafVal_xor` at an absolute template index, the form a generated rewrite uses. -/
theorem midLeafVal_xor_at (consts lv : Nat → F) (L : Nat) (mv : Nat → List (Nat × Nat × Nat))
    (k₁ k₂ : Nat) (hc₁ : consts k₁ = 1) (hc₂ : consts k₂ = -2) (hone : lv 0 = 1)
    (i j : Nat) (hij : i = L + j) (a b : Nat) (hj : mv j = [(k₁, 0, a), (k₁, 0, b), (k₂, a, b)]) :
    midLeafVal consts lv L mv i = xorVal (lv a) (lv b) := by
  subst hij; exact midLeafVal_xor consts lv L mv k₁ k₂ hc₁ hc₂ hone j a b hj

/-- The mirrored copy: the compiler sometimes emits the one-wire as the *second* operand. Two of
    the 52 copies in schedule instance 0 are of this form, so it is not a corner case. -/
theorem midLeafVal_copyR_at (consts lv : Nat → F) (L : Nat) (mv : Nat → List (Nat × Nat × Nat))
    (k₁ : Nat) (hc₁ : consts k₁ = 1) (hone : lv 0 = 1)
    (i j : Nat) (hij : i = L + j) (a : Nat) (hj : mv j = [(k₁, a, 0)]) :
    midLeafVal consts lv L mv i = lv a := by
  subst hij
  rw [midLeafVal, if_neg (by omega : ¬ (L + j < L)), show L + j - L = j from by omega, hj]
  simp only [List.foldl_cons, List.foldl_nil, hc₁, hone]; ring

theorem midLeafVal_expand_at (consts lv : Nat → F) (L : Nat)
    (mv : Nat → List (Nat × Nat × Nat)) (i j : Nat) (hij : i = L + j) :
    midLeafVal consts lv L mv i
      = (mv j).foldl (fun acc t => acc + consts t.1 * lv t.2.1 * lv t.2.2) 0 := by
  subst hij
  rw [midLeafVal, if_neg (by omega : ¬ (L + j < L)), show L + j - L = j from by omega]

/-- Expanding a mid that is neither a copy nor a xor — in practice the one merged linear node,
    whose terms are distributed across the addend groups by the regrouping `ring`. -/
theorem midLeafVal_expand (consts lv : Nat → F) (L : Nat) (mv : Nat → List (Nat × Nat × Nat))
    (i : Nat) (hi : L ≤ i) :
    midLeafVal consts lv L mv i
      = (mv (i - L)).foldl (fun acc t => acc + consts t.1 * lv t.2.1 * lv t.2.2) 0 := by
  rw [midLeafVal, if_neg (by omega)]

/-- **All the copy mids at once.** -/
theorem midBits_of_copyList (consts lv : Nat → F) (L : Nat) (mv : Nat → List (Nat × Nat × Nat))
    (k₁ : Nat) (hc₁ : consts k₁ = 1) (hone : lv 0 = 1) (cs : List (Nat × Nat))
    (hshape : cs.all (fun p => decide (mv p.1 = [(k₁, 0, p.2)])) = true)
    (hb : ∀ i, i < cs.length →
      lv (cs.getD i (0, 0)).2 = 0 ∨ lv (cs.getD i (0, 0)).2 = 1) :
    ∀ i, i < cs.length →
      midLeafVal consts lv L mv (L + (cs.getD i (0, 0)).1) = lv (cs.getD i (0, 0)).2
        ∧ (midLeafVal consts lv L mv (L + (cs.getD i (0, 0)).1) = 0
          ∨ midLeafVal consts lv L mv (L + (cs.getD i (0, 0)).1) = 1) := by
  intro i hi
  simp only [List.all_eq_true, decide_eq_true_eq] at hshape
  have heq := midLeafVal_copy consts lv L mv k₁ hc₁ hone
    (cs.getD i (0, 0)).1 (cs.getD i (0, 0)).2 (hshape _ (getD_mem cs (0, 0) hi))
  exact ⟨heq, by rw [heq]; exact hb i hi⟩

/-- **All the xor mids at once.** `hshape` is one `decide` over the instance's xor list; `hb` is
    the leaf booleanity the edge list already supplies. Indexed rather than membership-based, for
    the reason `bits_of_boolNodes_idx` is. -/
theorem midBits_of_xorList (consts lv : Nat → F) (L : Nat) (mv : Nat → List (Nat × Nat × Nat))
    (k₁ k₂ : Nat) (hc₁ : consts k₁ = 1) (hc₂ : consts k₂ = -2) (hone : lv 0 = 1)
    (xs : List (Nat × Nat × Nat))
    (hshape : xs.all (fun p =>
      decide (mv p.1 = [(k₁, 0, p.2.1), (k₁, 0, p.2.2), (k₂, p.2.1, p.2.2)])) = true)
    (hb : ∀ i, i < xs.length →
      (lv (xs.getD i (0, 0, 0)).2.1 = 0 ∨ lv (xs.getD i (0, 0, 0)).2.1 = 1) ∧
      (lv (xs.getD i (0, 0, 0)).2.2 = 0 ∨ lv (xs.getD i (0, 0, 0)).2.2 = 1)) :
    ∀ i, i < xs.length →
      midLeafVal consts lv L mv (L + (xs.getD i (0, 0, 0)).1)
          = xorVal (lv (xs.getD i (0, 0, 0)).2.1) (lv (xs.getD i (0, 0, 0)).2.2)
        ∧ (midLeafVal consts lv L mv (L + (xs.getD i (0, 0, 0)).1) = 0
          ∨ midLeafVal consts lv L mv (L + (xs.getD i (0, 0, 0)).1) = 1) := by
  intro i hi
  simp only [List.all_eq_true, decide_eq_true_eq] at hshape
  have hsh := hshape _ (getD_mem xs (0, 0, 0) hi)
  have heq := midLeafVal_xor consts lv L mv k₁ k₂ hc₁ hc₂ hone
    (xs.getD i (0, 0, 0)).1 (xs.getD i (0, 0, 0)).2.1 (xs.getD i (0, 0, 0)).2.2 hsh
  exact ⟨heq, by rw [heq]; exact xorVal_isBit (hb i hi).1 (hb i hi).2⟩

end Quadcert
