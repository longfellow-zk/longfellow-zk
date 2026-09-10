import quadcert.Bridge.Sha256Gf2.Gf2Bits

/-!
# An injection row's value, without a per-row proof

`Gf2Cone.chainNode_fac_pow` leaves exactly one obligation per injection factor: `hval`, saying
what bit the factor injects. There are 24,960 of them, so a per-row proof is the thing to avoid.

Two observations make it O(1) per *cone* instead:

1. A row's value is a `List.sum` over its operand pairs, and each pair is a product. So the value
   is invariant under permuting the pairs **and** under swapping within a pair — which is exactly
   the freedom the artifact uses. Measured, the five semantic forms appear in **29** distinct
   operand orders; `sum_eq_of_perm` makes all 29 the same statement, and the permutation is
   checked as data.
2. Which of the five forms a row is, and on which wires, is *data* — a `Form` per row. So a whole
   cone's rows are covered by one `Form.isBit` and two `decide`s: one that every row's pair list
   is a permutation of its form's, one that every form's wires are leaves of the cone.

`Form.pairs` fixes a canonical operand order per form; the generator picks the wires by matching
the row's truth table over all boolean assignments, so a misidentified form is caught by the
permutation `decide` rather than believed.
-/

namespace Sha256Gf2

open GF128

variable {F : Type} [Field F] [CharP F 2]

/-- The five functions an injection factor can inject, and the empty list a product row carries.
    `ch a b c` is `if a then b else c`; `maj` is the majority of its three wires. -/
inductive Form where
  | prod
  | one  (a : Nat)
  | xor2 (a b : Nat)
  | xor3 (a b c : Nat)
  | ch   (a b c : Nat)
  | maj  (a b c : Nat)
  deriving DecidableEq, Repr

/-- The canonical operand pairs of a form. Wire `0` is the `one` leaf. -/
def Form.pairs : Form → List (Nat × Nat)
  | .prod => []
  | .one a => [(0, a)]
  | .xor2 a b => [(0, a), (0, b)]
  | .xor3 a b c => [(0, a), (0, b), (0, c)]
  | .ch a b c => [(a, b), (0, c), (a, c)]
  | .maj a b c => [(a, b), (b, c), (a, c)]

/-- The wires whose booleanity the form needs. -/
def Form.wires : Form → List Nat
  | .prod => []
  | .one a => [a]
  | .xor2 a b => [a, b]
  | .xor3 a b c => [a, b, c]
  | .ch a b c => [a, b, c]
  | .maj a b c => [a, b, c]

/-- A pair with its operands in increasing order, so that swapping within a pair -- which the
    product makes free -- is not part of the permutation check. -/
def normPair (t : Nat × Nat) : Nat × Nat := if t.1 ≤ t.2 then t else (t.2, t.1)

theorem prod_normPair (lv : Nat → F) (t : Nat × Nat) :
    lv t.1 * lv t.2 = lv (normPair t).1 * lv (normPair t).2 := by
  unfold normPair
  split
  · rfl
  · exact mul_comm _ _

/-- **Operand order is free.** Two pair lists that agree as multisets after `normPair` give the
    same row value; this is what turns 29 measured operand orders into one statement. -/
theorem sum_eq_of_perm (lv : Nat → F) (ts ts' : List (Nat × Nat))
    (h : (ts.map normPair).Perm (ts'.map normPair)) :
    (ts.map (fun t => lv t.1 * lv t.2)).sum
      = (ts'.map (fun t => lv t.1 * lv t.2)).sum := by
  have e : ∀ l : List (Nat × Nat), (l.map (fun t => lv t.1 * lv t.2)).sum
      = ((l.map normPair).map (fun t => lv t.1 * lv t.2)).sum := by
    intro l
    rw [List.map_map]
    exact congrArg List.sum (List.map_congr_left (fun t _ => prod_normPair lv t))
  rw [e ts, e ts']
  exact (h.map _).sum_eq

/-- **Every form injects a bit.** One lemma, six cases; `Gf2Bits` supplies the algebra and this
    supplies the bookkeeping. -/
theorem Form.isBit (lv : Nat → F) (hone : lv 0 = 1) :
    ∀ f : Form, (∀ i ∈ f.wires, lv i = 0 ∨ lv i = 1) →
      (f.pairs.map (fun t => lv t.1 * lv t.2)).sum = 0
        ∨ (f.pairs.map (fun t => lv t.1 * lv t.2)).sum = 1
  | .prod, _ => Or.inl (by simp [Form.pairs])
  | .one a, h => by
      simpa [Form.pairs, hone] using h a (by simp [Form.wires])
  | .xor2 a b, h => by
      have := bit_xor2 (h a (by simp [Form.wires])) (h b (by simp [Form.wires]))
      simpa [Form.pairs, hone] using this
  | .xor3 a b c, h => by
      have := bit_xor3 (h a (by simp [Form.wires])) (h b (by simp [Form.wires]))
        (h c (by simp [Form.wires]))
      rw [show ((Form.xor3 a b c).pairs.map (fun t => lv t.1 * lv t.2)).sum
            = lv a + lv b + lv c from by simp [Form.pairs, hone]; ring]
      exact this
  | .ch a b c, h => by
      have := bit_ch (h a (by simp [Form.wires])) (h b (by simp [Form.wires]))
        (h c (by simp [Form.wires]))
      rw [show ((Form.ch a b c).pairs.map (fun t => lv t.1 * lv t.2)).sum
            = lv a * lv b + lv c + lv a * lv c from by simp [Form.pairs, hone]; ring]
      exact this
  | .maj a b c, h => by
      have := bit_maj (h a (by simp [Form.wires])) (h b (by simp [Form.wires]))
        (h c (by simp [Form.wires]))
      rw [show ((Form.maj a b c).pairs.map (fun t => lv t.1 * lv t.2)).sum
            = lv a * lv b + lv b * lv c + lv a * lv c from by simp [Form.pairs, hone]; ring]
      exact this

/-! ## A whole cone's rows, from two decidable checks -/

/-- **Every row of a cone injects a bit.** `hperm` says each row's operand pairs are its form's up
    to order, `hwire` that each form's wires are non-`one` leaves of the cone, and `hbl` is the
    booleanity the artifact's 6,656 `is_boolean` assertions give. All three are `∀ j < M`, so a
    cone costs one proof rather than `M`. -/
theorem rows_isBit (lv : Nat → F) (L M : Nat) (hone : lv 0 = 1)
    (hbl : ∀ i, i < L → i ≠ 0 → lv i = 0 ∨ lv i = 1)
    (ts : Nat → List (Nat × Nat)) (form : Nat → Form)
    (hperm : ∀ j, j < M → ((ts j).map normPair).Perm (((form j).pairs).map normPair))
    (hwire : ∀ j, j < M → ∀ i ∈ (form j).wires, i < L ∧ i ≠ 0) :
    ∀ j, j < M →
      ((ts j).map (fun t => lv t.1 * lv t.2)).sum = 0
        ∨ ((ts j).map (fun t => lv t.1 * lv t.2)).sum = 1 := by
  intro j hj
  rw [sum_eq_of_perm lv (ts j) ((form j).pairs) (hperm j hj)]
  exact Form.isBit lv hone (form j)
    (fun i hi => hbl i (hwire j hj i hi).1 (hwire j hj i hi).2)

/-- **…hence `hval` and `hn`, with `n` defined rather than assumed.** This is the pair
    `Gf2Cone.chainNode_fac_pow` asks for, so an injection cone's remaining obligation is
    discharged the moment its leaves are known to be bits. -/
theorem rows_val (lv : Nat → F) (M : Nat)
    (ts : Nat → List (Nat × Nat))
    (hbit : ∀ j, j < M →
      ((ts j).map (fun t => lv t.1 * lv t.2)).sum = 0
        ∨ ((ts j).map (fun t => lv t.1 * lv t.2)).sum = 1) :
    (∀ j, j < M → ((ts j).map (fun t => lv t.1 * lv t.2)).sum
        = ((bitOf ((ts j).map (fun t => lv t.1 * lv t.2)).sum : Nat) : F))
      ∧ (∀ j, j < M → bitOf ((ts j).map (fun t => lv t.1 * lv t.2)).sum = 0
          ∨ bitOf ((ts j).map (fun t => lv t.1 * lv t.2)).sum = 1) :=
  ⟨fun j hj => (bitOf_cast (hbit j hj)).symm, fun j _ => bitOf_isBit _⟩

end Sha256Gf2
