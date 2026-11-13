import LfzkV2.Current.HashCircuit
import LfzkV2.Current.ConcreteAdapterTopology

/-! Read separation of the ordinary hash component. Assertions are included
even when their sparse coefficient is zero. Adapter wires, R, the quotient
pads and the virtual leaves may vary freely; ordinary wires and checks remain
unchanged.

For a typed hash topology (`ConcreteAdapterTopology`) the static read
separation `ReadDisjoint` is a theorem: the hash's input-boundary fragments
read only its own input prefix, and its later fragments read only wires
outside the adapter's arrays, by type. It is never a premise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
namespace LfzkV2.Current.HashCircuit
open SumcheckV2 Layered Adapter.Circuit Adapter.ProductTree Adapter.Fragment
open scoped Classical
variable {F W O : Type} [Field F]

def TermAvoids (reserved : W → Prop) : Term O W F → Prop
  | .quadratic _ l r _ => ¬reserved l ∧ ¬reserved r
  | .linear _ l _ => ¬reserved l
  | .constant _ _ => True

def AssertionAvoids (reserved : W → Prop) : Native.AssertionTerm W → Prop
  | .quadratic l r => ¬reserved l ∧ ¬reserved r
  | .linear l => ¬reserved l

structure ExtensionAvoids {n out mid : ℕ} {output : Fin n ↪ Cube out}
    (extension : Extension (F := F) (mid := mid) output) (reserved : Cube mid → Prop) : Prop where
  terms : ∀ term ∈ extension.terms, TermAvoids reserved term
  assertions : ∀ i, AssertionAvoids reserved (extension.assertions i)

def AgreeOutside (reserved : W → Prop) (left right : W → F) : Prop :=
  ∀ i, ¬reserved i → left i = right i

private theorem term_value_eq (reserved : W → Prop) (left right : W → F)
    (same : AgreeOutside reserved left right) (term : Term O W F)
    (avoids : TermAvoids reserved term) : term.value left = term.value right := by
  cases term with
  | quadratic g l r k => exact congrArg₂ (fun x y => k*x*y) (same l avoids.1) (same r avoids.2)
  | linear g l k => exact congrArg (fun x => k*x) (same l avoids)
  | constant => rfl

private theorem residual_eq (reserved : W → Prop) (left right : W → F)
    (same : AgreeOutside reserved left right) (term : Native.AssertionTerm W)
    (avoids : AssertionAvoids reserved term) : term.residual left = term.residual right := by
  cases term with
  | quadratic l r => exact congrArg₂ (· * ·) (same l avoids.1) (same r avoids.2)
  | linear l => exact same l avoids

private theorem generated_zero {n out mid : ℕ} {V : Type}
    (rows : Fin n → Row V F) (input : V → Cube mid) (output : Fin n ↪ Cube out)
    (w : Cube mid → F) (u : Cube out) (outside : ¬∃ i, output i = u) :
    (((stream rows).map (Term.map output input)).map (Term.evaluated w u)).sum = 0 := by
  rw [List.map_map]
  apply List.sum_eq_zero
  intro value member
  obtain ⟨term,_,equal⟩ := List.mem_map.mp member
  rw [← equal]
  have ne : output term.output ≠ u := fun h => outside ⟨term.output,h⟩
  cases term <;> simp_all [Term.map,Term.evaluated,Term.output]

theorem layer_agree {n out mid : ℕ} {V V' : Type}
    (first : Fin n → Row V F) (second : Fin n → Row V' F)
    (input : V → Cube mid) (input' : V' → Cube mid) (output : Fin n ↪ Cube out)
    (other : Extension (F := F) (mid := mid) output) (reserved : Cube mid → Prop)
    (separated : ExtensionAvoids other reserved) (left right : Cube mid → F)
    (same : AgreeOutside reserved left right) :
    AgreeOutside (fun u => ∃ i, output i = u)
      ((layer first input output other).outputs left) ((layer second input' output other).outputs right) ∧
    (∀ i, (layer first input output other).residuals left i =
      (layer second input' output other).residuals right i) := by
  constructor
  · intro u outside
    simp only [layer,sparseLayer_outputs,List.map_append,List.sum_append,
      generated_zero first input output left u outside,
      generated_zero second input' output right u outside,zero_add]
    congr 1
    apply List.map_congr_left
    intro term member
    unfold Term.evaluated
    rw [term_value_eq reserved left right same term (separated.terms term member)]
  · intro i
    exact residual_eq reserved left right same (other.assertions i) (separated.assertions i)

/-- The static read separation used by the hash checks. For a typed hash
topology it holds by construction (`readDisjoint` below). -/
structure ReadDisjoint {leaves input final out : ℕ} (layout : Layout)
    (output : Fin 2 ↪ Cube final) (others : Others (F := F) layout leaves input final output)
    (carry : Cube out → Option (Cube final)) (reserved : Cube input → Prop) : Prop where
  first : ExtensionAvoids others.first reserved
  pair : ∀ n, ExtensionAvoids (others.pair n) (fun u => ∃ i, layout.flat n i = u)
  final : ExtensionAvoids others.final (fun u => ∃ i, layout.flat 2 i = u)
  carry : ∀ u tree, carry u ≠ some (output tree)

private theorem reduction_agree {input : ℕ} (layout : Layout)
    (others : ∀ n, Extension (F := F) (mid := layout.log n) (layout.flat (half n)))
    (separated : ∀ n, ExtensionAvoids (others n) (fun u => ∃ i, layout.flat n i = u))
    {n : ℕ} (shape : Shape n) (first second : Layered.Circuit F (layout.log n) input)
    (left right : Cube input → F)
    (same : AgreeOutside (fun u => ∃ i, layout.flat n i = u) (first.eval left) (second.eval right))
    (checks : first.Satisfies left ↔ second.Satisfies right) :
    AgreeOutside (fun u => ∃ i, layout.flat 2 i = u)
      ((reduction layout others shape first).eval left) ((reduction layout others shape second).eval right) ∧
    ((reduction layout others shape first).Satisfies left ↔
      (reduction layout others shape second).Satisfies right) := by
  induction shape with
  | root => exact ⟨same,checks⟩
  | @pair n next ih =>
    have step := layer_agree (pairRows n) (pairRows n) (layout.index n) (layout.index n)
      (layout.flat (half n)) (others n) _ (separated n) _ _ same
    refine ih (.layer (others n).checks
      (layer (pairRows n) (layout.index n) (layout.flat (half n)) (others n)) first)
      (.layer (others n).checks
      (layer (pairRows n) (layout.index n) (layout.flat (half n)) (others n)) second) ?_ ?_
    · simpa only [Layered.Circuit.eval] using step.1
    · change ((∀ i, _ = 0) ∧ _) ↔ ((∀ i, _ = 0) ∧ _)
      simp_rw [step.2,checks]

private theorem above_eval_eq_inputs {out mid input : ℕ} (above : Above F out mid)
    (first second : Layered.Circuit F mid input) (left right : Cube input → F)
    (same : first.eval left = second.eval right) :
    (above.plug first).eval left = (above.plug second).eval right := by
  induction above with
  | hole => exact same
  | entry _ mapping _ ih => exact congrArg mapping.previous (ih first second same)
  | layer _ body _ ih => exact congrArg body.outputs (ih first second same)

theorem checks_iff_of_readDisjoint {leaves input final out upper : ℕ}
    (layout : Layout) (output : Fin 2 ↪ Cube final) (shape : Shape (half leaves))
    (others : Others (F := F) layout leaves input final output)
    (carry : Cube out → Option (Cube final)) (above : Above F upper out)
    (reserved : Cube input → Prop) (separated : ReadDisjoint layout output others carry reserved)
    (read read' : Wire leaves → Cube input)
    (left right : Cube input → F) (same : AgreeOutside reserved left right) :
    Checks layout output shape others carry above read left ↔
      Checks layout output shape others carry above read' right := by
  have first := layer_agree (pairRows leaves) (pairRows leaves) read read'
    (layout.flat (half leaves)) others.first reserved separated.first left right same
  have reduced := reduction_agree layout others.pair separated.pair shape
    (.layer others.first.checks (layer (pairRows leaves) read (layout.flat (half leaves)) others.first) .input)
    (.layer others.first.checks (layer (pairRows leaves) read' (layout.flat (half leaves)) others.first) .input)
    left right (by simpa only [Layered.Circuit.eval] using first.1) (by
    change ((∀ i, _ = 0) ∧ True) ↔ ((∀ i, _ = 0) ∧ True)
    exact and_congr (forall_congr' fun i => congrArg (· = 0) (first.2 i) |> Iff.of_eq) Iff.rfl)
  have last := layer_agree finalRows finalRows (layout.index 2) (layout.index 2)
    output others.final _ separated.final _ _ reduced.1
  have evals : (withoutAdapterChecks layout output shape others carry read).eval left =
      (withoutAdapterChecks layout output shape others carry read').eval right := by
    funext u
    change (carry u).elim 0 _ = (carry u).elim 0 _
    cases h : carry u with
    | none => rfl
    | some i =>
      apply last.1 i
      rintro ⟨tree,rfl⟩
      exact separated.carry u tree h
  have checks : (withoutAdapterChecks layout output shape others carry read).Satisfies left ↔
      (withoutAdapterChecks layout output shape others carry read').Satisfies right := by
    change ((∀ i : Fin 0, _ = 0) ∧ (∀ i, _ = 0) ∧ _) ↔ ((∀ i : Fin 0, _ = 0) ∧ (∀ i, _ = 0) ∧ _)
    simp_rw [last.2,reduced.2]
    simp
  unfold Checks
  induction above with
  | hole => exact checks
  | entry n mapping rest ih =>
    change ((∀ i, _ = 0) ∧ _) ↔ ((∀ i, _ = 0) ∧ _)
    rw [above_eval_eq_inputs rest _ _ left right evals]
    exact and_congr Iff.rfl (ih carry separated evals checks)
  | layer n body rest ih =>
    change ((∀ i, _ = 0) ∧ _) ↔ ((∀ i, _ = 0) ∧ _)
    rw [above_eval_eq_inputs rest _ _ left right evals]
    exact and_congr Iff.rfl (ih carry separated evals checks)

section Typed
open ConcreteAdapterTopology

omit [Field F] in
/-- Typed reads avoid every position outside the range of the read map. -/
theorem extensionAvoids {n out mid : ℕ} {output : Fin n ↪ Cube out} {V : Type} {read : V → Cube mid}
    (extension : ConcreteAdapterTopology.Extension output V read F) (reserved : Cube mid → Prop)
    (outside : ∀ x, ¬reserved (read x)) : ExtensionAvoids extension.algebraic reserved where
  terms term member := by
    have h := extension.reads term member
    cases term with
    | quadratic g l r k =>
        obtain ⟨⟨x,rfl⟩,⟨y,rfl⟩⟩ := h
        exact ⟨outside x,outside y⟩
    | linear g l k =>
        obtain ⟨x,rfl⟩ := h
        exact outside x
    | constant => trivial
  assertions i := by
    have h := extension.assertion_reads i
    change AssertionAvoids reserved (ConcreteTopology.Layer.assertions extension.global i)
    generalize ConcreteTopology.Layer.assertions extension.global i = a at h ⊢
    cases a with
    | quadratic l r =>
        obtain ⟨⟨x,rfl⟩,⟨y,rfl⟩⟩ := h
        exact ⟨outside x,outside y⟩
    | linear l =>
        obtain ⟨x,rfl⟩ := h
        exact outside x

omit [Field F] in
/-- Read separation of a typed hash topology. The reserved inputs are all
positions outside the hash's own input prefix. -/
theorem readDisjoint {layout : Layout} {leaves width input final out : ℕ}
    {place : Fin width → Cube input} {output : Fin 2 ↪ Cube final}
    (others : ConcreteAdapterTopology.Others layout leaves width input final place output F)
    (carry : Cube out → Option (Avoid output)) :
    ReadDisjoint layout output others.algebraic (carryWires carry) (fun u => ∀ x, place x ≠ u) where
  first := extensionAvoids others.first _ (fun x h => h x rfl)
  pair n := extensionAvoids (others.pair n) _ (fun x ⟨i,h⟩ => x.property i h)
  final := extensionAvoids others.final _ (fun x ⟨i,h⟩ => x.property i h)
  carry u tree h := by
    unfold carryWires at h
    cases hc : carry u with
    | none => rw [hc] at h; cases h
    | some y =>
        rw [hc] at h
        exact y.property tree (Option.some.inj h).symm

/-- The hash checks of a typed topology depend only on the hash's own input
prefix. Neither R, the quotient pads, the virtual leaves nor the adapter's
leaf addresses can change them. -/
theorem checks_prefix {layout : Layout} {leaves width input final out upper : ℕ}
    {place : Fin width → Cube input} {output : Fin 2 ↪ Cube final}
    (shape : Shape (half leaves))
    (others : ConcreteAdapterTopology.Others layout leaves width input final place output F)
    (carry : Cube out → Option (Avoid output)) (above : Adapter.Fragment.Above F upper out)
    (read read' : Wire leaves → Cube input) (left right : Cube input → F)
    (same : ∀ x, left (place x) = right (place x)) :
    Checks layout output shape others.algebraic (carryWires carry) above read left ↔
      Checks layout output shape others.algebraic (carryWires carry) above read' right := by
  apply checks_iff_of_readDisjoint layout output shape others.algebraic (carryWires carry) above _
    (readDisjoint others carry) read read' left right
  intro u hu
  simp only [not_forall,not_not] at hu
  obtain ⟨x,rfl⟩ := hu
  exact same x

end Typed
end LfzkV2.Current.HashCircuit
