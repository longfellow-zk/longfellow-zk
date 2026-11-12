import LfzkV2.Current.HashCircuit

/-! Static read separation for the ordinary hash component. Assertions are
included even when their sparse coefficient is zero. Generated adapter wires
may vary freely; ordinary wires and checks remain unchanged. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
namespace LfzkV2.Current.HashCircuit
open SumcheckV2 Layered Adapter.Circuit Adapter.Circuit.Fragment
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

structure ReadDisjoint {d q input final out : ℕ} (layout : Layout)
    (output : Fin 2 ↪ Cube final) (others : Others (F := F) layout d q input final output)
    (carry : Cube out → Option (Cube final)) (reserved : Cube input → Prop) : Prop where
  leaf : ExtensionAvoids others.leaf reserved
  pair : ∀ d q, ExtensionAvoids (others.pair d q) (fun u => ∃ i, layout.flat d q i = u)
  final : ExtensionAvoids others.final (fun u => ∃ i, layout.flat 1 1 i = u)
  carry : ∀ u tree, carry u ≠ some (output tree)

private theorem reduction_agree {d q input : ℕ} (layout : Layout)
    (others : ∀ d q, Extension (F := F) (mid := layout.log d q)
      (layout.flat (half d) (half q)))
    (separated : ∀ d q, ExtensionAvoids (others d q) (fun u => ∃ i, layout.flat d q i = u))
    (shape : Shape d q) (first second : Layered.Circuit F (layout.log d q) input)
    (left right : Cube input → F)
    (same : AgreeOutside (fun u => ∃ i, layout.flat d q i = u) (first.eval left) (second.eval right))
    (checks : first.Satisfies left ↔ second.Satisfies right) :
    AgreeOutside (fun u => ∃ i, layout.flat 1 1 i = u)
      ((reduction layout others shape first).eval left) ((reduction layout others shape second).eval right) ∧
    ((reduction layout others shape first).Satisfies left ↔
      (reduction layout others shape second).Satisfies right) := by
  induction shape with
  | root => exact ⟨same,checks⟩
  | @pair d q next ih =>
    have step := layer_agree (pairRows d q) (pairRows d q) (layout.index d q) (layout.index d q)
      (layout.flat (half d) (half q)) (others d q) _ (separated d q) _ _ same
    refine ih (.layer (others d q).checks
      (layer (pairRows d q) (layout.index d q) (layout.flat (half d) (half q)) (others d q)) first)
      (.layer (others d q).checks
      (layer (pairRows d q) (layout.index d q) (layout.flat (half d) (half q)) (others d q)) second) ?_ ?_
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

theorem checks_iff_of_readDisjoint {d q input final out upper : ℕ}
    (layout : Layout) (output : Fin 2 ↪ Cube final) (shape : Shape d q)
    (others : Others (F := F) layout d q input final output)
    (carry : Cube out → Option (Cube final)) (above : Above F upper out)
    (reserved : Cube input → Prop) (separated : ReadDisjoint layout output others carry reserved)
    (sources : Fin d → Cube input) (pads : Fin 2 → Fin q → Cube input)
    (powers powers' : Fin 2 → Fin d → Fˣ) (base base' : Fˣ)
    (masked masked' : Fin 2 → Fin q → Bool) (targets targets' : Fin 2 → Fˣ)
    (left right : Cube input → F) (same : AgreeOutside reserved left right) :
    Checks layout output shape others carry above sources pads powers base masked targets left ↔
      Checks layout output shape others carry above sources pads powers' base' masked' targets' right := by
  have leaf := layer_agree (leafRows sources pads powers base masked)
    (leafRows sources pads powers' base' masked') id id (layout.flat d q) others.leaf
    reserved separated.leaf left right same
  have reduced := reduction_agree layout others.pair separated.pair shape
    (.layer others.leaf.checks (layer (leafRows sources pads powers base masked) id (layout.flat d q) others.leaf) .input)
    (.layer others.leaf.checks (layer (leafRows sources pads powers' base' masked') id (layout.flat d q) others.leaf) .input)
    left right leaf.1 (by
    change ((∀ i, _ = 0) ∧ True) ↔ ((∀ i, _ = 0) ∧ True)
    exact and_congr (forall_congr' fun i => congrArg (· = 0) (leaf.2 i) |> Iff.of_eq) Iff.rfl)
  have last := layer_agree (finalRows targets) (finalRows targets') (layout.index 1 1) (layout.index 1 1)
    output others.final _ separated.final _ _ reduced.1
  have evals : (withoutAdapterChecks layout output shape others carry sources pads powers base masked targets).eval left =
      (withoutAdapterChecks layout output shape others carry sources pads powers' base' masked' targets').eval right := by
    funext u
    change (carry u).elim 0 _ = (carry u).elim 0 _
    cases h : carry u with
    | none => rfl
    | some i =>
      apply last.1 i
      rintro ⟨tree,rfl⟩
      exact separated.carry u tree h
  have checks : (withoutAdapterChecks layout output shape others carry sources pads powers base masked targets).Satisfies left ↔
      (withoutAdapterChecks layout output shape others carry sources pads powers' base' masked' targets').Satisfies right := by
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

end LfzkV2.Current.HashCircuit
