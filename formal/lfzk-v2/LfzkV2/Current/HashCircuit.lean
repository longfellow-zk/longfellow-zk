import LfzkV2.Current.AdapterFragment

/-! Separate the trusted hash checks from the fixed adapter fragment's checks.
Removing the adapter's two zero-output assertions changes no gates, wire
values, ordinary assertions, or carried outputs. Consequently satisfaction
of the complete circuit is exactly the conjunction proved below.

This is a semantic decomposition of the existing circuit. Hash correctness
remains the explicitly trusted application-circuit relation; the adapter's
two assertions are unit products of its virtual leaves. -/
noncomputable section
namespace LfzkV2.Current.HashCircuit

open SumcheckV2 Layered
open Current.Adapter.Circuit Current.Adapter.ProductTree Current.Adapter.Fragment
open scoped Classical

variable {F : Type} [Field F]

theorem above_eval_eq {out mid input : ℕ} (above : Above F out mid)
    (first second : Layered.Circuit F mid input) (w : Cube input → F)
    (same : first.eval w = second.eval w) :
    (above.plug first).eval w = (above.plug second).eval w := by
  induction above with
  | hole => exact same
  | entry _ mapping _ ih => exact congrArg mapping.previous (ih first second same)
  | layer _ body _ ih => exact congrArg body.outputs (ih first second same)

theorem above_satisfies_iff {out mid input : ℕ} (above : Above F out mid)
    (first second : Layered.Circuit F mid input) (w : Cube input → F) (extra : Prop)
    (same : first.eval w = second.eval w)
    (base : first.Satisfies w ↔ second.Satisfies w ∧ extra) :
    (above.plug first).Satisfies w ↔ (above.plug second).Satisfies w ∧ extra := by
  induction above with
  | hole => exact base
  | entry checks mapping rest ih =>
      change ((∀ i, mapping.residuals ((rest.plug first).eval w) i = 0) ∧
          (rest.plug first).Satisfies w) ↔
        ((∀ i, mapping.residuals ((rest.plug second).eval w) i = 0) ∧
          (rest.plug second).Satisfies w) ∧ extra
      rw [above_eval_eq rest first second w same,ih first second same base]
      exact and_assoc.symm
  | layer checks body rest ih =>
      change ((∀ i, body.residuals ((rest.plug first).eval w) i = 0) ∧
          (rest.plug first).Satisfies w) ↔
        ((∀ i, body.residuals ((rest.plug second).eval w) i = 0) ∧
          (rest.plug second).Satisfies w) ∧ extra
      rw [above_eval_eq rest first second w same,ih first second same base]
      exact and_assoc.symm

variable {leaves input final out upper : ℕ}
variable (layout : Layout) (output : Fin 2 ↪ Cube final) (shape : Shape (half leaves))
variable (others : Others (F := F) layout leaves input final output)
variable (carry : Cube out → Option (Cube final)) (above : Above F upper out)
variable (read : Wire leaves → Cube input)

def withoutAdapterChecks : Layered.Circuit F out input :=
  .entry 0 ⟨carry,Fin.elim0⟩ (body layout output shape others read)

/-- Exactly the non-adapter assertions, evaluated with the actual combined
wire arrays. No adapter product equation is assumed by this predicate. -/
def Checks (w : Cube input → F) : Prop :=
  (above.plug (withoutAdapterChecks layout output shape others carry read)).Satisfies w

theorem build_satisfies_iff (w : Cube input → F) :
    (above.plug (build layout output shape others carry read)).Satisfies w ↔
      Checks layout output shape others carry above read w ∧
        Adapter.ProductTree.Satisfies (.pair shape) (w ∘ read) := by
  apply above_satisfies_iff above
    (build layout output shape others carry read)
    (withoutAdapterChecks layout output shape others carry read) w
    (Adapter.ProductTree.Satisfies (.pair shape) (w ∘ read))
  · rfl
  · simp only [build,withoutAdapterChecks,Layered.Circuit.Satisfies,
      Layered.Entry.residuals,Function.comp_apply,body_eval,Adapter.ProductTree.Satisfies]
    constructor
    · rintro ⟨adapter,hash⟩
      exact ⟨⟨fun i => Fin.elim0 i,hash⟩,adapter⟩
    · rintro ⟨⟨_,hash⟩,adapter⟩
      exact ⟨adapter,hash⟩

end LfzkV2.Current.HashCircuit
