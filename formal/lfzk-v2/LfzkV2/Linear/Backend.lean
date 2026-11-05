import LfzkV2.Linear.Soundness
import LfzkV2.Backend

/-!
# Linear-only Polygero boundary

The existing Polygero proof specializes to zero quadratic rows. Its product
predicate is then empty, and all committed cells belong to the ordinary
tableau. This specialization needs neither operand copies nor virtual output
reconstruction. It preserves the shared Polygero and V1 developments unchanged.
-/

namespace LfzkV2.Linear.Backend

open SumcheckV2 LigeroFamily Classical

variable {F Slot : Type} [Field F]

def rows {nw q : ℕ} (linear : List (LinearRow Slot F))
    (primary : Slot → Fin nw × Fin q) :
    Fin linear.length → LinearRow (LfzkV2.Backend.Address nw 0 q) F :=
  fun i => LfzkV2.Backend.remap (linear.get i) (LfzkV2.Backend.linearAddress primary)

/-- At zero quadratic rows, backend satisfaction is exactly the list of
affine equations over the committed vector. -/
theorem satisfies_iff {nw q : ℕ} (linear : List (LinearRow Slot F))
    (primary : Slot → Fin nw × Fin q) (core : CoreMessages F nw 0 q) :
    (LfzkV2.Backend.statement (rows linear primary)).Satisfies core ↔
      RowsHold linear (LfzkV2.Backend.read core ∘ LfzkV2.Backend.linearAddress primary) := by
  rw [LfzkV2.Backend.statement_satisfies_iff]
  simp only [rows, LfzkV2.Backend.eval_remap]
  constructor
  · rintro ⟨hrows, _⟩ row hrow
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hrow
    exact hrows i
  · intro hrows
    exact ⟨fun i => hrows _ (List.get_mem _ _), fun i => Fin.elim0 i⟩

/-- A backend statement built from renamed affine rows enforces those rows. -/
theorem satisfies_rows {E : Type} [Fintype E] {nw nq q : ℕ}
    (linear : List (LinearRow Slot F)) (primary : Slot → Fin nw × Fin q)
    (eqns : E ≃ Fin linear.length) (core : CoreMessages F nw nq q)
    (h : (LfzkV2.Backend.statement (fun e =>
      LfzkV2.Backend.remap (linear.get (eqns e)) (LfzkV2.Backend.linearAddress primary))).Satisfies core) :
    RowsHold linear (LfzkV2.Backend.read core ∘ LfzkV2.Backend.linearAddress primary) := by
  obtain ⟨hrows, _⟩ := (LfzkV2.Backend.statement_satisfies_iff _ _).mp h
  intro row hrow
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hrow
  have hr := hrows (eqns.symm i)
  simp only [Equiv.apply_symm_apply, LfzkV2.Backend.eval_remap] at hr
  rwa [hi] at hr

/-- Candidate recovery supplies the affine rows. This implication is also
valid before specializing the shared backend to zero quadratic rows. -/
theorem decoded_rows [Fintype F] [DecidableEq F]
    (I : RecursivePolygero.Instance F)
    (linear : List (LinearRow Slot F)) (primary : Slot → Fin I.nw × Fin I.q)
    (eqns : I.Equations ≃ Fin linear.length)
    (oracle : I.layer.Oracle) (coin : I.layer.Coin) (response : I.layer.Payload)
    (g : (RecursivePolygero.Counting.tupleCounts I).Index)
    (hdecode : RecursivePolygero.scanRecoverAt I
      (LfzkV2.Backend.statement (fun e =>
        LfzkV2.Backend.remap (linear.get (eqns e)) (LfzkV2.Backend.linearAddress primary)))
      oracle coin response = some g) :
    RowsHold linear
      (LfzkV2.Backend.read ((RecursivePolygero.Counting.tupleCounts I).witness g) ∘
        LfzkV2.Backend.linearAddress primary) := by
  have hs := RecursivePolygero.scanRecoverAt_valid I _ oracle coin response g hdecode
  obtain ⟨hrows, _⟩ := (LfzkV2.Backend.statement_satisfies_iff _ _).mp hs
  intro row hrow
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hrow
  have h := hrows (eqns.symm i)
  simp only [Equiv.apply_symm_apply, LfzkV2.Backend.eval_remap] at h
  rwa [hi] at h

end LfzkV2.Linear.Backend
