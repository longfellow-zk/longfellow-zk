import LfzkV2.Current.ZeroKnowledge.BackendCells

/-! Honest frontend rows compile to the exact two backend statements.
The tableau, addresses, fingerprint rows and equation order are constructed
here. Ordinary frontend/fingerprint equations suffice; no backend statement
satisfaction or independently supplied row-equivalence certificate is assumed. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.BackendStatement

open SumcheckV2 LigeroFamily Application WitnessSelection
open scoped Classical

section Rows
variable {F Slot Equations : Type} [Field F] [Fintype Equations]
variable {cells : ℕ}

theorem rows_satisfied (flat : Fin (cells+2) → F) (slot : Slot → Fin (cells+2))
    (rows : List (LinearRow Slot F)) (equations : Equations ≃ Fin rows.length)
    (holds : RowsHold rows (flat ∘ slot)) :
    (LfzkV2.Backend.statement (fun equation => LfzkV2.Backend.remap
      (rows.get (equations equation))
      (LfzkV2.Backend.linearAddress (fun index =>
        CellLayout.primary (by decide : 0<265) (ConcreteSetup.rows_capacity cells) (slot index))))).Satisfies
      (Backend.logical (BackendCells.tableau flat)) := by
  apply (LfzkV2.Backend.statement_satisfies_iff _ _).mpr
  constructor
  · intro equation
    rw [LfzkV2.Backend.eval_remap]
    have readback : LfzkV2.Backend.read (Backend.logical (BackendCells.tableau flat)) ∘
        LfzkV2.Backend.linearAddress (fun index =>
          CellLayout.primary (by decide : 0<265) (ConcreteSetup.rows_capacity cells) (slot index)) = flat ∘ slot := by
      funext index
      exact BackendCells.primary_read flat (slot index)
    rw [readback]
    exact holds _ (List.get_mem _ _)
  · intro row
    exact Fin.elim0 row

end Rows

variable {B I J PadB C : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable [Fintype I] [DecidableEq I] [Fintype J]
variable {p shared maskBits M K cellsB remaining padsN : ℕ} [Fact p.Prime]
variable (binaryNodes : Fin 2792 ↪ B) (primeNodes : Fin 2792 ↪ ZMod p)
variable (A : System B I J (Fin (cellsB+2)) PadB (CellLayout.Prime.Other remaining padsN)
  (Fin padsN) (Fin cellsB) (Fin (CellLayout.Prime.cells remaining padsN)) C C p shared maskBits M K)

/-- The public quotient/remainder addresses are the runtime's actual
265-wide layout, including the prime typed-slot permutation. -/
def addresses : StatementCompiler.Addresses (ConcreteSetup.backend binaryNodes cellsB)
    (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells remaining padsN)) cellsB remaining padsN where
  binary := CellLayout.primary (by decide : 0<265) (ConcreteSetup.rows_capacity cellsB)
  prime := (CellLayout.Prime.index remaining padsN).toEmbedding.trans
    (CellLayout.primary (by decide : 0<265)
      (ConcreteSetup.rows_capacity (CellLayout.Prime.cells remaining padsN)))

omit [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B] in
theorem addresses_checked :
    StatementCompiler.addresses (ConcreteSetup.backend binaryNodes cellsB)
      (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells remaining padsN)) cellsB remaining padsN =
      some (addresses binaryNodes primeNodes) := by
  unfold StatementCompiler.addresses
  rw [dif_pos]
  · rfl
  · exact ⟨(show 0<265 by decide),ConcreteSetup.rows_capacity cellsB,(show 0<265 by decide),
      ConcreteSetup.rows_capacity (CellLayout.Prime.cells remaining padsN)⟩

variable (countB countN : ℕ)
variable (coinsB : WitnessSelection.Coins B (Fin cellsB))
variable (coinsN : WitnessSelection.Coins (ZMod p) (Fin (CellLayout.Prime.cells remaining padsN)))
variable (targetB : B × B) (targetN : ZMod p × ZMod p)

theorem compile_satisfies
    (result : StatementData A ((ConcreteSetup.backend binaryNodes cellsB).indexed countB)
      ((ConcreteSetup.backend primeNodes (CellLayout.Prime.cells remaining padsN)).indexed countN))
    (compiled : StatementCompiler.compile (ConcreteSetup.backend binaryNodes cellsB)
      (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells remaining padsN)) A
      (addresses binaryNodes primeNodes) countB countN coinsB coinsN targetB targetN = some result)
    (flatB : Fin (cellsB+2) → B)
    (flatN : Fin (CellLayout.Prime.cells remaining padsN+2) → ZMod p)
    (binaryRows : RowsHold (A.binary.rows ++ FingerprintRows.rows
      (fun i => A.binaryLayout (.inl i)) (fun j => A.binaryLayout (.inr j)) coinsB targetB) flatB)
    (primeRows : RowsHold (A.primeRows ++ FingerprintRows.rows
      (fun i => A.primeLayout (.inl i)) (fun j => A.primeLayout (.inr j)) coinsN targetN)
        (BackendCells.primeRead flatN)) :
    result.statement.1.Satisfies (Backend.logical (BackendCells.tableau flatB)) ∧
      result.statement.2.Satisfies (Backend.logical (BackendCells.tableau flatN)) := by
  have fields := StatementCompiler.compile_fields (ConcreteSetup.backend binaryNodes cellsB)
    (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells remaining padsN)) A
    (addresses binaryNodes primeNodes) countB countN coinsB coinsN targetB targetN result compiled
  have binaryHeld : RowsHold (A.binary.rows ++ FingerprintRows.rows
      (fun i => A.binaryLayout (.inl i)) (fun j => A.binaryLayout (.inr j)) result.coinsB result.targetB) flatB := by
    rw [fields.2.2.1,fields.2.2.2.2.1]
    exact binaryRows
  have primeHeld : RowsHold (A.primeRows ++ FingerprintRows.rows
      (fun i => A.primeLayout (.inl i)) (fun j => A.primeLayout (.inr j)) result.coinsN result.targetN)
        (BackendCells.primeRead flatN) := by
    rw [fields.2.2.2.1,fields.2.2.2.2.2]
    exact primeRows
  constructor
  · change (LfzkV2.Backend.statement (fun equation => LfzkV2.Backend.remap
      ((A.binary.rows ++ FingerprintRows.rows (fun i => A.binaryLayout (.inl i))
        (fun j => A.binaryLayout (.inr j)) result.coinsB result.targetB).get (result.equationsB equation))
      (LfzkV2.Backend.linearAddress result.primaryB))).Satisfies _
    rw [fields.1]
    exact rows_satisfied flatB id _ result.equationsB binaryHeld
  · change (LfzkV2.Backend.statement (fun equation => LfzkV2.Backend.remap
      ((A.primeRows ++ FingerprintRows.rows (fun i => A.primeLayout (.inl i))
        (fun j => A.primeLayout (.inr j)) result.coinsN result.targetN).get (result.equationsN equation))
      (LfzkV2.Backend.linearAddress result.primaryN))).Satisfies _
    rw [fields.2.1]
    exact rows_satisfied flatN (CellLayout.Prime.index remaining padsN) _ result.equationsN primeHeld

/-- Successful compilation preserves the numerical list order of frontend
rows followed by the two fingerprint equations. -/
theorem compile_equation_values
    (result : StatementData A ((ConcreteSetup.backend binaryNodes cellsB).indexed countB)
      ((ConcreteSetup.backend primeNodes (CellLayout.Prime.cells remaining padsN)).indexed countN))
    (compiled : StatementCompiler.compile (ConcreteSetup.backend binaryNodes cellsB)
      (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells remaining padsN)) A
      (addresses binaryNodes primeNodes) countB countN coinsB coinsN targetB targetN = some result) :
    (∀ i : Fin countB, (result.equationsB i).val = i.val) ∧
      (∀ i : Fin countN, (result.equationsN i).val = i.val) := by
  unfold StatementCompiler.compile at compiled
  cases hb : StatementCompiler.equationIndex countB
      (A.binary.rows ++ FingerprintRows.rows (fun i => A.binaryLayout (.inl i))
        (fun j => A.binaryLayout (.inr j)) coinsB targetB).length with
  | none => simp only [hb] at compiled; contradiction
  | some equationsB =>
      simp only [hb] at compiled
      cases hn : StatementCompiler.equationIndex countN
          (A.primeRows ++ FingerprintRows.rows (fun i => A.primeLayout (.inl i))
            (fun j => A.primeLayout (.inr j)) coinsN targetN).length with
      | none => simp only [hn] at compiled; contradiction
      | some equationsN =>
          simp only [hn,pure] at compiled
          cases compiled
          exact ⟨fun i => StatementCompiler.equationIndex_value countB _ i _ hb,
            fun i => StatementCompiler.equationIndex_value countN _ i _ hn⟩

end LfzkV2.Current.ZeroKnowledge.BackendStatement
