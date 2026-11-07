import LfzkV2.Current.ZeroKnowledge.Backend

/-! Both fields use the same opening set.  Their private mask tapes remain
independent; the product change of variables preserves the entire pair of
responses and openings at that common set. No independence of verifier
failure events, or second opening challenge, is introduced. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Backend
open LigeroFamily RecursivePolygero.Local

variable {B N : Type} [Field B] [Field N] [Fintype B] [Fintype N]
variable {r w n bw nw s : ℕ}
variable (binary : PolygeroZk.Geometry B r w 0 n) (prime : PolygeroZk.Geometry N r w 0 n)
variable {BE NE : Type} [Fintype BE] [Fintype NE]

def jointSimulate (Q : QuerySet n r) (pivot : Fin w)
    (statements : ConstraintSystem B bw 0 w BE × ConstraintSystem N nw 0 w NE)
    (coins : Polygero.Coin B BE bw 0 s × Polygero.Coin N NE nw 0 s)
    (tape : Tape binary bw s × Tape prime nw s) :
    View (F := B) w bw s Q × View (F := N) w nw s Q :=
  (simulate binary Q pivot statements.1 coins.1 tape.1,
    simulate prime Q pivot statements.2 coins.2 tape.2)

def jointReal (Q : QuerySet n r)
    (cells : Cells B bw w × Cells N nw w)
    (statements : ConstraintSystem B bw 0 w BE × ConstraintSystem N nw 0 w NE)
    (coins : Polygero.Coin B BE bw 0 s × Polygero.Coin N NE nw 0 s)
    (tape : Tape binary bw s × Tape prime nw s) :
    View (F := B) w bw s Q × View (F := N) w nw s Q :=
  (real binary Q cells.1 statements.1 coins.1 tape.1,
    real prime Q cells.2 statements.2 coins.2 tape.2)

omit [Fintype B] [Fintype N] in
/-- The joint public simulator satisfies both opening-only verifiers at
the one supplied query. It has no private-cell argument. -/
theorem jointSimulate_verifies [DecidableEq B] [DecidableEq N]
    (hprimary : r+w+s ≤ n) (Q : QuerySet n r) (pivot : Fin w)
    (statements : ConstraintSystem B bw 0 w BE × ConstraintSystem N nw 0 w NE)
    (coins : Polygero.Coin B BE bw 0 s × Polygero.Coin N NE nw 0 s)
    (tape : Tape binary bw s × Tape prime nw s) :
    let simulated := jointSimulate binary prime Q pivot statements coins tape
    Polygero.verify binary.domain binary.k_le_n (ConstraintLayout.identity w)
      statements.1 coins.1 simulated.1.2 Q simulated.1.1 = true ∧
    Polygero.verify prime.domain prime.k_le_n (ConstraintLayout.identity w)
      statements.2 coins.2 simulated.2.2 Q simulated.2.1 = true :=
  ⟨simulate_verifies binary hprimary Q pivot statements.1 coins.1 tape.1,
    simulate_verifies prime hprimary Q pivot statements.2 coins.2 tape.2⟩

def jointCoupling (Q : QuerySet n r) (pivot : Fin w)
    (cells : Cells B bw w × Cells N nw w)
    (statements : ConstraintSystem B bw 0 w BE × ConstraintSystem N nw 0 w NE)
    (hsat : statements.1.Satisfies (logical cells.1) ∧ statements.2.Satisfies (logical cells.2))
    (coins : Polygero.Coin B BE bw 0 s × Polygero.Coin N NE nw 0 s) :
    (Tape binary bw s × Tape prime nw s) ≃ (Tape binary bw s × Tape prime nw s) :=
  (coupling binary Q pivot cells.1 statements.1 hsat.1 coins.1).prodCongr
    (coupling prime Q pivot cells.2 statements.2 hsat.2 coins.2)

theorem jointCoupling_view (Q : QuerySet n r) (pivot : Fin w)
    (cells : Cells B bw w × Cells N nw w)
    (statements : ConstraintSystem B bw 0 w BE × ConstraintSystem N nw 0 w NE)
    (hsat : statements.1.Satisfies (logical cells.1) ∧ statements.2.Satisfies (logical cells.2))
    (coins : Polygero.Coin B BE bw 0 s × Polygero.Coin N NE nw 0 s)
    (tape : Tape binary bw s × Tape prime nw s) :
    jointSimulate binary prime Q pivot statements coins
        (jointCoupling binary prime Q pivot cells statements hsat coins tape) =
      jointReal binary prime Q cells statements coins tape := by
  exact Prod.ext (coupling_view binary Q pivot cells.1 statements.1 hsat.1 coins.1 tape.1)
    (coupling_view prime Q pivot cells.2 statements.2 hsat.2 coins.2 tape.2)

/-- Exact equality of the complete joint backend view at every common Q,
under every public deterministic postprocessing (including wire encoding). -/
theorem joint_sameDistribution {Observed : Type} [DecidableEq Observed]
    (Q : QuerySet n r) (pivot : Fin w) (cells : Cells B bw w × Cells N nw w)
    (statements : ConstraintSystem B bw 0 w BE × ConstraintSystem N nw 0 w NE)
    (hsat : statements.1.Satisfies (logical cells.1) ∧ statements.2.Satisfies (logical cells.2))
    (coins : Polygero.Coin B BE bw 0 s × Polygero.Coin N NE nw 0 s)
    (observe : View (F := B) w bw s Q × View (F := N) w nw s Q → Observed) :
    SameDistribution
      (fun tape => observe (jointReal binary prime Q cells statements coins tape))
      (fun tape => observe (jointSimulate binary prime Q pivot statements coins tape)) := by
  apply sameDistribution_of_equiv (jointCoupling binary prime Q pivot cells statements hsat coins)
  intro tape
  rw [jointCoupling_view]

end LfzkV2.Current.ZeroKnowledge.Backend
