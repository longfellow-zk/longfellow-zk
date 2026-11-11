import LfzkV2.Current.ZeroKnowledge.BackendJoint

/-! Honest masked backend responses satisfy both actual Polygero checks
at every shared opening. Only ordinary affine statement satisfaction is
required; neither verification nor a simulator certificate is a premise. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Backend
open LigeroFamily RecursivePolygero.Local

variable {F : Type} [Field F] [DecidableEq F] {r w n nw s : ℕ}
variable (G : PolygeroZk.Geometry F r w 0 n)
variable {Equations : Type} [Fintype Equations]

theorem real_verifies (primary : r+w+s ≤ n) (Q : QuerySet n r)
    (cells : Cells F nw w) (statement : ConstraintSystem F nw 0 w Equations)
    (coin : Polygero.Coin F Equations nw 0 s) (tape : Tape G nw s)
    (satisfied : statement.Satisfies (logical cells)) :
    Polygero.verify G.domain G.k_le_n (ConstraintLayout.identity w)
      statement coin (real G Q cells statement coin tape).2 Q
      (real G Q cells statement coin tape).1 = true := by
  exact PolygeroZk.payload_verifies G primary Q statement coin (messages cells) tape
    (by rw [core_logical]; exact satisfied)

variable {B N : Type} [Field B] [Field N] [DecidableEq B] [DecidableEq N]
variable {bw : ℕ}
variable (binary : PolygeroZk.Geometry B r w 0 n) (prime : PolygeroZk.Geometry N r w 0 n)
variable {BE NE : Type} [Fintype BE] [Fintype NE]

theorem jointReal_verifies (primary : r+w+s ≤ n) (Q : QuerySet n r)
    (cells : Cells B bw w × Cells N nw w)
    (statements : ConstraintSystem B bw 0 w BE × ConstraintSystem N nw 0 w NE)
    (coins : Polygero.Coin B BE bw 0 s × Polygero.Coin N NE nw 0 s)
    (tape : Tape binary bw s × Tape prime nw s)
    (satisfied : statements.1.Satisfies (logical cells.1) ∧
      statements.2.Satisfies (logical cells.2)) :
    let honest := jointReal binary prime Q cells statements coins tape
    Polygero.verify binary.domain binary.k_le_n (ConstraintLayout.identity w)
      statements.1 coins.1 honest.1.2 Q honest.1.1 = true ∧
    Polygero.verify prime.domain prime.k_le_n (ConstraintLayout.identity w)
      statements.2 coins.2 honest.2.2 Q honest.2.1 = true :=
  ⟨real_verifies binary primary Q cells.1 statements.1 coins.1 tape.1 satisfied.1,
    real_verifies prime primary Q cells.2 statements.2 coins.2 tape.2 satisfied.2⟩

end LfzkV2.Current.ZeroKnowledge.Backend
