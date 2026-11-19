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

end LfzkV2.Current.ZeroKnowledge.Backend
