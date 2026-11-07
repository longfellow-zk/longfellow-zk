import LfzkV2.PolygeroZk
import LfzkV2.Current.BackendChallenges

/-! Simulation of the current linear-only Polygero backend.

All frontend pads, including product and Frobenius cells, are ordinary
logical cells here. Their internal relations are not additional backend
checks. The simulator encodes zero logical cells and adds the existing public
arithmetic correction, which vanishes at the selected openings. It therefore
requires a public affine statement but no satisfying witness.

The witness-dependent change of variables below proves joint privacy of both
response polynomials and every opened row. It is not the simulator algorithm.
Merkle and Fiat--Shamir compilation remain separate from this algebraic result. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Backend

open Polynomial LigeroFamily MultiplicativeCode RecursivePolygero.Local
open scoped Classical

variable {F : Type} [Field F] {r w n nw s : ℕ}
variable (G : PolygeroZk.Geometry F r w 0 n)

abbrev Cells (F : Type) (nw w : ℕ) := Fin nw → Fin w → F

def messages (cells : Cells F nw w) : PolygeroCoreMasking.Messages F w 0 nw 0 where
  ordinary := cells
  left := Fin.elim0
  right := Fin.elim0

def logical (cells : Cells F nw w) : CoreMessages F nw 0 w
  | .linear => cells
  | .left | .right | .output => Fin.elim0

theorem core_logical (cells : Cells F nw w) (tape : PolygeroCoreMasking.Tape F r nw 0) :
    layoutCoreMessages (ConstraintLayout.identity w) (PolygeroZk.core G (messages cells) tape) =
      logical cells := by
  funext block row col
  cases block with
  | linear => exact G.code.encode_witness (tape.1 row) (cells row) col
  | left | right | output => exact Fin.elim0 row

variable {Equations : Type} [Fintype Equations]

/-- With no quadratic rows, compatibility is precisely ordinary affine
statement satisfaction. There is no assumed product-row or privacy certificate. -/
def compatible (cells : Cells F nw w) (statement : ConstraintSystem F nw 0 w Equations)
    (hsat : statement.Satisfies (logical cells)) :
    PolygeroZk.Compatible G (messages cells) statement where
  supported := by
    intro equation block row col h
    cases block with
    | linear => exact (h (Or.inl rfl)).elim
    | left | right | output => exact Fin.elim0 row
  satisfied := by
    intro tape
    rw [core_logical]
    exact hsat

abbrev Tape (nw s : ℕ) := PolygeroZk.Tape G nw 0 s
abbrev View (w nw s : ℕ) (Q : QuerySet n r) :=
  Polygero.Opening F nw 0 n r Q × LigeroPayload F (r+w) s

def real (Q : QuerySet n r) (cells : Cells F nw w)
    (statement : ConstraintSystem F nw 0 w Equations)
    (coin : Polygero.Coin F Equations nw 0 s) (tape : Tape G nw s) : View (F := F) w nw s Q :=
  (Polygero.openOracle (PolygeroZk.oracle G (messages cells) tape) Q,
    PolygeroZk.payload G G.positive statement coin (messages cells) tape)

/-- This algorithm takes only public data and fresh backend coins. The
logical tableau is zero even when zero does not satisfy the affine statement. -/
def simulate (Q : QuerySet n r) (pivot : Fin w)
    (statement : ConstraintSystem F nw 0 w Equations)
    (coin : Polygero.Coin F Equations nw 0 s) (tape : Tape G nw s) : View (F := F) w nw s Q :=
  (Polygero.openOracle (PolygeroZk.oracle G 0 tape) Q,
    PolygeroZk.simPayload G G.positive Q pivot statement coin tape)

theorem real_primary (Q : QuerySet n r) (cells : Cells F nw w)
    (statement : ConstraintSystem F nw 0 w Equations)
    (coin : Polygero.Coin F Equations nw 0 s) (tape : Tape G nw s) :
    (real G Q cells statement coin tape).2.primary =
      PolygeroPrimaryMasking.batch G.positive coin.2
        (PolygeroZk.ordinaryRows G (messages cells) tape.1 tape.2.1) + tape.2.2 := rfl

theorem real_primary_sample [DecidableEq F] (Q : QuerySet n r) (cells : Cells F nw w)
    (statement : ConstraintSystem F nw 0 w Equations)
    (coin : Polygero.Coin F Equations nw 0 s)
    (core : PolygeroCoreMasking.Tape F r nw 0)
    (masks : PolygeroMasking.Tape G.code (PolygeroZk.sumFunctional F w))
    (nodes : Fin (r+w+s) → F) (injective : Function.Injective nodes)
    (samples : Fin (r+w+s) → F) (i : Fin (r+w+s)) :
    ((real G Q cells statement coin
      (core,masks,(Response.evaluationEquiv F nodes injective).symm samples)).2.primary : F[X]).eval
        (nodes i) =
      (PolygeroPrimaryMasking.batch G.positive coin.2
        (PolygeroZk.ordinaryRows G (messages cells) core masks) : F[X]).eval (nodes i) + samples i := by
  rw [real_primary]
  simp only [Submodule.coe_add,eval_add]
  rw [Response.evaluationEquiv_eval]

/-- H does not depend on Q, the correction pivot, or the affine statement.
Its sole last mask is added with coefficient one, exactly as in Rust. -/
theorem simulate_primary (Q : QuerySet n r) (pivot : Fin w)
    (statement : ConstraintSystem F nw 0 w Equations)
    (coin : Polygero.Coin F Equations nw 0 s) (tape : Tape G nw s) :
    (simulate G Q pivot statement coin tape).2.primary =
      PolygeroPrimaryMasking.batch G.positive coin.2
        (PolygeroZk.ordinaryRows G 0 tape.1 tape.2.1) + tape.2.2 := rfl

/-- Each serialized H sample is the ordinary-tape contribution plus its
corresponding independent fstar sample. A prefix-pinning argument can fix
the first contribution even when the commitment root depends on fstar. -/
theorem simulate_primary_sample [DecidableEq F] (Q : QuerySet n r) (pivot : Fin w)
    (statement : ConstraintSystem F nw 0 w Equations)
    (coin : Polygero.Coin F Equations nw 0 s)
    (core : PolygeroCoreMasking.Tape F r nw 0)
    (masks : PolygeroMasking.Tape G.code (PolygeroZk.sumFunctional F w))
    (nodes : Fin (r+w+s) → F) (injective : Function.Injective nodes)
    (samples : Fin (r+w+s) → F) (i : Fin (r+w+s)) :
    ((simulate G Q pivot statement coin
      (core,masks,(Response.evaluationEquiv F nodes injective).symm samples)).2.primary : F[X]).eval
        (nodes i) =
      (PolygeroPrimaryMasking.batch G.positive coin.2
        (PolygeroZk.ordinaryRows G 0 core masks) : F[X]).eval (nodes i) + samples i := by
  rw [simulate_primary]
  simp only [Submodule.coe_add, eval_add]
  rw [Response.evaluationEquiv_eval]

private theorem zero_arithmetic_sum (statement : ConstraintSystem F nw 0 w Equations)
    (weights : Equations → F) (tape : Tape G nw s) :
    PolygeroZk.sumFunctional F w
      (witnessValues (PolygeroZk.arithmeticRow G statement weights 0 tape).val) = 0 := by
  change PolygeroZk.sumFunctional F w
    (witnessValues (DirectVerifier.linearCore G.code (ConstraintLayout.identity w) statement weights
      (PolygeroZk.core G 0 tape.1)) +
      witnessValues (PolygeroMasking.response G.code G.basis (PolygeroZk.sumFunctional F w) tape.2.1)) = 0
  rw [map_add]
  have hc := PolygeroMasking.linearCore_sum G.code (ConstraintLayout.identity w)
    statement weights (PolygeroZk.core G 0 tape.1)
  change PolygeroZk.sumFunctional F w
    (witnessValues (DirectVerifier.linearCore G.code (ConstraintLayout.identity w) statement weights
      (PolygeroZk.core G 0 tape.1))) = _ at hc
  rw [hc]
  have hz : ∀ equation, statement.linearValue
      (layoutCoreMessages (ConstraintLayout.identity w) (PolygeroZk.core G 0 tape.1)) equation = 0 :=
    PolygeroCoreMasking.zero_encoding_linearValue G.domain G.k_le_n G.productSlots tape.1 statement
      (by
        intro equation block row col h
        cases block with
        | linear => exact (h (Or.inl rfl)).elim
        | left | right | output => exact Fin.elim0 row)
  simp only [hz, mul_zero, Finset.sum_const_zero, zero_add]
  exact (linearMaskMap G.code G.basis ∅ (PolygeroZk.sumFunctional F w) tape.2.1).2.2.2.2

/-- The simulated complete backend view passes the actual opening-only
verifier for every public statement. No witness or reference-witness search
appears in this theorem or in `simulate`. -/
theorem simulate_verifies [DecidableEq F] (hprimary : r+w+s ≤ n)
    (Q : QuerySet n r) (pivot : Fin w) (statement : ConstraintSystem F nw 0 w Equations)
    (coin : Polygero.Coin F Equations nw 0 s) (tape : Tape G nw s) :
    Polygero.verify G.domain G.k_le_n (ConstraintLayout.identity w) statement coin
      (simulate G Q pivot statement coin tape).2 Q (simulate G Q pivot statement coin tape).1 = true := by
  apply (Polygero.verify_openOracle_iff G.domain G.k_le_n hprimary
    (ConstraintLayout.identity w) statement (PolygeroZk.oracle G 0 tape) coin _ Q).2
  constructor
  · unfold Polygero.globalCheck
    simp only [simulate, PolygeroZk.simPayload, PolynomialDirect.responsePolynomial_eval]
    change PolygeroZk.sumFunctional F w
      (witnessValues (PolygeroZk.correctedArithmeticRow G Q pivot statement coin.1 tape).val) = _
    change PolygeroZk.sumFunctional F w
      (witnessValues (PolygeroZk.arithmeticRow G statement coin.1 0 tape).val +
        witnessValues (PolygeroMasking.correction G.code Q (ConstraintLayout.identity w) pivot
          (statement.combinedTarget coin.1))) = _
    rw [map_add, zero_arithmetic_sum]
    exact (zero_add _).trans
      (PolygeroMasking.correction_properties G.code Q (ConstraintLayout.identity w) pivot
        (statement.combinedTarget coin.1)).2.2.2
  · intro j hj
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
    · change (PolygeroPrimaryMasking.response G.positive coin.2
        (PolygeroZk.ordinaryRows G 0 tape.1 tape.2.1) tape.2.2 : F[X]).eval _ = _
      rw [PolygeroPrimaryMasking.response_eval]
      simp only [PolygeroZk.ordinaryRows_eval, RecursivePolygero.Local.response,
        PolynomialDirect.primaryCode, PolygeroZk.oracle]
    · change (PolynomialDirect.responsePolynomial G.domain G.k_le_n
        (PolygeroZk.correctedArithmeticRow G Q pivot statement coin.1 tape).val
        (PolygeroZk.correctedArithmeticRow G Q pivot statement coin.1 tape).property : F[X]).eval _ = _
      rw [PolynomialDirect.responsePolynomial_eval]
      change (PolygeroZk.arithmeticRow G statement coin.1 0 tape).val (codePosition j) +
        PolygeroMasking.correction G.code Q (ConstraintLayout.identity w) pivot
          (statement.combinedTarget coin.1) (codePosition j) = _
      rw [(PolygeroMasking.correction_properties G.code Q (ConstraintLayout.identity w) pivot
        (statement.combinedTarget coin.1)).2.2.1 j hj, add_zero]
      exact PolygeroZk.arithmeticRow_code G statement coin.1 0 tape j
    · intro row
      exact Fin.elim0 row

def coupling [Fintype F] (Q : QuerySet n r) (pivot : Fin w)
    (cells : Cells F nw w) (statement : ConstraintSystem F nw 0 w Equations)
    (hsat : statement.Satisfies (logical cells)) (coin : Polygero.Coin F Equations nw 0 s) :
    Tape G nw s ≃ Tape G nw s :=
  PolygeroZk.adaptiveEquiv G Q pivot (messages cells)
    (fun _ => statement) (fun _ => coin) (fun _ => compatible G cells statement hsat)

theorem coupling_view [Fintype F] (Q : QuerySet n r) (pivot : Fin w)
    (cells : Cells F nw w) (statement : ConstraintSystem F nw 0 w Equations)
    (hsat : statement.Satisfies (logical cells)) (coin : Polygero.Coin F Equations nw 0 s)
    (tape : Tape G nw s) :
    simulate G Q pivot statement coin (coupling G Q pivot cells statement hsat coin tape) =
      real G Q cells statement coin tape := by
  obtain ⟨ho,hp⟩ := PolygeroZk.adaptive_translate G Q pivot (messages cells)
    (fun _ => statement) (fun _ => coin) (fun _ => compatible G cells statement hsat) tape
  exact Prod.ext ho hp

theorem sameDistribution [Fintype F] {Observed : Type} [DecidableEq Observed]
    (Q : QuerySet n r) (pivot : Fin w) (cells : Cells F nw w)
    (statement : ConstraintSystem F nw 0 w Equations)
    (hsat : statement.Satisfies (logical cells)) (coin : Polygero.Coin F Equations nw 0 s)
    (observe : View (F := F) w nw s Q → Observed) :
    SameDistribution (fun tape => observe (real G Q cells statement coin tape))
      (fun tape => observe (simulate G Q pivot statement coin tape)) := by
  apply sameDistribution_of_equiv (coupling G Q pivot cells statement hsat coin)
  intro tape
  rw [coupling_view]

end LfzkV2.Current.ZeroKnowledge.Backend
