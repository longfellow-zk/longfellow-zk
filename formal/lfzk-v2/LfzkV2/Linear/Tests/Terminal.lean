import LfzkV2.Linear.Prover
import LfzkV2.Linear.Sizes
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-! Regression examples exercise arbitrary product pads and the two-root
loss. The product equality is deliberately false in the malicious example. -/

namespace LfzkV2.Linear.Tests

open SumcheckV2.LinearTerminal

private instance : Fact (Nat.Prime 101) := ⟨by decide⟩

private def malicious : Data (ZMod 101) :=
  ⟨2, 0, 0, -3, ⟨0, 0, 1, 0⟩⟩

example : malicious.pads.ab ≠ malicious.pads.a * malicious.pads.b := by
  norm_num [malicious]

example : malicious.Bad 1 ∧ malicious.Bad 2 := by
  norm_num [Data.Bad, Data.error, malicious, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
  decide

example : ¬ malicious.Bad 0 := by
  norm_num [Data.Bad, Data.error, malicious, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]

example : SumcheckV2.LinearTerminal.residual (2 : ZMod 101) (-3) 1 0 0 ⟨0,0,1,0⟩ = 0 := by
  norm_num [SumcheckV2.LinearTerminal.residual]

example (A B pA pB pD scale : ZMod 2) :
    SumcheckV2.LinearTerminal.residual (A*B) (A*pB+B*pA-pD) scale (A+scale*pA) (B+scale*pB)
      ⟨pA,pB,pA*pB,pD⟩ = 0 := completeness A B pA pB pD scale

example (A B : ZMod 101) (p : ZMod 101 × ZMod 101 × ZMod 101) :
    recoverPads A B 7 (honestMessages A B 7 p) = p :=
  recover_honest A B 7 (by decide) p

example (A B : ZMod 2) (p : ZMod 2 × ZMod 2 × ZMod 2) :
    recoverPads A B 1 (honestMessages A B 1 p) = p :=
  recover_honest A B 1 (by norm_num) p

/-- Zero scale exposes the true claims, hence the nonzero sampler is part of
both the protocol and the local hiding statement. -/
example (A B : ZMod 101) (p : ZMod 101 × ZMod 101 × ZMod 101) :
    (honestMessages A B 0 p).2 = (A,B) := by simp [honestMessages]

end LfzkV2.Linear.Tests
