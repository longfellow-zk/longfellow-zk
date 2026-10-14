import LigeroFamily.Protocol.IPCP

/-! # Ligero V2 masking and verifier

V2 is the checked four-row instance of the generic mask-scheme protocol.
These concrete types live in the Ligero V2 child; no record conversion is
needed to use the shared extractor or finite-protocol semantics.
-/

namespace Ligero.V2

open LigeroFamily
open LigeroFamily.MultiplicativeCode

variable {F Equations : Type*} [Field F] [Fintype Equations]
variable {r w n nw nq repetitions : ℕ}

/-- Four base-code masking rows included in V2's proximity matrix. -/
inductive Mask
  | quadraticVCoefficient
  | quadraticZWCoefficient
  | linearVCoefficient
  | linearZRCoefficient
  deriving DecidableEq, Fintype

@[simp] theorem mask_card : Fintype.card Mask = 4 := by decide

abbrev TestedRow (nw nq repetitions : ℕ) :=
  SchemeTestedRow Mask nw nq repetitions

abbrev Scheme (F : Type*) (r w n : ℕ) :=
  MaskScheme F Mask NoMask r w n

/-- V2's checked base-code masking scheme. -/
noncomputable def scheme
    (C : MultiplicativeCode F r w n) (M : C.MaskingBasis) :
    Scheme F r w n where
  linearAt position mask _ :=
    M.vanishing position * mask .linearVCoefficient +
      C.zR position * mask .linearZRCoefficient
  quadraticAt position mask _ :=
    M.vanishing position * mask .quadraticVCoefficient +
      C.zW position * mask .quadraticZWCoefficient

abbrev Oracle (F : Type*) (nw nq n repetitions : ℕ) :=
  SchemeOracle F Mask NoMask nw nq n repetitions

abbrev Opening (F : Type*) (nw nq repetitions n r : ℕ)
    (query : QuerySet n r) :=
  SchemeOpening F Mask NoMask nw nq repetitions n r query

abbrev RoundChallenge (F : Type*) (nw nq repetitions : ℕ)
    (Equations : Type*) :=
  SchemeRoundChallenge F Mask nw nq repetitions Equations

abbrev Challenge (F : Type*) (nw nq repetitions : ℕ) (Equations : Type*) :=
  SchemeChallenge F Mask nw nq repetitions Equations

namespace Verifier

noncomputable def linearMask
    (C : MultiplicativeCode F r w n) (M : C.MaskingBasis)
    (mask : Mask → EvaluationRow F r w n) : EvaluationRow F r w n :=
  rowMul M.vanishing (mask .linearVCoefficient) +
    rowMul C.zR (mask .linearZRCoefficient)

noncomputable def linearResponse
    (C : MultiplicativeCode F r w n) (M : C.MaskingBasis)
    (statement : ConstraintSystem F nw nq w Equations)
    (weights : Equations → F)
    (core : (block : CoreBlock) → Fin (block.rowCount nw nq) →
      EvaluationRow F r w n)
    (mask : Mask → EvaluationRow F r w n) : EvaluationRow F r w n :=
  LigeroFamily.Verifier.linearCore C statement weights core +
    linearMask C M mask

noncomputable def quadraticMask
    (C : MultiplicativeCode F r w n) (M : C.MaskingBasis)
    (mask : Mask → EvaluationRow F r w n) : EvaluationRow F r w n :=
  rowMul M.vanishing (mask .quadraticVCoefficient) +
    rowMul C.zW (mask .quadraticZWCoefficient)

noncomputable def quadraticResponse
    (C : MultiplicativeCode F r w n) (M : C.MaskingBasis)
    (weights : Fin nq → F)
    (core : (block : CoreBlock) → Fin (block.rowCount nw nq) →
      EvaluationRow F r w n)
    (mask : Mask → EvaluationRow F r w n) : EvaluationRow F r w n :=
  LigeroFamily.Verifier.quadraticCore weights core + quadraticMask C M mask

def ProximityAccepts
    (C : MultiplicativeCode F r w n)
    (weights : TestedRow nw nq repetitions → F)
    (response : EvaluationRow F r w n) (query : QuerySet n r)
    (opening : Opening F nw nq repetitions n r query)
    (h : Fin repetitions) : Prop :=
  SchemeVerifier.ProximityAccepts C weights response query opening h

noncomputable def LinearAccepts
    (C : MultiplicativeCode F r w n) (M : C.MaskingBasis)
    (statement : ConstraintSystem F nw nq w Equations) (weights : Equations → F)
    (response : EvaluationRow F r w n) (query : QuerySet n r)
    (opening : Opening F nw nq repetitions n r query)
    (h : Fin repetitions) : Prop :=
  SchemeVerifier.LinearAccepts C (scheme C M) statement weights response
    query opening h

def QuadraticAccepts
    (C : MultiplicativeCode F r w n) (M : C.MaskingBasis)
    (weights : Fin nq → F) (response : EvaluationRow F r w n)
    (query : QuerySet n r) (opening : Opening F nw nq repetitions n r query)
    (h : Fin repetitions) : Prop :=
  SchemeVerifier.QuadraticAccepts C (scheme C M) weights response query opening h

noncomputable def Accepts
    (C : MultiplicativeCode F r w n) (M : C.MaskingBasis)
    (statement : ConstraintSystem F nw nq w Equations)
    (challenge : Challenge F nw nq repetitions Equations)
    (response : Response F r w n repetitions) (query : QuerySet n r)
    (opening : Opening F nw nq repetitions n r query) : Prop :=
  SchemeVerifier.Accepts C (scheme C M) statement challenge response query opening

noncomputable def protocol
    (C : MultiplicativeCode F r w n) (M : C.MaskingBasis) :=
  SchemeVerifier.protocol (nw := nw) (nq := nq) (repetitions := repetitions)
    (Equations := Equations) C (scheme C M)

end Verifier

end Ligero.V2
