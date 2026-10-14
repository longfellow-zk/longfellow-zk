import LigeroFamily.Protocol.Policy

/-!
# Challenge-free direct product arithmetic

This is the common arithmetic policy used by V3.  It retains the ordinary
affine proximity response and the masked linear response, but checks every
quadratic row directly in each opened column.  There is no quadratic
challenge, response, mask, or aggregation.
-/

namespace LigeroFamily

open MultiplicativeCode

variable {F Equations : Type*} [Field F] [Fintype Equations]
variable {q r w n nw nq repetitions : ℕ}

/-- The two checked base-code rows needed by the linear response. -/
inductive LinearConstraintMask
  | vCoefficient
  | zRCoefficient
  deriving DecidableEq, Fintype

@[simp] theorem linearConstraintMask_card :
    Fintype.card LinearConstraintMask = 2 := by decide

/-- Honest encoding data for direct-product rows.  The input encoder may use
a lower-degree subcode, but malicious rows are checked only against `C.base`.
Products of honestly encoded inputs land in `C.base`, so the derived output
row participates in the ordinary proximity test. -/
structure DirectProductCode
    (C : MultiplicativeCode F r w n)
    (layout : ConstraintLayout F q w) where
  input : (Fin r → F) → (Fin q → F) → EvaluationRow F r w n
  input_mem : ∀ padding values, input padding values ∈ C.base
  input_random : ∀ padding values i,
    input padding values (randomPosition i) = padding i
  input_logical : ∀ padding values i,
    input padding values (logicalWitnessPosition layout i) = values i
  input_opening_injective : ∀ (Q : Finset (Fin n)), Q.card = r → ∀ values,
    Function.Injective (fun padding : Fin r → F ↦ fun j : ↥Q ↦
      input padding values (codePosition j.1))
  product_mem : ∀ {left right : EvaluationRow F r w n},
    left ∈ C.base → right ∈ C.base →
    (∃ leftPadding leftValues, left = input leftPadding leftValues) →
    (∃ rightPadding rightValues, right = input rightPadding rightValues) →
    rowMul left right ∈ C.base

namespace DirectProductCode

variable {C : MultiplicativeCode F r w n}
variable {layout : ConstraintLayout F q w}

/-- Reindex an `r`-element query set by `Fin r`. -/
noncomputable def queryCoordinateEquiv (query : QuerySet n r) :
    ↥query.coordinates ≃ Fin r :=
  Fintype.equivOfCardEq (by simp [QuerySet.card_coordinates])

/-- The two function spaces used by an `r`-opening map have equal finite
cardinality. -/
noncomputable def openingSpaceEquiv [Fintype F] (query : QuerySet n r) :
    (↥query.coordinates → F) ≃ (Fin r → F) where
  toFun opened i := opened ((queryCoordinateEquiv query).symm i)
  invFun padding j := padding (queryCoordinateEquiv query j)
  left_inv opened := by funext j; simp
  right_inv padding := by funext i; simp

/-- For a finite field, the input-opening injectivity contract is a
bijection: after fixing the logical values, arbitrary `r` openings determine
and are attained by a unique random prefix. -/
theorem input_opening_bijective [Fintype F]
    (P : DirectProductCode C layout) (query : QuerySet n r)
    (values : Fin q → F) :
    Function.Bijective (fun padding : Fin r → F ↦
      fun j : ↥query.coordinates ↦
        P.input padding values (codePosition j.1)) := by
  let opened := fun padding : Fin r → F ↦ fun j : ↥query.coordinates ↦
    P.input padding values (codePosition j.1)
  have hinjective : Function.Injective opened :=
    P.input_opening_injective query.coordinates
      (QuerySet.card_coordinates query) values
  let reindexed := openingSpaceEquiv query ∘ opened
  have hreindexed : Function.Injective reindexed :=
    (openingSpaceEquiv query).injective.comp hinjective
  have hsurjective : Function.Surjective opened := by
    intro target
    obtain ⟨padding, hpadding⟩ := hreindexed.bijective_of_finite.2
      (openingSpaceEquiv query target)
    exact ⟨padding, (openingSpaceEquiv query).injective hpadding⟩
  exact ⟨hinjective, hsurjective⟩

end DirectProductCode

structure DirectRoundChallenge (F Equations : Type*)
    (nw nq repetitions : ℕ) where
  proximity : SchemeTestedRow LinearConstraintMask nw nq repetitions → F
  linear : Equations → F

instance directRoundChallengeNonempty
    {F Equations : Type*} [Zero F] {nw nq repetitions : ℕ} :
    Nonempty (DirectRoundChallenge F Equations nw nq repetitions) :=
  ⟨⟨0, 0⟩⟩

def directRoundChallengeEquiv (F Equations : Type*)
    (nw nq repetitions : ℕ) :
    DirectRoundChallenge F Equations nw nq repetitions ≃
      (SchemeTestedRow LinearConstraintMask nw nq repetitions → F) ×
        (Equations → F) where
  toFun challenge := (challenge.proximity, challenge.linear)
  invFun fields := ⟨fields.1, fields.2⟩
  left_inv challenge := by cases challenge; rfl
  right_inv fields := by cases fields; rfl

noncomputable instance directRoundChallengeFintype
    {F Equations : Type*} [Fintype F] [Fintype Equations]
    {nw nq repetitions : ℕ} :
    Fintype (DirectRoundChallenge F Equations nw nq repetitions) := by
  letI : Fintype
      ((SchemeTestedRow LinearConstraintMask nw nq repetitions → F) ×
        (Equations → F)) := Fintype.ofFinite _
  exact Fintype.ofEquiv _
    (directRoundChallengeEquiv F Equations nw nq repetitions).symm

noncomputable instance directRoundChallengeDecidableEq
    {F Equations : Type*} [DecidableEq F] [DecidableEq Equations]
    {nw nq repetitions : ℕ} :
    DecidableEq (DirectRoundChallenge F Equations nw nq repetitions) :=
  Classical.decEq _

abbrev DirectChallenge (F Equations : Type*)
    (nw nq repetitions : ℕ) :=
  Fin repetitions → DirectRoundChallenge F Equations nw nq repetitions

structure DirectResponse (F : Type*) (r w n repetitions : ℕ) where
  proximity : Fin repetitions → EvaluationRow F r w n
  linear : Fin repetitions → EvaluationRow F r w n
  deriving DecidableEq

omit [Field F] in
@[ext] theorem DirectResponse.ext
    {first second : DirectResponse F r w n repetitions}
    (hproximity : first.proximity = second.proximity)
    (hlinear : first.linear = second.linear) : first = second := by
  cases first
  cases second
  simp_all

namespace DirectVerifier

noncomputable def coefficientRow
    (C : MultiplicativeCode F r w n) (layout : ConstraintLayout F q w)
    (statement : ConstraintSystem F nw nq q Equations)
    (weights : Equations → F) (block : CoreBlock)
    (row : Fin (block.rowCount nw nq)) : EvaluationRow F r w n :=
  C.encode 0 (layout.extend (statement.A weights block row))

noncomputable def linearCore
    (C : MultiplicativeCode F r w n) (layout : ConstraintLayout F q w)
    (statement : ConstraintSystem F nw nq q Equations)
    (weights : Equations → F)
    (core : (block : CoreBlock) → Fin (block.rowCount nw nq) →
      EvaluationRow F r w n) : EvaluationRow F r w n :=
  ∑ block : CoreBlock, ∑ row : Fin (block.rowCount nw nq),
    rowMul (coefficientRow C layout statement weights block row) (core block row)

noncomputable def linearMask
    (C : MultiplicativeCode F r w n) (M : C.MaskingBasis)
    (mask : LinearConstraintMask → EvaluationRow F r w n) :
    EvaluationRow F r w n :=
  rowMul M.vanishing (mask .vCoefficient) +
    rowMul C.zR (mask .zRCoefficient)

noncomputable def linearResponse
    (C : MultiplicativeCode F r w n) (M : C.MaskingBasis)
    (layout : ConstraintLayout F q w)
    (statement : ConstraintSystem F nw nq q Equations)
    (weights : Equations → F)
    (core : (block : CoreBlock) → Fin (block.rowCount nw nq) →
      EvaluationRow F r w n)
    (mask : LinearConstraintMask → EvaluationRow F r w n) :
    EvaluationRow F r w n :=
  linearCore C layout statement weights core + linearMask C M mask

def ProximityAccepts
    (C : MultiplicativeCode F r w n)
    (weights : SchemeTestedRow LinearConstraintMask nw nq repetitions → F)
    (response : EvaluationRow F r w n) (query : QuerySet n r)
    (opening : SchemeOpening F LinearConstraintMask NoMask nw nq repetitions n r query)
    (h : Fin repetitions) : Prop :=
  SchemeVerifier.ProximityAccepts C weights response query opening h

noncomputable def LinearAccepts
    (C : MultiplicativeCode F r w n) (M : C.MaskingBasis)
    (layout : ConstraintLayout F q w)
    (statement : ConstraintSystem F nw nq q Equations)
    (weights : Equations → F) (response : EvaluationRow F r w n)
    (query : QuerySet n r)
    (opening : SchemeOpening F LinearConstraintMask NoMask nw nq repetitions n r query)
    (h : Fin repetitions) : Prop :=
  response ∈ C.response ∧
    (∑ i : Fin q, response (logicalWitnessPosition layout i)) =
      statement.combinedTarget weights ∧
    ∀ j : ↥query.coordinates,
      response (codePosition j.1) =
        (∑ block : CoreBlock,
          ∑ row : Fin (block.rowCount nw nq),
            coefficientRow C layout statement weights block row
                (codePosition j.1) * (opening j).core block row) +
        M.vanishing (codePosition j.1) *
          (opening j).checkedMask h .vCoefficient +
        C.zR (codePosition j.1) *
          (opening j).checkedMask h .zRCoefficient

/-- Every multiplication row is checked separately at every opened code
coordinate. -/
def DirectProductAccepts
    (query : QuerySet n r)
    (opening : SchemeOpening F LinearConstraintMask NoMask nw nq repetitions n r query) :
    Prop :=
  ∀ j : ↥query.coordinates, ∀ row : Fin nq,
    (opening j).core .left row * (opening j).core .right row =
      (opening j).core .output row

noncomputable def Accepts
    (C : MultiplicativeCode F r w n) (M : C.MaskingBasis)
    (layout : ConstraintLayout F q w)
    (statement : ConstraintSystem F nw nq q Equations)
    (challenge : DirectChallenge F Equations nw nq repetitions)
    (response : DirectResponse F r w n repetitions)
    (query : QuerySet n r)
    (opening : SchemeOpening F LinearConstraintMask NoMask nw nq repetitions n r query) :
    Prop :=
  (∀ h : Fin repetitions,
    ProximityAccepts C (challenge h).proximity (response.proximity h)
      query opening h ∧
    LinearAccepts C M layout statement (challenge h).linear
      (response.linear h) query opening h) ∧
  DirectProductAccepts query opening

noncomputable def policy
    (C : MultiplicativeCode F r w n) (M : C.MaskingBasis)
    (layout : ConstraintLayout F q w) :
    SchemeProtocolPolicy (Equations := Equations) C layout
      (DirectChallenge F Equations nw nq repetitions)
      (DirectResponse F r w n repetitions)
      LinearConstraintMask NoMask nw nq repetitions where
  proximityWeights challenge h := (challenge h).proximity
  proximityResponse response h := response.proximity h
  accepts := Accepts C M layout
  accepts_proximity := by
    intro statement challenge response query opening haccept h
    exact (haccept.1 h).1

noncomputable def protocol
    (C : MultiplicativeCode F r w n) (M : C.MaskingBasis)
    (layout : ConstraintLayout F q w) :=
  (policy (Equations := Equations) (nw := nw) (nq := nq)
    (repetitions := repetitions) C M layout).protocol

end DirectVerifier

end LigeroFamily
