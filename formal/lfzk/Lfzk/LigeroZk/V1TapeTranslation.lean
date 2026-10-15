import Ligero.V1.Protocol.Protocol
import Lfzk.LigeroZk.CoreTranslation

-- Ported verbatim from `proofs/ligero/Ligero/V1/ZeroKnowledge/TapeTranslation.lean` (only the import paths are rewritten);
-- `formal/ligero/` must not change, so the module lives under `Lfzk.LigeroZk`.
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# V1 prover-tape reparameterization

V1 uses the same translated core rows as V2.  Its two direct response masks
are then translated by the difference of the old and new canonical response,
and its proximity blind is translated by the difference of the two challenged
core combinations.  Every adjustment vanishes on the queried columns.
-/

namespace Ligero.V1

open LigeroFamily

open MultiplicativeCode

variable {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Equations]
variable {r w n nw nq repetitions : ℕ}

namespace V1ProverRandomness

variable {C : MultiplicativeCode F r w n}
variable {statement : ConstraintSystem F nw nq w Equations}

/-- Translate every core prefix so that changing the witness leaves the
queried core openings unchanged. -/
noncomputable def translatedCorePadding
    (fromMessages toMessages : CoreMessages F nw nq w)
    (query : QuerySet n r) (seed : V1ProverRandomness C nw nq repetitions) :
    (block : CoreBlock) → Fin (block.rowCount nw nq) → Fin r → F :=
  fun block row ↦ translateCorePadding C query
    (fromMessages block row) (toMessages block row)
    (seed.corePadding block row)

/-- The temporary target encoding before the direct masks and proximity blind
are retuned. -/
noncomputable def coreTranslatedEncoding
    (fromMessages toMessages : CoreMessages F nw nq w)
    (toSatisfies : statement.Satisfies toMessages)
    (query : QuerySet n r) (seed : V1ProverRandomness C nw nq repetitions) :
    V1HonestEncoding (repetitions := repetitions) C statement toMessages :=
  ({ seed with corePadding :=
      translatedCorePadding fromMessages toMessages query seed } :
    V1ProverRandomness C nw nq repetitions).encoding toMessages toSatisfies

omit [Fintype F] [Fintype Equations] [DecidableEq F] in
theorem coreTranslatedEncoding_query
    (fromMessages toMessages : CoreMessages F nw nq w)
    (fromSatisfies : statement.Satisfies fromMessages)
    (toSatisfies : statement.Satisfies toMessages)
    (query : QuerySet n r) (seed : V1ProverRandomness C nw nq repetitions)
    (block : CoreBlock) (row : Fin (block.rowCount nw nq))
    (j : ↥query.coordinates) :
    (coreTranslatedEncoding fromMessages toMessages toSatisfies query seed).core
        block row (codePosition j.1) =
      (seed.encoding fromMessages fromSatisfies).core
        block row (codePosition j.1) := by
  exact congrFun
    (translateCorePadding_opening C query (fromMessages block row)
      (toMessages block row) (seed.corePadding block row)) j

/-- Difference of the old and new unmasked linear responses.  It is itself a
legal V1 linear mask. -/
noncomputable def linearAdjustment
    (fromMessages toMessages : CoreMessages F nw nq w)
    (fromSatisfies : statement.Satisfies fromMessages)
    (toSatisfies : statement.Satisfies toMessages)
    (query : QuerySet n r) (challenge : Challenge F nw nq repetitions Equations)
    (seed : V1ProverRandomness C nw nq repetitions) (h : Fin repetitions) :
    V1LinearMaskSpace C := by
  let source := seed.encoding fromMessages fromSatisfies
  let target := coreTranslatedEncoding fromMessages toMessages toSatisfies
    query seed
  let sourceCore := source.honestCore.linearResponse (challenge h).linear
  let targetCore := target.honestCore.linearResponse (challenge h).linear
  refine ⟨sourceCore - targetCore, ?_, ?_⟩
  · exact C.response.sub_mem
      (source.honestCore.linearResponse_mem (challenge h).linear)
      (target.honestCore.linearResponse_mem (challenge h).linear)
  · simp only [Pi.sub_apply, Finset.sum_sub_distrib]
    rw [source.honestCore.linearResponse_sum (challenge h).linear,
      target.honestCore.linearResponse_sum (challenge h).linear, sub_self]

/-- Difference of the old and new unmasked quadratic responses. -/
noncomputable def quadraticAdjustment
    (fromMessages toMessages : CoreMessages F nw nq w)
    (fromSatisfies : statement.Satisfies fromMessages)
    (toSatisfies : statement.Satisfies toMessages)
    (query : QuerySet n r) (challenge : Challenge F nw nq repetitions Equations)
    (seed : V1ProverRandomness C nw nq repetitions) (h : Fin repetitions) :
    V1QuadraticMaskSpace C := by
  let source := seed.encoding fromMessages fromSatisfies
  let target := coreTranslatedEncoding fromMessages toMessages toSatisfies
    query seed
  let sourceCore := source.honestCore.quadraticResponse (challenge h).quadratic
  let targetCore := target.honestCore.quadraticResponse (challenge h).quadratic
  refine ⟨sourceCore - targetCore, ?_, ?_⟩
  · exact C.response.sub_mem
      (source.honestCore.quadraticResponse_mem (challenge h).quadratic)
      (target.honestCore.quadraticResponse_mem (challenge h).quadratic)
  · intro i
    simp [sourceCore, targetCore,
      source.honestCore.quadraticResponse_witness (challenge h).quadratic i,
      target.honestCore.quadraticResponse_witness (challenge h).quadratic i]

omit [Fintype F] [DecidableEq F] in
theorem linearAdjustment_query
    (fromMessages toMessages : CoreMessages F nw nq w)
    (fromSatisfies : statement.Satisfies fromMessages)
    (toSatisfies : statement.Satisfies toMessages)
    (query : QuerySet n r) (challenge : Challenge F nw nq repetitions Equations)
    (seed : V1ProverRandomness C nw nq repetitions) (h : Fin repetitions)
    (j : ↥query.coordinates) :
    (linearAdjustment fromMessages toMessages fromSatisfies toSatisfies query
      challenge seed h : EvaluationRow F r w n) (codePosition j.1) = 0 := by
  simp only [linearAdjustment, HonestCore.linearResponse, Verifier.linearCore,
    Pi.sub_apply, Finset.sum_apply, rowMul_apply,
    V1HonestEncoding.honestCore]
  apply sub_eq_zero.mpr
  apply Finset.sum_congr rfl
  intro block _
  apply Finset.sum_congr rfl
  intro row _
  rw [coreTranslatedEncoding_query fromMessages toMessages fromSatisfies
    toSatisfies query seed block row j]

omit [Fintype F] [Fintype Equations] [DecidableEq F] in
theorem quadraticAdjustment_query
    (fromMessages toMessages : CoreMessages F nw nq w)
    (fromSatisfies : statement.Satisfies fromMessages)
    (toSatisfies : statement.Satisfies toMessages)
    (query : QuerySet n r) (challenge : Challenge F nw nq repetitions Equations)
    (seed : V1ProverRandomness C nw nq repetitions) (h : Fin repetitions)
    (j : ↥query.coordinates) :
    (quadraticAdjustment fromMessages toMessages fromSatisfies toSatisfies query
      challenge seed h : EvaluationRow F r w n) (codePosition j.1) = 0 := by
  simp only [quadraticAdjustment, HonestCore.quadraticResponse,
    Verifier.quadraticCore, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply,
    rowMul_apply, smul_eq_mul, V1HonestEncoding.honestCore]
  apply sub_eq_zero.mpr
  apply Finset.sum_congr rfl
  intro row _
  rw [coreTranslatedEncoding_query fromMessages toMessages fromSatisfies
      toSatisfies query seed .left row j,
    coreTranslatedEncoding_query fromMessages toMessages fromSatisfies
      toSatisfies query seed .right row j,
    coreTranslatedEncoding_query fromMessages toMessages fromSatisfies
      toSatisfies query seed .output row j]

/-- Difference of the challenged proximity combinations of old and new core
rows. -/
noncomputable def proximityAdjustment
    (fromMessages toMessages : CoreMessages F nw nq w)
    (fromSatisfies : statement.Satisfies fromMessages)
    (toSatisfies : statement.Satisfies toMessages)
    (query : QuerySet n r) (challenge : Challenge F nw nq repetitions Equations)
    (seed : V1ProverRandomness C nw nq repetitions) (h : Fin repetitions) :
    C.base := by
  let source := seed.encoding fromMessages fromSatisfies
  let target := coreTranslatedEncoding fromMessages toMessages toSatisfies
    query seed
  refine ⟨∑ row : SchemeTestedRow NoMask nw nq repetitions,
      (challenge h).proximity row •
        (match row with
        | Sum.inl core => source.core core.1 core.2 - target.core core.1 core.2
        | Sum.inr impossible => NoMask.elim impossible.2), ?_⟩
  apply Submodule.sum_mem
  intro row _
  cases row with
  | inl core =>
      exact C.base.smul_mem _
        (C.base.sub_mem (source.core_mem core.1 core.2)
          (target.core_mem core.1 core.2))
  | inr impossible => exact NoMask.elim impossible.2

omit [Fintype F] [Fintype Equations] [DecidableEq F] in
theorem proximityAdjustment_query
    (fromMessages toMessages : CoreMessages F nw nq w)
    (fromSatisfies : statement.Satisfies fromMessages)
    (toSatisfies : statement.Satisfies toMessages)
    (query : QuerySet n r) (challenge : Challenge F nw nq repetitions Equations)
    (seed : V1ProverRandomness C nw nq repetitions) (h : Fin repetitions)
    (j : ↥query.coordinates) :
    (proximityAdjustment fromMessages toMessages fromSatisfies toSatisfies query
      challenge seed h : EvaluationRow F r w n) (codePosition j.1) = 0 := by
  simp only [proximityAdjustment, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro row _
  cases row with
  | inl core =>
      change (challenge h).proximity (Sum.inl core) *
        ((seed.encoding fromMessages fromSatisfies).core core.1 core.2
            (codePosition j.1) -
          (coreTranslatedEncoding fromMessages toMessages toSatisfies query seed).core
            core.1 core.2 (codePosition j.1)) = 0
      rw [coreTranslatedEncoding_query fromMessages toMessages fromSatisfies
        toSatisfies query seed core.1 core.2 j]
      ring
  | inr impossible => exact NoMask.elim impossible.2

/-- Fixed-query, fixed-challenge translation of the complete V1 tape. -/
noncomputable def translateRandomness
    (fromMessages toMessages : CoreMessages F nw nq w)
    (fromSatisfies : statement.Satisfies fromMessages)
    (toSatisfies : statement.Satisfies toMessages)
    (query : QuerySet n r) (challenge : Challenge F nw nq repetitions Equations)
    (seed : V1ProverRandomness C nw nq repetitions) :
    V1ProverRandomness C nw nq repetitions := {
  corePadding := translatedCorePadding fromMessages toMessages query seed
  linearMask := fun h ↦ seed.linearMask h +
    linearAdjustment fromMessages toMessages fromSatisfies toSatisfies query
      challenge seed h
  quadraticMask := fun h ↦ seed.quadraticMask h +
    quadraticAdjustment fromMessages toMessages fromSatisfies toSatisfies query
      challenge seed h
  proximityBlind := fun h ↦ seed.proximityBlind h +
    proximityAdjustment fromMessages toMessages fromSatisfies toSatisfies query
      challenge seed h }

omit [Fintype F] [DecidableEq F] in
/-- Both arithmetic responses and the proximity response are invariant under
the V1 tape translation. -/
theorem translateRandomness_response
    (fromMessages toMessages : CoreMessages F nw nq w)
    (fromSatisfies : statement.Satisfies fromMessages)
    (toSatisfies : statement.Satisfies toMessages)
    (query : QuerySet n r) (challenge : Challenge F nw nq repetitions Equations)
    (seed : V1ProverRandomness C nw nq repetitions) :
    ((translateRandomness fromMessages toMessages fromSatisfies toSatisfies
      query challenge seed).encoding toMessages toSatisfies).response challenge =
      (seed.encoding fromMessages fromSatisfies).response challenge := by
  apply Response.ext
  · funext h
    let source := seed.encoding fromMessages fromSatisfies
    let target := coreTranslatedEncoding fromMessages toMessages toSatisfies
      query seed
    let sourceRow : SchemeTestedRow NoMask nw nq repetitions →
        EvaluationRow F r w n
      | Sum.inl core => source.core core.1 core.2
      | Sum.inr impossible => NoMask.elim impossible.2
    let targetRow : SchemeTestedRow NoMask nw nq repetitions →
        EvaluationRow F r w n
      | Sum.inl core => target.core core.1 core.2
      | Sum.inr impossible => NoMask.elim impossible.2
    let differenceRow : SchemeTestedRow NoMask nw nq repetitions →
        EvaluationRow F r w n
      | Sum.inl core => source.core core.1 core.2 - target.core core.1 core.2
      | Sum.inr impossible => NoMask.elim impossible.2
    have hsum :
        (∑ row, (challenge h).proximity row • targetRow row) +
            (∑ row, (challenge h).proximity row •
              differenceRow row) =
          ∑ row, (challenge h).proximity row • sourceRow row := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro row _
      cases row with
      | inl core => module
      | inr impossible => exact NoMask.elim impossible.2
    dsimp only [V1HonestEncoding.response, V1HonestEncoding.proximityResponse,
      V1ProverRandomness.encoding, translateRandomness]
    simp only [Submodule.coe_add, proximityAdjustment]
    change (∑ row, (challenge h).proximity row • targetRow row) +
          (seed.proximityBlind h +
            ∑ row, (challenge h).proximity row •
              differenceRow row) =
        (∑ row, (challenge h).proximity row • sourceRow row) +
          seed.proximityBlind h
    rw [show (∑ row, (challenge h).proximity row • targetRow row) +
          (seed.proximityBlind h +
            ∑ row, (challenge h).proximity row •
              differenceRow row) =
        ((∑ row, (challenge h).proximity row • targetRow row) +
          ∑ row, (challenge h).proximity row •
            differenceRow row) + seed.proximityBlind h by abel]
    rw [hsum]
  · funext h position
    let source := seed.encoding fromMessages fromSatisfies
    let target := coreTranslatedEncoding fromMessages toMessages toSatisfies
      query seed
    change (target.honestCore.linearResponse (challenge h).linear +
        (seed.linearMask h +
          linearAdjustment fromMessages toMessages fromSatisfies toSatisfies
            query challenge seed h)) position =
      (source.honestCore.linearResponse (challenge h).linear +
        seed.linearMask h) position
    simp only [linearAdjustment, Pi.add_apply, Pi.sub_apply, source, target]
    ring
  · funext h position
    let source := seed.encoding fromMessages fromSatisfies
    let target := coreTranslatedEncoding fromMessages toMessages toSatisfies
      query seed
    change (target.honestCore.quadraticResponse (challenge h).quadratic +
        (seed.quadraticMask h +
          quadraticAdjustment fromMessages toMessages fromSatisfies toSatisfies
            query challenge seed h)) position =
      (source.honestCore.quadraticResponse (challenge h).quadratic +
        seed.quadraticMask h) position
    simp only [quadraticAdjustment, Pi.add_apply, Pi.sub_apply,
      source, target]
    ring

omit [Fintype F] [DecidableEq F] in
/-- All queried V1 oracle columns are invariant under tape translation. -/
theorem translateRandomness_opening
    (fromMessages toMessages : CoreMessages F nw nq w)
    (fromSatisfies : statement.Satisfies fromMessages)
    (toSatisfies : statement.Satisfies toMessages)
    (query : QuerySet n r) (challenge : Challenge F nw nq repetitions Equations)
    (seed : V1ProverRandomness C nw nq repetitions) :
    openSchemeOracle
        ((translateRandomness fromMessages toMessages fromSatisfies toSatisfies
          query challenge seed).encoding toMessages toSatisfies).oracle query =
      openSchemeOracle (seed.encoding fromMessages fromSatisfies).oracle query := by
  funext j
  apply SchemeColumn.ext
  · funext block row
    exact coreTranslatedEncoding_query fromMessages toMessages fromSatisfies
      toSatisfies query seed block row j
  · funext h impossible
    exact NoMask.elim impossible
  · funext h kind
    cases kind <;>
      simp only [openSchemeOracle, SchemeOracle.column, V1HonestEncoding.oracle,
        V1ProverRandomness.encoding, translateRandomness, Submodule.coe_add,
        Pi.add_apply]
    · rw [linearAdjustment_query fromMessages toMessages fromSatisfies
        toSatisfies query challenge seed h j, add_zero]
    · rw [quadraticAdjustment_query fromMessages toMessages fromSatisfies
        toSatisfies query challenge seed h j, add_zero]
  · funext h
    simp only [openSchemeOracle, SchemeOracle.column, V1HonestEncoding.oracle,
      V1ProverRandomness.encoding, translateRandomness, Submodule.coe_add,
      Pi.add_apply]
    rw [proximityAdjustment_query fromMessages toMessages fromSatisfies
      toSatisfies query challenge seed h j, add_zero]

omit [Fintype F] [DecidableEq F] in
private theorem linearAdjustment_eq_of_corePadding_eq
    (fromMessages toMessages : CoreMessages F nw nq w)
    (fromSatisfies : statement.Satisfies fromMessages)
    (toSatisfies : statement.Satisfies toMessages)
    (query : QuerySet n r) (challenge : Challenge F nw nq repetitions Equations)
    (first second : V1ProverRandomness C nw nq repetitions)
    (hcore : first.corePadding = second.corePadding) (h : Fin repetitions) :
    linearAdjustment fromMessages toMessages fromSatisfies toSatisfies query
        challenge first h =
      linearAdjustment fromMessages toMessages fromSatisfies toSatisfies query
        challenge second h := by
  cases first; cases second; subst hcore; rfl

omit [Fintype F] [Fintype Equations] [DecidableEq F] in
private theorem quadraticAdjustment_eq_of_corePadding_eq
    (fromMessages toMessages : CoreMessages F nw nq w)
    (fromSatisfies : statement.Satisfies fromMessages)
    (toSatisfies : statement.Satisfies toMessages)
    (query : QuerySet n r) (challenge : Challenge F nw nq repetitions Equations)
    (first second : V1ProverRandomness C nw nq repetitions)
    (hcore : first.corePadding = second.corePadding) (h : Fin repetitions) :
    quadraticAdjustment fromMessages toMessages fromSatisfies toSatisfies query
        challenge first h =
      quadraticAdjustment fromMessages toMessages fromSatisfies toSatisfies query
        challenge second h := by
  cases first; cases second; subst hcore; rfl

omit [Fintype F] [Fintype Equations] [DecidableEq F] in
private theorem proximityAdjustment_eq_of_corePadding_eq
    (fromMessages toMessages : CoreMessages F nw nq w)
    (fromSatisfies : statement.Satisfies fromMessages)
    (toSatisfies : statement.Satisfies toMessages)
    (query : QuerySet n r) (challenge : Challenge F nw nq repetitions Equations)
    (first second : V1ProverRandomness C nw nq repetitions)
    (hcore : first.corePadding = second.corePadding) (h : Fin repetitions) :
    proximityAdjustment fromMessages toMessages fromSatisfies toSatisfies query
        challenge first h =
      proximityAdjustment fromMessages toMessages fromSatisfies toSatisfies query
        challenge second h := by
  cases first; cases second; subst hcore; rfl

omit [Fintype F] [DecidableEq F] in
/-- The V1 tape translation is injective. -/
theorem translateRandomness_injective
    (fromMessages toMessages : CoreMessages F nw nq w)
    (fromSatisfies : statement.Satisfies fromMessages)
    (toSatisfies : statement.Satisfies toMessages)
    (query : QuerySet n r) (challenge : Challenge F nw nq repetitions Equations) :
    Function.Injective
      (translateRandomness (C := C) fromMessages toMessages fromSatisfies
        toSatisfies query challenge) := by
  intro first second htranslated
  have htranslatedCore := congrArg V1ProverRandomness.corePadding htranslated
  have hcore : first.corePadding = second.corePadding := by
    funext block row
    exact (translateCorePaddingEquiv C query
      (fromMessages block row) (toMessages block row)).injective
      (congrFun (congrFun htranslatedCore block) row)
  have hlinear : first.linearMask = second.linearMask := by
    funext h
    have heq := congrFun (congrArg V1ProverRandomness.linearMask htranslated) h
    change first.linearMask h + linearAdjustment fromMessages toMessages
        fromSatisfies toSatisfies query challenge first h =
      second.linearMask h + linearAdjustment fromMessages toMessages
        fromSatisfies toSatisfies query challenge second h at heq
    rw [linearAdjustment_eq_of_corePadding_eq fromMessages toMessages
      fromSatisfies toSatisfies query challenge first second hcore h] at heq
    exact add_right_cancel heq
  have hquadratic : first.quadraticMask = second.quadraticMask := by
    funext h
    have heq := congrFun (congrArg V1ProverRandomness.quadraticMask htranslated) h
    change first.quadraticMask h + quadraticAdjustment fromMessages toMessages
        fromSatisfies toSatisfies query challenge first h =
      second.quadraticMask h + quadraticAdjustment fromMessages toMessages
        fromSatisfies toSatisfies query challenge second h at heq
    rw [quadraticAdjustment_eq_of_corePadding_eq fromMessages toMessages
      fromSatisfies toSatisfies query challenge first second hcore h] at heq
    exact add_right_cancel heq
  have hblind : first.proximityBlind = second.proximityBlind := by
    funext h
    have heq := congrFun (congrArg V1ProverRandomness.proximityBlind htranslated) h
    change first.proximityBlind h + proximityAdjustment fromMessages toMessages
        fromSatisfies toSatisfies query challenge first h =
      second.proximityBlind h + proximityAdjustment fromMessages toMessages
        fromSatisfies toSatisfies query challenge second h at heq
    rw [proximityAdjustment_eq_of_corePadding_eq fromMessages toMessages
      fromSatisfies toSatisfies query challenge first second hcore h] at heq
    exact add_right_cancel heq
  cases first; cases second
  simp_all

/-- V1 tape translation as an equivalence of uniform finite tapes. -/
noncomputable def translateRandomnessEquiv
    (fromMessages toMessages : CoreMessages F nw nq w)
    (fromSatisfies : statement.Satisfies fromMessages)
    (toSatisfies : statement.Satisfies toMessages)
    (query : QuerySet n r) (challenge : Challenge F nw nq repetitions Equations) :
    V1ProverRandomness C nw nq repetitions ≃
      V1ProverRandomness C nw nq repetitions :=
  Equiv.ofBijective
    (translateRandomness (C := C) fromMessages toMessages fromSatisfies
      toSatisfies query challenge)
    (translateRandomness_injective fromMessages toMessages fromSatisfies
      toSatisfies query challenge).bijective_of_finite

end V1ProverRandomness

end Ligero.V1
