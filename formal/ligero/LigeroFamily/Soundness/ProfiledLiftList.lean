import LigeroFamily.Protocol.MaskScheme











namespace LigeroFamily

open CodingTheory
open MultiplicativeCode

variable {F Equations CheckedMask DirectMask : Type*}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Equations] [DecidableEq Equations]
variable [Fintype CheckedMask] [DecidableEq CheckedMask]
variable {r w n nw nq e g radius failureNumerator failureDenominator L : ℕ}

/-- Affine commitment matrix: offset first, followed only by proximity-tested
rows. -/
def schemeLiftCommittedRows
    (oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1) :
    Option (SchemeTestedRow CheckedMask nw nq 1) → Word F n
  | none => oracle.proximityBlind 0
  | some index => oracle.testedRow index

def schemeLiftCandidateRows (offset : EvaluationRow F r w n)
    (rows : SchemeTestedRow CheckedMask nw nq 1 → EvaluationRow F r w n) :
    Option (SchemeTestedRow CheckedMask nw nq 1) → Word F n
  | none => codeword offset
  | some index => codeword (rows index)

/-- A common lift candidate.  Its row index depends only on the checked mask
representation, never on the direct arithmetic mask representation. -/
structure SchemeLiftCandidate
    (C : MultiplicativeCode F r w n)
    (oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1)
    (radius : ℕ) where
  offset : EvaluationRow F r w n
  row : SchemeTestedRow CheckedMask nw nq 1 → EvaluationRow F r w n
  offset_mem : offset ∈ C.base
  row_mem : ∀ index, row index ∈ C.base
  close : (matrixErrorCoordinates (schemeLiftCommittedRows oracle)
    (schemeLiftCandidateRows offset row)).card ≤ radius

omit [Fintype F] [Fintype Equations] [DecidableEq Equations]
    [DecidableEq CheckedMask] in
@[ext] theorem SchemeLiftCandidate.ext
    {C : MultiplicativeCode F r w n}
    {oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1}
    {radius : ℕ} {first second : SchemeLiftCandidate C oracle radius}
    (hoffset : first.offset = second.offset) (hrow : first.row = second.row) :
    first = second := by
  cases first
  cases second
  simp_all

noncomputable instance SchemeLiftCandidate.fintype
    {C : MultiplicativeCode F r w n}
    {oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1}
    {radius : ℕ} : Fintype (SchemeLiftCandidate C oracle radius) := by
  classical
  let embed : SchemeLiftCandidate C oracle radius →
      EvaluationRow F r w n ×
        (SchemeTestedRow CheckedMask nw nq 1 → EvaluationRow F r w n) :=
    fun candidate ↦ (candidate.offset, candidate.row)
  letI : Finite (SchemeLiftCandidate C oracle radius) :=
    Finite.of_injective embed fun first second h ↦
      SchemeLiftCandidate.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  exact Fintype.ofFinite _

namespace SchemeLiftCandidate

variable {C : MultiplicativeCode F r w n}
variable {oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1}

/-- A decoded core row, common to every mask representation. -/
def decodedCore (candidate : SchemeLiftCandidate C oracle radius)
    (block : CoreBlock) (row : Fin (block.rowCount nw nq)) :
    EvaluationRow F r w n :=
  candidate.row (Sum.inl ⟨block, row⟩)

/-- Witness messages extracted from a common lift candidate. -/
def decodedMessages (candidate : SchemeLiftCandidate C oracle radius) :
    CoreMessages F nw nq w :=
  fun block row ↦ witnessValues (candidate.decodedCore block row)

/-- The same committed codeword tuple is a candidate at every larger decoding radius. -/
def widen {small large : ℕ} (candidate : SchemeLiftCandidate C oracle small)
    (h : small ≤ large) : SchemeLiftCandidate C oracle large where
  offset := candidate.offset
  row := candidate.row
  offset_mem := candidate.offset_mem
  row_mem := candidate.row_mem
  close := candidate.close.trans h

omit [Fintype F] [DecidableEq CheckedMask] in
@[simp] theorem decodedMessages_widen {small large : ℕ}
    (candidate : SchemeLiftCandidate C oracle small) (h : small ≤ large) :
    (candidate.widen h).decodedMessages = candidate.decodedMessages := rfl

def linearResidual (candidate : SchemeLiftCandidate C oracle radius)
    (statement : ConstraintSystem F nw nq w Equations)
    (equation : Equations) : F :=
  statement.linearValue candidate.decodedMessages equation -
    statement.target equation

def quadraticResidual (candidate : SchemeLiftCandidate C oracle radius)
    (row : Fin nq) (i : Fin w) : F :=
  candidate.decodedMessages .left row i *
    candidate.decodedMessages .right row i -
    candidate.decodedMessages .output row i



omit [Fintype F] [Fintype Equations] [DecidableEq Equations]
    [DecidableEq CheckedMask] in
theorem residual_of_not_satisfies (candidate : SchemeLiftCandidate C oracle radius)
    (statement : ConstraintSystem F nw nq w Equations)
    (hns : ¬statement.Satisfies candidate.decodedMessages) :
    candidate.linearResidual statement ≠ 0 ∨
      ∃ i, (fun row ↦ candidate.quadraticResidual row i) ≠ 0 := by
  exact statement.residual_of_not_satisfies candidate.decodedMessages hns

noncomputable def badColumns (candidate : SchemeLiftCandidate C oracle radius) :
    Finset (Fin n) :=
  matrixErrorCoordinates (schemeLiftCommittedRows oracle)
    (schemeLiftCandidateRows candidate.offset candidate.row)

omit [Fintype F] [Fintype Equations] [DecidableEq Equations]
    [DecidableEq CheckedMask] in
theorem badColumns_card (candidate : SchemeLiftCandidate C oracle radius) :
    candidate.badColumns.card ≤ radius := candidate.close

omit [Fintype F] [Fintype Equations] [DecidableEq Equations]
    [DecidableEq CheckedMask] in
theorem offset_eq_of_not_bad (candidate : SchemeLiftCandidate C oracle radius)
    (j : Fin n) (hj : j ∉ candidate.badColumns) :
    oracle.proximityBlind 0 j = candidate.offset (codePosition j) := by
  have hnoError : ¬ ∃ row,
      schemeLiftCommittedRows oracle row j ≠
        schemeLiftCandidateRows candidate.offset candidate.row row j := by
    simpa [badColumns, matrixErrorCoordinates] using hj
  simpa [schemeLiftCommittedRows, schemeLiftCandidateRows, codeword] using
    not_ne_iff.mp (not_exists.mp hnoError none)

omit [Fintype F] [Fintype Equations] [DecidableEq Equations]
    [DecidableEq CheckedMask] in
theorem row_eq_of_not_bad (candidate : SchemeLiftCandidate C oracle radius)
    (index : SchemeTestedRow CheckedMask nw nq 1) (j : Fin n)
    (hj : j ∉ candidate.badColumns) :
    oracle.testedRow index j = candidate.row index (codePosition j) := by
  have hnoError : ¬ ∃ row,
      schemeLiftCommittedRows oracle row j ≠
        schemeLiftCandidateRows candidate.offset candidate.row row j := by
    simpa [badColumns, matrixErrorCoordinates] using hj
  simpa [schemeLiftCommittedRows, schemeLiftCandidateRows, codeword] using
    not_ne_iff.mp (not_exists.mp hnoError (some index))

noncomputable def proximityRow (candidate : SchemeLiftCandidate C oracle radius)
    (weights : SchemeTestedRow CheckedMask nw nq 1 → F) :
    EvaluationRow F r w n :=
  candidate.offset + ∑ index, weights index • candidate.row index

omit [Fintype F] [Fintype Equations] [DecidableEq Equations]
    [DecidableEq CheckedMask] in
theorem proximityRow_mem (candidate : SchemeLiftCandidate C oracle radius)
    (weights : SchemeTestedRow CheckedMask nw nq 1 → F) :
    candidate.proximityRow weights ∈ C.base := by
  apply C.base.add_mem candidate.offset_mem
  exact Submodule.sum_mem _ fun index _ ↦
    C.base.smul_mem (weights index) (candidate.row_mem index)

end SchemeLiftCandidate

/-- The affine combination of all proximity-tested rows and its blind. -/
noncomputable def schemeProximityObserved
    (oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1)
    (weights : SchemeTestedRow CheckedMask nw nq 1 → F) : Word F n :=
  fun j ↦ (∑ row, weights row * oracle.testedRow row j) +
    oracle.proximityBlind 0 j

/-- Columns on which a claimed proximity response disagrees with the actual
committed affine combination. -/
noncomputable def schemeProximityDisagreement
    (oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1)
    (weights : SchemeTestedRow CheckedMask nw nq 1 → F)
  (response : EvaluationRow F r w n) : Finset (Fin n) :=
  Finset.univ.filter fun j ↦
    response (codePosition j) ≠ schemeProximityObserved oracle weights j

/-- Columns on which the actual affine proximity word agrees with the claimed
response. This is mask-scheme independent because direct V1 masks do
not participate in proximity. -/
noncomputable def schemeProximityAgreement
    (oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1)
    (weights : SchemeTestedRow CheckedMask nw nq 1 → F)
  (response : EvaluationRow F r w n) : Finset (Fin n) :=
  Finset.univ.filter fun j ↦
    response (codePosition j) = schemeProximityObserved oracle weights j

omit [Fintype F] [Fintype Equations] [DecidableEq Equations]
    [DecidableEq CheckedMask] in
theorem schemeProximityAgreement_eq_compl_disagreement
    (oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1)
    (weights : SchemeTestedRow CheckedMask nw nq 1 → F)
    (response : EvaluationRow F r w n) :
    schemeProximityAgreement oracle weights response =
      Finset.univ \ schemeProximityDisagreement oracle weights response := by
  ext j
  simp [schemeProximityAgreement, schemeProximityDisagreement]

omit [Fintype F] [Fintype Equations] [DecidableEq Equations]
    [DecidableEq CheckedMask] in
theorem schemeProximityDisagreement_eq_compl_agreement
    (oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1)
    (weights : SchemeTestedRow CheckedMask nw nq 1 → F)
    (response : EvaluationRow F r w n) :
    schemeProximityDisagreement oracle weights response =
      Finset.univ \ schemeProximityAgreement oracle weights response := by
  ext j
  simp [schemeProximityAgreement, schemeProximityDisagreement]

omit [Fintype F] [Fintype Equations] [DecidableEq Equations]
    [DecidableEq CheckedMask] in
theorem support_observed_sub_codeword_eq_disagreement
    (oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1)
    (weights : SchemeTestedRow CheckedMask nw nq 1 → F)
    (response : EvaluationRow F r w n) :
    supportOn Finset.univ
        (schemeProximityObserved oracle weights - codeword response) =
      schemeProximityDisagreement oracle weights response := by
  ext j
  simp only [mem_supportOn, Finset.mem_univ, true_and, Pi.sub_apply,
    schemeProximityDisagreement, Finset.mem_filter, codeword]
  rw [sub_ne_zero]
  exact ne_comm

omit [Fintype F] [Fintype Equations] [DecidableEq Equations]
    [DecidableEq CheckedMask] in
theorem schemeProximity_partition
    (oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1)
    (weights : SchemeTestedRow CheckedMask nw nq 1 → F)
    (response : EvaluationRow F r w n) :
    (schemeProximityAgreement oracle weights response).card +
      (schemeProximityDisagreement oracle weights response).card = n := by
  simpa [schemeProximityAgreement, schemeProximityDisagreement, eq_comm] using
    Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n)))
      (fun j ↦ response (codePosition j) =
        schemeProximityObserved oracle weights j)

omit [Fintype F] [Fintype Equations] [DecidableEq Equations]
    [DecidableEq CheckedMask] in
theorem schemeProximity_query_subset_agreement
    {C : MultiplicativeCode F r w n}
    (oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1)
    (weights : SchemeTestedRow CheckedMask nw nq 1 → F)
    (response : EvaluationRow F r w n) (query : QuerySet n r)
    (haccept : SchemeVerifier.ProximityAccepts C weights response query
      (openSchemeOracle oracle query) 0) :
    query.coordinates ⊆ schemeProximityAgreement oracle weights response := by
  intro j hj
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  have hlocal := haccept.2 ⟨j, hj⟩
  simpa [openSchemeOracle, SchemeOracle.column, SchemeOracle.testedRow,
    schemeProximityObserved] using
    hlocal

omit [Fintype F] [Fintype Equations] [DecidableEq Equations]
    [DecidableEq CheckedMask] in
theorem schemeProximity_far_cover
    {C : MultiplicativeCode F r w n}
    (oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1)
    (weights : SchemeTestedRow CheckedMask nw nq 1 → F)
    (response : EvaluationRow F r w n) (query : QuerySet n r)
    (haccept : SchemeVerifier.ProximityAccepts C weights response query
      (openSchemeOracle oracle query) 0)
    (hfar : e < (schemeProximityDisagreement oracle weights response).card) :
    query.coordinates ⊆ schemeProximityAgreement oracle weights response ∧
      (schemeProximityAgreement oracle weights response).card ≤ n - e - 1 := by
  refine ⟨schemeProximity_query_subset_agreement oracle weights response query
    haccept, ?_⟩
  have hpartition := schemeProximity_partition oracle weights response
  omega

namespace SchemeLiftCandidate

noncomputable def remainingBadColumns
    {C : MultiplicativeCode F r w n}
    {oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1}
    (candidate : SchemeLiftCandidate C oracle radius)
    (weights : SchemeTestedRow CheckedMask nw nq 1 → F)
    (response : EvaluationRow F r w n) : Finset (Fin n) :=
  candidate.badColumns \ schemeProximityDisagreement oracle weights response

omit [Fintype F] [Fintype Equations] [DecidableEq Equations]
    [DecidableEq CheckedMask] in
theorem query_bad_subset_remaining
    {C : MultiplicativeCode F r w n}
    {oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1}
    (candidate : SchemeLiftCandidate C oracle radius)
    (weights : SchemeTestedRow CheckedMask nw nq 1 → F)
    (response : EvaluationRow F r w n) (query : QuerySet n r)
    (haccept : SchemeVerifier.ProximityAccepts C weights response query
      (openSchemeOracle oracle query) 0) :
    query.coordinates ∩ candidate.badColumns ⊆
      candidate.remainingBadColumns weights response := by
  intro j hj
  apply Finset.mem_sdiff.mpr
  refine ⟨(Finset.mem_inter.mp hj).2, ?_⟩
  intro hdisagree
  have hagree := (haccept.2 ⟨j, (Finset.mem_inter.mp hj).1⟩)
  exact (Finset.mem_filter.mp hdisagree).2 (by
    simpa [openSchemeOracle, SchemeOracle.column,
      SchemeOracle.testedRow, schemeProximityObserved] using hagree)

end SchemeLiftCandidate

/-- **The falsity hypothesis the soundness stack actually uses.**

Strictly weaker than `¬statement.Language`: it asks only that no *decodable* message vector — no
member of the radius-`radius` lift list of this oracle — satisfies the statement.  Every
unsatisfiable statement qualifies (`NoDecodedSolution.of_not_language`), so nothing that used the
old hypothesis is lost.

The point is the contrapositive.  Negating `¬statement.Language` yields `∃ messages, Satisfies` —
an abstract existence claim with no handle on where the messages came from.  Negating this yields
`∃ candidate : SchemeLiftCandidate C oracle radius, statement.Satisfies candidate.decodedMessages`,
and `SchemeLiftCandidate C oracle radius` is a `Fintype` **indexed by the oracle alone**, whose
cardinality is bounded by `SchemeLiftCandidate.univ_card_le_listBound` from the oracle alone.  That
is an extractor: a list of candidate witnesses named before any challenge is drawn. -/
def NoDecodedSolution (C : MultiplicativeCode F r w n)
    (oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1) (radius : ℕ)
    (statement : ConstraintSystem F nw nq w Equations) : Prop :=
  ∀ candidate : SchemeLiftCandidate C oracle radius,
    ¬statement.Satisfies candidate.decodedMessages

omit [Fintype F] [Fintype Equations] [DecidableEq Equations] [DecidableEq CheckedMask] in
/-- Falsity for a larger committed lift list implies falsity for every nested list. -/
theorem NoDecodedSolution.of_larger_radius
    {C : MultiplicativeCode F r w n}
    {oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1}
    {statement : ConstraintSystem F nw nq w Equations}
    {small large : ℕ} (h : small ≤ large)
    (hlarge : NoDecodedSolution C oracle large statement) :
    NoDecodedSolution C oracle small statement := by
  intro candidate hsat
  exact hlarge (candidate.widen h) (by simpa using hsat)

omit [Fintype F] [Fintype Equations] [DecidableEq Equations] [DecidableEq CheckedMask] in
/-- An unsatisfiable statement has no decodable solution either. -/
theorem NoDecodedSolution.of_not_language
    {C : MultiplicativeCode F r w n}
    {oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1}
    {statement : ConstraintSystem F nw nq w Equations}
    (hfalse : ¬statement.Language) : NoDecodedSolution C oracle radius statement :=
  fun candidate hsat ↦ hfalse ⟨candidate.decodedMessages, hsat⟩

/-! ## The lift list as a function of the oracle

`SchemeLiftCandidate C oracle radius` is a `Fintype` indexed by the oracle alone, and
`SchemeLiftCandidate.univ_card_le_listBound` bounds its cardinality — also from the oracle alone.
Enumerating it therefore gives a genuine extractor: a length-`L` tuple of candidate witnesses
named before any challenge is drawn.  The two declarations below are that enumeration and the
only fact about it anyone needs. -/

/-- Padding for an extractor's index range, used past the end of the lift list.  Any value would
do; nothing is claimed about the indices the list does not reach. -/
def zeroMessages (F : Type*) [Field F] (nw nq width : ℕ) : CoreMessages F nw nq width :=
  fun _ _ _ ↦ 0










noncomputable def finListIndex {Cand α : Type*} [Fintype Cand] (L : ℕ)
    (decode : Cand → α) (pad : α) (i : Fin L) : α :=
  match (Finset.univ : Finset Cand).toList[i.val]? with
  | some candidate => decode candidate
  | none => pad

/-- **Anything true of some candidate is true at some index.**

The bridge from `∃ candidate, P (decode candidate)` — which is what contraposing a counting
theorem gives — to `∃ i : Fin L, P (finListIndex … i)`, which is what a fixed-arity extractor
needs.  The hypothesis is a cardinality bound on the candidate type, supplied at each use by that
protocol's `univ_card_le_listBound`. -/
theorem exists_finListIndex {Cand α : Type*} [Fintype Cand] {L : ℕ}
    {decode : Cand → α} {pad : α} {P : α → Prop}
    (hcard : (Finset.univ : Finset Cand).card ≤ L)
    (h : ∃ candidate : Cand, P (decode candidate)) :
    ∃ i : Fin L, P (finListIndex L decode pad i) := by
  classical
  obtain ⟨candidate, hP⟩ := h
  have hmem : candidate ∈ (Finset.univ : Finset Cand).toList :=
    Finset.mem_toList.mpr (Finset.mem_univ candidate)
  obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hmem
  have hlen : (Finset.univ : Finset Cand).toList.length ≤ L := by
    rwa [Finset.length_toList]
  refine ⟨⟨j, lt_of_lt_of_le hj hlen⟩, ?_⟩
  rw [finListIndex, List.getElem?_eq_getElem hj]
  simpa [hget] using hP

/-- The oracle's lift list, decoded by `decode` and indexed by `Fin L`, padding with `pad` past
the end.  Nothing here depends on a statement, a challenge, a response, or a query set — only on
`C`, `oracle` and `radius`. -/
noncomputable def liftListIndex {α : Type*}
    (C : MultiplicativeCode F r w n)
    (oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1) (radius L : ℕ)
    (decode : SchemeLiftCandidate C oracle radius → α) (pad : α) (i : Fin L) : α :=
  finListIndex L decode pad i

omit [DecidableEq CheckedMask] in
/-- **Anything true of some list member is true at some index.**

The bridge from `∃ candidate, P (decode candidate)` — which is what contraposing the counting
theorem gives — to `∃ i : Fin L, P (liftListIndex … i)`, which is what a fixed-arity extractor
needs.  The hypothesis is exactly `univ_card_le_listBound`. -/
theorem exists_liftListIndex {α : Type*}
    {C : MultiplicativeCode F r w n}
    {oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1} {radius L : ℕ}
    {decode : SchemeLiftCandidate C oracle radius → α} {pad : α} {P : α → Prop}
    (hcard : (Finset.univ : Finset (SchemeLiftCandidate C oracle radius)).card ≤ L)
    (h : ∃ candidate : SchemeLiftCandidate C oracle radius, P (decode candidate)) :
    ∃ i : Fin L, P (liftListIndex C oracle radius L decode pad i) :=
  exists_finListIndex hcard h

end LigeroFamily
