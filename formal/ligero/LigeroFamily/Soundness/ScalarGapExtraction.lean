import LigeroFamily.Soundness.PolicySelectedMCA
import LigeroFamily.Soundness.PolicyProfiledMaster
import LigeroFamily.Soundness.PotentialPairs

/-!
# Scalar, response-assisted IOP extraction

The proximity exceptional set is fixed from the arbitrary committed oracle,
before both the arithmetic challenge and the response. Selected MCA supplies
this set by choosing one witnessing bad proximity response at each weight.
The affine blind remains arbitrary. A successful extraction returns a valid
common lift, with at most `g` unexplained proximity-agreement columns.

The specification below decodes from a finite family of base-code lifts, then
checks the statement. It makes no polynomial-time claim. It never reads the sampled query. The arithmetic
interface is response-uniform, and its instances must prove their budgets;
no response-code list bound or Fiat--Shamir argument is used here.
-/

set_option linter.unusedSectionVars false

namespace LigeroFamily.ScalarGapExtraction

open Finset CodingTheory MultiplicativeCode
open scoped BigOperators Classical

variable {F CheckedMask DirectMask Equations Challenge Response Tail : Type*}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype CheckedMask] [DecidableEq CheckedMask]
variable [Fintype Equations] [DecidableEq Equations]
variable [Fintype Challenge] [DecidableEq Challenge]
variable [Fintype Tail] [DecidableEq Tail]
variable {q r w n nw nq e g d lineBound : ℕ}
variable (C : MultiplicativeCode F r w n)
variable (oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1)

/-- A weight is bad if any close, code-valued proximity response has no lift.
This set is independent of the actual prover response and arithmetic coins. -/
noncomputable def badWeights : Finset (SchemeSelectedMCA.Weights F CheckedMask nw nq) := by
  classical
  exact univ.filter fun weights => ∃ response : EvaluationRow F r w n,
    response ∈ C.base ∧ (schemeProximityDisagreement oracle weights response).card ≤ e ∧
      ¬ Nonempty (SchemeGLiftWitness C oracle weights response g)

/-- The strategy-uniform proximity theorem implies an all-response gap with
the same budget, by selecting one witness at each bad weight. -/
theorem badWeights_density [Nonempty (SchemeTestedRow CheckedMask nw nq 1)]
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (hline : SelectedMCA.LineFailureBound C.baseCode e g lineBound)
    (hthree : 3 * g < d - e) (hfield : g + 1 < Fintype.card F) :
    (Fintype.card F - (g + 1)) * (badWeights (e := e) (g := g) C oracle).card ≤
      lineBound * Fintype.card (SchemeSelectedMCA.Weights F CheckedMask nw nq) := by
  classical
  let respond := fun weights : SchemeSelectedMCA.Weights F CheckedMask nw nq =>
    if h : ∃ response : EvaluationRow F r w n,
        response ∈ C.base ∧ (schemeProximityDisagreement oracle weights response).card ≤ e ∧
          ¬ Nonempty (SchemeGLiftWitness C oracle weights response g)
    then h.choose else 0
  have heq : badWeights (e := e) (g := g) C oracle =
      SchemeSelectedMCA.badWeights (C := C) (oracle := oracle) (e := e) (g := g) respond := by
    ext weights
    simp only [badWeights, SchemeSelectedMCA.badWeights, mem_filter, mem_univ, true_and]
    constructor
    · intro h
      have he : respond weights = h.choose := by
        dsimp only [respond]
        rw [dif_pos h]
      rw [he]
      exact h.choose_spec
    · intro h
      exact ⟨respond weights, h⟩
  rw [heq]
  exact SchemeSelectedMCA.badWeights_density respond hmin hline hthree hfield

variable {C oracle}
variable {layout : ConstraintLayout F q w}
variable (policy : SchemeProtocolPolicy (Equations := Equations) C layout
  Challenge Response CheckedMask DirectMask nw nq 1)

def Compatible (candidate : SchemeLiftCandidate C oracle (e + g))
    (challenge : Challenge) (response : Response) : Prop :=
  candidate.proximityRow (policy.proximityWeights challenge 0) =
      policy.proximityResponse response 0 ∧
    (candidate.remainingBadColumns (policy.proximityWeights challenge 0)
      (policy.proximityResponse response 0)).card ≤ g

/-- Decoding is unique on the actual proximity-agreement coordinates, even
when the full oracle lies beyond the global unique-decoding radius. -/
theorem compatible_unique
    (hmin : HasMinimumDistanceAtLeast C.baseCode d) (hradius : e + 2 * g < d)
    (challenge : Challenge) (response : Response)
    (hsmall : (schemeProximityDisagreement oracle (policy.proximityWeights challenge 0)
      (policy.proximityResponse response 0)).card ≤ e)
    (first second : SchemeLiftCandidate C oracle (e + g))
    (hfirst : Compatible policy first challenge response)
    (hsecond : Compatible policy second challenge response) : first = second := by
  classical
  let disagreement := schemeProximityDisagreement oracle (policy.proximityWeights challenge 0)
    (policy.proximityResponse response 0)
  let remaining₁ := first.remainingBadColumns (policy.proximityWeights challenge 0)
    (policy.proximityResponse response 0)
  let remaining₂ := second.remainingBadColumns (policy.proximityWeights challenge 0)
    (policy.proximityResponse response 0)
  let errors := disagreement ∪ (remaining₁ ∪ remaining₂)
  have herr : errors.card ≤ e + 2 * g := by
    have h := card_union_le disagreement (remaining₁ ∪ remaining₂)
    have h' := card_union_le remaining₁ remaining₂
    have h₁ : remaining₁.card ≤ g := hfirst.2
    have h₂ : remaining₂.card ≤ g := hsecond.2
    change disagreement.card ≤ e at hsmall
    change (disagreement ∪ (remaining₁ ∪ remaining₂)).card ≤ e + 2 * g
    omega
  apply SchemeLiftCandidate.candidateRows_injective
  funext index
  let word₁ := schemeLiftCandidateRows first.offset first.row index
  let word₂ := schemeLiftCandidateRows second.offset second.row index
  have hmem₁ : word₁ ∈ C.baseCode := by
    cases index with
    | none => exact C.codeword_mem_baseCode first.offset_mem
    | some row => exact C.codeword_mem_baseCode (first.row_mem row)
  have hmem₂ : word₂ ∈ C.baseCode := by
    cases index with
    | none => exact C.codeword_mem_baseCode second.offset_mem
    | some row => exact C.codeword_mem_baseCode (second.row_mem row)
  have hsupport : supportOn univ (word₁ - word₂) ⊆ errors := by
    intro j hj
    by_contra hnot
    have hd : j ∉ disagreement := fun h => hnot (mem_union_left _ h)
    have h₁ : j ∉ remaining₁ := fun h => hnot (mem_union_right _ (mem_union_left _ h))
    have h₂ : j ∉ remaining₂ := fun h => hnot (mem_union_right _ (mem_union_right _ h))
    have hb₁ : j ∉ first.badColumns := by
      intro h; exact h₁ (mem_sdiff.mpr ⟨h, hd⟩)
    have hb₂ : j ∉ second.badColumns := by
      intro h; exact h₂ (mem_sdiff.mpr ⟨h, hd⟩)
    have heq : word₁ j = word₂ j := by
      cases index with
      | none =>
        exact (first.offset_eq_of_not_bad j hb₁).symm.trans
          (second.offset_eq_of_not_bad j hb₂)
      | some row =>
        exact (first.row_eq_of_not_bad row j hb₁).symm.trans
          (second.row_eq_of_not_bad row j hb₂)
    exact (mem_supportOn univ (word₁ - word₂) j).mp hj |>.2 (sub_eq_zero.mpr heq)
  have hweight : weight (word₁ - word₂) ≤ e + 2 * g :=
    (card_le_card hsupport).trans herr
  exact sub_eq_zero.mp (AffineAgreement.eq_zero_of_weight_lt_distance hmin
    (C.baseCode.sub_mem hmem₁ hmem₂) (hweight.trans_lt hradius))

/-- Bounded-distance decoding on the response-guided agreement set. The
finite specification chooses a compatible lift without inspecting the statement. -/
noncomputable def decode (challenge : Challenge) (response : Response) :
    Option (SchemeLiftCandidate C oracle (e + g)) :=
  if h : ∃ candidate, Compatible policy candidate challenge response then some h.choose else none

theorem decode_valid (challenge : Challenge) (response : Response)
    (candidate : SchemeLiftCandidate C oracle (e + g))
    (h : decode (oracle := oracle) (e := e) (g := g) policy challenge response = some candidate) :
    Compatible policy candidate challenge response := by
  classical
  unfold decode at h
  split_ifs at h with hex
  cases Option.some.inj h
  exact hex.choose_spec

theorem decode_eq_some_of_compatible
    (hmin : HasMinimumDistanceAtLeast C.baseCode d) (hradius : e + 2 * g < d)
    (challenge : Challenge) (response : Response)
    (hsmall : (schemeProximityDisagreement oracle (policy.proximityWeights challenge 0)
      (policy.proximityResponse response 0)).card ≤ e)
    (candidate : SchemeLiftCandidate C oracle (e + g))
    (hcompatible : Compatible policy candidate challenge response) :
    decode (oracle := oracle) (e := e) (g := g) policy challenge response = some candidate := by
  classical
  have hex : ∃ candidate, Compatible policy candidate challenge response := ⟨candidate, hcompatible⟩
  unfold decode
  rw [dif_pos hex]
  exact congrArg some (compatible_unique policy hmin hradius challenge response hsmall
    hex.choose candidate hex.choose_spec hcompatible)

/-- Decode first, then check the original constraints. Neither operation
reads the sampled query. This is an IOP extractor specification, not an FS extractor. -/
noncomputable def extract
    (messages : SchemeLiftCandidate C oracle (e + g) → CoreMessages F nw nq q)
    (statement : ConstraintSystem F nw nq q Equations)
    (challenge : Challenge) (response : Response) : Option (SchemeLiftCandidate C oracle (e + g)) :=
  (decode (oracle := oracle) (e := e) (g := g) policy challenge response).bind fun candidate =>
    if statement.Satisfies (messages candidate) then some candidate else none

theorem extract_valid
    (messages : SchemeLiftCandidate C oracle (e + g) → CoreMessages F nw nq q)
    (statement : ConstraintSystem F nw nq q Equations)
    (challenge : Challenge) (response : Response) (candidate)
    (h : extract policy messages statement challenge response = some candidate) :
    Compatible policy candidate challenge response ∧ statement.Satisfies (messages candidate) := by
  classical
  simp only [extract, Option.bind_eq_some_iff] at h
  obtain ⟨decoded, hdecoded, hcheck⟩ := h
  split_ifs at hcheck with hsat
  have hc := decode_valid policy challenge response decoded hdecoded
  cases Option.some.inj hcheck
  exact ⟨hc, hsat⟩

theorem extract_none_of_no_valid
    (messages : SchemeLiftCandidate C oracle (e + g) → CoreMessages F nw nq q)
    (statement : ConstraintSystem F nw nq q Equations) (challenge : Challenge) (response : Response)
    (hfalse : ∀ candidate, ¬statement.Satisfies (messages candidate)) :
    extract policy messages statement challenge response = none := by
  classical
  simp only [extract, Option.bind_eq_none_iff]
  intro candidate _
  simp [hfalse candidate]

theorem extract_none_invalid_of_compatible
    (messages : SchemeLiftCandidate C oracle (e + g) → CoreMessages F nw nq q)
    (statement : ConstraintSystem F nw nq q Equations)
    (hmin : HasMinimumDistanceAtLeast C.baseCode d) (hradius : e + 2 * g < d)
    (challenge : Challenge) (response : Response)
    (hsmall : (schemeProximityDisagreement oracle (policy.proximityWeights challenge 0)
      (policy.proximityResponse response 0)).card ≤ e)
    (candidate : SchemeLiftCandidate C oracle (e + g))
    (hcompatible : Compatible policy candidate challenge response)
    (hext : extract policy messages statement challenge response = none) :
    ¬statement.Satisfies (messages candidate) := by
  classical
  have hd := decode_eq_some_of_compatible policy hmin hradius challenge response hsmall candidate hcompatible
  intro hsat
  simp [extract, hd, hsat] at hext

/-- The loss on any accepting query is a common set of at most `g` columns.
It is not silently replaced by lossless agreement. -/
theorem extract_agreement_errors
    (messages : SchemeLiftCandidate C oracle (e + g) → CoreMessages F nw nq q)
    (statement : ConstraintSystem F nw nq q Equations) (challenge : Challenge)
    (response : Response) (candidate)
    (hext : extract policy messages statement challenge response = some candidate) :
    ((schemeProximityAgreement oracle (policy.proximityWeights challenge 0)
      (policy.proximityResponse response 0)) ∩ candidate.badColumns).card ≤ g := by
  have hc := (extract_valid policy messages statement challenge response candidate hext).1.2
  apply (card_le_card (t := candidate.remainingBadColumns (policy.proximityWeights challenge 0)
    (policy.proximityResponse response 0)) ?_).trans hc
  intro j hj
  refine mem_sdiff.mpr ⟨(mem_inter.mp hj).2, ?_⟩
  intro hdisagree
  exact (mem_filter.mp hdisagree).2 ((mem_filter.mp (mem_inter.mp hj).1).2)

/-- Every accepted query lies in the same response-guided agreement set. -/
theorem extract_query_errors
    (messages : SchemeLiftCandidate C oracle (e + g) → CoreMessages F nw nq q)
    (statement : ConstraintSystem F nw nq q Equations) (challenge : Challenge)
    (response : Response) (candidate) (query : QuerySet n r)
    (hext : extract policy messages statement challenge response = some candidate)
    (hacc : policy.accepts statement challenge response query (openSchemeOracle oracle query)) :
    (query.coordinates ∩ candidate.badColumns).card ≤ g := by
  have hc := (extract_valid policy messages statement challenge response candidate hext).1.2
  exact (card_le_card (candidate.query_bad_subset_remaining
    (policy.proximityWeights challenge 0) (policy.proximityResponse response 0) query
    (policy.accepts_proximity statement challenge response query _ hacc 0))).trans hc

variable (extractor : SchemeExtractorPolicy policy Tail)

noncomputable def gapChallenges : Finset Challenge :=
  ((univ : Finset Tail) ×ˢ badWeights (e := e) (g := g) C oracle).map
    extractor.challengeProductEquiv.symm.toEmbedding

theorem mem_gapChallenges (challenge : Challenge) :
    challenge ∈ gapChallenges (oracle := oracle) (e := e) (g := g) policy extractor ↔
      policy.proximityWeights challenge 0 ∈ badWeights (e := e) (g := g) C oracle := by
  classical
  simp only [gapChallenges, mem_map, mem_product, mem_univ, true_and]
  constructor
  · rintro ⟨pair, hpair, heq⟩
    have hp := congrArg extractor.challengeProductEquiv heq
    change extractor.challengeProductEquiv (extractor.challengeProductEquiv.symm pair) =
      extractor.challengeProductEquiv challenge at hp
    rw [extractor.challengeProductEquiv.apply_symm_apply] at hp
    rw [hp] at hpair
    simpa only [extractor.weights_eq] using hpair
  · intro h
    exact ⟨extractor.challengeProductEquiv challenge, by simpa only [extractor.weights_eq] using h,
      extractor.challengeProductEquiv.symm_apply_apply challenge⟩

theorem gapChallenges_density [Nonempty (SchemeTestedRow CheckedMask nw nq 1)]
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (hline : SelectedMCA.LineFailureBound C.baseCode e g lineBound)
    (hthree : 3 * g < d - e) (hfield : g + 1 < Fintype.card F) :
    (Fintype.card F - (g + 1)) *
        (gapChallenges (oracle := oracle) (e := e) (g := g) policy extractor).card ≤
      lineBound * Fintype.card Challenge := by
  classical
  have h := badWeights_density C oracle hmin hline hthree hfield
  have hcard := Fintype.card_congr extractor.challengeProductEquiv
  simp only [Fintype.card_prod] at hcard
  simp only [gapChallenges, card_map, card_product, card_univ]
  rw [hcard]
  nlinarith

theorem compatible_of_not_gap
    (hmin : HasMinimumDistanceAtLeast C.baseCode d) (hradius : e + g < d)
    (challenge : Challenge) (response : Response)
    (hnot : challenge ∉ gapChallenges (oracle := oracle) (e := e) (g := g) policy extractor)
    (hresponse : policy.proximityResponse response 0 ∈ C.base)
    (hsmall : (schemeProximityDisagreement oracle (policy.proximityWeights challenge 0)
      (policy.proximityResponse response 0)).card ≤ e) :
    ∃ candidate : SchemeLiftCandidate C oracle (e + g), Compatible policy candidate challenge response := by
  classical
  have hw : Nonempty (SchemeGLiftWitness C oracle
      (policy.proximityWeights challenge 0) (policy.proximityResponse response 0) g) := by
    by_contra hn
    apply hnot
    rw [mem_gapChallenges]
    exact mem_filter.mpr ⟨mem_univ _, ⟨_, hresponse, hsmall, hn⟩⟩
  obtain ⟨witness⟩ := hw
  obtain ⟨candidate, hagg, hremain⟩ :=
    witness.exists_schemeLiftCandidate hresponse hsmall hmin hradius
  exact ⟨candidate, hagg, hremain⟩

noncomputable def acceptingQueries
    (statement : ConstraintSystem F nw nq q Equations)
    (challenge : Challenge) (response : Response) : Finset (QuerySet n r) := by
  classical
  exact univ.filter fun query => policy.accepts statement challenge response query
    (openSchemeOracle oracle query)

theorem cover_card (statement : ConstraintSystem F nw nq q Equations)
    (challenge : Challenge) (response : Response) {b : ℕ}
    (cover : PolicyAcceptingQueryCover policy oracle statement challenge response b) :
    (acceptingQueries (oracle := oracle) policy statement challenge response).card ≤ b.choose r := by
  classical
  apply (card_le_card (t := queriesWithin cover.allowed) ?_).trans
    (card_queriesWithin_le cover.allowed cover.allowed_card)
  intro query hquery
  exact mem_filter.mpr ⟨mem_univ _, cover.covers query (mem_filter.mp hquery).2⟩

/-- The local certificate has a single exceptional set and a single envelope
for all responses. Its extraction-failure bound also applies to true statements. -/
structure Certificate
    (messages : SchemeLiftCandidate C oracle (e + g) → CoreMessages F nw nq q)
    (statement : ConstraintSystem F nw nq q Equations) (baseline : ℕ) (error : ℚ) where
  bad : Finset Challenge
  cover : ∀ challenge, challenge ∉ bad → ∀ response,
    extract policy messages statement challenge response = none →
      (acceptingQueries (oracle := oracle) policy statement challenge response).card ≤ baseline.choose r
  density : (bad.card : ℚ) / Fintype.card Challenge ≤ error

namespace Certificate

variable {policy}
variable {messages : SchemeLiftCandidate C oracle (e + g) → CoreMessages F nw nq q}
variable {statement : ConstraintSystem F nw nq q Equations} {baseline : ℕ} {error : ℚ}

noncomputable def envelope (cert : Certificate policy messages statement baseline error)
    (challenge : Challenge) : ℚ :=
  hypergeometricRatio baseline n r + (1 - hypergeometricRatio baseline n r) *
    (if challenge ∈ cert.bad then 1 else 0)

theorem envelope_nonneg (cert : Certificate policy messages statement baseline error)
    (_hbase : baseline ≤ n) (challenge : Challenge) : 0 ≤ cert.envelope challenge := by
  classical
  by_cases hb : challenge ∈ cert.bad
  · simp [envelope, hb]
  · simp only [envelope, if_neg hb, mul_zero, add_zero, hypergeometricRatio]
    positivity

theorem response_fraction_le_envelope
    (cert : Certificate policy messages statement baseline error)
    (_hbase : baseline ≤ n) (challenge : Challenge) (response : Response)
    (hext : extract policy messages statement challenge response = none) :
    ((acceptingQueries (oracle := oracle) policy statement challenge response).card : ℚ) /
      n.choose r ≤ cert.envelope challenge := by
  classical
  have hN : (0 : ℚ) < n.choose r := by exact_mod_cast Nat.choose_pos C.query_le_length
  by_cases hb : challenge ∈ cert.bad
  · simp only [envelope, if_pos hb, mul_one, add_sub_cancel]
    apply (div_le_one hN).mpr
    exact_mod_cast (show (acceptingQueries (oracle := oracle) policy statement challenge response).card ≤ n.choose r from by
      simpa only [QuerySet.fintype_card] using card_le_univ
        (acceptingQueries (oracle := oracle) policy statement challenge response))
  · simp only [envelope, if_neg hb, mul_zero, add_zero, hypergeometricRatio]
    exact div_le_div_of_nonneg_right (by exact_mod_cast cert.cover challenge hb response hext) hN.le

theorem envelope_mean [Nonempty Challenge]
    (cert : Certificate policy messages statement baseline error) (hbase : baseline ≤ n) :
    (∑ challenge, cert.envelope challenge) / Fintype.card Challenge ≤
      hypergeometricRatio baseline n r + (1 - hypergeometricRatio baseline n r) * error := by
  classical
  have hc : (0 : ℚ) < Fintype.card Challenge := by exact_mod_cast Fintype.card_pos
  have hN : (0 : ℚ) < n.choose r := by exact_mod_cast Nat.choose_pos C.query_le_length
  have hdelta : hypergeometricRatio baseline n r ≤ 1 := by
    unfold hypergeometricRatio
    apply (div_le_one hN).mpr
    exact_mod_cast Nat.choose_le_choose r hbase
  have heq : (∑ challenge, cert.envelope challenge) / Fintype.card Challenge =
      hypergeometricRatio baseline n r + (1 - hypergeometricRatio baseline n r) *
        ((cert.bad.card : ℚ) / Fintype.card Challenge) := by
    simp only [envelope, sum_add_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul]
    rw [show (∑ challenge : Challenge, if challenge ∈ cert.bad then (1 : ℚ) else 0) =
        cert.bad.card from by simp]
    field_simp
  rw [heq]
  exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left cert.density (sub_nonneg.mpr hdelta))

/-- Joint IOP probability: acceptance and failure of the transcript-assisted
extractor. No false-statement premise and no post-query witness selection. -/
theorem extraction_failure [Nonempty Challenge]
    (cert : Certificate policy messages statement baseline error) (hbase : baseline ≤ n)
    (respond : Challenge → Response) :
    ((univ.filter fun pair : Challenge × QuerySet n r =>
      policy.accepts statement pair.1 (respond pair.1) pair.2 (openSchemeOracle oracle pair.2) ∧
      extract policy messages statement pair.1 (respond pair.1) = none).card : ℚ) /
        Fintype.card (Challenge × QuerySet n r) ≤
      hypergeometricRatio baseline n r + (1 - hypergeometricRatio baseline n r) * error := by
  classical
  letI : Nonempty (QuerySet n r) := QuerySet.nonempty C.query_le_length
  let fiber := fun challenge => univ.filter fun query : QuerySet n r =>
    policy.accepts statement challenge (respond challenge) query (openSchemeOracle oracle query) ∧
      extract policy messages statement challenge (respond challenge) = none
  have hf : ∀ challenge, ((fiber challenge).card : ℚ) / n.choose r ≤ cert.envelope challenge := by
    intro challenge
    by_cases hext : extract policy messages statement challenge (respond challenge) = none
    · have heq : fiber challenge = acceptingQueries (oracle := oracle) policy statement
          challenge (respond challenge) := by ext query; simp [fiber, acceptingQueries, hext]
      rw [heq]
      exact cert.response_fraction_le_envelope hbase challenge (respond challenge) hext
    · have heq : fiber challenge = ∅ := by ext query; simp [fiber, hext]
      simpa [heq] using cert.envelope_nonneg hbase challenge
  have hflat := PotentialProfile.pair_ratio_le_flat
    (fun challenge query =>
      policy.accepts statement challenge (respond challenge) query
        (openSchemeOracle oracle query) ∧
      extract policy messages statement challenge (respond challenge) = none)
    cert.envelope (by
      intro challenge
      simpa only [QuerySet.fintype_card, fiber] using hf challenge)
  simpa only [Fintype.card_prod, Nat.cast_mul] using
    hflat.trans (cert.envelope_mean hbase)

/-- The local extraction bound on the concrete public-coin IOP execution. -/
theorem iop_extraction_failure [Nonempty Challenge]
    (cert : Certificate policy messages statement baseline error) (hbase : baseline ≤ n)
    (prover : IPCPProver (ConstraintSystem F nw nq q Equations)
      (SchemeOracle F CheckedMask DirectMask nw nq n 1) Challenge Response)
    (hcommit : prover.commit statement = oracle) :
    ((univ.filter fun coins : Challenge × QuerySet n r =>
      policy.protocol.accepts prover statement coins = true ∧
      extract policy messages statement coins.1 (prover.respond statement oracle coins.1) = none).card : ℚ) /
      Fintype.card (Challenge × QuerySet n r) ≤
    hypergeometricRatio baseline n r + (1 - hypergeometricRatio baseline n r) * error := by
  simpa only [PublicCoinIPCP.accepts, PublicCoinIPCP.run, SchemeProtocolPolicy.protocol,
    hcommit, decide_eq_true_eq] using
    cert.extraction_failure hbase (prover.respond statement oracle)

/-- False statements always make the checked extractor fail, so extraction
soundness implies ordinary IOP soundness at the same bound. -/
theorem false_statement [Nonempty Challenge]
    (cert : Certificate policy messages statement baseline error) (hbase : baseline ≤ n)
    (hfalse : ¬statement.Language) (respond : Challenge → Response) :
    ((univ.filter fun pair : Challenge × QuerySet n r =>
      policy.accepts statement pair.1 (respond pair.1) pair.2
        (openSchemeOracle oracle pair.2)).card : ℚ) /
      Fintype.card (Challenge × QuerySet n r) ≤
    hypergeometricRatio baseline n r + (1 - hypergeometricRatio baseline n r) * error := by
  have hext : ∀ challenge, extract policy messages statement challenge (respond challenge) = none := by
    intro challenge
    exact extract_none_of_no_valid policy messages statement challenge (respond challenge)
      (fun candidate hsat => hfalse ⟨messages candidate, hsat⟩)
  simpa only [hext, and_true] using cert.extraction_failure hbase respond

end Certificate

/-- Construct the response-uniform local certificate from a proved scalar
proximity gap and response-uniform arithmetic evidence for each invalid lift.
Concrete verifier instances discharge `special`, its density, and its cover. -/
theorem certificate_of_gap_with_labels
    [Nonempty Challenge] [Nonempty (SchemeTestedRow CheckedMask nw nq 1)]
    (extractor : SchemeExtractorPolicy policy Tail)
    (messages : SchemeLiftCandidate C oracle (e + g) → CoreMessages F nw nq q)
    (statement : ConstraintSystem F nw nq q Equations)
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : SelectedMCALineConditions C.baseCode (Fintype.card F) e g d lineBound)
    (_hk : 0 < C.k) (cutoff L arithmeticLabels : ℕ)
    (hlist : (univ : Finset (SchemeLiftCandidate C oracle (e + g))).card ≤ L)
    (special : SchemeLiftCandidate C oracle (e + g) → Finset Challenge)
    (hspecial : ∀ candidate, Fintype.card F * (special candidate).card ≤
      arithmeticLabels * Fintype.card Challenge)
    (hcover : ∀ candidate, ¬statement.Satisfies (messages candidate) →
      ∀ challenge, challenge ∉ special candidate → ∀ response,
      Compatible policy candidate challenge response →
      Nonempty (PolicyAcceptingQueryCover policy oracle statement challenge response
        (min n (g + cutoff)))) :
    Nonempty (Certificate policy messages statement
      (max (n - e - 1) (min n (g + cutoff)))
      ((lineBound : ℚ) / (Fintype.card F - (g + 1) : ℕ) + ((L * arithmeticLabels : ℕ) : ℚ) / Fintype.card F)) := by
  classical
  let gap := gapChallenges (oracle := oracle) (e := e) (g := g) policy extractor
  let arithmetic := (univ : Finset (SchemeLiftCandidate C oracle (e + g))).biUnion special
  let bad := gap ∪ arithmetic
  have hgap := gapChallenges_density (oracle := oracle) policy extractor hmin conditions.line
    conditions.punctured.punctured_three_radius conditions.punctured.field_large
  have harith : Fintype.card F * arithmetic.card ≤ (L * arithmeticLabels) * Fintype.card Challenge := by
    calc
      _ ≤ Fintype.card F * ∑ candidate : SchemeLiftCandidate C oracle (e + g),
          (special candidate).card := Nat.mul_le_mul_left _ card_biUnion_le
      _ = ∑ candidate : SchemeLiftCandidate C oracle (e + g),
          Fintype.card F * (special candidate).card := mul_sum _ _ _
      _ ≤ ∑ _candidate : SchemeLiftCandidate C oracle (e + g),
          arithmeticLabels * Fintype.card Challenge := sum_le_sum (fun candidate _ => hspecial candidate)
      _ ≤ (L * arithmeticLabels) * Fintype.card Challenge := by
        simpa [Nat.mul_assoc] using Nat.mul_le_mul_right (arithmeticLabels * Fintype.card Challenge) hlist
  have hden : (0 : ℚ) < (Fintype.card F - (g + 1) : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt conditions.punctured.field_large
  have hF : (0 : ℚ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hC : (0 : ℚ) < Fintype.card Challenge := by exact_mod_cast Fintype.card_pos
  refine ⟨{ bad := bad, cover := ?_, density := ?_ }⟩
  · intro challenge hnot response hext
    have hnotGap : challenge ∉ gap := fun h => hnot (mem_union_left _ h)
    have hnotArith : challenge ∉ arithmetic := fun h => hnot (mem_union_right _ h)
    by_cases hfar : e < (schemeProximityDisagreement oracle (policy.proximityWeights challenge 0)
        (policy.proximityResponse response 0)).card
    · let allowed := schemeProximityAgreement oracle (policy.proximityWeights challenge 0)
        (policy.proximityResponse response 0)
      by_cases hex : ∃ query : QuerySet n r, policy.accepts statement challenge response query
          (openSchemeOracle oracle query)
      · obtain ⟨query, hacc⟩ := hex
        have hsize := (policyProximity_far_cover statement challenge response query hacc hfar).2
        apply (cover_card policy statement challenge response {
          allowed := allowed
          allowed_card := hsize
          covers := fun query hacc => policyProximity_query_subset_agreement statement challenge response query hacc }).trans
        exact Nat.choose_le_choose r (le_max_left _ _)
      · have hempty : acceptingQueries (oracle := oracle) policy statement challenge response = ∅ := by
          ext query; simp only [acceptingQueries, mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
          exact fun h => hex ⟨query, h⟩
        simp [hempty]
    · by_cases hex : ∃ query : QuerySet n r, policy.accepts statement challenge response query
          (openSchemeOracle oracle query)
      · obtain ⟨query, hacc⟩ := hex
        have hresponse := (policy.accepts_proximity statement challenge response query _ hacc 0).1
        have hradius : e + g < d := by have := conditions.punctured.punctured_three_radius; omega
        obtain ⟨candidate, hcompatible⟩ := compatible_of_not_gap policy extractor hmin hradius
          challenge response hnotGap hresponse (Nat.le_of_not_gt hfar)
        have hradius₂ : e + 2 * g < d := by
          have := conditions.punctured.punctured_three_radius
          omega
        have hns := extract_none_invalid_of_compatible policy messages statement hmin hradius₂
          challenge response (Nat.le_of_not_gt hfar) candidate hcompatible hext
        have hnotSpecial : challenge ∉ special candidate := by
          intro h; apply hnotArith; exact mem_biUnion.mpr ⟨candidate, mem_univ _, h⟩
        obtain ⟨cover⟩ := hcover candidate hns challenge hnotSpecial response hcompatible
        exact (cover_card policy statement challenge response cover).trans
          (Nat.choose_le_choose r (le_max_right _ _))
      · have hempty : acceptingQueries (oracle := oracle) policy statement challenge response = ∅ := by
          ext query; simp only [acceptingQueries, mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
          exact fun h => hex ⟨query, h⟩
        simp [hempty]
  · have hg : (gap.card : ℚ) / Fintype.card Challenge ≤
        (lineBound : ℚ) / (Fintype.card F - (g + 1) : ℕ) := by
      rw [div_le_div_iff₀ hC hden]
      have hn : gap.card * (Fintype.card F - (g + 1)) ≤ lineBound * Fintype.card Challenge := by
        simpa only [gap, Nat.mul_comm] using hgap
      exact_mod_cast hn
    have ha : (arithmetic.card : ℚ) / Fintype.card Challenge ≤
        ((L * arithmeticLabels : ℕ) : ℚ) / Fintype.card F := by
      rw [div_le_div_iff₀ hC hF]
      have hn : arithmetic.card * Fintype.card F ≤ (L * arithmeticLabels) * Fintype.card Challenge := by
        simpa only [Nat.mul_comm] using harith
      exact_mod_cast hn
    have hb : (bad.card : ℚ) ≤ gap.card + arithmetic.card := by exact_mod_cast card_union_le gap arithmetic
    exact (div_le_div_of_nonneg_right hb hC.le).trans (by rw [add_div]; exact add_le_add hg ha)


/-- Checked arithmetic has one exceptional label per invalid candidate. -/
theorem certificate_of_gap
    [Nonempty Challenge] [Nonempty (SchemeTestedRow CheckedMask nw nq 1)]
    (extractor : SchemeExtractorPolicy policy Tail)
    (messages : SchemeLiftCandidate C oracle (e + g) → CoreMessages F nw nq q)
    (statement : ConstraintSystem F nw nq q Equations)
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : SelectedMCALineConditions C.baseCode (Fintype.card F) e g d lineBound)
    (_hk : 0 < C.k) (cutoff L : ℕ)
    (hlist : (univ : Finset (SchemeLiftCandidate C oracle (e + g))).card ≤ L)
    (special : SchemeLiftCandidate C oracle (e + g) → Finset Challenge)
    (hspecial : ∀ candidate, Fintype.card F * (special candidate).card ≤ Fintype.card Challenge)
    (hcover : ∀ candidate, ¬statement.Satisfies (messages candidate) →
      ∀ challenge, challenge ∉ special candidate → ∀ response,
      Compatible policy candidate challenge response →
      Nonempty (PolicyAcceptingQueryCover policy oracle statement challenge response
        (min n (g + cutoff)))) :
    Nonempty (Certificate policy messages statement
      (max (n - e - 1) (min n (g + cutoff)))
      ((lineBound : ℚ) / (Fintype.card F - (g + 1) : ℕ) + (L : ℚ) / Fintype.card F)) := by
  simpa only [Nat.mul_one, one_mul] using
    certificate_of_gap_with_labels policy extractor messages statement hmin conditions _hk cutoff L 1
      hlist special (by simpa using hspecial) hcover

end LigeroFamily.ScalarGapExtraction
