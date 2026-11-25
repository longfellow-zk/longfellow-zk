import LfzkV1.LigeroHighMass125
import LigeroFamily.Soundness.SchemePolicyExtractor
import LigeroFamily.Protocol.FiniteResponse

/-!
# Scalar Ligero response families

These are families of complete response tuples of the scalar V1 verifier.
The same commitment and challenge are used for every response in a family.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace LfzkV1.LigeroHighMass125

open Finset LigeroFamily LigeroFamily.AgreementProfile Ligero.V1
open CodingTheory MultiplicativeCode
open scoped Classical

variable {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Equations] [DecidableEq Equations]
variable {r w n nw nq e g d a L : ℕ}
variable {C : MultiplicativeCode F r w n}
variable (oracle : Oracle F nw nq n 1)
variable (statement : ConstraintSystem F nw nq w Equations)

local notation "Challenge" => SchemeChallenge F NoMask nw nq 1 Equations
local notation "Reply" => Response F r w n 1
local notation "v1Policy" => SchemeVerifier.policy (Equations := Equations) (nw := nw)
  (nq := nq) (repetitions := 1) C scheme
local notation "extractor" => schemeExtractorPolicy (Equations := Equations)
  (nw := nw) (nq := nq) C (scheme (F := F))

noncomputable def columns (challenge : Challenge) (response : Reply) : Finset (Fin n) :=
  policyAcceptingCoordinates v1Policy oracle statement challenge response

theorem columns_subset_proximity (challenge : Challenge) (response : Reply) :
    columns (C := C) oracle statement challenge response ⊆
      schemeProximityAgreement oracle (challenge 0).proximity (response.proximity 0) := by
  intro j hj
  obtain ⟨query, haccept, hmem⟩ := (mem_filter.mp hj).2
  exact policyProximity_query_subset_agreement statement challenge response query haccept hmem

theorem columns_pairwise_overlap (challenge : Challenge) {u v : Reply}
    (hne : u ≠ v) :
    (columns (C := C) oracle statement challenge u ∩
      columns (C := C) oracle statement challenge v).card ≤ 2 * C.k - 1 := by
  classical
  let common := columns (C := C) oracle statement challenge u ∩
    columns (C := C) oracle statement challenge v
  by_contra hlt
  have hpos : 0 < common.card := by
    change ¬common.card ≤ _ at hlt
    omega
  obtain ⟨j, hj⟩ := card_pos.mp hpos
  have use_column (response : Reply) (i : Fin n)
      (hi : i ∈ columns (C := C) oracle statement challenge response) :
      ∃ query : QuerySet n r, ∃ h : i ∈ query.coordinates,
        SchemeVerifier.Accepts C scheme statement challenge response query
          (openSchemeOracle oracle query) :=
    let ⟨query, hpass, hmem⟩ := (mem_filter.mp hi).2
    ⟨query, hmem, hpass⟩
  obtain ⟨qu, _, hu⟩ := use_column u j (mem_inter.mp hj).1
  obtain ⟨qv, _, hv⟩ := use_column v j (mem_inter.mp hj).2
  have same_at (row : Reply → EvaluationRow F r w n)
      (hmemu : row u ∈ C.response) (hmemv : row v ∈ C.response)
      (hlocal : ∀ i ∈ common, row u (codePosition i) = row v (codePosition i)) :
      row u = row v := by
    by_contra hneRow
    apply hlt
    refine (card_le_card (t := responseAgreement (row u) (row v)) ?_).trans
      (responseAgreement_card_le C hmemu hmemv hneRow)
    intro i hi
    exact (mem_responseAgreement _ _ _).mpr (hlocal i hi)
  apply hne
  apply Response.ext
  · funext j
    rw [Subsingleton.elim j 0]
    apply same_at (fun u => u.proximity 0)
      (C.base_le_response (hu 0).1.1) (C.base_le_response (hv 0).1.1)
    intro i hi
    have hu' := columns_subset_proximity oracle statement challenge u
      (mem_inter.mp hi).1
    have hv' := columns_subset_proximity oracle statement challenge v
      (mem_inter.mp hi).2
    simp only [schemeProximityAgreement, mem_filter, mem_univ, true_and] at hu' hv'
    exact hu'.trans hv'.symm
  · funext j
    rw [Subsingleton.elim j 0]
    apply same_at (fun u => u.linear 0) (hu 0).2.1.1 (hv 0).2.1.1
    intro i hi
    obtain ⟨qu, hiu, hu'⟩ := use_column u i (mem_inter.mp hi).1
    obtain ⟨qv, hiv, hv'⟩ := use_column v i (mem_inter.mp hi).2
    have h1 := (hu' 0).2.1.2.2 ⟨i, hiu⟩
    have h2 := (hv' 0).2.1.2.2 ⟨i, hiv⟩
    exact h1.trans h2.symm
  · funext j
    rw [Subsingleton.elim j 0]
    apply same_at (fun u => u.quadratic 0) (hu 0).2.2.1 (hv 0).2.2.1
    intro i hi
    obtain ⟨qu, hiu, hu'⟩ := use_column u i (mem_inter.mp hi).1
    obtain ⟨qv, hiv, hv'⟩ := use_column v i (mem_inter.mp hi).2
    have h1 := (hu' 0).2.2.2.2 ⟨i, hiu⟩
    have h2 := (hv' 0).2.2.2.2 ⟨i, hiv⟩
    exact h1.trans h2.symm

theorem fixed_response_opening_density (challenge : Challenge) (response : Reply) :
    (↑(univ.filter (fun query : QuerySet n r =>
      (v1Policy).accepts statement challenge response query (openSchemeOracle oracle query))).card : ℚ) /
      n.choose r ≤ hypergeometricRatio (columns (C := C) oracle statement challenge response).card n r := by
  classical
  unfold hypergeometricRatio
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [← card_queriesWithin]
  exact_mod_cast card_le_card (fun query hquery => by
    apply mem_filter.mpr
    exact ⟨mem_univ _, query_subset_policyAcceptingCoordinates_of_accepts
      v1Policy oracle statement challenge response query (mem_filter.mp hquery).2⟩)

/-- High accepting responses without a punctured lift are chosen on the full
scalar challenge before any opening sample is read. -/
noncomputable def noLiftResponses (a g : ℕ) (challenge : Challenge) : Finset Reply :=
  (policyResponseAgreementList v1Policy oracle statement challenge a).filter fun response =>
    ¬ Nonempty (SchemeGLiftWitness C oracle (challenge 0).proximity (response.proximity 0) g)

theorem noLift_selected_tail_density
    [Nonempty (SchemeTestedRow NoMask nw nq 1)]
    {outerBound : ℕ} {localBound : ℕ → ℕ}
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : IntegratedSelectedMCALineConditions C.baseCode
      (Fintype.card F) e g d outerBound localBound)
    (ha : n - e ≤ a) (b : ℕ) (hab : a ≤ b) :
    SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator (Fintype.card F) g *
      (restrictedTailSet (active (noLiftResponses (C := C) oracle statement a g))
        (peakAgreement (noLiftResponses (C := C) oracle statement a g)
          (columns (C := C) oracle statement)) b).card ≤
      (SchemeSelectedMCA.selectedMCAOptimizedIntegratedFailureProfile
        (Fintype.card F) n e g d outerBound localBound).labelsAtLeast b *
        Fintype.card Challenge := by
  classical
  let responses := noLiftResponses (C := C) oracle statement a g
  let cols := columns (C := C) oracle statement
  have hchoice : ∀ c : Challenge, ∃ response : Reply, (responses c).Nonempty →
      response ∈ responses c ∧ peakAgreement responses cols c = (cols c response).card := by
    intro c
    by_cases hnonempty : (responses c).Nonempty
    · obtain ⟨response, hmem, hagree⟩ := (responses c).exists_mem_eq_sup hnonempty
        (fun response => (cols c response).card)
      exact ⟨response, fun _ => ⟨hmem, hagree⟩⟩
    · exact ⟨⟨0, 0, 0⟩, fun h => (hnonempty h).elim⟩
  choose respond hrespond using hchoice
  have hsub : restrictedTailSet (active responses) (peakAgreement responses cols) b ⊆
      restrictedTailSet
        ((extractor).badChallenges (oracle := oracle) (respond := respond) (e := e) (g := g))
        (SchemeExtractorPolicy.failureAgreement (policy := v1Policy) (oracle := oracle)
          (respond := respond)) b := by
    intro c hc
    obtain ⟨hactive, hpeak⟩ := mem_filter.mp hc
    obtain ⟨hresp, hagree⟩ := hrespond c (mem_filter.mp hactive).2
    have hnoLift := (mem_filter.mp hresp).2
    obtain ⟨⟨query, hpass⟩, _⟩ := (mem_filter.mp (mem_filter.mp hresp).1).2
    have hprox := columns_subset_proximity (C := C) oracle statement c (respond c)
    have hcard : b ≤ (schemeProximityAgreement oracle (c 0).proximity
        ((respond c).proximity 0)).card := (hpeak.trans_eq hagree).trans (card_le_card hprox)
    have hdist := schemeProximity_partition oracle (c 0).proximity ((respond c).proximity 0)
    have hclose : (schemeProximityDisagreement oracle (c 0).proximity
        ((respond c).proximity 0)).card ≤ e := by omega
    refine mem_filter.mpr ⟨?_, hcard⟩
    simp only [SchemeExtractorPolicy.badChallenges, SchemeExtractorPolicy.badChallengePairs,
      mem_map, mem_filter, mem_univ, true_and, Equiv.toEmbedding_apply]
    refine ⟨(extractor).challengeProductEquiv c, ?_, (extractor).challengeProductEquiv.symm_apply_apply c⟩
    simp only [SchemeSelectedMCA.badWeights, mem_filter, mem_univ, true_and,
      SchemeExtractorPolicy.responseAtTail]
    rw [show (extractor).challengeProductEquiv.symm
        (((extractor).challengeProductEquiv c).1, ((extractor).challengeProductEquiv c).2) = c
      from (extractor).challengeProductEquiv.symm_apply_apply c]
    rw [(extractor).weights_eq]
    exact ⟨(hpass 0).1.1, hclose, hnoLift⟩
  have hd := (extractor).badChallenges_agreement_density_endpointOptimizedIntegratedOfLine
    (respond := respond) (oracle := oracle) hmin conditions b
  exact (Nat.mul_le_mul_left _ (card_le_card hsub)).trans hd

/-- Sum over the entire high no-lift family, even if the same commitment has
other responses with a satisfying punctured lift. -/
theorem noLift_average_mass_le
    [Nonempty (SchemeTestedRow NoMask nw nq 1)]
    {outerBound : ℕ} {localBound : ℕ → ℕ}
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : IntegratedSelectedMCALineConditions C.baseCode
      (Fintype.card F) e g d outerBound localBound)
    (ha : n - e ≤ a) (hlarge : 2 * C.k - 1 < a)
    (hfamily : UniformFamilyBound n a (2 * C.k - 1) L) :
    (∑ c : Challenge, ∑ response ∈ noLiftResponses (C := C) oracle statement a g c,
      hypergeometricRatio (columns (C := C) oracle statement c response).card n r) /
        Fintype.card Challenge ≤
      let q := SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator (Fintype.card F) g
      let profile := SchemeSelectedMCA.selectedMCAOptimizedIntegratedFailureProfile
        (Fintype.card F) n e g d outerBound localBound
      (truncateBelow profile a).contribution q n n 0 r +
      (L : ℚ) * hypergeometricRatio ((n + (2 * C.k - 1)) / 2) n r * profile.tail q a := by
  classical
  let replies := noLiftResponses (C := C) oracle statement a g
  let cols := columns (C := C) oracle statement
  let profile := SchemeSelectedMCA.selectedMCAOptimizedIntegratedFailureProfile
    (Fintype.card F) n e g d outerBound localBound
  have hlarge' (c : Challenge) (u : Reply) (hu : u ∈ replies c) : a ≤ (cols c u).card :=
    (mem_filter.mp (mem_filter.mp hu).1).2.2
  have hoverlap (c : Challenge) (u : Reply) (_hu : u ∈ replies c)
      (v : Reply) (_hv : v ∈ replies c) (hne : u ≠ v) :
      (cols c u ∩ cols c v).card ≤ 2 * C.k - 1 :=
    columns_pairwise_overlap oracle statement c hne
  letI : Nonempty Challenge := ⟨fun _ => ⟨0, 0, 0⟩⟩
  have hq : 0 < SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator
      (Fintype.card F) g := by
    unfold SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator
    exact Nat.mul_pos Fintype.card_pos (Nat.sub_pos_of_lt conditions.outer.punctured.field_large)
  apply selected_average_mass_le replies cols hq profile
    (fun c => family_card_le (replies c) (cols c) hlarge (hlarge' c) (hoverlap c) hfamily)
    hoverlap hlarge'
  intro b hab _
  exact noLift_selected_tail_density oracle statement hmin conditions ha b hab

end LfzkV1.LigeroHighMass125
