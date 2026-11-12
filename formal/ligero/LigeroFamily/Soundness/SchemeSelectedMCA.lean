import SelectedMCA.DoubleAveraging
import LigeroFamily.Soundness.SchemeLiftBridge
import LigeroFamily.Soundness.AgreementProfile
import LigeroFamily.Soundness.SelectedMCAParameters

/-!
# Mask-scheme-generic selected-response lift density

This is the protocol-facing double-averaging layer.  The response may depend
on the whole simultaneous challenge; after the non-proximity coordinates are
fixed, it is simply an arbitrary function of the proximity weights.
-/

namespace LigeroFamily

open CodingTheory
open MultiplicativeCode
open AffineAgreement SelectedMCA

variable {F CheckedMask DirectMask : Type*}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype CheckedMask] [DecidableEq CheckedMask]
variable {r w n nw nq e g d bound : ℕ}

namespace SchemeSelectedMCA

variable {C : MultiplicativeCode F r w n}
variable {oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1}
variable [Nonempty (SchemeTestedRow CheckedMask nw nq 1)]

abbrev Weights (F CheckedMask : Type*) (nw nq : ℕ) :=
  SchemeTestedRow CheckedMask nw nq 1 → F

/-- A direction that has no radius-`g` codeword representative on the actual
agreement coordinates of one selected response. -/
def DirectionFar (weights direction : Weights F CheckedMask nw nq)
    (response : EvaluationRow F r w n) : Prop :=
  ¬∃ decoded ∈ C.baseCode,
    (supportOn (schemeProximityAgreement oracle weights response)
      (wordCombination oracle.testedRow direction - decoded)).card ≤ g

/-- Close, code-valued selected responses for which no punctured lift exists. -/
noncomputable def badWeights
    (respond : Weights F CheckedMask nw nq → EvaluationRow F r w n) :
    Finset (Weights F CheckedMask nw nq) := by
  classical
  exact Finset.univ.filter fun weights ↦
    respond weights ∈ C.base ∧
    (schemeProximityDisagreement oracle weights
      (respond weights)).card ≤ e ∧
    ¬Nonempty (SchemeGLiftWitness C oracle weights (respond weights) g)

noncomputable def badFarWeights
    (respond : Weights F CheckedMask nw nq → EvaluationRow F r w n)
    (direction : Weights F CheckedMask nw nq) : Finset (Weights F CheckedMask nw nq) := by
  classical
  exact (badWeights (C := C) (oracle := oracle) (e := e) (g := g)
    respond).filter fun weights ↦
      DirectionFar (C := C) (oracle := oracle) (g := g)
        weights direction (respond weights)

/-- Bad selected proximity responses with at least `a` actual agreement
columns. -/
noncomputable def badWeightsAtAgreement
    (respond : Weights F CheckedMask nw nq → EvaluationRow F r w n)
    (a : ℕ) : Finset (Weights F CheckedMask nw nq) := by
  classical
  exact (badWeights (C := C) (oracle := oracle) (e := e) (g := g)
    respond).filter fun weights ↦
      a ≤ (schemeProximityAgreement oracle weights (respond weights)).card

/-- Agreement-refined bad responses that also see one direction as far. -/
noncomputable def badFarWeightsAtAgreement
    (respond : Weights F CheckedMask nw nq → EvaluationRow F r w n)
    (direction : Weights F CheckedMask nw nq) (a : ℕ) :
    Finset (Weights F CheckedMask nw nq) := by
  classical
  exact (badWeightsAtAgreement (C := C) (oracle := oracle)
    (e := e) (g := g) respond a).filter fun weights ↦
      DirectionFar (C := C) (oracle := oracle) (g := g)
        weights direction (respond weights)

/-- Radius-dependent selected-MCA profile.  Below `d/3` it uses the sharp
one-line theorem; elsewhere it falls back to the proved clique bound at the
outer test radius. -/
def selectedMCAFailureProfile
    (n g d lineBound : ℕ) : AgreementProfile n where
  labelsAtLeast a :=
    if n < a then 0
    else if 3 * (n - a) < d then 1 + (n - a) / (g + 1)
    else lineBound

/-- Agreement-local selected-MCA profile.  At and above `cutoff`, actual
agreement forces decoding radius at most `n - cutoff`, so a second clique
certificate at that radius can replace the outer-radius line bound.  Taking
the minimum preserves the sharper three-radius tail. -/
def selectedMCARefinedFailureProfile
    (n g d outerLineBound cutoff localLineBound : ℕ) : AgreementProfile n where
  labelsAtLeast a :=
    if cutoff ≤ a then
      min ((selectedMCAFailureProfile n g d outerLineBound).labelsAtLeast a)
        ((selectedMCAFailureProfile n g d localLineBound).labelsAtLeast a)
    else
      (selectedMCAFailureProfile n g d outerLineBound).labelsAtLeast a

/-- Threshold-free pointwise MCA profile.  At every agreement level where
the observed agreement itself improves the decoding radius, use the proved
line bound for radius `n - a`; otherwise retain the outer bound.  The exact
`AgreementProfile.contribution` sum integrates these values directly. -/
def selectedMCAIntegratedFailureProfile
    (n e g d outerLineBound : ℕ) (localLineBound : ℕ → ℕ) :
    AgreementProfile n where
  labelsAtLeast a :=
    if n - e ≤ a ∧ a ≤ n then
      min ((selectedMCAFailureProfile n g d outerLineBound).labelsAtLeast a)
        ((selectedMCAFailureProfile n g d (localLineBound a)).labelsAtLeast a)
    else
      (selectedMCAFailureProfile n g d outerLineBound).labelsAtLeast a

/-- Replace the generic selected-MCA normalization by a common denominator
and take the sharper direct chord count at full agreement.  Away from `n`
this is exactly the original profile with numerator and denominator both
scaled by `fieldSize`; at `n` it is the minimum of that unchanged bound and
the direct close-direction bound. -/
def endpointOptimizedProfile (fieldSize g : ℕ)
    (profile : AgreementProfile n) : AgreementProfile n where
  labelsAtLeast a :=
    if a = n then
      min (fieldSize * profile.labelsAtLeast a)
        ((g + 1) * (fieldSize - (g + 1)))
    else
      fieldSize * profile.labelsAtLeast a

/-- The public threshold-free MCA profile: pointwise radius refinement plus
the exact full-agreement chord count. -/
def selectedMCAOptimizedIntegratedFailureProfile
    (fieldSize n e g d outerLineBound : ℕ) (localLineBound : ℕ → ℕ) :
    AgreementProfile n :=
  endpointOptimizedProfile fieldSize g
    (selectedMCAIntegratedFailureProfile n e g d outerLineBound localLineBound)

/-- Common denominator used by the optimized integrated profile. -/
def selectedMCAOptimizedFailureDenominator (fieldSize g : ℕ) : ℕ :=
  fieldSize * (fieldSize - (g + 1))

/-- The selected-MCA failure profile has an exact three-band envelope: the
global line bound, the largest sharp one-line value, and the final value one. -/
theorem selectedMCAFailureProfile_contribution_le_three_bands
    (failureDenominator n g d lineBound queryCount : ℕ)
    (hdenominator : 0 < failureDenominator)
    (hfirst : 1 < n - (d - 1) / 3)
    (hmiddle : n - (d - 1) / 3 - 1 ≤ n - g - 1)
    (hsharp : ∀ a, n - (d - 1) / 3 ≤ a → a ≤ n → 3 * (n - a) < d)
    (hmedium : ∀ a, n - (d - 1) / 3 ≤ a → a ≤ n - g - 1 →
      (n - a) / (g + 1) ≤ (d - 1) / 3 / (g + 1))
    (hlast : ∀ a, n - g - 1 < a → a ≤ n → n - a < g + 1) :
    (selectedMCAFailureProfile n g d lineBound).contribution
        failureDenominator n n 0 queryCount ≤
      AgreementProfile.coverRatio n n 0 queryCount 0 +
      ((lineBound : ℚ) / failureDenominator) *
        AgreementProfile.coverRatio n n 0 queryCount (n - (d - 1) / 3 - 1) +
      ((1 + (d - 1) / 3 / (g + 1) : ℕ) : ℚ) / failureDenominator *
        AgreementProfile.coverRatio n n 0 queryCount (n - g - 1) +
      ((1 : ℚ) / failureDenominator) *
        AgreementProfile.coverRatio n n 0 queryCount n := by
  apply contribution_le_four_ranges failureDenominator n n 0 queryCount
    1 (n - (d - 1) / 3 - 1) (n - g - 1)
    (selectedMCAFailureProfile n g d lineBound)
      ((lineBound : ℚ) / failureDenominator)
      (((1 + (d - 1) / 3 / (g + 1) : ℕ) : ℚ) / failureDenominator)
      ((1 : ℚ) / failureDenominator)
  · norm_num
  · omega
  · omega
  · positivity
  · positivity
  · positivity
  · intro a ha _ _
    unfold AgreementProfile.tail
    apply (min_le_right _ _).trans
    apply div_le_div_of_nonneg_right
    · exact_mod_cast (show
        (selectedMCAFailureProfile n g d lineBound).labelsAtLeast a ≤ lineBound by
        unfold selectedMCAFailureProfile
        simp only [show ¬n < a by omega, ↓reduceIte]
        split <;> omega)
    · positivity
  · intro a ha hmiddleA _
    unfold AgreementProfile.tail
    apply (min_le_right _ _).trans
    apply div_le_div_of_nonneg_right
    · exact_mod_cast (show
        (selectedMCAFailureProfile n g d lineBound).labelsAtLeast a ≤
          1 + (d - 1) / 3 / (g + 1) by
        unfold selectedMCAFailureProfile
        simp only [show ¬n < a by omega, ↓reduceIte,
          show 3 * (n - a) < d by exact hsharp a (by omega) ha]
        exact Nat.add_le_add_left (hmedium a (by omega) (by omega)) 1)
    · positivity
  · intro a ha hlastA
    unfold AgreementProfile.tail
    apply (min_le_right _ _).trans
    apply div_le_div_of_nonneg_right
    · exact_mod_cast (show
        (selectedMCAFailureProfile n g d lineBound).labelsAtLeast a ≤ 1 by
        unfold selectedMCAFailureProfile
        simp only [show ¬n < a by omega, ↓reduceIte,
          show 3 * (n - a) < d by
            exact hsharp a (by omega) ha]
        rw [Nat.div_eq_of_lt (hlast a hlastA ha)])
    · positivity

omit [Nonempty (SchemeTestedRow CheckedMask nw nq 1)] in
/-- Outside `badWeights`, a close code-valued response has a punctured lift.
This is the single classical double-negation boundary in the certificate
assembly. -/
theorem gLiftWitness_nonempty_of_not_mem_badWeights
    (respond : Weights F CheckedMask nw nq → EvaluationRow F r w n)
    (weights : Weights F CheckedMask nw nq)
    (hnotBad : weights ∉
      badWeights (C := C) (oracle := oracle) (e := e) (g := g) respond)
    (hresponse : respond weights ∈ C.base)
    (hsmall : (schemeProximityDisagreement oracle weights
      (respond weights)).card ≤ e) :
    Nonempty (SchemeGLiftWitness C oracle weights (respond weights) g) := by
  classical
  exact Classical.not_not.mp fun hnone ↦
    hnotBad <| Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hresponse, hsmall, hnone⟩

omit [DecidableEq CheckedMask] in
/-- If no punctured lift exists, at least one row direction is far on the
actual agreement coordinates. -/
theorem exists_directionFar_of_no_gLiftWitness
    (weights : Weights F CheckedMask nw nq) (response : EvaluationRow F r w n)
    (hresponse : response ∈ C.base)
    (hsmall : (schemeProximityDisagreement oracle weights response).card
      ≤ e)
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (hthree : 3 * g < d - e) (hfield : g + 1 < Fintype.card F)
    (hnone : ¬Nonempty (SchemeGLiftWitness C oracle weights response g)) :
    ∃ direction, DirectionFar (C := C) (oracle := oracle) (g := g)
      weights direction response := by
  classical
  exact Classical.not_not.mp fun hfar ↦
    hnone <|
      SchemeGLiftWitness.nonempty_of_all_directional_combinations
        hresponse hsmall hmin hthree hfield (by
          intro direction
          exact Classical.not_not.mp fun hdirectionFar ↦
            hfar ⟨direction, hdirectionFar⟩)

/-- At full agreement the generic double-averaging loss is unnecessary.
Fixing one bad response, subtraction injects every other full-agreement bad
response into the locally close direction set at that response: the difference
of the two selected codewords is exactly the corresponding row combination.
The sharp close-direction count therefore applies directly. -/
theorem badWeightsAtFullAgreement_card_le
    (respond : Weights F CheckedMask nw nq → EvaluationRow F r w n)
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (hthree : 3 * g < d - e) (hfield : g + 1 < Fintype.card F) :
    (badWeightsAtAgreement (C := C) (oracle := oracle)
      (e := e) (g := g) respond n).card ≤
      (g + 1) * Fintype.card F ^
        (Fintype.card (SchemeTestedRow CheckedMask nw nq 1) - 1) := by
  classical
  let selected := badWeightsAtAgreement (C := C) (oracle := oracle)
    (e := e) (g := g) respond n
  change selected.card ≤
    (g + 1) * Fintype.card F ^
      (Fintype.card (SchemeTestedRow CheckedMask nw nq 1) - 1)
  by_cases hempty : selected = ∅
  · simp [selected, hempty]
  · obtain ⟨base, hbase⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hbaseParts := Finset.mem_filter.mp hbase
    have hbaseBad := Finset.mem_filter.mp hbaseParts.1 |>.2
    have hbaseAgreementCard :
        (schemeProximityAgreement oracle base (respond base)).card = n := by
      have hle :
          (schemeProximityAgreement oracle base (respond base)).card ≤ n := by
        simpa using Finset.card_le_univ
          (schemeProximityAgreement oracle base (respond base))
      omega
    have hbaseAgreement :
        schemeProximityAgreement oracle base (respond base) = Finset.univ := by
      apply Finset.eq_univ_of_card
      simpa using hbaseAgreementCard
    obtain ⟨farDirection, hfarDirection⟩ :=
      exists_directionFar_of_no_gLiftWitness
        (C := C) (oracle := oracle) base (respond base)
        hbaseBad.1 hbaseBad.2.1 hmin hthree hfield hbaseBad.2.2
    let close := SelectedMCA.closeCombinationChallengesOn C.baseCode
      oracle.testedRow
      (schemeProximityAgreement oracle base (respond base)) g
    have hcloseCard : close.card ≤
        (g + 1) * Fintype.card F ^
          (Fintype.card (SchemeTestedRow CheckedMask nw nq 1) - 1) := by
      apply SelectedMCA.closeCombinationChallengesOn_card_le_of_direction_far
        (e := e) C.baseCode oracle.testedRow
        (schemeProximityAgreement oracle base (respond base)) hmin
        (direction := farDirection)
      · have hdisagreement := schemeProximityDisagreement_eq_compl_agreement
          oracle base (respond base)
        rw [← hdisagreement]
        exact hbaseBad.2.1
      · exact hthree
      · exact hfarDirection
    let translate : Weights F CheckedMask nw nq →
        Weights F CheckedMask nw nq := fun weights ↦ weights - base
    have htranslate : selected.image translate ⊆ close := by
      intro direction hdirection
      obtain ⟨weights, hweights, rfl⟩ := Finset.mem_image.mp hdirection
      have hweightsParts := Finset.mem_filter.mp hweights
      have hweightsBad := Finset.mem_filter.mp hweightsParts.1 |>.2
      have hweightsAgreementCard :
          (schemeProximityAgreement oracle weights (respond weights)).card = n := by
        have hle :
            (schemeProximityAgreement oracle weights (respond weights)).card ≤ n := by
          simpa using Finset.card_le_univ
            (schemeProximityAgreement oracle weights (respond weights))
        omega
      have hweightsAgreement :
          schemeProximityAgreement oracle weights (respond weights) =
            Finset.univ := by
        apply Finset.eq_univ_of_card
        simpa using hweightsAgreementCard
      have hbaseObserved : schemeProximityObserved oracle base =
          codeword (respond base) := by
        funext j
        have hj : j ∈ schemeProximityAgreement oracle base (respond base) := by
          rw [hbaseAgreement]
          simp
        simpa [schemeProximityAgreement, codeword, eq_comm] using hj
      have hweightsObserved : schemeProximityObserved oracle weights =
          codeword (respond weights) := by
        funext j
        have hj : j ∈
            schemeProximityAgreement oracle weights (respond weights) := by
          rw [hweightsAgreement]
          simp
        simpa [schemeProximityAgreement, codeword, eq_comm] using hj
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, codeword (respond weights) - codeword (respond base),
        C.baseCode.sub_mem
          (C.codeword_mem_baseCode hweightsBad.1)
          (C.codeword_mem_baseCode hbaseBad.1), ?_⟩
      have hcombination : wordCombination oracle.testedRow (weights - base) =
          codeword (respond weights) - codeword (respond base) := by
        rw [← hweightsObserved, ← hbaseObserved]
        have hsub : weights - base = weights + (-1 : F) • base := by
          funext row
          simp [sub_eq_add_neg]
        rw [hsub, wordCombination_add_smul]
        have observed_eq (challenge : Weights F CheckedMask nw nq) :
            schemeProximityObserved oracle challenge =
              wordCombination oracle.testedRow challenge +
                oracle.proximityBlind 0 := by
          funext j
          simp [schemeProximityObserved, wordCombination_apply]
        rw [observed_eq weights, observed_eq base]
        funext j
        simp [sub_eq_add_neg]
      dsimp [translate]
      rw [hcombination, sub_self]
      simp [supportOn]
    have hcard : selected.card ≤
        (g + 1) * Fintype.card F ^
          (Fintype.card (SchemeTestedRow CheckedMask nw nq 1) - 1) := by
      calc
        selected.card = (selected.image translate).card := by
          symm
          apply Finset.card_image_of_injective
          intro first second heq
          dsimp [translate] at heq
          exact sub_left_injective heq
        _ ≤ close.card := Finset.card_le_card htranslate
        _ ≤ (g + 1) * Fintype.card F ^
            (Fintype.card (SchemeTestedRow CheckedMask nw nq 1) - 1) :=
          hcloseCard
    exact hcard

omit [Fintype F] [DecidableEq F] [DecidableEq CheckedMask]
    [Nonempty (SchemeTestedRow CheckedMask nw nq 1)] in
private theorem observed_affine
    (base direction : Weights F CheckedMask nw nq) (scalar : F) :
    schemeProximityObserved oracle (base + scalar • direction) =
      affineWord (schemeProximityObserved oracle base)
        (wordCombination oracle.testedRow direction) scalar := by
  have observed_eq (weights : Weights F CheckedMask nw nq) :
      schemeProximityObserved oracle weights =
        wordCombination oracle.testedRow weights + oracle.proximityBlind 0 := by
    funext j
    simp [schemeProximityObserved, wordCombination_apply]
  rw [observed_eq, observed_eq, wordCombination_add_smul]
  funext j
  simp [affineWord]
  ring

/-- On every nonzero direction, a per-line selected-MCA bound bounds the
number of bad selected responses whose actual agreement set also sees that
direction as far.  The line bound is supplied by whichever proximity theorem the
certificate uses -- the marked-triples clique condition through
`SelectedMCA.lineFailureBound_of_directClique`, or the Johnson regime through
`JBAgreement.lineFailureBound_of_johnson`. -/
theorem bad_far_on_direction_card_le
    (respond : Weights F CheckedMask nw nq → EvaluationRow F r w n)
    (hline : SelectedMCA.LineFailureBound C.baseCode e g
      (bound))
    (direction : Weights F CheckedMask nw nq) (hdirection : direction ≠ 0) :
    (badFarWeights (C := C) (oracle := oracle) (e := e) (g := g)
      respond direction).card ≤
      bound *
        Fintype.card F ^ (Fintype.card (SchemeTestedRow CheckedMask nw nq 1) - 1) := by
  classical
  simp only [badFarWeights]
  have hfilterEq :
      ((badWeights (C := C) (oracle := oracle) (e := e) (g := g)
        respond).filter fun weights ↦
          DirectionFar (C := C) (oracle := oracle) (g := g)
            weights direction (respond weights)) =
      Finset.univ.filter fun weights ↦
        weights ∈ badWeights (C := C) (oracle := oracle) (e := e) (g := g)
          respond ∧
        DirectionFar (C := C) (oracle := oracle) (g := g)
          weights direction (respond weights) := by
    ext weights
    simp
  rw [hfilterEq]
  apply CodingTheory.card_filter_univ_le_mul_pow_of_affine_line_card
    (property := fun weights ↦ weights ∈
        badWeights (C := C) (oracle := oracle) (e := e) (g := g) respond ∧
      DirectionFar (C := C) (oracle := oracle) (g := g)
        weights direction (respond weights))
    direction hdirection
    (bound)
  intro base
  let parameters := Finset.univ.filter fun scalar : F ↦
    base + scalar • direction ∈
        badWeights (C := C) (oracle := oracle) (e := e) (g := g) respond ∧
      DirectionFar (C := C) (oracle := oracle) (g := g)
        (base + scalar • direction) direction
        (respond (base + scalar • direction))
  let data : AffineAgreement.DecoderData
      (e := e) (m := parameters.card) C.baseCode
      (schemeProximityObserved oracle base)
      (wordCombination oracle.testedRow direction) := {
    parameters := parameters
    decoder := fun scalar ↦ codeword (respond (base + scalar.1 • direction))
    card_parameters := rfl
    decoder_mem := fun scalar ↦ by
      have hbad := Finset.mem_filter.mp scalar.2 |>.2.1
      exact C.codeword_mem_baseCode (Finset.mem_filter.mp hbad |>.2.1)
    decoder_near := fun scalar ↦ by
      have hbad := Finset.mem_filter.mp scalar.2 |>.2.1
      have hsmall := Finset.mem_filter.mp hbad |>.2.2.1
      have heq := observed_affine (oracle := oracle) base direction scalar.1
      rw [← heq]
      have hsupport := support_observed_sub_codeword_eq_disagreement oracle
        (base + scalar.1 • direction)
        (respond (base + scalar.1 • direction))
      simpa [weight, hsupport] using hsmall }
  have hallNonliftable : data.parameters ⊆
      SelectedMCA.directionallyNonliftableParameters
        data g := by
    intro scalar hscalar
    have hparts := Finset.mem_filter.mp hscalar |>.2
    apply Finset.mem_filter.mpr
    refine ⟨hscalar, ?_⟩
    intro hliftable
    rcases hliftable with ⟨decoded, hdecoded, hsmall⟩
    apply hparts.2
    refine ⟨decoded, hdecoded, ?_⟩
    have hagreement :
        SelectedMCA.selectedAgreementCoordinates
          data scalar =
        schemeProximityAgreement oracle
          (base + scalar • direction)
          (respond (base + scalar • direction)) := by
      ext j
      simp only [SelectedMCA.mem_selectedAgreementCoordinates]
      rw [data.codeword_eq hscalar]
      change affineWord (schemeProximityObserved oracle base)
          (wordCombination oracle.testedRow direction) scalar j =
          codeword (respond (base + scalar • direction)) j ↔
        j ∈ schemeProximityAgreement oracle
          (base + scalar • direction) (respond (base + scalar • direction))
      rw [← observed_affine (oracle := oracle) base direction scalar]
      simp [schemeProximityAgreement, codeword, eq_comm]
    simpa [hagreement] using hsmall
  have hbound := hline data
  have hparameters : parameters.card ≤
      bound :=
    (Finset.card_le_card hallNonliftable).trans hbound
  simpa [parameters] using hparameters

/-- Per-direction bad-response bound refined by actual agreement size. -/
theorem bad_far_atAgreement_on_direction_card_le
    (respond : Weights F CheckedMask nw nq → EvaluationRow F r w n)
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (hline : SelectedMCA.LineFailureBound C.baseCode e g
      (bound))
    (a : ℕ) (direction : Weights F CheckedMask nw nq)
    (hdirection : direction ≠ 0) :
    (badFarWeightsAtAgreement (C := C) (oracle := oracle)
      (e := e) (g := g) respond direction a).card ≤
      (selectedMCAFailureProfile n g d
        (bound)).labelsAtLeast a *
        Fintype.card F ^
          (Fintype.card (SchemeTestedRow CheckedMask nw nq 1) - 1) := by
  classical
  by_cases han : n < a
  · have hempty : badFarWeightsAtAgreement (C := C) (oracle := oracle)
        (e := e) (g := g) respond direction a = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro weights hweights
      have hagreement := (Finset.mem_filter.mp hweights).1
      have ha := (Finset.mem_filter.mp hagreement).2
      have hcard :
          (schemeProximityAgreement oracle weights (respond weights)).card ≤ n := by
        simpa using Finset.card_le_univ
          (schemeProximityAgreement oracle weights (respond weights))
      omega
    simp [hempty, selectedMCAFailureProfile, han]
  · by_cases hsharp : 3 * (n - a) < d
    · have hfilterEq :
          badFarWeightsAtAgreement (C := C) (oracle := oracle)
              (e := e) (g := g) respond direction a =
            Finset.univ.filter fun weights ↦
              weights ∈ badWeights (C := C) (oracle := oracle)
                (e := e) (g := g) respond ∧
              a ≤ (schemeProximityAgreement oracle weights
                (respond weights)).card ∧
      DirectionFar (C := C) (oracle := oracle) (g := g)
                weights direction (respond weights) := by
        ext weights
        simp [badFarWeightsAtAgreement, badWeightsAtAgreement, and_assoc]
      rw [hfilterEq]
      simp only [selectedMCAFailureProfile, han, hsharp, ↓reduceIte]
      apply CodingTheory.card_filter_univ_le_mul_pow_of_affine_line_card
        (property := fun weights ↦
          weights ∈ badWeights (C := C) (oracle := oracle)
              (e := e) (g := g) respond ∧
            a ≤ (schemeProximityAgreement oracle weights
              (respond weights)).card ∧
            DirectionFar (C := C) (oracle := oracle) (g := g)
              weights direction (respond weights))
        direction hdirection (1 + (n - a) / (g + 1))
      intro base
      let parameters := Finset.univ.filter fun scalar : F ↦
        base + scalar • direction ∈
            badWeights (C := C) (oracle := oracle) (e := e) (g := g) respond ∧
          a ≤ (schemeProximityAgreement oracle
            (base + scalar • direction)
            (respond (base + scalar • direction))).card ∧
          DirectionFar (C := C) (oracle := oracle) (g := g)
            (base + scalar • direction) direction
            (respond (base + scalar • direction))
      let data : AffineAgreement.DecoderData
          (e := n - a) (m := parameters.card) C.baseCode
          (schemeProximityObserved oracle base)
          (wordCombination oracle.testedRow direction) := {
        parameters := parameters
        decoder := fun scalar ↦ codeword
          (respond (base + scalar.1 • direction))
        card_parameters := rfl
        decoder_mem := fun scalar ↦ by
          have hbad := Finset.mem_filter.mp scalar.2 |>.2.1
          exact C.codeword_mem_baseCode (Finset.mem_filter.mp hbad |>.2.1)
        decoder_near := fun scalar ↦ by
          have hparts := Finset.mem_filter.mp scalar.2 |>.2
          have hagreement := hparts.2.1
          have hpartition := schemeProximity_partition oracle
            (base + scalar.1 • direction)
            (respond (base + scalar.1 • direction))
          have hsmall :
              (schemeProximityDisagreement oracle
                (base + scalar.1 • direction)
                (respond (base + scalar.1 • direction))).card ≤ n - a := by
            omega
          have heq := observed_affine (oracle := oracle)
            base direction scalar.1
          rw [← heq]
          have hsupport := support_observed_sub_codeword_eq_disagreement oracle
            (base + scalar.1 • direction)
            (respond (base + scalar.1 • direction))
          simpa [weight, hsupport] using hsmall }
      have hallNonliftable : data.parameters ⊆
          SelectedMCA.directionallyNonliftableParameters data g := by
        intro scalar hscalar
        have hparts := Finset.mem_filter.mp hscalar |>.2
        apply Finset.mem_filter.mpr
        refine ⟨hscalar, ?_⟩
        intro hliftable
        rcases hliftable with ⟨decoded, hdecoded, hsmall⟩
        apply hparts.2.2
        refine ⟨decoded, hdecoded, ?_⟩
        have hagreement :
            SelectedMCA.selectedAgreementCoordinates data scalar =
              schemeProximityAgreement oracle
                (base + scalar • direction)
                (respond (base + scalar • direction)) := by
          ext j
          simp only [SelectedMCA.mem_selectedAgreementCoordinates]
          rw [data.codeword_eq hscalar]
          change affineWord (schemeProximityObserved oracle base)
              (wordCombination oracle.testedRow direction) scalar j =
              codeword (respond (base + scalar • direction)) j ↔
            j ∈ schemeProximityAgreement oracle
              (base + scalar • direction)
              (respond (base + scalar • direction))
          rw [← observed_affine (oracle := oracle) base direction scalar]
          simp [schemeProximityAgreement, codeword, eq_comm]
        simpa [hagreement] using hsmall
      have hbound :=
        SelectedMCA.directionallyNonliftableParameters_card_le_of_three_radius
          (g := g) data hmin hsharp
      have hparameters : parameters.card ≤ 1 + (n - a) / (g + 1) :=
        (Finset.card_le_card hallNonliftable).trans hbound
      simpa [parameters] using hparameters
    · have hsubset : badFarWeightsAtAgreement (C := C) (oracle := oracle)
          (e := e) (g := g) respond direction a ⊆
          badFarWeights (C := C) (oracle := oracle)
            (e := e) (g := g) respond direction := by
        intro weights hweights
        have hparts := Finset.mem_filter.mp hweights
        exact Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hparts.1).1, hparts.2⟩
      have hbound := bad_far_on_direction_card_le
        (C := C) (oracle := oracle) respond hline
          direction hdirection
      have hcard := (Finset.card_le_card hsubset).trans hbound
      simpa [selectedMCAFailureProfile, han, hsharp] using hcard

/-- Denominator-cleared density of nonliftable close responses at an actual
agreement threshold.  The numerator is the radius-dependent profile rather
than the outer-radius clique constant. -/
theorem badWeightsAtAgreement_density
    (respond : Weights F CheckedMask nw nq → EvaluationRow F r w n)
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (hline : SelectedMCA.LineFailureBound C.baseCode e g
      (bound))
    (hthree : 3 * g < d - e) (hfield : g + 1 < Fintype.card F)
    (a : ℕ) :
    (Fintype.card F - (g + 1)) *
        (badWeightsAtAgreement (C := C) (oracle := oracle)
          (e := e) (g := g) respond a).card ≤
      (selectedMCAFailureProfile n g d
        (bound)).labelsAtLeast a *
        Fintype.card (Weights F CheckedMask nw nq) := by
  classical
  let q := Fintype.card F
  let rows := Fintype.card (SchemeTestedRow CheckedMask nw nq 1)
  let power := q ^ (rows - 1)
  let missing := (g + 1) * power
  let profileBound := (selectedMCAFailureProfile n g d
    (bound)).labelsAtLeast a
  let perDirection := profileBound * power
  let selected := badWeightsAtAgreement (C := C) (oracle := oracle)
    (e := e) (g := g) respond a
  let far : Weights F CheckedMask nw nq → Weights F CheckedMask nw nq → Prop :=
    fun weights direction ↦
      DirectionFar (C := C) (oracle := oracle) (g := g)
        weights direction (respond weights)
  have hmany (weights : Weights F CheckedMask nw nq)
      (hweights : weights ∈ selected) :
      Fintype.card (Weights F CheckedMask nw nq) - missing ≤
        (Finset.univ.filter fun direction ↦ far weights direction).card := by
    have hbadAgreement := Finset.mem_filter.mp hweights
    have hbad := Finset.mem_filter.mp hbadAgreement.1 |>.2
    have hsomeFar : ∃ direction, far weights direction := by
      simpa [far] using exists_directionFar_of_no_gLiftWitness
        (C := C) (oracle := oracle) weights (respond weights)
        hbad.1 hbad.2.1 hmin hthree hfield hbad.2.2
    obtain ⟨farDirection, hfarDirection⟩ := hsomeFar
    have hdeleted : (Finset.univ \
        schemeProximityAgreement oracle weights (respond weights)).card
        ≤ e := by
      rw [← schemeProximityDisagreement_eq_compl_agreement]
      exact hbad.2.1
    have hclose :=
      SelectedMCA.closeCombinationChallengesOn_card_le_of_direction_far
        C.baseCode oracle.testedRow
        (schemeProximityAgreement oracle weights (respond weights))
        hmin hdeleted hthree farDirection hfarDirection
    have hpartition := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Weights F CheckedMask nw nq)))
      (fun direction ↦ ¬far weights direction)
    have hcloseEq : (Finset.univ.filter fun direction ↦
        ¬far weights direction) =
        SelectedMCA.closeCombinationChallengesOn C.baseCode
          oracle.testedRow
          (schemeProximityAgreement oracle weights (respond weights)) g := by
      ext direction
      simp [far, DirectionFar, SelectedMCA.closeCombinationChallengesOn]
    rw [hcloseEq] at hpartition
    have hfarEq : (Finset.univ.filter fun direction ↦
        ¬¬far weights direction) =
        (Finset.univ.filter fun direction ↦ far weights direction) := by
      ext direction
      simp
    rw [hfarEq] at hpartition
    have hcloseMissing :
        (SelectedMCA.closeCombinationChallengesOn C.baseCode
          oracle.testedRow
          (schemeProximityAgreement oracle weights (respond weights))
          g).card ≤ missing := by
      simpa [missing, power, q, rows] using hclose
    have huniv : (Finset.univ : Finset (Weights F CheckedMask nw nq)).card =
        Fintype.card (Weights F CheckedMask nw nq) := Finset.card_univ
    rw [huniv] at hpartition
    omega
  have hfew (direction : Weights F CheckedMask nw nq) :
      (selected.filter fun weights ↦ far weights direction).card ≤
        perDirection := by
    by_cases hdirection : direction = 0
    · subst direction
      have hfarZero (weights : Weights F CheckedMask nw nq) :
          ¬far weights 0 := by
        intro hfar
        apply hfar
        exact ⟨0, C.baseCode.zero_mem, by simp [wordCombination, supportOn]⟩
      have hempty : (selected.filter fun weights ↦ far weights 0) = ∅ :=
        Finset.filter_eq_empty_iff.mpr fun _weights _hbad ↦ hfarZero _weights
      simp [hempty]
    · dsimp [perDirection, profileBound, power, rows, q, selected]
      simpa [badFarWeightsAtAgreement, far] using
        bad_far_atAgreement_on_direction_card_le
          (C := C) (oracle := oracle) respond hmin hline
            a direction hdirection
  have hdouble := SelectedMCA.double_averaging_card
    selected far missing perDirection hmany hfew
  have hqpos : 0 < q := Fintype.card_pos
  have hrowpos : 0 < rows := Fintype.card_pos
  have hpowerpos : 0 < power := pow_pos hqpos _
  have hweightsCard : Fintype.card (Weights F CheckedMask nw nq) = q * power := by
    rw [Fintype.card_fun]
    change q ^ rows = q * power
    rw [show rows = (rows - 1) + 1 by omega, pow_succ]
    ring
  have hremaining : Fintype.card (Weights F CheckedMask nw nq) - missing =
      (q - (g + 1)) * power := by
    rw [hweightsCard]
    dsimp [missing]
    rw [Nat.sub_mul]
  rw [hremaining] at hdouble
  have hcanceled : ((q - (g + 1)) * selected.card) * power ≤
      (profileBound * Fintype.card (Weights F CheckedMask nw nq)) * power := by
    calc
      ((q - (g + 1)) * selected.card) * power =
          selected.card * ((q - (g + 1)) * power) := by ring
      _ ≤ Fintype.card (Weights F CheckedMask nw nq) * perDirection := hdouble
      _ = (profileBound * Fintype.card
          (Weights F CheckedMask nw nq)) * power := by
        dsimp [perDirection]
        ring
  have hresult := (Nat.le_of_mul_le_mul_right hcanceled) hpowerpos
  simpa [q, selected, profileBound] using hresult

omit [Nonempty (SchemeTestedRow CheckedMask nw nq 1)] in
/-- Once actual agreement reaches `cutoff`, the outer radius in the bad-weight
set can be replaced by the forced local radius `n - cutoff`. -/
theorem badWeightsAtAgreement_eq_localRadius
    (respond : Weights F CheckedMask nw nq → EvaluationRow F r w n)
    (cutoff a : ℕ) (hradius : n - e ≤ cutoff) (hcutoff : cutoff ≤ a) :
    badWeightsAtAgreement (C := C) (oracle := oracle)
        (e := e) (g := g) respond a =
      badWeightsAtAgreement (C := C) (oracle := oracle)
        (e := n - cutoff) (g := g) respond a := by
  classical
  ext weights
  simp only [badWeightsAtAgreement, Finset.mem_filter]
  constructor
  · rintro ⟨hbad, hagreement⟩
    have hparts := Finset.mem_filter.mp hbad
    have hpartition := schemeProximity_partition oracle weights (respond weights)
    apply And.intro
    · apply Finset.mem_filter.mpr
      refine ⟨hparts.1, hparts.2.1, ?_, hparts.2.2.2⟩
      omega
    · exact hagreement
  · rintro ⟨hbad, hagreement⟩
    have hparts := Finset.mem_filter.mp hbad
    apply And.intro
    · apply Finset.mem_filter.mpr
      refine ⟨hparts.1, hparts.2.1, ?_, hparts.2.2.2⟩
      omega
    · exact hagreement

/-- Density bound for the agreement-local profile.  Above `cutoff`, the same
bad responses are viewed at radius `n - cutoff` and both the outer and local
clique bounds are available; below it this is the existing profile theorem. -/
theorem badWeightsAtAgreement_density_refined
    {threshold cutoff localThreshold : ℕ}
    (respond : Weights F CheckedMask nw nq → EvaluationRow F r w n)
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : LigeroFamily.RefinedSelectedMCAParameterConditions
      (Fintype.card F) n e g d threshold cutoff localThreshold)
    (a : ℕ) :
    (Fintype.card F - (g + 1)) *
        (badWeightsAtAgreement (C := C) (oracle := oracle)
          (e := e) (g := g) respond a).card ≤
      (selectedMCARefinedFailureProfile n g d
        (SelectedMCA.directLineFailureBound threshold) cutoff
        (SelectedMCA.directLineFailureBound localThreshold)).labelsAtLeast a *
        Fintype.card (Weights F CheckedMask nw nq) := by
  have houter := badWeightsAtAgreement_density
    (C := C) (oracle := oracle) respond hmin
      (conditions.toSelectedMCAParameterConditions.direct.lineFailure hmin)
      conditions.toSelectedMCAParameterConditions.punctured.punctured_three_radius
      conditions.toSelectedMCAParameterConditions.punctured.field_large a
  by_cases hcutoff : cutoff ≤ a
  · have heq := badWeightsAtAgreement_eq_localRadius
      (C := C) (oracle := oracle) (e := e) (g := g) respond cutoff a
      conditions.radius_le_cutoff hcutoff
    have hlocal := badWeightsAtAgreement_density
      (C := C) (oracle := oracle) (e := n - cutoff) (g := g)
      respond hmin
      (SelectedMCA.lineFailureBound_of_directClique hmin conditions.localDirect)
      conditions.local_three_radius
      conditions.toSelectedMCAParameterConditions.punctured.field_large a
    rw [← heq] at hlocal
    simp only [selectedMCARefinedFailureProfile, hcutoff, ↓reduceIte]
    by_cases hle :
        (selectedMCAFailureProfile n g d
          (SelectedMCA.directLineFailureBound threshold)).labelsAtLeast a ≤
        (selectedMCAFailureProfile n g d
          (SelectedMCA.directLineFailureBound localThreshold)).labelsAtLeast a
    · rw [min_eq_left hle]
      exact houter
    · rw [min_eq_right (Nat.le_of_not_ge hle)]
      exact hlocal
  · simp only [selectedMCARefinedFailureProfile, hcutoff, ↓reduceIte]
    exact houter

/-- Route-agnostic density bound for the agreement-local profile. -/
theorem badWeightsAtAgreement_density_refinedOfLine
    {outerBound cutoff localBound : ℕ}
    (respond : Weights F CheckedMask nw nq → EvaluationRow F r w n)
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : LigeroFamily.RefinedSelectedMCALineConditions C.baseCode
      (Fintype.card F) e g d outerBound cutoff localBound)
    (a : ℕ) :
    (Fintype.card F - (g + 1)) *
        (badWeightsAtAgreement (C := C) (oracle := oracle)
          (e := e) (g := g) respond a).card ≤
      (selectedMCARefinedFailureProfile n g d
        outerBound cutoff localBound).labelsAtLeast a *
        Fintype.card (Weights F CheckedMask nw nq) := by
  have houter := badWeightsAtAgreement_density
    (C := C) (oracle := oracle) respond hmin conditions.outer.line
      conditions.outer.punctured.punctured_three_radius
      conditions.outer.punctured.field_large a
  by_cases hcutoff : cutoff ≤ a
  · have heq := badWeightsAtAgreement_eq_localRadius
      (C := C) (oracle := oracle) (e := e) (g := g) respond cutoff a
      conditions.radius_le_cutoff hcutoff
    have hlocal := badWeightsAtAgreement_density
      (C := C) (oracle := oracle) (e := n - cutoff) (g := g)
      respond hmin conditions.localLine conditions.local_three_radius
      conditions.outer.punctured.field_large a
    rw [← heq] at hlocal
    simp only [selectedMCARefinedFailureProfile, hcutoff, ↓reduceIte]
    by_cases hle :
        (selectedMCAFailureProfile n g d outerBound).labelsAtLeast a ≤
        (selectedMCAFailureProfile n g d localBound).labelsAtLeast a
    · rw [min_eq_left hle]
      exact houter
    · rw [min_eq_right (Nat.le_of_not_ge hle)]
      exact hlocal
  · simp only [selectedMCARefinedFailureProfile, hcutoff, ↓reduceIte]
    exact houter

/-- Threshold-free density theorem.  The local radius is specialized to the
actual tail level `a`, so the resulting profile can be integrated without an
arbitrary cutoff. -/
theorem badWeightsAtAgreement_density_integratedOfLine
    {outerBound : ℕ} {localBound : ℕ → ℕ}
    (respond : Weights F CheckedMask nw nq → EvaluationRow F r w n)
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : LigeroFamily.IntegratedSelectedMCALineConditions C.baseCode
      (Fintype.card F) e g d outerBound localBound)
    (a : ℕ) :
    (Fintype.card F - (g + 1)) *
        (badWeightsAtAgreement (C := C) (oracle := oracle)
          (e := e) (g := g) respond a).card ≤
      (selectedMCAIntegratedFailureProfile n e g d
        outerBound localBound).labelsAtLeast a *
        Fintype.card (Weights F CheckedMask nw nq) := by
  have houter := badWeightsAtAgreement_density
    (C := C) (oracle := oracle) respond hmin conditions.outer.line
      conditions.outer.punctured.punctured_three_radius
      conditions.outer.punctured.field_large a
  by_cases hrange : n - e ≤ a ∧ a ≤ n
  · have heq := badWeightsAtAgreement_eq_localRadius
      (C := C) (oracle := oracle) (e := e) (g := g) respond a a
      hrange.1 le_rfl
    have hlocal := badWeightsAtAgreement_density
      (C := C) (oracle := oracle) (e := n - a) (g := g)
      respond hmin (conditions.localLine a hrange.1 hrange.2)
      (conditions.local_three_radius a hrange.1 hrange.2)
      conditions.outer.punctured.field_large a
    rw [← heq] at hlocal
    simp only [selectedMCAIntegratedFailureProfile, hrange]
    by_cases hle :
        (selectedMCAFailureProfile n g d outerBound).labelsAtLeast a ≤
          (selectedMCAFailureProfile n g d (localBound a)).labelsAtLeast a
    · rw [min_eq_left hle]
      exact houter
    · rw [min_eq_right (Nat.le_of_not_ge hle)]
      exact hlocal
  · simp only [selectedMCAIntegratedFailureProfile, hrange, ↓reduceIte]
    exact houter

/-- Threshold-free selected MCA with the exact full-agreement normalization.
The common denominator keeps a single `AgreementProfile` while changing no
tail below full agreement. -/
theorem badWeightsAtAgreement_density_endpointOptimizedIntegratedOfLine
    {outerBound : ℕ} {localBound : ℕ → ℕ}
    (respond : Weights F CheckedMask nw nq → EvaluationRow F r w n)
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : LigeroFamily.IntegratedSelectedMCALineConditions C.baseCode
      (Fintype.card F) e g d outerBound localBound)
    (a : ℕ) :
    (Fintype.card F * (Fintype.card F - (g + 1))) *
        (badWeightsAtAgreement (C := C) (oracle := oracle)
          (e := e) (g := g) respond a).card ≤
      (endpointOptimizedProfile (Fintype.card F) g
        (selectedMCAIntegratedFailureProfile n e g d
          outerBound localBound)).labelsAtLeast a *
        Fintype.card (Weights F CheckedMask nw nq) := by
  let q := Fintype.card F
  let selected := badWeightsAtAgreement (C := C) (oracle := oracle)
    (e := e) (g := g) respond a
  let profile := selectedMCAIntegratedFailureProfile n e g d
    outerBound localBound
  have hgeneric := badWeightsAtAgreement_density_integratedOfLine
    (C := C) (oracle := oracle) respond hmin conditions a
  have hgenericScaled :
      (q * (q - (g + 1))) * selected.card ≤
        (q * profile.labelsAtLeast a) *
          Fintype.card (Weights F CheckedMask nw nq) := by
    calc
      (q * (q - (g + 1))) * selected.card =
          q * ((q - (g + 1)) * selected.card) := by ring
      _ ≤ q * (profile.labelsAtLeast a *
          Fintype.card (Weights F CheckedMask nw nq)) :=
        Nat.mul_le_mul_left q (by simpa [q, selected, profile] using hgeneric)
      _ = (q * profile.labelsAtLeast a) *
          Fintype.card (Weights F CheckedMask nw nq) := by ring
  by_cases ha : a = n
  · subst a
    have hfull := badWeightsAtFullAgreement_card_le
      (C := C) (oracle := oracle) (e := e) (g := g)
      respond hmin conditions.outer.punctured.punctured_three_radius
        conditions.outer.punctured.field_large
    let power := q ^
      (Fintype.card (SchemeTestedRow CheckedMask nw nq 1) - 1)
    have hweightsCard :
        Fintype.card (Weights F CheckedMask nw nq) = q * power := by
      rw [Fintype.card_fun]
      have hrowpos : 0 <
          Fintype.card (SchemeTestedRow CheckedMask nw nq 1) :=
        Fintype.card_pos
      rw [show Fintype.card (SchemeTestedRow CheckedMask nw nq 1) =
          (Fintype.card (SchemeTestedRow CheckedMask nw nq 1) - 1) + 1 by
        omega, pow_succ]
      ring
    have hfullDensity : q * selected.card ≤
        (g + 1) * Fintype.card (Weights F CheckedMask nw nq) := by
      calc
        q * selected.card ≤ q * ((g + 1) * power) :=
          Nat.mul_le_mul_left q (by simpa [selected, power] using hfull)
        _ = (g + 1) * Fintype.card
            (Weights F CheckedMask nw nq) := by rw [hweightsCard]; ring
    have hfullScaled :
        (q * (q - (g + 1))) * selected.card ≤
          ((g + 1) * (q - (g + 1))) *
            Fintype.card (Weights F CheckedMask nw nq) := by
      calc
        (q * (q - (g + 1))) * selected.card =
            (q - (g + 1)) * (q * selected.card) := by ring
        _ ≤ (q - (g + 1)) *
            ((g + 1) * Fintype.card (Weights F CheckedMask nw nq)) :=
          Nat.mul_le_mul_left _ hfullDensity
        _ = ((g + 1) * (q - (g + 1))) *
            Fintype.card (Weights F CheckedMask nw nq) := by ring
    simpa [endpointOptimizedProfile, q, selected, profile] using
      (le_min hgenericScaled hfullScaled)
  · simpa [endpointOptimizedProfile, ha, q, selected, profile] using
      hgenericScaled

/-- The unprofiled density bound is the zero-agreement specialization of the
profiled theorem. -/
theorem badWeights_density
    (respond : Weights F CheckedMask nw nq → EvaluationRow F r w n)
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (hline : SelectedMCA.LineFailureBound C.baseCode e g
      (bound))
    (hthree : 3 * g < d - e) (hfield : g + 1 < Fintype.card F) :
    (Fintype.card F - (g + 1)) *
        (badWeights (C := C) (oracle := oracle) (e := e) (g := g)
          respond).card ≤
      bound *
        Fintype.card (Weights F CheckedMask nw nq) := by
  have hprofile := badWeightsAtAgreement_density
    (C := C) (oracle := oracle) respond hmin hline
      hthree hfield 0
  have hbad :
      badWeightsAtAgreement (C := C) (oracle := oracle)
        (e := e) (g := g) respond 0 =
      badWeights (C := C) (oracle := oracle) (e := e) (g := g) respond := by
    ext weights
    simp [badWeightsAtAgreement]
  have hnotSharp : ¬3 * n < d := by
    have := hmin.distance_le_length
    omega
  simpa [hbad, selectedMCAFailureProfile, hnotSharp] using hprofile

end SchemeSelectedMCA

end LigeroFamily
