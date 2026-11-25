import LfzkV1.LigeroHighMass125V1
import LfzkV1.LiftOpening125

/-!
# Response-specific charge for unsatisfying scalar lifts

Fix an unsatisfying candidate of the commitment before the challenge.
An accepted response translates to a pair of arithmetic offsets. The set
of positions where these offsets match their masks outside the candidate's
error set is fixed independently of the challenge. Charge each possible
offset pair on a single selected violated equation.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace LfzkV1.LigeroHighMass125

open Finset LigeroFamily LigeroFamily.AgreementProfile Ligero.V1
open CodingTheory MultiplicativeCode Ligero.V1.SchemeLiftCandidate
open scoped Classical

variable {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Equations] [DecidableEq Equations]
variable {r w n nw nq e g d a L radius : ℕ}
variable {C : MultiplicativeCode F r w n}
variable {oracle : Oracle F nw nq n 1}
variable (statement : ConstraintSystem F nw nq w Equations)

local notation "Challenge" => SchemeChallenge F NoMask nw nq 1 Equations
local notation "Reply" => Response F r w n 1
local notation "Lift" => SchemeLiftCandidate C oracle radius
local notation "Offsets" => EvaluationRow F r w n × EvaluationRow F r w n
local notation "v1Policy" => SchemeVerifier.policy (Equations := Equations) (nw := nw)
  (nq := nq) (repetitions := 1) C scheme

noncomputable def offsetOf (candidate : Lift) (challenge : Challenge) (u : Reply) : Offsets :=
  (u.linear 0 - v1LinearCanonical candidate statement (challenge 0).linear,
    u.quadratic 0 - v1QuadraticCanonical candidate (challenge 0).quadratic)

noncomputable def offsetColumns (candidate : Lift) (offset : Offsets) : Finset (Fin n) :=
  LiftOpening125.agreement candidate ∩
    (wordAgreement (oracle.directMask 0 .linear) (codeword offset.1) ∩
      wordAgreement (oracle.directMask 0 .quadratic) (codeword offset.2))

/-- The fixed offsets with enough agreement to originate from a high response. -/
noncomputable def labelFamily (candidate : Lift) (a g : ℕ) : Finset Offsets :=
  univ.filter fun offset => offset.1 ∈ C.response ∧ offset.2 ∈ C.response ∧
    a - g ≤ (offsetColumns candidate offset).card

/-- High responses that admit this particular punctured lift. -/
noncomputable def liftedResponses (candidate : Lift) (a g : ℕ) (c : Challenge) : Finset Reply :=
  (policyResponseAgreementList v1Policy oracle statement c a).filter fun u =>
    candidate.proximityRow (c 0).proximity = u.proximity 0 ∧
    (candidate.remainingBadColumns (c 0).proximity (u.proximity 0)).card ≤ g

theorem offsetOf_injective (candidate : Lift) (c : Challenge) (a g : ℕ) :
    Set.InjOn (offsetOf statement candidate c)
      (↑(liftedResponses statement candidate a g c) : Set Reply) := by
  intro u hu v hv heq
  have hu' := (mem_filter.mp (show u ∈ liftedResponses statement candidate a g c from hu)).2.1
  have hv' := (mem_filter.mp (show v ∈ liftedResponses statement candidate a g c from hv)).2.1
  apply Response.ext
  · funext i
    rw [Subsingleton.elim i 0, ← hu', hv']
  · funext i
    rw [Subsingleton.elim i 0]
    exact sub_left_inj.mp (congrArg Prod.fst heq)
  · funext i
    rw [Subsingleton.elim i 0]
    exact sub_left_inj.mp (congrArg Prod.snd heq)

theorem columns_le_offsetColumns_add (candidate : Lift) {c : Challenge} {u : Reply}
    (hu : u ∈ liftedResponses statement candidate a g c) :
    (columns (C := C) oracle statement c u).card ≤
      (offsetColumns candidate (offsetOf statement candidate c u)).card +
        min g candidate.badColumns.card := by
  classical
  let remaining := candidate.remainingBadColumns (c 0).proximity (u.proximity 0)
  let offsets := offsetColumns candidate (offsetOf statement candidate c u)
  have hsub : columns (C := C) oracle statement c u ⊆ offsets ∪ remaining := by
    intro j hj
    obtain ⟨query, hpass, hjq⟩ := (mem_filter.mp hj).2
    by_cases hr : j ∈ remaining
    · exact mem_union_right _ hr
    · have hbad := candidate.query_bad_subset_remaining (c 0).proximity
        (u.proximity 0) query (hpass 0).1
      have hgood : j ∈ LiftOpening125.agreement candidate := by
        rw [LiftOpening125.agreement, mem_compl]
        exact fun h => hr (hbad (mem_inter.mpr ⟨hjq, h⟩))
      have hl := v1_linear_query_cover candidate statement (c 0).linear (u.linear 0)
        query (hpass 0).2.1 remaining hbad hjq
      have hq := v1_quadratic_query_cover candidate (c 0).quadratic (u.quadratic 0)
        query (hpass 0).2.2 remaining hbad hjq
      exact mem_union_left _ (mem_inter.mpr
        ⟨hgood, mem_inter.mpr ⟨(mem_union.mp hl).resolve_left hr,
          (mem_union.mp hq).resolve_left hr⟩⟩)
  calc
    _ ≤ (offsets ∪ remaining).card := card_le_card hsub
    _ ≤ offsets.card + remaining.card := card_union_le _ _
    _ ≤ _ := Nat.add_le_add_left (le_min (mem_filter.mp hu).2.2
      (card_le_card (sdiff_subset))) _

theorem offsetOf_mem_labelFamily (candidate : Lift) {c : Challenge} {u : Reply}
    (hu : u ∈ liftedResponses statement candidate a g c) :
    offsetOf statement candidate c u ∈ labelFamily candidate a g := by
  obtain ⟨⟨query, hpass⟩, ha⟩ := (mem_filter.mp (mem_filter.mp hu).1).2
  have hsize := columns_le_offsetColumns_add statement candidate hu
  exact mem_filter.mpr ⟨mem_univ _, C.response.sub_mem (hpass 0).2.1.1
      (v1LinearCanonical_mem candidate statement (c 0).linear),
    C.response.sub_mem (hpass 0).2.2.1 (v1QuadraticCanonical_mem candidate (c 0).quadratic),
    by
      change a ≤ (columns (C := C) oracle statement c u).card at ha
      have hmin := min_le_left g candidate.badColumns.card
      omega⟩

theorem offsetColumns_overlap (candidate : Lift) {x y : Offsets}
    (hx : x ∈ labelFamily candidate a g) (hy : y ∈ labelFamily candidate a g)
    (hne : x ≠ y) :
    (offsetColumns candidate x ∩ offsetColumns candidate y).card ≤ 2 * C.k - 1 := by
  obtain ⟨hx1, hx2, _⟩ := (mem_filter.mp hx).2
  obtain ⟨hy1, hy2, _⟩ := (mem_filter.mp hy).2
  by_cases h1 : x.1 = y.1
  · have h2 : x.2 ≠ y.2 := fun h => hne (Prod.ext h1 h)
    refine (card_le_card (t := responseAgreement x.2 y.2) ?_).trans
      (responseAgreement_card_le C hx2 hy2 h2)
    intro j hj
    obtain ⟨hleft, hright⟩ := mem_inter.mp hj
    have hleft' := (mem_inter.mp (mem_inter.mp hleft).2).2
    have hright' := (mem_inter.mp (mem_inter.mp hright).2).2
    exact (mem_responseAgreement _ _ _).mpr
      (((mem_wordAgreement _ _ _).mp hleft').symm.trans ((mem_wordAgreement _ _ _).mp hright'))
  · refine (card_le_card (t := responseAgreement x.1 y.1) ?_).trans
      (responseAgreement_card_le C hx1 hy1 h1)
    intro j hj
    obtain ⟨hleft, hright⟩ := mem_inter.mp hj
    have hleft' := (mem_inter.mp (mem_inter.mp hleft).2).1
    have hright' := (mem_inter.mp (mem_inter.mp hright).2).1
    exact (mem_responseAgreement _ _ _).mpr
      (((mem_wordAgreement _ _ _).mp hleft').symm.trans ((mem_wordAgreement _ _ _).mp hright'))

/-- A secondary candidate with small agreement supports at most one high
response to a fixed batch, regardless of whether the candidate satisfies
the statement. -/
theorem liftedResponse_unique (candidate : Lift) {c : Challenge} {u v : Reply}
    (hsmall : (LiftOpening125.agreement candidate).card + (2 * C.k - 1) < 2 * (a - g))
    (hu : u ∈ liftedResponses statement candidate a g c)
    (hv : v ∈ liftedResponses statement candidate a g c) : u = v := by
  let family := labelFamily candidate a g
  let x : {z : Offsets // z ∈ family} :=
    ⟨offsetOf statement candidate c u, offsetOf_mem_labelFamily statement candidate hu⟩
  let y : {z : Offsets // z ∈ family} :=
    ⟨offsetOf statement candidate c v, offsetOf_mem_labelFamily statement candidate hv⟩
  have he : x = y := LiftOpening125.response_unique
    (fun z : {z : Offsets // z ∈ family} => offsetColumns candidate z.val)
    (LiftOpening125.agreement candidate) (a - g) (2 * C.k - 1)
    (fun _ => inter_subset_left)
    (fun z w hne => offsetColumns_overlap candidate z.property w.property
      (fun h => hne (Subtype.ext h))) hsmall
    (mem_filter.mp x.property).2.2.2 (mem_filter.mp y.property).2.2.2
  exact offsetOf_injective statement candidate c a g hu hv (congrArg Subtype.val he)

theorem offset_label_density (candidate : Lift)
    (violation : V1Violation candidate statement) (offset : Offsets) :
    Fintype.card F *
      (univ.filter fun c : Challenge =>
        offset ∈ (liftedResponses statement candidate a g c).image
          (offsetOf statement candidate c)).card ≤ Fintype.card Challenge := by
  classical
  let cuts : Finset Challenge := univ.filter fun c : Challenge =>
    offset ∈ (liftedResponses statement candidate a g c).image (offsetOf statement candidate c)
  cases hkind : violation.kind with
  | linear =>
    let residual := v1LinearResidual candidate statement
    let label : F := -(∑ i : Fin w, offset.1 (witnessPosition i))
    let special := finiteDotLabelPreimage residual {label}
    have hnonzero : residual ≠ 0 := by simpa [hkind] using violation.nonzero
    have hsub : cuts ⊆ SchemeInternal.liftLinear (CheckedMask := NoMask)
        (nw := nw) (nq := nq) special := by
      intro c hc
      obtain ⟨u, hu, heq⟩ := mem_image.mp (mem_filter.mp hc).2
      obtain ⟨⟨query, hpass⟩, _⟩ := (mem_filter.mp (mem_filter.mp hu).1).2
      have hequation := v1_linear_offset_label candidate statement (c 0).linear (u.linear 0)
        (hpass 0).2.1.2.1
      have h := congrArg Prod.fst heq
      change u.linear 0 - v1LinearCanonical candidate statement (c 0).linear = offset.1 at h
      rw [h] at hequation
      exact mem_filter.mpr ⟨mem_univ _, mem_filter.mpr ⟨mem_univ _, mem_singleton.mpr hequation.symm⟩⟩
    have hdensity : Fintype.card F * special.card ≤ 1 * Nat.card (Equations → F) := by
      simpa [special, Nat.card_eq_fintype_card] using
        finiteDotLabelPreimage_density residual {label} hnonzero
    simpa [cuts, Nat.card_eq_fintype_card] using
      (Nat.mul_le_mul_left (Fintype.card F) (card_le_card hsub)).trans
        (SchemeInternal.liftLinear_density (CheckedMask := NoMask) (nw := nw) (nq := nq)
          (Fintype.card F) 1 special hdensity)
  | quadratic i =>
    let residual : Fin nq → F := fun row => v1QuadraticResidual candidate row i
    let label : F := - offset.2 (witnessPosition i)
    let special := finiteDotLabelPreimage residual {label}
    have hnonzero : residual ≠ 0 := by simpa [hkind] using violation.nonzero
    have hsub : cuts ⊆ SchemeInternal.liftQuadratic (CheckedMask := NoMask)
        (Equations := Equations) (nw := nw) special := by
      intro c hc
      obtain ⟨u, hu, heq⟩ := mem_image.mp (mem_filter.mp hc).2
      obtain ⟨⟨query, hpass⟩, _⟩ := (mem_filter.mp (mem_filter.mp hu).1).2
      have hequation := v1_quadratic_offset_label candidate (c 0).quadratic i (u.quadratic 0)
        ((hpass 0).2.2.2.1 i)
      have h := congrArg Prod.snd heq
      change u.quadratic 0 - v1QuadraticCanonical candidate (c 0).quadratic = offset.2 at h
      rw [h] at hequation
      exact mem_filter.mpr ⟨mem_univ _, mem_filter.mpr ⟨mem_univ _, mem_singleton.mpr hequation.symm⟩⟩
    have hdensity : Fintype.card F * special.card ≤ 1 * Nat.card (Fin nq → F) := by
      simpa [special, Nat.card_eq_fintype_card] using
        finiteDotLabelPreimage_density residual {label} hnonzero
    simpa [cuts, Nat.card_eq_fintype_card] using
      (Nat.mul_le_mul_left (Fintype.card F) (card_le_card hsub)).trans
        (SchemeInternal.liftQuadratic_density (CheckedMask := NoMask)
          (Equations := Equations) (nw := nw) (Fintype.card F) 1 special hdensity)

/-- Sum all high responses supported by one unsatisfying candidate. The
extra columns are charged only where the candidate can actually disagree. -/
theorem lifted_average_mass_le (candidate : Lift)
    (hns : ¬statement.Satisfies candidate.decodedMessages)
    (hlarge : 2 * C.k - 1 < a - g)
    (hfamily : UniformFamilyBound n (a - g) (2 * C.k - 1) L) :
    (∑ c : Challenge, ∑ u ∈ liftedResponses statement candidate a g c,
      hypergeometricRatio (columns (C := C) oracle statement c u).card n r) /
        Fintype.card Challenge ≤
      (hypergeometricRatio (min n ((LiftOpening125.agreement candidate).card + g)) n r +
        (L : ℚ) * hypergeometricRatio ((n + (2 * C.k - 1) + g) / 2) n r) /
        Fintype.card F := by
  classical
  letI : Nonempty Challenge := ⟨fun _ => ⟨0, 0, 0⟩⟩
  let labels := labelFamily candidate a g
  let responses : Challenge → Finset Offsets := fun c => (liftedResponses statement candidate a g c).image
    (offsetOf statement candidate c)
  let size : Offsets → ℕ := fun offset =>
    (offsetColumns candidate offset).card + min g candidate.badColumns.card
  let weight : Offsets → ℚ := fun offset => hypergeometricRatio (size offset) n r
  have hagree : (LiftOpening125.agreement candidate).card + candidate.badColumns.card = n := by
    simp only [LiftOpening125.agreement, card_compl, Fintype.card_fin]
    have hcard := card_le_univ (s := candidate.badColumns)
    rw [Fintype.card_fin] at hcard
    omega
  have hsize (u : Offsets) : (offsetColumns candidate u).card ≤
      (LiftOpening125.agreement candidate).card := card_le_card (inter_subset_left)
  have hinject (c : Challenge) : Set.InjOn (offsetOf statement candidate c)
      (↑(liftedResponses statement candidate a g c) : Set Reply) :=
    offsetOf_injective statement candidate c a g
  have hsubset (c : Challenge) : responses c ⊆ labels := by
    intro offset hmem
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hmem
    exact offsetOf_mem_labelFamily statement candidate hu
  obtain ⟨violation⟩ := V1Violation.nonempty_of_false candidate hns
  have hratio (c : Challenge) :
      ∑ u ∈ liftedResponses statement candidate a g c,
        hypergeometricRatio (columns (C := C) oracle statement c u).card n r ≤
      ∑ offset ∈ responses c, weight offset := by
    change _ ≤ ∑ offset ∈ (liftedResponses statement candidate a g c).image
      (offsetOf statement candidate c), weight offset
    rw [sum_image (hinject c)]
    exact sum_le_sum fun u hu => opening_mono (columns_le_offsetColumns_add statement candidate hu)
  have haverage : (∑ c : Challenge, ∑ offset ∈ responses c, weight offset) / Fintype.card Challenge ≤
      (∑ offset ∈ labels, weight offset) / Fintype.card F := by
    apply labeled_average_mass_le (X := Challenge) (R := Offsets) responses labels weight
      (q := Fintype.card F) Fintype.card_pos hsubset
    · exact fun offset _ => opening_nonneg (size offset)
    · intro offset _
      have hd := offset_label_density (a := a) (g := g) statement candidate violation offset
      simpa only [responses] using hd
  have hcount : labels.card ≤ L :=
    family_card_le labels (offsetColumns candidate) hlarge
      (fun u hu => (mem_filter.mp hu).2.2.2)
      (fun _ hu _ hv hne => offsetColumns_overlap candidate hu hv hne) hfamily
  calc
    _ ≤ (∑ c : Challenge, ∑ offset ∈ responses c, weight offset) / Fintype.card Challenge := by
      exact div_le_div_of_nonneg_right (sum_le_sum fun c _ => hratio c) (by positivity)
    _ ≤ (∑ offset ∈ labels, weight offset) / Fintype.card F := haverage
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mass_le_peak_add_of_pair_card labels size (pairBound := n + (2 * C.k - 1) + g)
        (peak := min n ((LiftOpening125.agreement candidate).card + g)) hcount
      · intro u _
        have hbad : min g candidate.badColumns.card ≤ candidate.badColumns.card := min_le_right _ _
        have hg : min g candidate.badColumns.card ≤ g := min_le_left _ _
        exact le_min (by dsimp [size]; have := hsize u; omega)
          (Nat.add_le_add (hsize u) hg)
      · intro u hu v hv hne
        have hsub := card_le_card
          (show (offsetColumns candidate u ∪ offsetColumns candidate v) ⊆
            LiftOpening125.agreement candidate from
            union_subset inter_subset_left inter_subset_left)
        have hmeet := offsetColumns_overlap candidate hu hv hne
        have hsum := card_union_add_card_inter (offsetColumns candidate u)
          (offsetColumns candidate v)
        have hbad : min g candidate.badColumns.card ≤ candidate.badColumns.card := min_le_right _ _
        have hg : min g candidate.badColumns.card ≤ g := min_le_left _ _
        dsimp [size]
        omega

end LfzkV1.LigeroHighMass125
