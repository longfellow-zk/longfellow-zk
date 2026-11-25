import LigeroFamily.Soundness.SchemeFixedLiftList
import LigeroFamily.Soundness.SchemeLiftBridge

/-!
# Selecting a v1 lift from the opened columns

A punctured lift may disagree with the committed tableau on some opened
columns. Two lifts that both explain the openings must nevertheless share
most of those columns. Their common agreement is bounded by the base-code
distance.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LfzkV1.LiftOpening125

open Finset LigeroFamily CodingTheory MultiplicativeCode
open scoped Classical

section Lift

variable {F CheckedMask DirectMask : Type*}
variable [Field F] [DecidableEq F] [Fintype CheckedMask]
variable {n r w nw nq radius d g : ℕ}
variable {C : MultiplicativeCode F r w n}
variable {oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1}

noncomputable def agreement (lift : SchemeLiftCandidate C oracle radius) : Finset (Fin n) :=
  lift.badColumnsᶜ

/-- All but at most `g` opened columns agree with this lift. -/
def Compatible (lift : SchemeLiftCandidate C oracle radius) (query : QuerySet n r)
    (g : ℕ) : Prop :=
  (query.coordinates \ lift.badColumnsᶜ).card ≤ g

theorem agreement_inter_card_le (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    {x y : SchemeLiftCandidate C oracle radius} (hne : x ≠ y) :
    (agreement x ∩ agreement y).card ≤ n - d := by
  let rows := fun z : SchemeLiftCandidate C oracle radius =>
    schemeLiftCandidateRows z.offset z.row
  have hrow (z : SchemeLiftCandidate C oracle radius)
      (i : Option (SchemeTestedRow CheckedMask nw nq 1)) : rows z i ∈ C.baseCode := by
    cases i with
    | none => exact C.codeword_mem_baseCode z.offset_mem
    | some i => exact C.codeword_mem_baseCode (z.row_mem i)
  have hdist := InterleavedJohnson.matrixErrorCoordinates_card_ge_distance
    C.baseCode hmin (hrow x) (hrow y)
      (fun h => hne (SchemeLiftCandidate.candidateRows_injective h))
  have hsubset : agreement x ∩ agreement y ⊆ (matrixErrorCoordinates (rows x) (rows y))ᶜ := by
    intro j hj
    obtain ⟨hx, hy⟩ := mem_inter.mp hj
    rw [agreement, mem_compl] at hx hy
    simp only [mem_compl, matrixErrorCoordinates, mem_filter, mem_univ, true_and]
    rintro ⟨i, hdiff⟩
    apply hdiff
    cases i with
    | none => exact (x.offset_eq_of_not_bad j hx).symm.trans (y.offset_eq_of_not_bad j hy)
    | some i => exact (x.row_eq_of_not_bad i j hx).symm.trans (y.row_eq_of_not_bad i j hy)
  refine (card_le_card hsubset).trans ?_
  rw [card_compl, Fintype.card_fin]
  exact Nat.sub_le_sub_left hdist n

/-- The smaller agreement set of two lifts has at most half the sum of the
ambient size and the common-agreement bound. -/
theorem secondary_card_le (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    {x y : SchemeLiftCandidate C oracle radius} (hne : x ≠ y)
    (horder : (agreement y).card ≤ (agreement x).card) :
    (agreement y).card ≤ (n + (n - d)) / 2 := by
  have hcommon := agreement_inter_card_le hmin hne
  have hunion : (agreement x ∪ agreement y).card ≤ n :=
    (card_le_card (subset_univ _)).trans (by simp)
  have hsum := card_union_add_card_inter (agreement x) (agreement y)
  omega

theorem compatible_of_remainingBadColumns
    {x : SchemeLiftCandidate C oracle radius}
    {weights : SchemeTestedRow CheckedMask nw nq 1 → F}
    {response : EvaluationRow F r w n} {query : QuerySet n r}
    (hprox : SchemeVerifier.ProximityAccepts C weights response query
      (openSchemeOracle oracle query) 0)
    (hremain : (x.remainingBadColumns weights response).card ≤ g) :
    Compatible x query g := by
  have hsub := x.query_bad_subset_remaining weights response query hprox
  have heq : query.coordinates \ x.badColumnsᶜ = query.coordinates ∩ x.badColumns := by
    ext i
    simp
  simpa only [Compatible, heq] using (card_le_card hsub).trans hremain

/-- Two compatible lifts force almost every opened column into their
intersection, even though each lift may discard different columns. -/
theorem common_openings_of_compatible
    {x y : SchemeLiftCandidate C oracle radius} {query : QuerySet n r}
    (hx : Compatible x query g) (hy : Compatible y query g) :
    r - 2 * g ≤ (query.coordinates ∩ (agreement x ∩ agreement y)).card := by
  have hex : query.coordinates \ (agreement x ∩ agreement y) =
      (query.coordinates \ agreement x) ∪ (query.coordinates \ agreement y) := by
    ext i
    simp only [mem_sdiff, mem_inter, mem_union]
    tauto
  have hx' : (query.coordinates \ agreement x).card ≤ g := hx
  have hy' : (query.coordinates \ agreement y).card ≤ g := hy
  have hc := card_sdiff_add_card_inter query.coordinates (agreement x ∩ agreement y)
  rw [hex, QuerySet.card_coordinates] at hc
  have hu := card_union_le (query.coordinates \ agreement x)
    (query.coordinates \ agreement y)
  omega

variable [Fintype (SchemeLiftCandidate C oracle radius)]

private theorem exists_primary (h : Nonempty (SchemeLiftCandidate C oracle radius)) :
    ∃ x : SchemeLiftCandidate C oracle radius,
      ∀ y : SchemeLiftCandidate C oracle radius, (agreement y).card ≤ (agreement x).card := by
  obtain ⟨x, _, hx⟩ := univ.exists_max_image (fun y : SchemeLiftCandidate C oracle radius =>
    (agreement y).card) ⟨Classical.choice h, mem_univ _⟩
  exact ⟨x, fun y => hx y (mem_univ _)⟩

/-- Select a greatest agreement set from the fixed cut. This choice uses
the commitment table and no transcript challenge. -/
noncomputable def primary (C : MultiplicativeCode F r w n)
    (oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1) (radius : ℕ)
    [Fintype (SchemeLiftCandidate C oracle radius)] :
    Option (SchemeLiftCandidate C oracle radius) :=
  if h : Nonempty (SchemeLiftCandidate C oracle radius) then some (exists_primary h).choose else none

theorem secondary_of_ne_primary (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (y : SchemeLiftCandidate C oracle radius) (hne : primary C oracle radius ≠ some y) :
    (agreement y).card ≤ (n + (n - d)) / 2 := by
  have hnonempty : Nonempty (SchemeLiftCandidate C oracle radius) := ⟨y⟩
  let x := (exists_primary hnonempty).choose
  have hp : primary C oracle radius = some x := by simp only [primary, dif_pos hnonempty, x]
  have hxy : x ≠ y := fun he => hne (hp.trans (congrArg some he))
  exact secondary_card_le hmin hxy ((exists_primary hnonempty).choose_spec y)

theorem secondary_unique (hcard : Fintype.card (SchemeLiftCandidate C oracle radius) ≤ 2)
    {x y : SchemeLiftCandidate C oracle radius}
    (hx : primary C oracle radius ≠ some x) (hy : primary C oracle radius ≠ some y) : x = y := by
  by_contra hxy
  have hnonempty : Nonempty (SchemeLiftCandidate C oracle radius) := ⟨x⟩
  let p := (exists_primary hnonempty).choose
  have hp : primary C oracle radius = some p := by simp only [primary, dif_pos hnonempty, p]
  have hpx : p ≠ x := fun h => hx (hp.trans (congrArg some h))
  have hpy : p ≠ y := fun h => hy (hp.trans (congrArg some h))
  have h := card_le_card (subset_univ ({p, x, y} : Finset (SchemeLiftCandidate C oracle radius)))
  simp [hpx, hpy, hxy] at h
  omega

end Lift

section Counting

variable {n r b : ℕ}

private theorem card_queriesContaining_le (required : Finset (Fin n)) :
    (univ.filter fun j : QuerySet n r => required ⊆ j.coordinates).card ≤
      (n - required.card).choose (r - required.card) := by
  classical
  rw [← show requiredᶜ.card = n - required.card by rw [card_compl, Fintype.card_fin],
    ← card_powersetCard]
  apply card_le_card_of_injOn (fun j : QuerySet n r => j.coordinates \ required)
  · intro j hj
    have hsub := (mem_filter.mp hj).2
    exact mem_powersetCard.mpr
      ⟨fun i hi => mem_compl.mpr (mem_sdiff.mp hi).2,
        by rw [card_sdiff_of_subset hsub, QuerySet.card_coordinates]⟩
  · intro i hi j hj heq
    change i.coordinates \ required = j.coordinates \ required at heq
    apply Subtype.ext
    change i.coordinates = j.coordinates
    rw [← union_sdiff_of_subset (mem_filter.mp hi).2,
      ← union_sdiff_of_subset (mem_filter.mp hj).2, heq]

/-- Count openings with at least `b` positions in a given set by choosing
those positions and then completing the opening. -/
theorem card_manyInside_le (allowed : Finset (Fin n)) :
    (univ.filter fun j : QuerySet n r => b ≤ (j.coordinates ∩ allowed).card).card ≤
      allowed.card.choose b * (n - b).choose (r - b) := by
  classical
  let tails (required : Finset (Fin n)) : Finset (QuerySet n r) :=
    univ.filter fun j => required ⊆ j.coordinates
  have hsub : (univ.filter fun j : QuerySet n r => b ≤ (j.coordinates ∩ allowed).card) ⊆
      (allowed.powersetCard b).biUnion tails := by
    intro j hj
    obtain ⟨required, hsub, hcard⟩ := exists_subset_card_eq (mem_filter.mp hj).2
    exact mem_biUnion.mpr ⟨required, mem_powersetCard.mpr
      ⟨hsub.trans inter_subset_right, hcard⟩, mem_filter.mpr
      ⟨mem_univ _, hsub.trans inter_subset_left⟩⟩
  calc
    _ ≤ ((allowed.powersetCard b).biUnion tails).card := card_le_card hsub
    _ ≤ (allowed.powersetCard b).card * (n - b).choose (r - b) := by
      apply card_biUnion_le_card_mul
      intro required hrequired
      simpa only [(mem_powersetCard.mp hrequired).2] using
        (card_queriesContaining_le (r := r) required)
    _ = _ := by rw [card_powersetCard]

/-- If there are only two lifts and they are both compatible, the opening
falls in the single tail fixed by that pair. -/
theorem card_ambiguous_le {Candidate : Type*} [Fintype Candidate]
    (agreement : Candidate → Finset (Fin n)) (accepts : Candidate → QuerySet n r → Prop)
    (g cap : ℕ) (hlist : Fintype.card Candidate ≤ 2)
    (hinter : ∀ x y, x ≠ y → (agreement x ∩ agreement y).card ≤ cap)
    (hcommon : ∀ x y j, accepts x j → accepts y j →
      r - 2 * g ≤ (j.coordinates ∩ (agreement x ∩ agreement y)).card) :
    (univ.filter fun j : QuerySet n r =>
      ∃ x y, x ≠ y ∧ accepts x j ∧ accepts y j).card ≤
      cap.choose (r - 2 * g) * (n - (r - 2 * g)).choose (r - (r - 2 * g)) := by
  classical
  by_cases hex : ∃ x y : Candidate, x ≠ y
  · obtain ⟨x, y, hxy⟩ := hex
    have hall (z : Candidate) : z = x ∨ z = y := by
      by_contra! hz
      have hsub : ({z, x, y} : Finset Candidate) ⊆ univ := subset_univ _
      have hcard := card_le_card hsub
      simp [hz.1, hz.2, hxy] at hcard
      omega
    calc
      _ ≤ (univ.filter fun j : QuerySet n r =>
          r - 2 * g ≤ (j.coordinates ∩ (agreement x ∩ agreement y)).card).card := by
        apply card_le_card
        intro j hj
        obtain ⟨a, b, hab, ha, hb⟩ := (mem_filter.mp hj).2
        refine mem_filter.mpr ⟨mem_univ _, ?_⟩
        rcases hall a with hax | hay <;> rcases hall b with hbx | hby
        · exact (hab (hax.trans hbx.symm)).elim
        · exact hcommon x y j (hax ▸ ha) (hby ▸ hb)
        · exact hcommon x y j (hbx ▸ hb) (hay ▸ ha)
        · exact (hab (hay.trans hby.symm)).elim
      _ ≤ _ := (card_manyInside_le _).trans
        (Nat.mul_le_mul_right _ (Nat.choose_le_choose _ (hinter x y hxy)))
  · have he : (univ.filter fun j : QuerySet n r =>
          ∃ x y, x ≠ y ∧ accepts x j ∧ accepts y j) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro j hj
        obtain ⟨x, y, hxy, _, _⟩ := (mem_filter.mp hj).2
        exact hex ⟨x, y, hxy⟩
    simp [he]

/-- Two responses agreeing with the same small set on sufficiently many
positions must be equal, given the code's bound on pairwise agreement. -/
theorem response_unique {Response : Type*} (supported : Response → Finset (Fin n))
    (allowed : Finset (Fin n)) (threshold overlap : ℕ)
    (hsub : ∀ x, supported x ⊆ allowed)
    (hinter : ∀ x y, x ≠ y → (supported x ∩ supported y).card ≤ overlap)
    (hroom : allowed.card + overlap < 2 * threshold)
    {x y : Response} (hx : threshold ≤ (supported x).card)
    (hy : threshold ≤ (supported y).card) : x = y := by
  classical
  by_contra hne
  have hc := card_union_add_card_inter (supported x) (supported y)
  have hi := hinter x y hne
  have hu := card_le_card (union_subset (hsub x) (hsub y))
  omega

end Counting

end LfzkV1.LiftOpening125
