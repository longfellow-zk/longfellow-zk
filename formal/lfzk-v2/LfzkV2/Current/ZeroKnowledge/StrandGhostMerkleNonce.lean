import Bcs.TotalOracle

/-! Indexed hidden-nonce counting for leaf-only Merkle simulation.

A raw query decodes to at most one column index and nonce. The later ghost
observer may adapt to all disclosed nonces, but has no hidden nonce argument.
We count in that full ghost experiment, without conditioning on earlier
misses. The existing off-coordinate counting theorem supplies the bound;
there is no union bound charging every query against every column. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.StrandGhostMerkle.Nonce
open Finset Bcs.TotalOracle
open scoped Classical

variable {Index Nonce Raw : Type} [Fintype Index] [Fintype Nonce]
variable (decode : Raw → Option (Index × Nonce))

def guesses (queries : List Raw) (index : Index) : Finset Nonce :=
  ((queries.filterMap decode).toFinset.filter fun entry => entry.1 = index).image Prod.snd

omit [Fintype Nonce] in
theorem guesses_sum_le (queries : List Raw) :
    ∑ index : Index, (guesses decode queries index).card ≤ queries.length := by
  let pairs := (queries.filterMap decode).toFinset
  calc
    _ ≤ ∑ index : Index, (pairs.filter fun entry => entry.1 = index).card :=
      Finset.sum_le_sum fun _ _ => Finset.card_image_le
    _ = pairs.card := by
      symm
      exact Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (s := pairs)
        (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
    _ ≤ (queries.filterMap decode).length := List.toFinset_card_le _
    _ ≤ queries.length := List.length_filterMap_le _ _

variable (opened : Finset Index) (prior : List Raw)
variable (later : ({index // index ∈ opened} → Nonce) → List Raw)

/-- Only opened nonce coordinates are supplied to the later computation.
Its output may be the full adaptive observer trace, not a fixed query list. -/
def disclosed (nonces : Index → Nonce) : {index // index ∈ opened} → Nonce :=
  fun index => nonces index.val

def candidates (nonces : Index → Nonce) (index : Index) : Finset Nonce :=
  guesses decode prior index ∪
    if index ∈ opened then ∅ else guesses decode (later (disclosed opened nonces)) index

omit [Fintype Index] [Fintype Nonce] in
theorem candidates_off (index : Index) (first second : Index → Nonce)
    (off : AgreeOff index first second) :
    candidates decode opened prior later first index = candidates decode opened prior later second index := by
  by_cases member : index ∈ opened
  · simp only [candidates,member,↓reduceIte]
  · have same : disclosed opened first = disclosed opened second := by
      funext other
      exact off other.val (fun equal => member (equal ▸ other.property))
    simp only [candidates,member,↓reduceIte,same]

omit [Fintype Nonce] in
theorem candidates_sum_le (nonces : Index → Nonce) :
    ∑ index : Index, (candidates decode opened prior later nonces index).card ≤
      prior.length + (later (disclosed opened nonces)).length := by
  calc
    _ ≤ ∑ index : Index,
        ((guesses decode prior index).card +
          (guesses decode (later (disclosed opened nonces)) index).card) := by
      apply Finset.sum_le_sum
      intro index _
      unfold candidates
      by_cases member : index ∈ opened
      · simp only [member,↓reduceIte,union_empty]
        exact Nat.le_add_right _ _
      · simp only [member,↓reduceIte]
        exact Finset.card_union_le _ _
    _ = (∑ index : Index, (guesses decode prior index).card) +
        ∑ index : Index, (guesses decode (later (disclosed opened nonces)) index).card :=
      Finset.sum_add_distrib
    _ ≤ prior.length + (later (disclosed opened nonces)).length :=
      Nat.add_le_add (guesses_sum_le decode prior) (guesses_sum_le decode _)

def bad (index : Index) (nonces : Index → Nonce) (value : Nonce) : Prop :=
  value ∈ candidates decode opened prior later nonces index

omit [Fintype Index] [Fintype Nonce] in
theorem bad_off (index : Index) (first second : Index → Nonce)
    (off : AgreeOff index first second) (value : Nonce) :
    bad decode opened prior later index first value → bad decode opened prior later index second value :=
  by
    unfold bad
    rw [candidates_off decode opened prior later index first second off]
    exact id

omit [Fintype Index] in
theorem bad_local (index : Index) (nonces : Index → Nonce) :
    (univ.filter (bad decode opened prior later index nonces)).card ≤
      (candidates decode opened prior later nonces index).card := by
  have equal : univ.filter (bad decode opened prior later index nonces) =
      candidates decode opened prior later nonces index := by
    ext value
    simp only [mem_filter,mem_univ,true_and,bad]
  rw [equal]

abbrev Hit (nonces : Index → Nonce) : Prop :=
  ∃ index, bad decode opened prior later index nonces (nonces index)

omit [Fintype Index] [Fintype Nonce] in
theorem hit_of_later (nonces : Index → Nonce) (index : Index) (hidden : index ∉ opened)
    (raw : Raw) (member : raw ∈ later (disclosed opened nonces))
    (decoded : decode raw = some (index,nonces index)) : Hit decode opened prior later nonces := by
  refine ⟨index,?_⟩
  unfold bad candidates
  apply Finset.mem_union_right
  rw [if_neg hidden]
  apply Finset.mem_image.mpr
  refine ⟨(index,nonces index),Finset.mem_filter.mpr ⟨?_,rfl⟩,rfl⟩
  exact List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨raw,member,decoded⟩)

omit [Fintype Index] [Fintype Nonce] in
theorem hit_of_prior (nonces : Index → Nonce) (index : Index)
    (raw : Raw) (member : raw ∈ prior)
    (decoded : decode raw = some (index,nonces index)) : Hit decode opened prior later nonces := by
  refine ⟨index,?_⟩
  unfold bad candidates
  apply Finset.mem_union_left
  apply Finset.mem_image.mpr
  refine ⟨(index,nonces index),Finset.mem_filter.mpr ⟨?_,rfl⟩,rfl⟩
  exact List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨raw,member,decoded⟩)

/-- Prior queries may target any column. Later queries count only hidden
columns; repeated guesses are counted once. The total-query form is a
conservative bound, with no factor for the number of committed columns. -/
theorem hit_card_mul_le (postQueries : ℕ)
    (bounded : ∀ revealed, (later revealed).length ≤ postQueries) :
    (univ.filter (Hit decode opened prior later)).card * Fintype.card Nonce ≤
      (prior.length + postQueries) * Fintype.card Nonce ^ Fintype.card Index := by
  have totalBound : ∀ nonces,
      ∑ index : Index, (candidates decode opened prior later nonces index).card ≤ prior.length + postQueries := by
    intro nonces
    exact (candidates_sum_le decode opened prior later nonces).trans
      (Nat.add_le_add_left (bounded _) _)
  exact card_exists_coord_le
    (bad decode opened prior later)
    (bad_off decode opened prior later)
    (fun index nonces => (candidates decode opened prior later nonces index).card)
    (bad_local decode opened prior later) (prior.length + postQueries) totalBound

theorem hit_ratio_le [Nonempty Nonce] (postQueries : ℕ)
    (bounded : ∀ revealed, (later revealed).length ≤ postQueries) :
    ((univ.filter (Hit decode opened prior later)).card : ℚ) /
        (Fintype.card Nonce : ℚ) ^ Fintype.card Index ≤
      (prior.length + postQueries : ℕ) / (Fintype.card Nonce : ℚ) := by
  have positive : (0 : ℚ) < Fintype.card Nonce := by exact_mod_cast Fintype.card_pos
  have counted := hit_card_mul_le decode opened prior later postQueries bounded
  rw [div_le_div_iff₀ (pow_pos positive _) positive]
  exact_mod_cast counted

/-- Any concrete disagreement event excluded by absence of indexed nonce
hits inherits the same bound. This keeps counting separate from replay. -/
theorem event_ratio_le [Nonempty Nonce] (event : (Index → Nonce) → Prop)
    (excluded : ∀ nonces, ¬ Hit decode opened prior later nonces → ¬ event nonces)
    (postQueries : ℕ) (bounded : ∀ revealed, (later revealed).length ≤ postQueries) :
    ((univ.filter event).card : ℚ) / (Fintype.card Nonce : ℚ) ^ Fintype.card Index ≤
      (prior.length + postQueries : ℕ) / (Fintype.card Nonce : ℚ) := by
  have contained : univ.filter event ⊆ univ.filter (Hit decode opened prior later) := by
    intro nonces member
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    by_contra miss
    exact excluded nonces miss (mem_filter.mp member).2
  calc
    _ ≤ ((univ.filter (Hit decode opened prior later)).card : ℚ) /
        (Fintype.card Nonce : ℚ) ^ Fintype.card Index := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg (Nat.cast_nonneg _) _)
      exact_mod_cast card_le_card contained
    _ ≤ _ := hit_ratio_le decode opened prior later postQueries bounded

end LfzkV2.Current.ZeroKnowledge.StrandGhostMerkle.Nonce
