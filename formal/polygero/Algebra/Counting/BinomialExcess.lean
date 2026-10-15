import polygero.Algebra.Counting.DiscreteThreshold
import CodingTheory.ListDecoding.HahnDelsarte
import CodingTheory.ListDecoding.InterleavedJohnson

/-! Binomial excess budgets for finite families of actual sets. -/
namespace RecursivePolygero.DirectBinomial
open Finset
variable {ι Ω : Type*} [DecidableEq ι] [DecidableEq Ω]

omit [DecidableEq ι] in
private theorem normalized_sum_le (A : Finset Ω) (I : Finset ι) (D : ι → Finset Ω)
    (t ell q : ℕ) (θ : ℚ) (hN : 0 < A.card.choose t) (hθ : θ ≤ 1)
    (hD : ∀ i ∈ I, D i ⊆ A)
    (ho : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (D i ∩ D j).card ≤ ell)
    (hc : DiscreteThreshold.Condition q ((ell.choose t : ℚ)/A.card.choose t) θ)
    (hIq : I.card ≤ q) :
    ∑ i ∈ I, ((D i).card.choose t : ℚ)/A.card.choose t ≤
      1+((I.card : ℚ)-1)*θ := by
  by_cases he : I.card = 0
  · simp only [card_eq_zero.mp he,sum_empty,card_empty]
    norm_num
    linarith
  by_cases hs : I.card = 1
  · obtain ⟨i,rfl⟩ := card_eq_one.mp hs
    simp only [sum_singleton,card_singleton,Nat.cast_one,sub_self,zero_mul,add_zero]
    apply (div_le_one (by exact_mod_cast hN)).mpr
    exact_mod_cast Nat.choose_le_choose t (card_le_card (hD i (mem_singleton_self i)))
  exact DiscreteThreshold.sum_le_threshold (by omega) hIq (by positivity) hc
    (fun u => normalized_linear A I D t u ell hD ho hN (by omega))

omit [DecidableEq ι] in
/-- Any at most `q` binomial counts have total excess at most `N-U`.
The threshold condition is stated after division by the positive query count `N`. -/
theorem excess_le (A : Finset Ω) (I : Finset ι) (D : ι → Finset Ω)
    (t ell q : ℕ) (U : ℚ) (hN : 0 < A.card.choose t)
    (hU : U ≤ A.card.choose t)
    (hD : ∀ i ∈ I, D i ⊆ A)
    (ho : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (D i ∩ D j).card ≤ ell)
    (hc : DiscreteThreshold.Condition q ((ell.choose t : ℚ)/A.card.choose t)
      (U/A.card.choose t)) (hIq : I.card ≤ q) :
    ∑ i ∈ I, max 0 (((D i).card.choose t : ℚ)-U) ≤ A.card.choose t-U := by
  classical
  let J := I.filter fun i => U < ((D i).card.choose t : ℚ)
  have hN' : (0 : ℚ) < A.card.choose t := by exact_mod_cast hN
  have hs := normalized_sum_le A J D t ell q (U/A.card.choose t) hN
    ((div_le_one hN').mpr hU) (fun i hi => hD i (mem_filter.mp hi).1)
    (fun i hi j hj => ho i (mem_filter.mp hi).1 j (mem_filter.mp hj).1) hc
    ((card_le_card (filter_subset _ _)).trans hIq)
  rw [← sum_div] at hs
  have hs' := (div_le_iff₀ hN').mp hs
  have he : (∑ i ∈ I, max 0 (((D i).card.choose t : ℚ)-U)) =
      ∑ i ∈ J, (((D i).card.choose t : ℚ)-U) := by
    simp only [J,sum_filter]
    apply sum_congr rfl
    intro i _
    split_ifs with hi
    · exact max_eq_right (by linarith)
    · exact max_eq_left (by linarith)
  rw [he,sum_sub_distrib,sum_const,nsmul_eq_mul]
  have hid : (1+((J.card : ℚ)-1)*(U/A.card.choose t))*(A.card.choose t) =
      A.card.choose t+((J.card : ℚ)-1)*U := by field_simp
  rw [hid] at hs'
  linarith

omit [DecidableEq ι] in
/-- The normalized form of the binomial excess budget. -/
theorem normalized_excess_le (A : Finset Ω) (I : Finset ι) (D : ι → Finset Ω)
    (t ell q : ℕ) (θ : ℚ) (hN : 0 < A.card.choose t) (hθ : θ ≤ 1)
    (hD : ∀ i ∈ I, D i ⊆ A)
    (ho : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (D i ∩ D j).card ≤ ell)
    (hc : DiscreteThreshold.Condition q ((ell.choose t : ℚ)/A.card.choose t) θ)
    (hIq : I.card ≤ q) :
    ∑ i ∈ I, max 0 (((D i).card.choose t : ℚ)/A.card.choose t-θ) ≤ 1-θ := by
  have hN' : (0 : ℚ) < A.card.choose t := by exact_mod_cast hN
  have h := excess_le A I D t ell q (θ*A.card.choose t) hN
    (by nlinarith only [hθ,hN']) hD ho
    (by simpa only [mul_div_cancel_right₀ _ hN'.ne'] using hc) hIq
  have he (i : ι) : max 0 (((D i).card.choose t : ℚ)/A.card.choose t-θ) =
      max 0 (((D i).card.choose t : ℚ)-θ*A.card.choose t)/A.card.choose t := by
    rw [← max_div_div_right hN'.le,zero_div,sub_div,mul_div_cancel_right₀ _ hN'.ne']
  simp_rw [he]
  rw [← sum_div]
  have hd := div_le_div_of_nonneg_right h hN'.le
  simpa only [sub_div,div_self hN'.ne',mul_div_cancel_right₀ _ hN'.ne'] using hd

section HahnExcess
variable {n : ℕ}

omit [DecidableEq ι] in
/-- Any indexed family of subsets of `Fin n` of size at least `w > ell` whose
distinct indices meet in at most `ell` coordinates has cardinality bounded by
any `UniformFamilyBound n w ell L`. -/
theorem active_card_le_of_uniformFamilyBound (I : Finset ι) (D : ι → Finset (Fin n))
    (w ell L : ℕ) (hlow : ell < w)
    (hsize : ∀ i ∈ I, w ≤ (D i).card)
    (ho : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (D i ∩ D j).card ≤ ell)
    (hbound : CodingTheory.UniformFamilyBound n w ell L) :
    I.card ≤ L := by
  classical
  have hsub : ∀ i ∈ I, ∃ B ⊆ D i, B.card = w := fun i hi ↦
    exists_subset_card_eq (hsize i hi)
  choose! shrink hshrinkSub hshrinkCard using hsub
  have hinj : Set.InjOn shrink I := by
    intro i hi j hj hij
    by_contra hne
    have hle : (shrink i).card ≤ (D i ∩ D j).card := by
      apply card_le_card
      intro x hx
      have hxj : x ∈ shrink j := by
        have hij' : shrink i = shrink j := hij
        rwa [← hij']
      exact mem_inter.mpr ⟨hshrinkSub i hi hx, hshrinkSub j hj hxj⟩
    have hmeet := ho i hi j hj hne
    rw [hshrinkCard i hi] at hle
    omega
  have himage := hbound (I.image shrink)
    (fun B hB ↦ by
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hB
      exact hshrinkCard i hi)
    (fun B hB B' hB' hne ↦ by
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hB
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hB'
      have hij : i ≠ j := fun heq ↦ hne (heq ▸ rfl)
      calc
        (shrink i ∩ shrink j).card ≤ (D i ∩ D j).card :=
          card_le_card (inter_subset_inter (hshrinkSub i hi) (hshrinkSub j hj))
        _ ≤ ell := ho i hi j hj hij)
  rwa [card_image_of_injOn hinj] at himage

omit [DecidableEq ι] in
/-- If two distinct sets in `Fin n` meet in at most `ell` points and the second
has size at least `w`, the first has size at most `n + ell - w`. -/
theorem pairwise_complement_card_le (D : ι → Finset (Fin n)) {i j : ι} {w ell : ℕ}
    (hj : w ≤ (D j).card) (ho : (D i ∩ D j).card ≤ ell) :
    (D i).card ≤ n + ell - w := by
  have hunion := card_union_add_card_inter (D i) (D j)
  have hle : (D i ∪ D j).card ≤ n := by
    simpa using card_le_univ (D i ∪ D j)
  omega

/-- A query-fraction strictly above the `(w - 1)`-column floor forces at least
`w` columns. -/
theorem size_ge_of_choose_div_gt {m w t : ℕ} {θ : ℚ}
    (hN : 0 < n.choose t)
    (hfloor : ((w - 1).choose t : ℚ) / n.choose t ≤ θ)
    (hgt : θ < (m.choose t : ℚ) / n.choose t) :
    w ≤ m := by
  have hN' : (0 : ℚ) < n.choose t := by exact_mod_cast hN
  have hlt : ((w - 1).choose t : ℚ) < m.choose t :=
    (div_lt_div_iff_of_pos_right hN').mp (hfloor.trans_lt hgt)
  have hltNat : (w - 1).choose t < m.choose t := by exact_mod_cast hlt
  by_contra hcon
  have hle : m.choose t ≤ (w - 1).choose t := Nat.choose_le_choose t (by omega)
  omega

omit [DecidableEq ι] in
/-- When at most one active set can exceed `θ`, the total excess is at most `1 - θ`
with no overlap penalty. -/
theorem normalized_excess_le_of_card_le_one (I : Finset ι) (D : ι → Finset (Fin n))
    (t : ℕ) (θ : ℚ) (hN : 0 < n.choose t) (hθ : θ ≤ 1)
    (hcard : (I.filter fun i ↦ θ < ((D i).card.choose t : ℚ) / n.choose t).card ≤ 1) :
    ∑ i ∈ I, max 0 (((D i).card.choose t : ℚ) / n.choose t - θ) ≤ 1 - θ := by
  classical
  let J := I.filter fun i ↦ θ < ((D i).card.choose t : ℚ) / n.choose t
  have hN' : (0 : ℚ) < n.choose t := by exact_mod_cast hN
  have he : (∑ i ∈ I, max 0 (((D i).card.choose t : ℚ) / n.choose t - θ)) =
      ∑ i ∈ J, (((D i).card.choose t : ℚ) / n.choose t - θ) := by
    simp only [J, sum_filter]
    apply sum_congr rfl
    intro i _
    split_ifs with hi
    · exact max_eq_right (by linarith)
    · exact max_eq_left (by linarith)
  rw [he]
  change J.card ≤ 1 at hcard
  have hJ : J.card = 0 ∨ J.card = 1 := by omega
  rcases hJ with h0 | h1
  · simp only [card_eq_zero.mp h0, sum_empty]
    linarith
  · obtain ⟨i, hi⟩ := card_eq_one.mp h1
    rw [hi, sum_singleton]
    have hle : (D i).card ≤ n := by simpa using card_le_univ (D i)
    have hdiv : ((D i).card.choose t : ℚ) / n.choose t ≤ 1 := by
      apply (div_le_one hN').mpr
      exact_mod_cast Nat.choose_le_choose t hle
    linarith

omit [DecidableEq ι] in
/-- **Route A (Hahn/Delsarte + `DiscreteThreshold`).** A `UniformFamilyBound` at
cutoff `w` caps the active set count at `min q L`, replacing `q` by `min q L`
in `DiscreteThreshold.Condition` (and discharging `min q L ≤ 1` directly). -/
theorem normalized_excess_le_of_uniformFamilyBound_threshold (I : Finset ι)
    (D : ι → Finset (Fin n)) (t ell q w L : ℕ) (θ : ℚ)
    (hN : 0 < n.choose t) (hθ : θ ≤ 1) (hlow : ell < w)
    (hfloor : ((w - 1).choose t : ℚ) / n.choose t ≤ θ)
    (ho : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (D i ∩ D j).card ≤ ell)
    (hbound : CodingTheory.UniformFamilyBound n w ell L)
    (hc : min q L ≤ 1 ∨
      DiscreteThreshold.Condition (min q L) ((ell.choose t : ℚ) / n.choose t) θ)
    (hIq : I.card ≤ q) :
    ∑ i ∈ I, max 0 (((D i).card.choose t : ℚ) / n.choose t - θ) ≤ 1 - θ := by
  classical
  let J := I.filter fun i ↦ θ < ((D i).card.choose t : ℚ) / n.choose t
  have hJsize : ∀ i ∈ J, w ≤ (D i).card := fun i hi ↦
    size_ge_of_choose_div_gt hN hfloor (mem_filter.mp hi).2
  have hJL : J.card ≤ L :=
    active_card_le_of_uniformFamilyBound J D w ell L hlow hJsize
      (fun i hi j hj ↦ ho i (mem_filter.mp hi).1 j (mem_filter.mp hj).1) hbound
  have hJq : J.card ≤ q := (card_le_card (filter_subset _ _)).trans hIq
  have hJmin : J.card ≤ min q L := Nat.le_min.mpr ⟨hJq, hJL⟩
  rcases hc with hle1 | hcond
  · exact normalized_excess_le_of_card_le_one I D t θ hN hθ (hJmin.trans hle1)
  · have hNuniv : 0 < (univ : Finset (Fin n)).card.choose t := by simpa using hN
    have hexcessJ := normalized_excess_le (univ : Finset (Fin n)) J D t ell (min q L) θ
      hNuniv hθ (fun _ _ ↦ subset_univ _)
      (fun i hi j hj ↦ ho i (mem_filter.mp hi).1 j (mem_filter.mp hj).1)
      (by simpa using hcond) hJmin
    have he : (∑ i ∈ I, max 0 (((D i).card.choose t : ℚ) / n.choose t - θ)) =
        ∑ i ∈ J, max 0 (((D i).card.choose t : ℚ) / n.choose t - θ) := by
      simp only [J, sum_filter]
      apply sum_congr rfl
      intro i _
      split_ifs with hi
      · rfl
      · exact max_eq_left (by linarith)
    rw [he]
    simpa using hexcessJ

omit [DecidableEq ι] in
/-- **Route B (Direct Hahn/Delsarte pairwise-complement excess bound).** Whenever
two or more active sets exist, each has size at most `n + ell - w`, bounding
the binomial excess directly from `UniformFamilyBound n w ell L` without
`DiscreteThreshold`. -/
theorem normalized_excess_le_of_uniformFamilyBound_direct (I : Finset ι)
    (D : ι → Finset (Fin n)) (t ell q w L : ℕ) (θ : ℚ)
    (hN : 0 < n.choose t) (hθ : θ ≤ 1) (hlow : ell < w)
    (hfloor : ((w - 1).choose t : ℚ) / n.choose t ≤ θ)
    (ho : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (D i ∩ D j).card ≤ ell)
    (hbound : CodingTheory.UniformFamilyBound n w ell L)
    (hdirect : ((min q L : ℕ) : ℚ) * (((n + ell - w).choose t : ℚ) / n.choose t) ≤
      1 + (((min q L : ℕ) : ℚ) - 1) * θ)
    (hIq : I.card ≤ q) :
    ∑ i ∈ I, max 0 (((D i).card.choose t : ℚ) / n.choose t - θ) ≤ 1 - θ := by
  classical
  let J := I.filter fun i ↦ θ < ((D i).card.choose t : ℚ) / n.choose t
  have hN' : (0 : ℚ) < n.choose t := by exact_mod_cast hN
  have hJsize : ∀ i ∈ J, w ≤ (D i).card := fun i hi ↦
    size_ge_of_choose_div_gt hN hfloor (mem_filter.mp hi).2
  have hJL : J.card ≤ L :=
    active_card_le_of_uniformFamilyBound J D w ell L hlow hJsize
      (fun i hi j hj ↦ ho i (mem_filter.mp hi).1 j (mem_filter.mp hj).1) hbound
  have hJq : J.card ≤ q := (card_le_card (filter_subset _ _)).trans hIq
  have hJmin : J.card ≤ min q L := Nat.le_min.mpr ⟨hJq, hJL⟩
  by_cases hcard : J.card ≤ 1
  · exact normalized_excess_le_of_card_le_one I D t θ hN hθ hcard
  · have h2 : 2 ≤ J.card := by omega
    let β : ℚ := ((n + ell - w).choose t : ℚ) / n.choose t
    have hcap : ∀ i ∈ J, ((D i).card.choose t : ℚ) / n.choose t ≤ β := by
      intro i hi
      have hcardErase : 0 < (J.erase i).card := by
        rw [card_erase_of_mem hi]
        omega
      obtain ⟨j, hjErase⟩ := card_pos.mp hcardErase
      have hjJ : j ∈ J := mem_of_mem_erase hjErase
      have hji : j ≠ i := ne_of_mem_erase hjErase
      have hcomp := pairwise_complement_card_le D (hJsize j hjJ)
        (ho i (mem_filter.mp hi).1 j (mem_filter.mp hjJ).1 hji.symm)
      exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.choose_le_choose t hcomp) hN'.le
    obtain ⟨i₀, hi₀⟩ := card_pos.mp (by omega : 0 < J.card)
    have hθβ : θ ≤ β := le_of_lt ((mem_filter.mp hi₀).2.trans_le (hcap i₀ hi₀))
    have he : (∑ i ∈ I, max 0 (((D i).card.choose t : ℚ) / n.choose t - θ)) =
        ∑ i ∈ J, (((D i).card.choose t : ℚ) / n.choose t - θ) := by
      simp only [J, sum_filter]
      apply sum_congr rfl
      intro i _
      split_ifs with hi
      · exact max_eq_right (by linarith)
      · exact max_eq_left (by linarith)
    rw [he]
    have hsum : ∑ i ∈ J, (((D i).card.choose t : ℚ) / n.choose t - θ) ≤
        (J.card : ℚ) * (β - θ) := by
      calc
        ∑ i ∈ J, (((D i).card.choose t : ℚ) / n.choose t - θ) ≤
            ∑ _i ∈ J, (β - θ) := sum_le_sum fun i hi ↦ by linarith [hcap i hi]
        _ = (J.card : ℚ) * (β - θ) := by rw [sum_const, nsmul_eq_mul]
    have hJmin' : (J.card : ℚ) ≤ ((min q L : ℕ) : ℚ) := by exact_mod_cast hJmin
    have hmul : (J.card : ℚ) * (β - θ) ≤ ((min q L : ℕ) : ℚ) * (β - θ) :=
      mul_le_mul_of_nonneg_right hJmin' (by linarith)
    change ((min q L : ℕ) : ℚ) * β ≤ 1 + (((min q L : ℕ) : ℚ) - 1) * θ at hdirect
    linarith

/-- Unified excess condition discharging the binomial excess from a
`UniformFamilyBound n w ell L` via any of:
1. `min q L ≤ 1` (single-system / Plotkin regime),
2. the direct Hahn/Delsarte pairwise-complement bound (Route B), or
3. `DiscreteThreshold.Condition` with `min q L` in place of `q` (Route A). -/
def HahnExcessCondition (n t ell q w L : ℕ) (θ : ℚ) : Prop :=
  min q L ≤ 1 ∨
    ((min q L : ℕ) : ℚ) * (((n + ell - w).choose t : ℚ) / n.choose t) ≤
      1 + (((min q L : ℕ) : ℚ) - 1) * θ ∨
    DiscreteThreshold.Condition (min q L) ((ell.choose t : ℚ) / n.choose t) θ

omit [DecidableEq ι] in
/-- Master binomial excess theorem using a `UniformFamilyBound` at column cutoff `w`. -/
theorem normalized_excess_le_of_hahn (I : Finset ι)
    (D : ι → Finset (Fin n)) (t ell q w L : ℕ) (θ : ℚ)
    (hN : 0 < n.choose t) (hθ : θ ≤ 1) (hlow : ell < w)
    (hfloor : ((w - 1).choose t : ℚ) / n.choose t ≤ θ)
    (ho : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (D i ∩ D j).card ≤ ell)
    (hbound : CodingTheory.UniformFamilyBound n w ell L)
    (hc : HahnExcessCondition n t ell q w L θ)
    (hIq : I.card ≤ q) :
    ∑ i ∈ I, max 0 (((D i).card.choose t : ℚ) / n.choose t - θ) ≤ 1 - θ := by
  rcases hc with h1 | hdirect | hthresh
  · exact normalized_excess_le_of_uniformFamilyBound_threshold I D t ell q w L θ
      hN hθ hlow hfloor ho hbound (Or.inl h1) hIq
  · exact normalized_excess_le_of_uniformFamilyBound_direct I D t ell q w L θ
      hN hθ hlow hfloor ho hbound hdirect hIq
  · exact normalized_excess_le_of_uniformFamilyBound_threshold I D t ell q w L θ
      hN hθ hlow hfloor ho hbound (Or.inr hthresh) hIq

omit [DecidableEq ι] in
/-- Binomial excess bound directly from a checked integer Hahn/Delsarte
certificate `coeffs`. -/
theorem normalized_excess_le_of_hahnCertificate (I : Finset ι)
    (D : ι → Finset (Fin n)) (t ell q w : ℕ) (coeffs : List ℕ) (θ : ℚ)
    (hN : 0 < n.choose t) (hθ : θ ≤ 1) (hlow : ell < w)
    (hfloor : ((w - 1).choose t : ℚ) / n.choose t ≤ θ)
    (ho : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (D i ∩ D j).card ≤ ell)
    (hvalid : CodingTheory.HahnDelsarte.certificateValid n w ell coeffs = true)
    (hc : HahnExcessCondition n t ell q w
      (CodingTheory.HahnDelsarte.certifiedBound n w coeffs) θ)
    (hIq : I.card ≤ q) :
    ∑ i ∈ I, max 0 (((D i).card.choose t : ℚ) / n.choose t - θ) ≤ 1 - θ :=
  normalized_excess_le_of_hahn I D t ell q w
    (CodingTheory.HahnDelsarte.certifiedBound n w coeffs) θ
    hN hθ hlow hfloor ho
    (CodingTheory.HahnDelsarte.uniformFamilyBound_of_certificate hvalid) hc hIq

/-- An active-family size bound `L` at cutoff `w` and pairwise intersection `ell`
is certified either by a `UniformFamilyBound` (such as Hahn/Delsarte or Johnson)
or trivially whenever `q ≤ L`. -/
def ActiveFamilyBound (n w ell q L : ℕ) : Prop :=
  CodingTheory.UniformFamilyBound n w ell L ∨ q ≤ L

omit [DecidableEq ι] in
theorem normalized_excess_le_of_activeFamilyBound (I : Finset ι)
    (D : ι → Finset (Fin n)) (t ell q w L : ℕ) (θ : ℚ)
    (hN : 0 < n.choose t) (hθ : θ ≤ 1) (hlow : ell < w)
    (hfloor : ((w - 1).choose t : ℚ) / n.choose t ≤ θ)
    (ho : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (D i ∩ D j).card ≤ ell)
    (hbound : ActiveFamilyBound n w ell q L)
    (hc : HahnExcessCondition n t ell q w L θ)
    (hIq : I.card ≤ q) :
    ∑ i ∈ I, max 0 (((D i).card.choose t : ℚ) / n.choose t - θ) ≤ 1 - θ := by
  rcases hbound with hub | hqL
  · exact normalized_excess_le_of_hahn I D t ell q w L θ hN hθ hlow hfloor ho hub hc hIq
  · classical
    let J := I.filter fun i ↦ θ < ((D i).card.choose t : ℚ) / n.choose t
    have hN' : (0 : ℚ) < n.choose t := by exact_mod_cast hN
    have hJsize : ∀ i ∈ J, w ≤ (D i).card := fun i hi ↦
      size_ge_of_choose_div_gt hN hfloor (mem_filter.mp hi).2
    have hJq : J.card ≤ q := (card_le_card (filter_subset _ _)).trans hIq
    have hJmin : J.card ≤ min q L := Nat.le_min.mpr ⟨hJq, hJq.trans hqL⟩
    rcases hc with hle1 | hdirect | hcond
    · exact normalized_excess_le_of_card_le_one I D t θ hN hθ (hJmin.trans hle1)
    · by_cases hcard : J.card ≤ 1
      · exact normalized_excess_le_of_card_le_one I D t θ hN hθ hcard
      · have h2 : 2 ≤ J.card := by omega
        let β : ℚ := ((n + ell - w).choose t : ℚ) / n.choose t
        have hcap : ∀ i ∈ J, ((D i).card.choose t : ℚ) / n.choose t ≤ β := by
          intro i hi
          have hcardErase : 0 < (J.erase i).card := by
            rw [card_erase_of_mem hi]
            omega
          obtain ⟨j, hjErase⟩ := card_pos.mp hcardErase
          have hjJ : j ∈ J := mem_of_mem_erase hjErase
          have hji : j ≠ i := ne_of_mem_erase hjErase
          have hcomp := pairwise_complement_card_le D (hJsize j hjJ)
            (ho i (mem_filter.mp hi).1 j (mem_filter.mp hjJ).1 hji.symm)
          exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.choose_le_choose t hcomp) hN'.le
        obtain ⟨i₀, hi₀⟩ := card_pos.mp (by omega : 0 < J.card)
        have hθβ : θ ≤ β := le_of_lt ((mem_filter.mp hi₀).2.trans_le (hcap i₀ hi₀))
        have he : (∑ i ∈ I, max 0 (((D i).card.choose t : ℚ) / n.choose t - θ)) =
            ∑ i ∈ J, (((D i).card.choose t : ℚ) / n.choose t - θ) := by
          simp only [J, sum_filter]
          apply sum_congr rfl
          intro i _
          split_ifs with hi
          · exact max_eq_right (by linarith)
          · exact max_eq_left (by linarith)
        rw [he]
        have hsum : ∑ i ∈ J, (((D i).card.choose t : ℚ) / n.choose t - θ) ≤
            (J.card : ℚ) * (β - θ) := by
          calc
            ∑ i ∈ J, (((D i).card.choose t : ℚ) / n.choose t - θ) ≤
                ∑ _i ∈ J, (β - θ) := sum_le_sum fun i hi ↦ by linarith [hcap i hi]
            _ = (J.card : ℚ) * (β - θ) := by rw [sum_const, nsmul_eq_mul]
        have hJmin' : (J.card : ℚ) ≤ ((min q L : ℕ) : ℚ) := by exact_mod_cast hJmin
        have hmul : (J.card : ℚ) * (β - θ) ≤ ((min q L : ℕ) : ℚ) * (β - θ) :=
          mul_le_mul_of_nonneg_right hJmin' (by linarith)
        change ((min q L : ℕ) : ℚ) * β ≤ 1 + (((min q L : ℕ) : ℚ) - 1) * θ at hdirect
        linarith
    · have hNuniv : 0 < (univ : Finset (Fin n)).card.choose t := by simpa using hN
      have hexcessJ := normalized_excess_le (univ : Finset (Fin n)) J D t ell (min q L) θ
        hNuniv hθ (fun _ _ ↦ subset_univ _)
        (fun i hi j hj ↦ ho i (mem_filter.mp hi).1 j (mem_filter.mp hj).1)
        (by simpa using hcond) hJmin
      have he : (∑ i ∈ I, max 0 (((D i).card.choose t : ℚ) / n.choose t - θ)) =
          ∑ i ∈ J, max 0 (((D i).card.choose t : ℚ) / n.choose t - θ) := by
        simp only [J, sum_filter]
        apply sum_congr rfl
        intro i _
        split_ifs with hi
        · rfl
        · exact max_eq_left (by linarith)
      rw [he]
      simpa using hexcessJ

end HahnExcess

end RecursivePolygero.DirectBinomial
