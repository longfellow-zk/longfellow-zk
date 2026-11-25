import Ligero.V1.Soundness.V1Profile
import LigeroFamily.Soundness.SchemeSelectedMCA

/-!
# High response mass for scalar Ligero V1

The complete response tuple matters for Fiat–Shamir. Its agreement set determines
its opening probability. Reed–Solomon distance bounds the pairwise overlap of
these sets, so a count of the responses by itself does not need to multiply the
largest opening probability.
-/

set_option autoImplicit false

namespace LfzkV1.LigeroHighMass125

open Finset LigeroFamily LigeroFamily.AgreementProfile CodingTheory
open scoped Classical

variable {n r : ℕ}

/-- Monotonicity of the normalized opening count. -/
theorem opening_mono : Monotone (fun a => hypergeometricRatio a n r) := by
  intro a b hab
  unfold hypergeometricRatio
  exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.choose_le_choose r hab) (by positivity)

theorem opening_nonneg (a : ℕ) : 0 ≤ hypergeometricRatio a n r := by
  unfold hypergeometricRatio
  positivity

theorem opening_le_one {a : ℕ} (ha : a ≤ n) :
    hypergeometricRatio a n r ≤ 1 := by
  unfold hypergeometricRatio
  by_cases h : r ≤ n
  · exact (div_le_one (by exact_mod_cast Nat.choose_pos h)).mpr
      (by exact_mod_cast Nat.choose_le_choose r ha)
  · simp [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge h)]

/-- A uniformly bounded family of large sets indexes at most (L) responses:
two large sets cannot coincide when their overlap is smaller than the cutoff. -/
theorem family_card_le {R : Type*} (S : Finset R) (cols : R → Finset (Fin n))
    {a lam L : ℕ} (hlt : lam < a) (hlarge : ∀ u ∈ S, a ≤ (cols u).card)
    (hoverlap : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → (cols u ∩ cols v).card ≤ lam)
    (hbound : UniformFamilyBound n a lam L) :
    S.card ≤ L := by
  classical
  have hsub (u : R) (hu : u ∈ S) : ∃ A ⊆ cols u, A.card = a :=
    exists_subset_card_eq (hlarge u hu)
  choose! shrink hshrinkSub hshrinkCard using hsub
  have hmeet (u : R) (hu : u ∈ S) (v : R) (hv : v ∈ S) (hne : u ≠ v) :
      (shrink u ∩ shrink v).card ≤ lam :=
    (card_le_card (inter_subset_inter (hshrinkSub u hu) (hshrinkSub v hv))).trans
      (hoverlap u hu v hv hne)
  have hshrinking : Set.InjOn shrink (↑S : Set R) := by
    intro u hu v hv heq
    by_contra hne
    have h := hmeet u hu v hv hne
    rw [heq, inter_self, hshrinkCard v hv] at h
    exact (Nat.not_le_of_lt hlt) h
  rw [← card_image_of_injOn hshrinking]
  apply hbound (S.image shrink)
  · intro A hA
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hA
    exact hshrinkCard u hu
  · intro A hA B hB hne
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hA
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hB
    exact hmeet u hu v hv (fun h => hne (congrArg shrink h))

theorem mass_le_peak_add_of_pair_card {R : Type*} (S : Finset R) (size : R → ℕ)
    {pairBound L peak : ℕ} (hcard : S.card ≤ L)
    (hpeak : ∀ u ∈ S, size u ≤ peak)
    (hpair : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → size u + size v ≤ pairBound) :
    ∑ u ∈ S, hypergeometricRatio (size u) n r ≤
      hypergeometricRatio peak n r +
        (L : ℚ) * hypergeometricRatio (pairBound / 2) n r := by
  classical
  let m := pairBound / 2
  by_cases hbig : ∃ u ∈ S, m < size u
  · obtain ⟨u, hu, hlarge⟩ := hbig
    rw [← sum_erase_add _ _ hu]
    have hrest : ∑ v ∈ S.erase u, hypergeometricRatio (size v) n r ≤
        (L : ℚ) * hypergeometricRatio m n r := by
      calc
        _ ≤ ∑ _v ∈ S.erase u, hypergeometricRatio m n r := by
          apply sum_le_sum
          intro v hv
          have h := hpair u hu v (mem_erase.mp hv).2 (Ne.symm (mem_erase.mp hv).1)
          exact opening_mono (by dsimp [m] at hlarge ⊢; omega)
        _ = ((S.erase u).card : ℚ) * hypergeometricRatio m n r := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (by
          exact_mod_cast (card_le_card (erase_subset u S)).trans hcard) (opening_nonneg _)
    simpa [m, add_comm] using add_le_add hrest (opening_mono (hpeak u hu))
  · push Not at hbig
    calc
      _ ≤ ∑ _u ∈ S, hypergeometricRatio m n r :=
        sum_le_sum (fun u hu => opening_mono (hbig u hu))
      _ = (S.card : ℚ) * hypergeometricRatio m n r := by simp
      _ ≤ _ := by
        have hmul := mul_le_mul_of_nonneg_right
          (show (S.card : ℚ) ≤ L by exact_mod_cast hcard) (opening_nonneg (n := n) (r := r) m)
        exact hmul.trans (le_add_of_nonneg_left (opening_nonneg _))

/-- At most one set can exceed the midpoint between the ground-set size and
the pairwise overlap cap. Account for that set at the largest opening probability
and for the others at the midpoint probability. -/
theorem mass_le_peak_add {R : Type*} (S : Finset R) (cols : R → Finset (Fin n))
    {lam L peak g : ℕ} (hcard : S.card ≤ L)
    (hpeak : ∀ u ∈ S, (cols u).card + g ≤ peak)
    (hoverlap : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → (cols u ∩ cols v).card ≤ lam) :
    ∑ u ∈ S, hypergeometricRatio ((cols u).card + g) n r ≤
      hypergeometricRatio peak n r +
      (L : ℚ) * hypergeometricRatio ((n + lam) / 2 + g) n r := by
  rw [show (n + lam) / 2 + g = (n + lam + 2 * g) / 2 by omega]
  apply mass_le_peak_add_of_pair_card S (fun u => (cols u).card + g) hcard hpeak
  intro u hu v hv hne
  have h := card_union_add_card_inter (cols u) (cols v)
  have huniv := card_le_univ (s := cols u ∪ cols v)
  rw [Fintype.card_fin] at huniv
  have hi := hoverlap u hu v hv hne
  omega

/-- A list of at most two candidates has at most one large agreement set.
The second peak is bounded by the midpoint even after its residual is added. -/
theorem two_candidate_peaks_le {R : Type*} (S : Finset R) (cols : R → Finset (Fin n))
    {lam g : ℕ} (hcard : S.card ≤ 2)
    (hoverlap : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → (cols u ∩ cols v).card ≤ lam) :
    ∑ u ∈ S, hypergeometricRatio (min n ((cols u).card + g)) n r ≤
      1 + hypergeometricRatio ((n + lam) / 2 + g) n r := by
  classical
  by_cases htwo : S.card = 2
  · obtain ⟨u, v, hne, hS⟩ := card_eq_two.mp htwo
    have hmeet := hoverlap u (by simp [hS]) v (by simp [hS]) hne
    have hunion : (cols u ∪ cols v).card ≤ n := by
      simpa using card_le_univ (s := cols u ∪ cols v)
    have hsum := card_union_add_card_inter (cols u) (cols v)
    have hmin : (cols u).card ≤ (n + lam) / 2 ∨ (cols v).card ≤ (n + lam) / 2 := by
      omega
    rw [hS, sum_pair hne]
    rcases hmin with hu | hv
    · rw [add_comm]
      exact add_le_add (opening_le_one (min_le_left _ _))
        (opening_mono ((min_le_right _ _).trans (Nat.add_le_add_right hu _)))
    · exact add_le_add (opening_le_one (min_le_left _ _))
        (opening_mono ((min_le_right _ _).trans (Nat.add_le_add_right hv _)))
  · calc
      _ ≤ ∑ _u ∈ S, (1 : ℚ) := sum_le_sum fun _ _ => opening_le_one (min_le_left _ _)
      _ = (S.card : ℚ) := by simp
      _ ≤ 1 := by exact_mod_cast (by omega : S.card ≤ 1)
      _ ≤ _ := le_add_of_nonneg_right (opening_nonneg _)

theorem sum_union_le {R : Type*} [DecidableEq R] {A B : Finset R} {f : R → ℚ}
    (hf : ∀ u, 0 ≤ f u) : ∑ u ∈ A ∪ B, f u ≤ (∑ u ∈ A, f u) + ∑ u ∈ B, f u := by
  rw [← sdiff_union_self_eq_union, sum_union disjoint_sdiff.symm]
  exact add_le_add
    (sum_le_sum_of_subset_of_nonneg sdiff_subset (fun u _ _ => hf u)) le_rfl

theorem sum_biUnion_le {X R : Type*} [DecidableEq R] (S : Finset X)
    (A : X → Finset R) {f : R → ℚ} (hf : ∀ u, 0 ≤ f u) :
    ∑ u ∈ S.biUnion A, f u ≤ ∑ x ∈ S, ∑ u ∈ A x, f u := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert x S hx ih =>
    rw [biUnion_insert, sum_insert hx]
    exact (sum_union_le hf).trans (add_le_add le_rfl ih)

/-- Extend the tail at the high-agreement cutoff to all smaller agreement
levels, where the selected high response is present on the same challenges. -/
def truncateBelow (profile : AgreementProfile n) (a : ℕ) : AgreementProfile n :=
  ⟨fun b => profile.labelsAtLeast (max a b)⟩

section SelectedMass

variable {X R : Type*} [Fintype X]

/-- Fix the maximum agreement of the selected responses for each challenge. -/
noncomputable def peakAgreement (responses : X → Finset R)
    (cols : X → R → Finset (Fin n)) (x : X) : ℕ :=
  (responses x).sup (fun u => (cols x u).card)

/-- Challenges that have a selected high-agreement response. -/
noncomputable def active (responses : X → Finset R) : Finset X :=
  univ.filter (fun x => (responses x).Nonempty)

omit [Fintype X] in
theorem peakAgreement_le (responses : X → Finset R)
    (cols : X → R → Finset (Fin n)) (x : X) :
    peakAgreement responses cols x ≤ n := by
  apply Finset.sup_le
  intro u _
  simpa using card_le_univ (s := cols x u)

/-- The selected no-lift mass: integrate just the largest accepting set against
the selected-MCA tail. The smaller responses share the midpoint cap and incur
that term only on challenges on which a selected response exists. -/
theorem selected_average_mass_le [Nonempty X] (responses : X → Finset R)
    (cols : X → R → Finset (Fin n))
    {lam L q a : ℕ} (hq : 0 < q)
    (profile : AgreementProfile n)
    (hcard : ∀ x, (responses x).card ≤ L)
    (hoverlap : ∀ x, ∀ u ∈ responses x, ∀ v ∈ responses x, u ≠ v →
      (cols x u ∩ cols x v).card ≤ lam)
    (hlarge : ∀ x, ∀ u ∈ responses x, a ≤ (cols x u).card)
    (hdensity : ∀ b, a ≤ b → b ≤ n →
      q * (restrictedTailSet (active responses) (peakAgreement responses cols) b).card ≤
        profile.labelsAtLeast b * Fintype.card X) :
    (∑ x : X, ∑ u ∈ responses x, hypergeometricRatio (cols x u).card n r) /
        Fintype.card X ≤
      (truncateBelow profile a).contribution q n n 0 r +
      (L : ℚ) * hypergeometricRatio ((n + lam) / 2) n r * profile.tail q a := by
  classical
  let selected := active responses
  let peak := peakAgreement responses cols
  let truncated := truncateBelow profile a
  let rest := (L : ℚ) * hypergeometricRatio ((n + lam) / 2) n r
  have hrest : 0 ≤ rest := mul_nonneg (by positivity) (opening_nonneg _)
  have hN : 0 < (Fintype.card X : ℚ) := by exact_mod_cast Fintype.card_pos
  have hactive (x : X) (hx : x ∈ selected) : a ≤ peak x := by
    obtain ⟨u, hu⟩ := (mem_filter.mp hx).2
    exact (hlarge x u hu).trans (Finset.le_sup (f := fun v => (cols x v).card) hu)
  have htail (b : ℕ) : restrictedTailSet selected peak b =
      restrictedTailSet selected peak (max a b) := by
    ext x
    simp only [restrictedTailSet, mem_filter]
    exact ⟨fun ⟨hx, hb⟩ => ⟨hx, max_le (hactive x hx) hb⟩,
      fun ⟨hx, hb⟩ => ⟨hx, (le_max_right a b).trans hb⟩⟩
  have hcut : restrictedTailSet selected peak a = selected := by
    ext x
    simp only [restrictedTailSet, mem_filter, and_iff_left_iff_imp]
    exact hactive x
  by_cases hzero : selected = ∅
  · have hz (x : X) : responses x = ∅ := by
      by_contra hne
      have hx : x ∈ selected := mem_filter.mpr ⟨mem_univ _, nonempty_iff_ne_empty.mpr hne⟩
      simp [hzero] at hx
    simp only [hz, sum_empty, sum_const_zero, zero_div]
    exact add_nonneg (contribution_nonnegative q n n 0 r truncated)
      (mul_nonneg hrest (tail_nonnegative q profile a))
  have ha : a ≤ n := by
    obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr hzero
    exact (hactive x hx).trans (peakAgreement_le responses cols x)
  have htruncated (b : ℕ) (hb : b ≤ n) :
      q * (restrictedTailSet selected peak b).card ≤
        truncated.labelsAtLeast b * Fintype.card X := by
    rw [htail b]
    exact hdensity (max a b) (le_max_left a b) (max_le ha hb)
  have hpeak : (∑ x ∈ selected, hypergeometricRatio (peak x) n r) /
        Fintype.card X ≤ truncated.contribution q n n 0 r := by
    have h := restricted_average_coverRatio_le_contribution q n n 0 r truncated
      selected peak hq (fun x _ => peakAgreement_le responses cols x) htruncated
    have heq (x : X) : coverRatio n n 0 r (peak x) = hypergeometricRatio (peak x) n r := by
      have hle : peak x ≤ n := peakAgreement_le responses cols x
      simp [coverRatio, min_eq_right hle]
    simpa only [heq] using h
  have hselected : (selected.card : ℚ) / Fintype.card X ≤ profile.tail q a := by
    apply le_min
    · exact (div_le_one hN).mpr (by exact_mod_cast card_le_univ (s := selected))
    · rw [div_le_div_iff₀ hN (by exact_mod_cast hq)]
      have h := hdensity a le_rfl ha
      change q * (restrictedTailSet selected peak a).card ≤ _ at h
      rw [hcut] at h
      exact_mod_cast (by simpa [Nat.mul_comm] using h)
  have hsum : (∑ x : X, ∑ u ∈ responses x, hypergeometricRatio (cols x u).card n r) =
      ∑ x ∈ selected, ∑ u ∈ responses x, hypergeometricRatio (cols x u).card n r := by
    rw [show selected = univ.filter (fun x => (responses x).Nonempty) from rfl, sum_filter]
    apply sum_congr rfl
    intro x _
    split_ifs with hx
    · rfl
    · simp [not_nonempty_iff_eq_empty.mp hx]
  rw [hsum]
  calc
    _ ≤ (∑ x ∈ selected, (hypergeometricRatio (peak x) n r + rest)) / Fintype.card X := by
      apply div_le_div_of_nonneg_right _ hN.le
      apply sum_le_sum
      intro x _
      have h := mass_le_peak_add (r := r) (responses x) (cols x)
        (g := 0) (peak := peak x) (hcard x)
        (fun u hu => by
          rw [Nat.add_zero]
          exact Finset.le_sup (f := fun v => (cols x v).card) hu)
        (hoverlap x)
      simpa using h
    _ = (∑ x ∈ selected, hypergeometricRatio (peak x) n r) / Fintype.card X +
        rest * ((selected.card : ℚ) / Fintype.card X) := by
      rw [sum_add_distrib, add_div]
      simp only [sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := add_le_add hpeak (mul_le_mul_of_nonneg_left hselected hrest)

/-- Charge each response label only on the challenges allowing that very
label. Every label can have a different opening weight. -/
theorem labeled_average_mass_le [Nonempty X] (responses : X → Finset R)
    (labels : Finset R) (weight : R → ℚ) {q : ℕ} (hq : 0 < q)
    (hsubset : ∀ x, responses x ⊆ labels) (hweight : ∀ u ∈ labels, 0 ≤ weight u)
    (hdensity : ∀ u ∈ labels,
      q * (univ.filter fun x => u ∈ responses x).card ≤ Fintype.card X) :
    (∑ x : X, ∑ u ∈ responses x, weight u) / Fintype.card X ≤
      (∑ u ∈ labels, weight u) / q := by
  classical
  have hN : 0 < (Fintype.card X : ℚ) := by exact_mod_cast Fintype.card_pos
  have hsum (x : X) : ∑ u ∈ responses x, weight u =
      ∑ u ∈ labels, if u ∈ responses x then weight u else 0 := by
    rw [← sum_filter]
    congr 1
    ext u
    simp only [mem_filter]
    exact ⟨fun hu => ⟨hsubset x hu, hu⟩, And.right⟩
  simp_rw [hsum]
  rw [sum_comm]
  simp_rw [← sum_filter]
  simp only [sum_const, nsmul_eq_mul]
  rw [div_eq_mul_inv, sum_mul, div_eq_mul_inv, sum_mul]
  apply sum_le_sum
  intro u hu
  have hden : (↑(univ.filter fun x => u ∈ responses x).card : ℚ) / Fintype.card X ≤
      1 / (q : ℚ) := by
    rw [div_le_div_iff₀ hN (by exact_mod_cast hq), one_mul]
    exact_mod_cast (by simpa [Nat.mul_comm] using hdensity u hu)
  calc
    _ = weight u * ((↑(univ.filter fun x => u ∈ responses x).card : ℚ) /
        Fintype.card X) := by ring
    _ ≤ weight u * (1 / (q : ℚ)) := mul_le_mul_of_nonneg_left hden (hweight u hu)
    _ = _ := by ring

end SelectedMass

end LfzkV1.LigeroHighMass125
