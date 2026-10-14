import CodingTheory.ListDecoding.InterleavedDistance

/-!
# Uniform intersection families

`UniformFamilyBound n w lam L` asserts that every family of `w`-subsets of
`Fin n` whose distinct members meet in at most `lam` coordinates has at most
`L` members.  It is the purely combinatorial interface between list-size
arguments and their consumers: the Johnson count (degree one) and the
Hahn/Delsarte count (`CodingTheory.HahnDelsarte`) both produce such bounds.

`card_le_of_uniformFamilyBound` reduces a list of rowwise codeword matrices
within a fixed column radius to this interface.  Its proof is the
agreement-set selection previously embedded in the Johnson list bound.
-/

namespace CodingTheory

open scoped BigOperators

/-- Every `w`-uniform family on `Fin n` whose distinct members meet in at most
`lam` points has at most `L` members. -/
def UniformFamilyBound (n w lam L : ℕ) : Prop :=
  ∀ family : Finset (Finset (Fin n)),
    (∀ A ∈ family, A.card = w) →
    (∀ A ∈ family, ∀ B ∈ family, A ≠ B → (A ∩ B).card ≤ lam) →
    family.card ≤ L

theorem UniformFamilyBound.mono {n w lam L L' : ℕ}
    (h : UniformFamilyBound n w lam L) (hL : L ≤ L') :
    UniformFamilyBound n w lam L' :=
  fun family hcard hinter ↦ (h family hcard hinter).trans hL

theorem UniformFamilyBound.min {n w lam L L' : ℕ}
    (h : UniformFamilyBound n w lam L) (h' : UniformFamilyBound n w lam L') :
    UniformFamilyBound n w lam (min L L') :=
  fun family hcard hinter ↦ Nat.le_min.mpr
    ⟨h family hcard hinter, h' family hcard hinter⟩

/-- Two large agreement sets cannot coexist past the unique-list threshold. -/
theorem uniformFamilyBound_one_of_two_mul_gt {n w lam : ℕ}
    (h : n + lam < 2 * w) : UniformFamilyBound n w lam 1 := by
  classical
  intro family hcard hinter
  rw [Finset.card_le_one_iff]
  intro A B hA hB
  by_contra hne
  have hmeet := hinter A hA B hB hne
  have hunion : (A ∪ B).card ≤ n := by
    exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
  have heq := Finset.card_union_add_card_inter A B
  rw [hcard A hA, hcard B hB] at heq
  omega

/-- Bonferroni's three-set inequality gives an integer list bound of two.
It can improve the real-valued second-moment Johnson bound after flooring. -/
theorem uniformFamilyBound_two_of_three_mul_gt {n w lam : ℕ}
    (h : n + 3 * lam < 3 * w) : UniformFamilyBound n w lam 2 := by
  classical
  intro family hcard hinter
  by_contra hlarge
  obtain ⟨A, B, C, hA, hB, hC, hAB, hAC, hBC⟩ :=
    Finset.two_lt_card_iff.mp (by omega : 2 < family.card)
  have hABmeet := hinter A hA B hB hAB
  have hACmeet := hinter A hA C hC hAC
  have hBCmeet := hinter B hB C hC hBC
  have hfirst := Finset.card_union_add_card_inter A B
  have hsecond := Finset.card_union_add_card_inter (A ∪ B) C
  have hsplit : ((A ∪ B) ∩ C).card ≤ (A ∩ C).card + (B ∩ C).card := by
    rw [Finset.union_inter_distrib_right]
    exact Finset.card_union_le _ _
  have hunion : ((A ∪ B) ∪ C).card ≤ n := by
    exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
  rw [hcard A hA, hcard B hB] at hfirst
  rw [hcard C hC] at hsecond
  omega

/-- A bound for `w`-uniform families also bounds families of larger sets:
shrinking every member to `w` points keeps distinct members distinct, because
two members sharing a `w`-subset would meet in `w > lam` points. -/
theorem UniformFamilyBound.of_le_size {n w w' lam L : ℕ}
    (h : UniformFamilyBound n w lam L) (hww' : w ≤ w') (hlam : lam < w) :
    UniformFamilyBound n w' lam L := by
  classical
  intro family hcard hinter
  have hsub : ∀ A ∈ family, ∃ B ⊆ A, B.card = w := fun A hA ↦
    Finset.exists_subset_card_eq (by rw [hcard A hA]; exact hww')
  choose! shrink hshrinkSub hshrinkCard using hsub
  have hinj : Set.InjOn shrink family := by
    intro A hA B hB hAB
    by_contra hne
    have hle : (shrink A).card ≤ (A ∩ B).card := by
      apply Finset.card_le_card
      intro x hx
      have hxB : x ∈ shrink B := by
        have hAB' : shrink A = shrink B := hAB
        rw [← hAB']
        exact hx
      exact Finset.mem_inter.mpr ⟨hshrinkSub A hA hx, hshrinkSub B hB hxB⟩
    have hmeet := hinter A hA B hB hne
    rw [hshrinkCard A hA] at hle
    omega
  have himage := h (family.image shrink)
    (fun B hB ↦ by
      obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hB
      exact hshrinkCard A hA)
    (fun B hB B' hB' hne ↦ by
      obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hB
      obtain ⟨A', hA', rfl⟩ := Finset.mem_image.mp hB'
      have hAA' : A ≠ A' := fun heq ↦ hne (heq ▸ rfl)
      calc
        (shrink A ∩ shrink A').card ≤ (A ∩ A').card :=
          Finset.card_le_card (Finset.inter_subset_inter (hshrinkSub A hA) (hshrinkSub A' hA'))
        _ ≤ lam := hinter A hA A' hA' hAA')
  rwa [Finset.card_image_of_injOn hinj] at himage

variable {F Row : Type*} [Field F] [DecidableEq F] [Fintype Row]
variable {n E d L : ℕ}

/-- **Codeword-list reduction.**  Distinct rowwise codeword matrices within
column radius `E` of one received matrix select distinct `(n - E)`-subsets of
agreement columns, and two such subsets meet in at most `n - d` columns.  Any
uniform-family bound therefore bounds the list. -/
theorem card_le_of_uniformFamilyBound
    (C : LinearCode F n) (received : Row → Word F n)
    (candidates : Finset (Row → Word F n))
    (hmin : HasMinimumDistanceAtLeast C d)
    (hcode : ∀ candidate ∈ candidates, ∀ row, candidate row ∈ C)
    (hclose : ∀ candidate ∈ candidates,
      (matrixErrorCoordinates received candidate).card ≤ E)
    (hEd : E < d) (hbound : UniformFamilyBound n (n - E) (n - d) L) :
    candidates.card ≤ L := by
  classical
  have hd : d ≤ n := hmin.distance_le_length
  let agreement : candidates → Finset (Fin n) := fun candidate ↦
    Finset.univ \ matrixErrorCoordinates received candidate.1
  have hagreementCard (candidate : candidates) :
      n - E ≤ (agreement candidate).card := by
    have herror := hclose candidate.1 candidate.2
    have hsub := Nat.sub_le_sub_left herror n
    have hagreementEq : (agreement candidate).card =
        n - (matrixErrorCoordinates received candidate.1).card := by
      simp [agreement, Finset.card_sdiff]
    rw [hagreementEq]
    exact hsub
  choose selected hselected hselectedCard using fun candidate : candidates ↦
    Finset.exists_subset_card_eq (hagreementCard candidate)
  have hpair (first second : candidates) (hne : first ≠ second) :
      (selected first ∩ selected second).card ≤ n - d := by
    let difference := matrixErrorCoordinates first.1 second.1
    have hsubset : selected first ∩ selected second ⊆
        Finset.univ \ difference := by
      intro j hj
      have hjFirst := hselected first (Finset.mem_inter.mp hj).1
      have hjSecond := hselected second (Finset.mem_inter.mp hj).2
      have hjFirstAgreement := Finset.mem_sdiff.mp hjFirst
      have hjSecondAgreement := Finset.mem_sdiff.mp hjSecond
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hjDifference
      obtain ⟨row, hrow⟩ := (Finset.mem_filter.mp hjDifference).2
      have hfirst (row : Row) : received row j = first.1 row j := by
        apply not_ne_iff.mp
        intro hneRow
        exact hjFirstAgreement.2
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, row, hneRow⟩)
      have hsecond (row : Row) : received row j = second.1 row j := by
        apply not_ne_iff.mp
        intro hneRow
        exact hjSecondAgreement.2
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, row, hneRow⟩)
      exact hrow ((hfirst row).symm.trans (hsecond row))
    have hdifference : d ≤ difference.card := by
      apply InterleavedJohnson.matrixErrorCoordinates_card_ge_distance C hmin
        (hcode first.1 first.2) (hcode second.1 second.2)
      intro heq
      exact hne (Subtype.ext heq)
    calc
      (selected first ∩ selected second).card ≤
          (Finset.univ \ difference).card := Finset.card_le_card hsubset
      _ = n - difference.card := by
        simp [Finset.card_sdiff]
      _ ≤ n - d := Nat.sub_le_sub_left hdifference n
  have hselectedInjective : Function.Injective selected := by
    intro first second heq
    by_contra hne
    have hbound := hpair first second hne
    rw [heq, Finset.inter_self, hselectedCard second] at hbound
    omega
  let family : Finset (Finset (Fin n)) := Finset.univ.image selected
  have hfamilyCard : family.card = candidates.card := by
    change (Finset.univ.image selected).card = candidates.card
    rw [Finset.card_image_of_injective _ hselectedInjective]
    simp
  have hfamilyMemberCard (A : Finset (Fin n)) (hA : A ∈ family) :
      A.card = n - E := by
    obtain ⟨candidate, _hcandidate, rfl⟩ := Finset.mem_image.mp hA
    exact hselectedCard candidate
  have hfamilyPair (A : Finset (Fin n)) (hA : A ∈ family)
      (A' : Finset (Fin n)) (hA' : A' ∈ family) (hne : A ≠ A') :
      (A ∩ A').card ≤ n - d := by
    obtain ⟨first, _hfirst, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨second, _hsecond, rfl⟩ := Finset.mem_image.mp hA'
    exact hpair first second (fun heq ↦ hne (congrArg selected heq))
  rw [← hfamilyCard]
  exact hbound family hfamilyMemberCard hfamilyPair

end CodingTheory
