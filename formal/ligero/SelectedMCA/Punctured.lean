import SelectedMCA.DoubleAveraging
import AffineAgreement.Secant
import AffineAgreement.AffineSupport
import AffineAgreement.Globalization

/-!
# Small-radius punctured globalization

The audited general selected-response proof globalizes only after puncturing
to the prover's actual agreement set. At this stage the radius is `g`, and
the elementary three-error condition uses the effective punctured distance
`d-e`. This module proves that step
without invoking the older large-radius correlated-agreement theorem.
-/

namespace SelectedMCA

open CodingTheory AffineAgreement

variable {F Row : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Row] [DecidableEq Row] [Nonempty Row]
variable {n g d : ℕ}

/-- If every row combination is radius-`g` close to a linear code, then all
rows have codeword representatives with one common set of at most `g` bad
columns, provided `3g < d` and the field has more than `g+1` elements. -/
theorem interleavedWithinRadius_of_all_combinations_close_three
    (C : LinearCode F n) (rows : Row → Word F n)
    (hmin : HasMinimumDistanceAtLeast C d)
    (hthree : 3 * g < d) (hfield : g + 1 < Fintype.card F)
    (hall : ∀ weights : Row → F,
      WithinRadius C g (wordCombination rows weights)) :
    InterleavedWithinRadius C g rows := by
  have hallOn (weights : Row → F) : ∃ decoded ∈ C,
      (supportOn Finset.univ
        (wordCombination rows weights - decoded)).card ≤ g := by
    simpa [WithinRadius, weight] using hall weights
  obtain ⟨decodedRows, hdecoded, hbad⟩ :=
    AffineAgreement.interleavedWithinRadiusOn_of_all_combinations_close_three
      (e := 0) C rows Finset.univ hmin (by simp) (by simpa using hthree)
      hfield hallOn
  exact ⟨decodedRows, hdecoded, by
    simpa [matrixErrorCoordinates] using hbad⟩

omit [Fintype F] in
/-- More than `g+1` locally radius-`g` points on an affine received line
force its direction to be locally radius `g` from a codeword direction. -/
theorem directionWithinRadiusOn_of_many_affine_close
    {e : ℕ} (C : LinearCode F n) (u v : Word F n)
    (allowed : Finset (Fin n)) (S : Finset F)
    (hmin : HasMinimumDistanceAtLeast C d)
    (hdeleted : (Finset.univ \ allowed).card ≤ e)
    (hthree : 3 * g < d - e) (hmany : g + 1 < S.card)
    (hclose : ∀ scalar ∈ S, ∃ decoded ∈ C,
      (supportOn allowed (affineWord u v scalar - decoded)).card ≤ g) :
    ∃ direction ∈ C,
      (supportOn allowed (v - direction)).card ≤ g := by
  classical
  let decoded (scalar : F) : Word F n :=
    if hscalar : scalar ∈ S then Classical.choose (hclose scalar hscalar)
    else 0
  have hdecodedMem (scalar : F) (hscalar : scalar ∈ S) :
      decoded scalar ∈ C := by
    simpa only [decoded, dif_pos hscalar] using
      (Classical.choose_spec (hclose scalar hscalar)).1
  have hdecodedClose (scalar : F) (hscalar : scalar ∈ S) :
      (supportOn allowed
        (affineWord u v scalar - decoded scalar)).card ≤ g := by
    simpa only [decoded, dif_pos hscalar] using
      (Classical.choose_spec (hclose scalar hscalar)).2
  have hStwo : 1 < Fintype.card S := by simpa using (show 1 < S.card by omega)
  obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp hStwo
  have ha : a.1 ∈ S := a.2
  have hb : b.1 ∈ S := b.2
  have habF : a.1 ≠ b.1 := fun h ↦ hab (Subtype.ext h)
  let direction : Word F n := fun i ↦
    (b.1 - a.1)⁻¹ * (decoded b.1 i - decoded a.1 i)
  let base : Word F n := decoded a.1 - fun i ↦ a.1 * direction i
  have hdirectionMem : direction ∈ C := by
    dsimp [direction]
    exact C.smul_mem _ (C.sub_mem (hdecodedMem b.1 hb) (hdecodedMem a.1 ha))
  have hbaseMem : base ∈ C := by
    dsimp [base]
    exact C.sub_mem (hdecodedMem a.1 ha) (C.smul_mem _ hdirectionMem)
  have hlineA : affineWord base direction a.1 = decoded a.1 := by
    funext i
    dsimp [base, direction]
    field_simp [sub_ne_zero.mpr habF.symm]
    ring
  have hlineB : affineWord base direction b.1 = decoded b.1 := by
    funext i
    dsimp [base, direction]
    field_simp [sub_ne_zero.mpr habF.symm]
    ring
  have hline (scalar : F) (hscalar : scalar ∈ S) :
      affineWord base direction scalar = decoded scalar := by
    by_cases hsa : scalar = a.1
    · simpa [hsa] using hlineA
    by_cases hsb : scalar = b.1
    · simpa [hsb] using hlineB
    let defect := decoded scalar - affineWord base direction scalar
    have hdefectMem : defect ∈ C :=
      C.sub_mem (hdecodedMem scalar hscalar)
        (C.add_mem hbaseMem (C.smul_mem scalar hdirectionMem))
    let error (t : F) := affineWord u v t - decoded t
    have hlocalSubset : supportOn allowed defect ⊆
        supportOn allowed (error a.1) ∪
          supportOn allowed (error b.1) ∪ supportOn allowed (error scalar) := by
      intro j hj
      by_contra hnot
      have hnotA : j ∉ supportOn allowed (error a.1) := fun hjA ↦
        hnot (Finset.mem_union_left _ (Finset.mem_union_left _ hjA))
      have hnotB : j ∉ supportOn allowed (error b.1) := fun hjB ↦
        hnot (Finset.mem_union_left _ (Finset.mem_union_right _ hjB))
      have hnotScalar : j ∉ supportOn allowed (error scalar) := fun hjScalar ↦
        hnot (Finset.mem_union_right _ hjScalar)
      have hzero (t : F) (ht : j ∉ supportOn allowed (error t)) :
          error t j = 0 := by
        apply not_ne_iff.mp
        intro hne
        exact ht ((mem_supportOn allowed (error t) j).mpr
          ⟨(mem_supportOn allowed defect j).mp hj |>.1, hne⟩)
      have haAgree := sub_eq_zero.mp (hzero a.1 hnotA)
      have hbAgree := sub_eq_zero.mp (hzero b.1 hnotB)
      have hsAgree := sub_eq_zero.mp (hzero scalar hnotScalar)
      have hreceived := congrFun
        (AffineAgreement.received_secant u v a.1 b.1 scalar habF) j
      have hcandidate : affineWord base direction scalar j =
          affineWord u v scalar j := by
        calc
          affineWord base direction scalar j =
              affineWord
                (decoded a.1 - fun i ↦ a.1 *
                  ((b.1 - a.1)⁻¹ * (decoded b.1 i - decoded a.1 i)))
                (fun i ↦ (b.1 - a.1)⁻¹ *
                  (decoded b.1 i - decoded a.1 i)) scalar j := rfl
          _ = affineWord
                (affineWord u v a.1 - fun i ↦ a.1 *
                  ((b.1 - a.1)⁻¹ *
                    (affineWord u v b.1 i - affineWord u v a.1 i)))
                (fun i ↦ (b.1 - a.1)⁻¹ *
                  (affineWord u v b.1 i - affineWord u v a.1 i)) scalar j := by
              simp only [affineWord, Pi.sub_apply]
              rw [← haAgree, ← hbAgree]
              simp [affineWord]
          _ = affineWord u v scalar j := hreceived.symm
      have hz : defect j = 0 := by
        dsimp [defect]
        exact sub_eq_zero.mpr (hsAgree.symm.trans hcandidate.symm)
      exact (mem_supportOn allowed defect j).mp hj |>.2 hz
    have hlocal : (supportOn allowed defect).card ≤ 3 * g := by
      calc
        (supportOn allowed defect).card ≤
            ((supportOn allowed (error a.1) ∪
              supportOn allowed (error b.1)) ∪
                supportOn allowed (error scalar)).card :=
          Finset.card_le_card hlocalSubset
        _ ≤ (supportOn allowed (error a.1)).card +
              (supportOn allowed (error b.1)).card +
                (supportOn allowed (error scalar)).card :=
          (Finset.card_union_le _ _).trans
            (Nat.add_le_add_right (Finset.card_union_le _ _) _)
        _ ≤ 3 * g := by
          have h₁ := hdecodedClose a.1 ha
          have h₂ := hdecodedClose b.1 hb
          have h₃ := hdecodedClose scalar hscalar
          change (supportOn allowed (error a.1)).card ≤ g at h₁
          change (supportOn allowed (error b.1)).card ≤ g at h₂
          change (supportOn allowed (error scalar)).card ≤ g at h₃
          omega
    have hweight : weight defect < d := by
      have htotal := weight_le_supportOn_add_complement allowed defect
      have : weight defect ≤ 3 * g + e :=
        htotal.trans (Nat.add_le_add hlocal hdeleted)
      have hed : e ≤ d := by omega
      have hsplit : d - e + e = d := Nat.sub_add_cancel hed
      omega
    have hzero : defect = 0 :=
      AffineAgreement.eq_zero_of_weight_lt_distance hmin hdefectMem hweight
    exact (sub_eq_zero.mp hzero).symm
  let mask (word : Word F n) : Word F n := fun j ↦
    if j ∈ allowed then word j else 0
  let residualBase := mask (u - base)
  let residualDirection := mask (v - direction)
  have hmaskedWeight (scalar : F) (hscalar : scalar ∈ S) :
      weight (affineWord residualBase residualDirection scalar) ≤ g := by
    have heq : affineWord residualBase residualDirection scalar =
        mask (affineWord u v scalar - decoded scalar) := by
      rw [← hline scalar hscalar]
      funext j
      by_cases hj : j ∈ allowed
      · simp [residualBase, residualDirection, mask, affineWord, hj]
        ring
      · simp [residualBase, residualDirection, mask, affineWord, hj]
    rw [heq]
    have hsupport : supportOn Finset.univ
        (mask (affineWord u v scalar - decoded scalar)) =
        supportOn allowed (affineWord u v scalar - decoded scalar) := by
      ext j
      by_cases hj : j ∈ allowed <;> simp [supportOn, mask, hj]
    simpa [weight, hsupport] using hdecodedClose scalar hscalar
  have hactive : (jointSupport residualBase residualDirection).card ≤ g := by
    by_contra hnot
    have hbound := AffineAgreement.affineLine_card_le_of_support_lower residualBase
      residualDirection S (by omega) (by omega : g < g + 1)
        (show g + 1 ≤ (jointSupport residualBase residualDirection).card by omega)
        hmaskedWeight
    simp at hbound
    omega
  refine ⟨direction, hdirectionMem, ?_⟩
  have hsubset : supportOn allowed (v - direction) ⊆
      jointSupport residualBase residualDirection := by
    intro j hj
    apply Finset.mem_union_right
    exact (mem_supportOn Finset.univ residualDirection j).mpr
      ⟨Finset.mem_univ _, by
        simpa [residualDirection, mask,
          (mem_supportOn allowed (v - direction) j).mp hj |>.1] using
          (mem_supportOn allowed (v - direction) j).mp hj |>.2⟩
  exact (Finset.card_le_card hsubset).trans hactive

/-- Coefficient vectors whose row combination is locally radius `g` from
the code on `allowed`. -/
noncomputable def closeCombinationChallengesOn
    (C : LinearCode F n) (rows : Row → Word F n)
    (allowed : Finset (Fin n)) (g : ℕ) : Finset (Row → F) := by
  classical
  exact Finset.univ.filter fun weights ↦ ∃ decoded ∈ C,
    (supportOn allowed (wordCombination rows weights - decoded)).card ≤ g

/-- If one direction is not locally radius `g`, the sharp `g+1` affine-line
threshold bounds the density of all locally close combinations by
`(g+1)/|F|`. -/
theorem closeCombinationChallengesOn_card_le_of_direction_far
    {e : ℕ} (C : LinearCode F n) (rows : Row → Word F n)
    (allowed : Finset (Fin n))
    (hmin : HasMinimumDistanceAtLeast C d)
    (hdeleted : (Finset.univ \ allowed).card ≤ e)
    (hthree : 3 * g < d - e)
    (direction : Row → F)
    (hfar : ¬∃ decoded ∈ C,
      (supportOn allowed
        (wordCombination rows direction - decoded)).card ≤ g) :
    (closeCombinationChallengesOn C rows allowed g).card ≤
      (g + 1) * Fintype.card F ^ (Fintype.card Row - 1) := by
  classical
  have hdirection : direction ≠ 0 := by
    intro hzero
    subst direction
    apply hfar
    refine ⟨0, C.zero_mem, ?_⟩
    simp [wordCombination, supportOn]
  apply card_filter_univ_le_mul_pow_of_affine_line_card
    (property := fun weights ↦ ∃ decoded ∈ C,
      (supportOn allowed
        (wordCombination rows weights - decoded)).card ≤ g)
    direction hdirection (g + 1)
  intro base
  let closeScalars := Finset.univ.filter fun scalar : F ↦
    ∃ decoded ∈ C,
      (supportOn allowed
        (wordCombination rows (base + scalar • direction) - decoded)).card ≤ g
  change closeScalars.card ≤ g + 1
  by_contra hnot
  have hmany : g + 1 < closeScalars.card := Nat.lt_of_not_ge hnot
  have hclose (scalar : F) (hscalar : scalar ∈ closeScalars) :
      ∃ decoded ∈ C,
        (supportOn allowed
          (affineWord (wordCombination rows base)
            (wordCombination rows direction) scalar - decoded)).card ≤ g := by
    obtain ⟨decoded, hdecoded, hsmall⟩ :=
      (Finset.mem_filter.mp hscalar).2
    refine ⟨decoded, hdecoded, ?_⟩
    have heq : wordCombination rows (base + scalar • direction) =
        affineWord (wordCombination rows base)
          (wordCombination rows direction) scalar := by
      rw [wordCombination_add_smul]
      rfl
    rw [← heq]
    exact hsmall
  obtain ⟨decodedDirection, hdecodedDirection, hsmallDirection⟩ :=
    directionWithinRadiusOn_of_many_affine_close C
      (wordCombination rows base) (wordCombination rows direction)
      allowed closeScalars hmin hdeleted hthree hmany hclose
  exact hfar ⟨decodedDirection, hdecodedDirection, hsmallDirection⟩

/-- Punctured form of the three-error globalization theorem.  Decoding
errors are measured only on `allowed`; the deleted complement costs its
cardinality from the original code distance. -/
theorem interleavedWithinRadiusOn_of_all_combinations_close_three
    {e : ℕ}
    (C : LinearCode F n) (rows : Row → Word F n)
    (allowed : Finset (Fin n))
    (hmin : HasMinimumDistanceAtLeast C d)
    (hdeleted : (Finset.univ \ allowed).card ≤ e)
    (hthree : 3 * g < d - e) (hfield : g + 1 < Fintype.card F)
    (hall : ∀ weights : Row → F, ∃ decoded ∈ C,
      (supportOn allowed
        (wordCombination rows weights - decoded)).card ≤ g) :
    ∃ decodedRows : Row → Word F n,
      (∀ row, decodedRows row ∈ C) ∧
      (allowed.filter fun j ↦ ∃ row, rows row j ≠ decodedRows row j).card ≤ g :=
  AffineAgreement.interleavedWithinRadiusOn_of_all_combinations_close_three
    C rows allowed hmin hdeleted hthree hfield hall

end SelectedMCA
