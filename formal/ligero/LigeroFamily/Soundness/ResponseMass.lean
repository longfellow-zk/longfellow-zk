import LigeroFamily.Soundness.AgreementProfile
import LigeroFamily.Soundness.PotentialProfile

/-!
# Packing distinct high-agreement responses

The agreement sets of distinct legal responses need not have the same size.
Shrinking each one to `a` columns reduces their count to the existing
uniform-family packing interface. This lemma is independent of the protocol
and can use either a Johnson or a Hahn/Delsarte family bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LigeroFamily.ResponseMass

open Finset CodingTheory
open scoped Classical

/-- A packing bound for response agreement sets of size at least `a`.
Unlike `UniformFamilyBound`, the original sets may have different sizes. -/
theorem card_le_of_overlap
    {Response : Type*} [DecidableEq Response]
    {n a lambda L : ℕ}
    (responses : Finset Response)
    (good : Response → Finset (Fin n))
    (hsize : ∀ response ∈ responses, a ≤ (good response).card)
    (hoverlap : ∀ response ∈ responses, ∀ other ∈ responses,
      response ≠ other → ((good response) ∩ (good other)).card ≤ lambda)
    (hlambda : lambda < a)
    (hpack : UniformFamilyBound n a lambda L) :
    responses.card ≤ L := by
  classical
  have hsub : ∀ response ∈ responses,
      ∃ picked ⊆ good response, picked.card = a := by
    intro response hresponse
    exact Finset.exists_subset_card_eq (hsize response hresponse)
  choose! picked hpicked hcard using hsub
  have hinj : Set.InjOn picked responses := by
    intro response hresponse other hother heq
    by_contra hne
    have hsubset : picked response ⊆
        good response ∩ good other := by
      intro j hj
      have hjother : j ∈ picked other := heq ▸ hj
      exact Finset.mem_inter.mpr
        ⟨hpicked response hresponse hj, hpicked other hother hjother⟩
    have hlarge := Finset.card_le_card hsubset
    rw [hcard response hresponse] at hlarge
    have hsmall := hoverlap response hresponse other hother hne
    omega
  have himage := hpack (responses.image picked)
    (by
      intro A hA
      obtain ⟨response, hresponse, rfl⟩ := Finset.mem_image.mp hA
      exact hcard response hresponse)
    (by
      intro A hA B hB hne
      obtain ⟨response, hresponse, rfl⟩ := Finset.mem_image.mp hA
      obtain ⟨other, hother, rfl⟩ := Finset.mem_image.mp hB
      have hneq : response ≠ other := by
        intro heq
        exact hne (heq ▸ rfl)
      calc
        ((picked response) ∩ (picked other)).card ≤
            ((good response) ∩ (good other)).card :=
          Finset.card_le_card
            (Finset.inter_subset_inter
              (hpicked response hresponse) (hpicked other hother))
        _ ≤ lambda := hoverlap response hresponse other hother hneq)
  rwa [Finset.card_image_of_injOn hinj] at himage

/-- Layer-cake accounting for the *total* mass of responses, rather than
the largest response at each challenge. The packing hypothesis bounds the
number of responses above each agreement level for one challenge; the tail
hypothesis bounds the fraction of challenges where that level is reachable.
This is the analytic input needed by a grouped two-stage FS compiler. -/
theorem mean_curve_le
    {Challenge Response : Type*} [Fintype Challenge] [Nonempty Challenge]
    [Fintype Response]
    {n : ℕ}
    (agreement : Challenge → Response → ℕ)
    (maximum : Challenge → ℕ)
    (hagreement : ∀ challenge response, agreement challenge response ≤ n)
    (hmax : ∀ challenge response,
      agreement challenge response ≤ maximum challenge)
    (ψ : PotentialProfile.Curve n)
    (packing : ℕ → ℕ) (tail : ℕ → ℚ)
    (hpack : ∀ challenge a, a ≤ n →
      (univ.filter fun response : Response =>
        a ≤ agreement challenge response).card ≤ packing a)
    (htail : ∀ a ≤ n,
      ((AgreementProfile.tailSet maximum a).card : ℚ) /
        Fintype.card Challenge ≤ tail a) :
    (∑ challenge : Challenge, ∑ response : Response,
        ψ.value (agreement challenge response)) /
        Fintype.card Challenge ≤
      ∑ a ∈ range (n + 1),
        ψ.increment a * (packing a : ℚ) * tail a := by
  classical
  have hcard (a : ℕ) (ha : a ≤ n) :
      (∑ challenge : Challenge,
        (univ.filter fun response : Response =>
          a ≤ agreement challenge response).card) ≤
        packing a * (AgreementProfile.tailSet maximum a).card := by
    calc
      (∑ challenge : Challenge,
        (univ.filter fun response : Response =>
          a ≤ agreement challenge response).card) ≤
          ∑ challenge : Challenge,
            if a ≤ maximum challenge then packing a else 0 := by
              apply Finset.sum_le_sum
              intro challenge _
              split_ifs with hgood
              · exact hpack challenge a ha
              · have hempty :
                    (univ.filter fun response : Response =>
                      a ≤ agreement challenge response) = ∅ := by
                  ext response
                  have hfalse : ¬ a ≤ agreement challenge response :=
                    fun hresponse => hgood (hresponse.trans (hmax challenge response))
                  simp [hfalse]
                simp [hempty]
      _ = packing a * (AgreementProfile.tailSet maximum a).card := by
            rw [← Finset.sum_filter]
            simp [AgreementProfile.tailSet, Nat.mul_comm]
  have hsum :
      (∑ challenge : Challenge, ∑ response : Response,
          ψ.value (agreement challenge response)) =
        ∑ a ∈ range (n + 1), ψ.increment a *
          (∑ challenge : Challenge,
            (univ.filter fun response : Response =>
              a ≤ agreement challenge response).card) := by
    calc
      (∑ challenge : Challenge, ∑ response : Response,
          ψ.value (agreement challenge response)) =
          ∑ challenge : Challenge, ∑ response : Response,
            ∑ a ∈ range (n + 1),
              if a ≤ agreement challenge response then ψ.increment a else 0 := by
                apply Finset.sum_congr rfl
                intro challenge _
                apply Finset.sum_congr rfl
                intro response _
                exact ψ.value_eq_tail_sum
                  (agreement challenge) response (hagreement challenge response)
      _ = ∑ a ∈ range (n + 1),
          ∑ challenge : Challenge, ∑ response : Response,
            if a ≤ agreement challenge response then ψ.increment a else 0 := by
              simp_rw [Finset.sum_comm (s := (univ : Finset Response))
                (t := range (n + 1))]
              rw [Finset.sum_comm]
      _ = _ := by
            apply Finset.sum_congr rfl
            intro a _
            simp_rw [← Finset.sum_filter]
            simp [Finset.mul_sum, mul_comm]
  rw [hsum, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro a ha
  have han : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  have hcount :
      ((∑ challenge : Challenge,
        (univ.filter fun response : Response =>
          a ≤ agreement challenge response).card : ℕ) : ℚ) /
          Fintype.card Challenge ≤
        (packing a : ℚ) * tail a := by
    calc
      ((∑ challenge : Challenge,
        (univ.filter fun response : Response =>
          a ≤ agreement challenge response).card : ℕ) : ℚ) /
          Fintype.card Challenge ≤
        (packing a : ℚ) *
          (((AgreementProfile.tailSet maximum a).card : ℚ) /
            Fintype.card Challenge) := by
              have h := hcard a han
              have h' :
                  ((∑ challenge : Challenge,
                    (univ.filter fun response : Response =>
                      a ≤ agreement challenge response).card : ℕ) : ℚ) ≤
                    (packing a : ℚ) *
                      (AgreementProfile.tailSet maximum a).card := by
                exact_mod_cast h
              exact div_le_div_of_nonneg_right h' (by positivity) |>.trans_eq
                (by ring)
      _ ≤ (packing a : ℚ) * tail a :=
        mul_le_mul_of_nonneg_left (htail a han) (Nat.cast_nonneg _)
  calc
    (ψ.increment a *
        (∑ challenge : Challenge,
          (univ.filter fun response : Response =>
            a ≤ agreement challenge response).card)) *
        (Fintype.card Challenge : ℚ)⁻¹ =
      ψ.increment a *
        (((∑ challenge : Challenge,
          (univ.filter fun response : Response =>
            a ≤ agreement challenge response).card : ℕ) : ℚ) /
          Fintype.card Challenge) := by push_cast; ring
    _ ≤ ψ.increment a * ((packing a : ℚ) * tail a) :=
      mul_le_mul_of_nonneg_left hcount (ψ.increment_nonneg a han)
    _ = ψ.increment a * (packing a : ℚ) * tail a := by ring

/-- Feed a family-packing theorem into the response-mass envelope. Levels at
or below `cutoff` use the trivial number of responses; a curve that vanishes
there never charges that part of the envelope. -/
theorem mean_curve_le_of_overlap
    {Challenge Response : Type*} [Fintype Challenge] [Nonempty Challenge]
    [Fintype Response] [DecidableEq Response]
    {n cutoff lambda : ℕ}
    (good : Challenge → Response → Finset (Fin n))
    (maximum : Challenge → ℕ)
    (hmax : ∀ challenge response,
      (good challenge response).card ≤ maximum challenge)
    (hoverlap : ∀ challenge response other, response ≠ other →
      ((good challenge response) ∩ (good challenge other)).card ≤ lambda)
    (ψ : PotentialProfile.Curve n)
    (packing : ℕ → ℕ) (tail : ℕ → ℚ)
    (hlambda : lambda ≤ cutoff)
    (hpacking : ∀ a, cutoff < a → a ≤ n →
      UniformFamilyBound n a lambda (packing a))
    (htail : ∀ a ≤ n,
      ((AgreementProfile.tailSet maximum a).card : ℚ) /
        Fintype.card Challenge ≤ tail a) :
    (∑ challenge : Challenge, ∑ response : Response,
        ψ.value (good challenge response).card) /
        Fintype.card Challenge ≤
      ∑ a ∈ range (n + 1), ψ.increment a *
        (if a ≤ cutoff then Fintype.card Response else packing a : ℕ) * tail a := by
  classical
  apply mean_curve_le (agreement := fun challenge response =>
      (good challenge response).card) maximum
    (fun challenge response => by
      exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp))
    hmax ψ (fun a => if a ≤ cutoff then Fintype.card Response else packing a)
    tail ?_ htail
  intro challenge a ha
  by_cases hac : a ≤ cutoff
  · simp only [hac, ↓reduceIte]
    exact Finset.card_le_univ _
  · simp only [hac, ↓reduceIte]
    apply card_le_of_overlap
      (responses := univ.filter fun response : Response =>
        a ≤ (good challenge response).card)
      (good challenge)
    · intro response hresponse
      exact (Finset.mem_filter.mp hresponse).2
    · intro response hresponse other hother hne
      exact hoverlap challenge response other hne
    · omega
    · exact hpacking a (by omega) ha

end LigeroFamily.ResponseMass
