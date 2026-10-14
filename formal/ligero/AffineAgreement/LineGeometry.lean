import AffineAgreement.TripleCounting
import AffineAgreement.Secant
import AffineAgreement.AffineCodewordLine

/-! Affine codeword lines determined by large triple intersections. -/

namespace AffineAgreement

open scoped BigOperators

variable {F : Type*} [Field F] [DecidableEq F]

namespace Internal

omit [DecidableEq F] in
private theorem affine_secant_left {n : ℕ} (a b : F) (hab : a ≠ b)
    (ca cb : Word F n) :
    affineWord
      (ca - fun i ↦ a * ((b - a)⁻¹ * (cb i - ca i)))
      (fun i ↦ (b - a)⁻¹ * (cb i - ca i)) a = ca := by
  funext i
  simp only [affineWord, Pi.sub_apply]
  field_simp [sub_ne_zero.mpr hab.symm]
  ring

omit [DecidableEq F] in
private theorem affine_secant_right {n : ℕ} (a b : F) (hab : a ≠ b)
    (ca cb : Word F n) :
    affineWord
      (ca - fun i ↦ a * ((b - a)⁻¹ * (cb i - ca i)))
      (fun i ↦ (b - a)⁻¹ * (cb i - ca i)) b = cb := by
  funext i
  simp only [affineWord, Pi.sub_apply]
  field_simp [sub_ne_zero.mpr hab.symm]
  ring

/-- Two distinct selected decodings determine an affine codeword line. -/
theorem exists_affineCodewordLine_through_two {n e m : ℕ}
    {C : LinearCode F n} {u v : Word F n}
    (D : DecoderData (e := e) (m := m) C u v)
    {a b : F} (ha : a ∈ D.parameters) (hb : b ∈ D.parameters)
    (hab : a ≠ b) :
    ∃ line : AffineCodewordLine D,
      a ∈ line.followingParameters D ∧
      b ∈ line.followingParameters D := by
  let direction : Word F n := fun i ↦
    (b - a)⁻¹ * (D.codeword b i - D.codeword a i)
  let base : Word F n := D.codeword a - fun i ↦ a * direction i
  have hdirection : direction ∈ C := by
    dsimp [direction]
    exact C.smul_mem _ (C.sub_mem (D.codeword_mem hb) (D.codeword_mem ha))
  have hbase : base ∈ C := by
    dsimp [base]
    exact C.sub_mem (D.codeword_mem ha) (C.smul_mem _ hdirection)
  have hleft : affineWord base direction a = D.codeword a := by
    simpa [base, direction] using
      affine_secant_left a b hab (D.codeword a) (D.codeword b)
  have hright : affineWord base direction b = D.codeword b := by
    simpa [base, direction] using
      affine_secant_right a b hab (D.codeword a) (D.codeword b)
  let line : AffineCodewordLine D := {
    base := base
    direction := direction
    base_mem := hbase
    direction_mem := hdirection }
  refine ⟨line, ?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨ha, hleft.symm⟩
  · exact Finset.mem_filter.mpr ⟨hb, hright.symm⟩

/-- Three selected codewords that all agree with their received words on more
than `n-d` common coordinates lie on one affine codeword line.  This is the
geometric core shared by both selected-clique arguments. -/
theorem affineCodewordLine_of_common_agreement {n e m d : ℕ}
    {C : LinearCode F n} {u v : Word F n}
    (D : DecoderData (e := e) (m := m) C u v)
    (hmin : HasMinimumDistanceAtLeast C d)
    (t : Finset F) (ht : t ∈ D.parameters.powersetCard 3)
    (common : Finset (Fin n))
    (hagree : ∀ x ∈ t, ∀ i ∈ common,
      affineWord u v x i = D.codeword x i)
    (hlarge : n - d < common.card) :
    ∃ line : AffineCodewordLine D, t ⊆ line.followingParameters D := by
  obtain ⟨a, b, c, hab, hac, hbc, htEq⟩ :=
    Finset.card_eq_three.mp (Finset.mem_powersetCard.mp ht).2
  have htS : t ⊆ D.parameters := (Finset.mem_powersetCard.mp ht).1
  have ha : a ∈ D.parameters := htS (by simp [htEq])
  have hb : b ∈ D.parameters := htS (by simp [htEq])
  have hc : c ∈ D.parameters := htS (by simp [htEq])
  let p₁ : Word F n := fun i ↦
    (b - a)⁻¹ * (D.codeword b i - D.codeword a i)
  let p₀ : Word F n := D.codeword a - fun i ↦ a * p₁ i
  have hp₁ : p₁ ∈ C := by
    dsimp [p₁]
    exact C.smul_mem _ (C.sub_mem (D.codeword_mem hb) (D.codeword_mem ha))
  have hp₀ : p₀ ∈ C := by
    dsimp [p₀]
    exact C.sub_mem (D.codeword_mem ha) (C.smul_mem _ hp₁)
  have hpa : affineWord p₀ p₁ a = D.codeword a := by
    simpa [p₀, p₁] using
      affine_secant_left a b hab (D.codeword a) (D.codeword b)
  have hpb : affineWord p₀ p₁ b = D.codeword b := by
    simpa [p₀, p₁] using
      affine_secant_right a b hab (D.codeword a) (D.codeword b)
  have hpc : affineWord p₀ p₁ c = D.codeword c := by
    apply eq_of_agree_on hmin (C.add_mem hp₀ (C.smul_mem c hp₁))
      (D.codeword_mem hc) common hlarge
    intro i hi
    have hea := hagree a (by simp [htEq]) i hi
    have heb := hagree b (by simp [htEq]) i hi
    have hec := hagree c (by simp [htEq]) i hi
    calc
      affineWord p₀ p₁ c i =
          affineWord
            (affineWord u v a - fun j ↦
              a * ((b - a)⁻¹ *
                (affineWord u v b j - affineWord u v a j)))
            (fun j ↦ (b - a)⁻¹ *
              (affineWord u v b j - affineWord u v a j)) c i := by
        simp only [p₀, p₁, affineWord, Pi.sub_apply]
        rw [← hea, ← heb]
        rfl
      _ = affineWord u v c i :=
        congrFun (received_secant u v a b c hab).symm i
      _ = D.codeword c i := hec
  let line : AffineCodewordLine D := {
    base := p₀
    direction := p₁
    base_mem := hp₀
    direction_mem := hp₁ }
  refine ⟨line, ?_⟩
  intro x hx
  have hxabc : x = a ∨ x = b ∨ x = c := by
    simpa [htEq] using hx
  apply Finset.mem_filter.mpr
  refine ⟨htS hx, ?_⟩
  rcases hxabc with rfl | rfl | rfl
  · exact hpa.symm
  · exact hpb.symm
  · exact hpc.symm

/-- A large triple intersection for padded decoding errors determines one
affine codeword line. -/
theorem affineCodewordLine_of_large_intersection {n e m d : ℕ}
    {C : LinearCode F n} {u v : Word F n}
    (D : DecoderData (e := e) (m := m) C u v) (P : PaddedErrorFamily D)
    (hmin : HasMinimumDistanceAtLeast C d)
    (t : Finset F) (ht : t ∈ D.parameters.powersetCard 3)
    (hlarge : n - d < (agreementIntersection P.error t).card) :
    ∃ line : AffineCodewordLine D, t ⊆ line.followingParameters D := by
  apply affineCodewordLine_of_common_agreement D hmin t ht
    (agreementIntersection P.error t) _ hlarge
  intro x hx i hi
  have htS : t ⊆ D.parameters := (Finset.mem_powersetCard.mp ht).1
  have hiE : i ∉ P.error x :=
    (mem_agreementIntersection P.error t i).mp hi x hx
  have hiActual : i ∉ supportOn Finset.univ
      (affineWord u v x - D.codeword x) :=
    fun h ↦ hiE (P.actual_subset (htS hx) h)
  have hz : (affineWord u v x - D.codeword x) i = 0 := by
    simpa [supportOn] using hiActual
  exact sub_eq_zero.mp hz

end Internal

export Internal (exists_affineCodewordLine_through_two
  affineCodewordLine_of_common_agreement
  affineCodewordLine_of_large_intersection)

end AffineAgreement
