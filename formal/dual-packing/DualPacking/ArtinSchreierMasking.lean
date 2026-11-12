import DualPacking.ArtinSchreier

/-! Privacy of the actual dependent-mask construction.  The zeroth mask is
not fresh randomness: it is the basis-weighted sum of all the free masks.
This restriction removes exactly the base-field kernel of the coordinatewise
Artin--Schreier map.  Consequently its output is uniform on the full product
of trace-zero spaces, rather than merely having trace zero coordinatewise. -/
noncomputable section
namespace DualPacking.ArtinSchreier.Masking

open Finset Module
open scoped Classical

variable {K F I : Type*} [Field K] [Fintype K] [Field F] [Fintype F]
  [Algebra K F] [Fintype I] [DecidableEq I]

abbrev TraceZero (K F : Type*) [Field K] [Field F] [Algebra K F] :=
  LinearMap.ker (Algebra.trace K F)

def dependent (e : Basis I K F) (pivot : I) (free : {i : I // i ≠ pivot} → F) (i : I) : F :=
  if h : i = pivot then ∑ j : {i : I // i ≠ pivot}, e j.val * free j
  else free ⟨i,h⟩

def maskMap (e : Basis I K F) (pivot : I) :
    ({i : I // i ≠ pivot} → F) →ₗ[K] (I → TraceZero K F) where
  toFun free i := ⟨frobenius K F (dependent e pivot free i) - dependent e pivot free i, by
    apply (algebraMap K F).injective
    simpa only [traceF, map_zero] using
      (trace_mask (K := K) (F := F) (dependent e pivot free i))⟩
  map_add' a b := by
    ext i
    have hd : dependent e pivot (a+b) i = dependent e pivot a i + dependent e pivot b i := by
      by_cases h : i = pivot <;> simp [dependent, h, mul_add, sum_add_distrib]
    change frobenius K F (dependent e pivot (a+b) i) - dependent e pivot (a+b) i = _
    rw [hd, map_add]
    simp only [Pi.add_apply, Submodule.coe_add]
    ring
  map_smul' a free := by
    ext i
    have hd : dependent e pivot (a • free) i = a • dependent e pivot free i := by
      by_cases h : i = pivot <;> simp [dependent, h, Algebra.smul_def, Finset.mul_sum, mul_left_comm]
    change frobenius K F (dependent e pivot (a • free) i) - dependent e pivot (a • free) i = _
    rw [hd, map_smul]
    simp only [Pi.smul_apply, Submodule.coe_smul_of_tower, smul_sub, RingHom.id_apply]

theorem maskMap_injective (e : Basis I K F) (pivot : I) (hp : e pivot = 1) :
    Function.Injective (maskMap e pivot) := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro free hf
  have hz (i : I) : frobenius K F (dependent e pivot free i) = dependent e pivot free i := by
    have h := congrArg (fun v : I → TraceZero K F => (v i).val) hf
    exact sub_eq_zero.mp h
  choose a ha using fun i => (frobenius_fixed_iff (K := K) (dependent e pivot free i)).mp (hz i)
  have hpivot : algebraMap K F (a pivot) =
      ∑ j : {i : I // i ≠ pivot}, e j.val * algebraMap K F (a j.val) := by
    calc
      _ = dependent e pivot free pivot := ha pivot
      _ = ∑ j : {i : I // i ≠ pivot}, e j.val * free j := by simp [dependent]
      _ = _ := by
        apply sum_congr rfl
        intro j _
        rw [ha]
        simp only [dependent, dif_neg j.property]
  have hcoord (j : {i : I // i ≠ pivot}) : a j.val = 0 := by
    have h := congrArg (fun x : F => e.repr x j.val) hpivot
    have hleft : e.repr (algebraMap K F (a pivot)) j.val = 0 := by
      rw [← mul_one (algebraMap K F (a pivot)), ← hp, ← Algebra.smul_def]
      simp [j.property]
    rw [hleft] at h
    have hright : e.repr (∑ k : {i : I // i ≠ pivot},
        e k.val * algebraMap K F (a k.val)) j.val = a j.val := by
      simp_rw [mul_comm (e _), ← Algebra.smul_def, map_sum, map_smul]
      simp [Finsupp.single_apply, Subtype.val_inj]
    exact (h.trans hright).symm
  funext j
  change free j = 0
  have h := ha j.val
  simpa only [dependent, dif_neg j.property, hcoord j, map_zero] using h.symm

theorem maskMap_bijective (e : Basis I K F) (pivot : I) (hp : e pivot = 1) :
    Function.Bijective (maskMap e pivot) := by
  have htr : finrank K (LinearMap.range (Algebra.trace K F)) = 1 := by
    rw [LinearMap.range_eq_top.mpr (Algebra.trace_surjective K F)]
    simp
  have hdim := LinearMap.finrank_range_add_finrank_ker (Algebra.trace K F)
  have he : finrank K F = Fintype.card I := Module.finrank_eq_card_basis e
  have hcard : Fintype.card {i : I // i ≠ pivot} + 1 = Fintype.card I := by
    have h := Fintype.card_subtype_compl (fun i : I => i = pivot)
    have hone : Fintype.card {i : I // i = pivot} = 1 := by simp
    rw [hone] at h
    have hpos : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨pivot⟩
    have hc : Fintype.card {i : I // i ≠ pivot} = Fintype.card I - 1 := h
    rw [hc]
    omega
  have hsame : finrank K ({i : I // i ≠ pivot} → F) = finrank K (I → TraceZero K F) := by
    rw [Module.finrank_pi_fintype, Module.finrank_pi_fintype]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    change Fintype.card {i : I // i ≠ pivot} * finrank K F =
      Fintype.card I * finrank K (LinearMap.ker (Algebra.trace K F))
    rw [htr] at hdim
    nlinarith
  exact ⟨maskMap_injective e pivot hp,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hsame).mp
      (maskMap_injective e pivot hp)⟩

def maskEquiv (e : Basis I K F) (pivot : I) (hp : e pivot = 1) :
    ({i : I // i ≠ pivot} → F) ≃ (I → TraceZero K F) :=
  Equiv.ofBijective (maskMap e pivot) (maskMap_bijective e pivot hp)

/-- The final response hides the dependent masks even when its challenge is
chosen after observing the complete trace-zero vector. -/
def responseEquiv (shift : (I → TraceZero K F) → F) :
    ((I → TraceZero K F) × F) ≃ ((I → TraceZero K F) × F) where
  toFun x := (x.1,x.2+shift x.1)
  invFun x := (x.1,x.2-shift x.1)
  left_inv x := by simp
  right_inv x := by simp

/-- Simulator output is simply uniform on `(trace-zero vector, field scalar)`.
The clear offset and recovered masks occur only in this proof coupling.
In particular delta may depend arbitrarily on U and on any fixed earlier prefix. -/
def transcriptEquiv (e : Basis I K F) (pivot : I) (hp : e pivot = 1)
    (offset : I → TraceZero K F) (delta : (I → TraceZero K F) → I → F) :
    (({i : I // i ≠ pivot} → F) × F) ≃ ((I → TraceZero K F) × F) :=
  let first := (maskEquiv e pivot hp).trans (Equiv.addRight offset)
  (Equiv.prodCongr first (Equiv.refl F)).trans
    (responseEquiv fun u => ∑ i, delta u i * dependent e pivot (first.symm u) i)

theorem transcriptEquiv_apply (e : Basis I K F) (pivot : I) (hp : e pivot = 1)
    (offset : I → TraceZero K F) (delta : (I → TraceZero K F) → I → F)
    (free : {i : I // i ≠ pivot} → F) (r : F) :
    transcriptEquiv e pivot hp offset delta (free,r) =
      (maskMap e pivot free+offset,
        r+∑ i, delta (maskMap e pivot free+offset) i * dependent e pivot free i) := by
  have h : ((maskEquiv e pivot hp).trans (Equiv.addRight offset)).symm
      (maskMap e pivot free+offset) = free :=
    ((maskEquiv e pivot hp).trans (Equiv.addRight offset)).symm_apply_apply free
  simp only [transcriptEquiv, Equiv.trans_apply, Equiv.prodCongr_apply,
    responseEquiv, Equiv.coe_fn_mk]
  change (maskMap e pivot free+offset,
    r+∑ i, delta (maskMap e pivot free+offset) i *
      dependent e pivot (((maskEquiv e pivot hp).trans (Equiv.addRight offset)).symm
        (maskMap e pivot free+offset)) i) = _
  rw [h]

/-- Every joint response has exactly one preimage in the honest free mask
tape. This is a joint distribution statement, not two marginal hiding claims. -/
theorem transcript_uniform_fiber (e : Basis I K F) (pivot : I) (hp : e pivot = 1)
    (offset : I → TraceZero K F) (delta : (I → TraceZero K F) → I → F)
    (view : (I → TraceZero K F) × F) :
    (univ.filter fun tape => transcriptEquiv e pivot hp offset delta tape = view).card = 1 := by
  have heq : (univ.filter fun tape => transcriptEquiv e pivot hp offset delta tape = view) =
      {(transcriptEquiv e pivot hp offset delta).symm view} := by
    ext tape
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    exact (transcriptEquiv e pivot hp offset delta).apply_eq_iff_eq_symm_apply
  rw [heq, card_singleton]

section Instance
variable {J : Type*} [Fintype J]

/-- For a true input claim, the witness-dependent offset is trace zero.
It merely translates the same public simulator output space. -/
def honestOffset (P : Instance K F I J) (htrue : P.target = P.trueValue) :
    I → TraceZero K F := fun i =>
  ⟨P.B i - P.basis.traceDual i * P.target, by
    apply (algebraMap K F).injective
    have hz : traceF K (P.B i - P.basis.traceDual i * P.target) = 0 := by
      rw [trace_sub, Instance.B, trace_forms, trace_dual, htrue]
      exact sub_self _
    simpa only [traceF, map_zero] using hz⟩

/-- This identifies the bijection with the exact U/A formulas used by the
protocol. The honest Frobenius cell is deterministic and never fresh coins. -/
theorem honest_transcript (P : Instance K F I J) (hp : P.basis P.pivot = 1)
    (htrue : P.target = P.trueValue)
    (delta : (I → TraceZero K F) → I → F) :
    let view := transcriptEquiv P.basis P.pivot hp (honestOffset P htrue) delta (P.masks,P.r)
    (fun i => (view.1 i).val) = P.honestU ∧ view.2 = P.honestA (delta view.1) := by
  dsimp only
  rw [transcriptEquiv_apply]
  constructor
  · funext i
    change (frobenius K F (dependent P.basis P.pivot P.masks i) -
      dependent P.basis P.pivot P.masks i) +
      (P.B i-P.basis.traceDual i*P.target) = _
    change (frobenius K F (P.mask i)-P.mask i) +
      (P.B i-P.basis.traceDual i*P.target) = P.honestU i
    exact add_comm _ _
  · rfl

end Instance

end DualPacking.ArtinSchreier.Masking
