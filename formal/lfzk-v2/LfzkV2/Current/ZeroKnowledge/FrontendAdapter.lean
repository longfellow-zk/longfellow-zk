import Bcs.SameDistribution
import LfzkV2.Current.ZeroKnowledge.FrontendAdapterBits
import LfzkV2.Current.AdapterParameters

/-! Privacy of the current cross-field adapter's public masked scalar and
quotient advice. The honest quotient is a bounded integer, never a sampled
field element. Its XOR pad is independent private randomness; uniformity is
over every canonical pair of ten-bit public words, not just honest quotient words.

The two rescalings may be arbitrary public functions of the masked scalar.
No field challenge or quotient is fixed after looking at an OTP bit. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.Adapter
open SumcheckV2
open scoped Classical
variable {p bits K : ℕ} [Fact p.Prime]

theorem scaledSum_mod (weights : Fin bits → ZMod p) (values : Fin bits → Bool)
    (target alpha : ZMod p) (htrue : Current.Adapter.residual weights values target = 0) :
    Current.Adapter.scaledSum weights values alpha % p = (alpha*target).val := by
  have h := Current.Adapter.difference_cast weights values target alpha 0
  rw [htrue,mul_zero] at h
  have hs : (Current.Adapter.scaledSum weights values alpha : ZMod p) = alpha*target := by
    simpa [Current.Adapter.difference,sub_eq_zero] using h
  simpa only [ZMod.val_natCast] using congrArg ZMod.val hs

theorem scaledSum_lt (weights : Fin bits → ZMod p) (values : Fin bits → Bool)
    (alpha : ZMod p) (hbits : bits ≤ K) (hK : 0 < K) :
    Current.Adapter.scaledSum weights values alpha < K*p := by
  have hp := (Fact.out (p := p.Prime)).pos
  have hs : Current.Adapter.scaledSum weights values alpha ≤ bits*(p-1) := by
    have each (i : Fin bits) : (if values i then (alpha*weights i).val else 0) ≤ p-1 := by
      split
      · have := (alpha*weights i).val_lt; omega
      · omega
    calc
      _ ≤ ∑ _i : Fin bits, (p-1) := Finset.sum_le_sum fun i _ => each i
      _ = bits*(p-1) := by simp
  have hk := Nat.mul_le_mul_right (p-1) hbits
  have hp1 : p-1+1 = p := by omega
  nlinarith

def honestQuotient (weights : Fin bits → ZMod p) (values : Fin bits → Bool) (alpha : ZMod p)
    (hbits : bits ≤ K) (hK : 0 < K) : Fin K :=
  ⟨Current.Adapter.scaledSum weights values alpha / p,
    (Nat.div_lt_iff_lt_mul (Fact.out (p := p.Prime)).pos).mpr
      (scaledSum_lt weights values alpha hbits hK)⟩

theorem honestQuotient_equation (weights : Fin bits → ZMod p) (values : Fin bits → Bool)
    (target alpha : ZMod p) (hbits : bits ≤ K) (hK : 0 < K)
    (htrue : Current.Adapter.residual weights values target = 0) :
    Current.Adapter.scaledSum weights values alpha = (alpha*target).val +
      (honestQuotient weights values alpha hbits hK).val*p := by
  have h := Nat.mod_add_div (Current.Adapter.scaledSum weights values alpha) p
  rw [scaledSum_mod weights values target alpha htrue] at h
  dsimp only [honestQuotient]
  nlinarith

/-- These are exactly the subtraction and division success conditions in
the runtime encoder. There is no rare abort to discard or condition on. -/
theorem honestQuotient_runtime (weights : Fin bits → ZMod p) (values : Fin bits → Bool)
    (target alpha : ZMod p) (hbits : bits ≤ K) (hK : 0 < K)
    (htrue : Current.Adapter.residual weights values target = 0) :
    (alpha*target).val ≤ Current.Adapter.scaledSum weights values alpha ∧
      (Current.Adapter.scaledSum weights values alpha - (alpha*target).val) % p = 0 ∧
      (Current.Adapter.scaledSum weights values alpha - (alpha*target).val) / p =
        (honestQuotient weights values alpha hbits hK).val := by
  rw [honestQuotient_equation weights values target alpha hbits hK htrue]
  simp [(Fact.out (p := p.Prime)).pos]

def canonicalMask {n : ℕ} (capacity : p ≤ 2^n) (mask : ZMod p) : Fin n → Bool :=
  (AdapterBits.wordEquiv n).symm ⟨mask.val,lt_of_lt_of_le mask.val_lt capacity⟩

theorem canonicalMask_bits {n : ℕ} (capacity : p ≤ 2^n) (mask : ZMod p) (i : Fin n) :
    canonicalMask capacity mask i = mask.val.testBit i.val :=
  AdapterBits.wordEquiv_decode n _ i

/-- The prime scalar and its binary copy are reconstructed from the same
canonical value. Their equality is derived, not an extra simulation premise. -/
theorem canonicalMask_value {n : ℕ} (capacity : p ≤ 2^n) (mask : ZMod p) :
    Handoff.binaryMask (canonicalMask capacity mask) = mask := by
  have h := AdapterBits.wordEquiv_value n (canonicalMask capacity mask)
  have hc := congrArg (fun v : ℕ => (v : ZMod p)) h
  simp only [canonicalMask,Equiv.apply_symm_apply] at hc
  simp only [Nat.cast_sum,Nat.cast_ite,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_zero,
    ZMod.natCast_zmod_val] at hc
  exact hc.symm

def muEquiv (offset : ZMod p) : ZMod p ≃ ZMod p where
  toFun mask := offset+mask
  invFun mu := mu-offset
  left_inv _ := by ring
  right_inv _ := by ring

def muAdviceEquiv (offset : ZMod p) (quotient : ZMod p → MdocAdvice.Value) :
    (ZMod p × MdocAdvice.Value) ≃ (ZMod p × MdocAdvice.Value) :=
  (Equiv.prodCongr (muEquiv offset) (Equiv.refl _)).trans
    (Equiv.prodCongrRight fun mu => AdapterBits.xorValue (quotient mu))

theorem muAdviceEquiv_mu (offset : ZMod p) (quotient : ZMod p → MdocAdvice.Value)
    (mask : ZMod p) (otp : MdocAdvice.Value) :
    (muAdviceEquiv offset quotient (mask,otp)).1 = offset+mask := rfl

theorem muAdviceEquiv_bits (offset : ZMod p) (quotient : ZMod p → MdocAdvice.Value)
    (mask : ZMod p) (otp : MdocAdvice.Value) (tree : Fin 2) (i : Fin 10) :
    MdocAdvice.bits (muAdviceEquiv offset quotient (mask,otp)).2 tree i =
      Bool.xor (MdocAdvice.bits (quotient (offset+mask)) tree i) (MdocAdvice.bits otp tree i) :=
  AdapterBits.xorValue_bits _ _ tree i

/-- Sampling this public pair directly is witness-free. Arbitrarily
adaptive quotient functions remain confined to the proof coupling. -/
theorem muAdvice_sameDistribution {Observed : Type} [DecidableEq Observed]
    (offset : ZMod p) (quotient : ZMod p → MdocAdvice.Value)
    (observe : ZMod p × MdocAdvice.Value → Observed) :
    LigeroFamily.SameDistribution
      (fun tape => observe (muAdviceEquiv offset quotient tape)) observe := by
  apply LigeroFamily.sameDistribution_of_equiv (muAdviceEquiv offset quotient)
  intro tape
  rfl

def rawMuAdviceEquiv (offset : ZMod p) (quotient : ZMod p → MdocAdvice.Value) :
    (ZMod p × (Fin 2 → AdapterBits.RawWord)) ≃ ((ZMod p × MdocAdvice.Value) × AdapterBits.Unused) :=
  (((Equiv.prodCongr (Equiv.refl _) AdapterBits.rawOtpEquiv).trans
    (Equiv.prodAssoc _ _ _).symm).trans
      (Equiv.prodCongr (muAdviceEquiv offset quotient) (Equiv.refl _)))

theorem rawMuAdviceEquiv_inverse_response (offset : ZMod p) (quotient : ZMod p → MdocAdvice.Value)
    (coins : (ZMod p × MdocAdvice.Value) × AdapterBits.Unused) :
    let raw := (rawMuAdviceEquiv offset quotient).symm coins
    (offset+raw.1,AdapterBits.xorValue (quotient (offset+raw.1)) (AdapterBits.rawOtpEquiv raw.2).1) = coins.1 :=
  congrArg Prod.fst ((rawMuAdviceEquiv offset quotient).apply_symm_apply coins)

theorem rawMuAdvice_sameDistribution {Observed : Type} [DecidableEq Observed]
    (offset : ZMod p) (quotient : ZMod p → MdocAdvice.Value)
    (observe : ZMod p × MdocAdvice.Value → Observed) :
    LigeroFamily.SameDistribution
      (fun tape => observe (rawMuAdviceEquiv offset quotient tape).1)
      (fun coins : (ZMod p × MdocAdvice.Value) × AdapterBits.Unused => observe coins.1) := by
  apply LigeroFamily.sameDistribution_of_equiv (rawMuAdviceEquiv offset quotient)
  intro tape
  rfl

end LfzkV2.Current.ZeroKnowledge.Frontend.Adapter
