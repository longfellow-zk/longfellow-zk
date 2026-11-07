import LfzkV2.Current.ZeroKnowledge.FrontendSelection
import LfzkV2.Current.MdocAdvice
import LfzkV2.Current.AdapterTree
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Bitwise

/-! Canonical little-endian words and the adapter's one-time pad.  Only
twenty of the twenty-four sampled OTP bits are committed or used. Keeping
the unused four bits as an inert coordinate makes the raw-byte coupling
bijective without assigning a nonuniform distribution to canonical advice. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.AdapterBits
open scoped Classical

def wordEquiv (n : ℕ) : (Fin n → Bool) ≃ Fin (2^n) :=
  (Equiv.piCongrRight fun _ => finTwoEquiv.symm).trans finFunctionFinEquiv

theorem wordEquiv_decode (n : ℕ) (word : Fin (2^n)) (i : Fin n) :
    (wordEquiv n).symm word i = word.val.testBit i.val := by
  simp [wordEquiv,finFunctionFinEquiv,finTwoEquiv,Nat.testBit_eq_decide_div_mod_eq,
    Bool.beq_eq_decide_eq,Fin.ext_iff]

theorem wordEquiv_value (n : ℕ) (bits : Fin n → Bool) :
    (wordEquiv n bits).val = ∑ i, if bits i then 2^i.val else 0 := by
  simp only [wordEquiv,Equiv.trans_apply,finFunctionFinEquiv_apply,Equiv.piCongrRight_apply]
  apply Finset.sum_congr rfl
  intro i _
  cases h : bits i <;> simp [finTwoEquiv,h]

theorem binaryValue_ofFn {n : ℕ} (bits : Fin n → Bool) :
    Current.Adapter.Tree.binaryValue (List.ofFn bits) = ∑ i, if bits i then 2^i.val else 0 := by
  induction n with
  | zero => simp [Current.Adapter.Tree.binaryValue]
  | succ n ih =>
      rw [List.ofFn_succ,Current.Adapter.Tree.binaryValue,ih,Fin.sum_univ_succ]
      simp only [Fin.val_zero,pow_zero,Fin.val_succ,pow_succ]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      cases bits i.succ <;> simp [Nat.mul_comm]

theorem binaryValue_word {n : ℕ} (word : Fin (2^n)) :
    Current.Adapter.Tree.binaryValue (List.ofFn fun i : Fin n => word.val.testBit i.val) = word.val := by
  have h := wordEquiv_value n ((wordEquiv n).symm word)
  simp only [Equiv.apply_symm_apply] at h
  rw [binaryValue_ofFn]
  simpa only [wordEquiv_decode] using h.symm

def xorEquiv {n : ℕ} (clear : Fin (2^n)) : Fin (2^n) ≃ Fin (2^n) where
  toFun pad := ⟨pad.val ^^^ clear.val,Nat.xor_lt_two_pow pad.isLt clear.isLt⟩
  invFun masked := ⟨masked.val ^^^ clear.val,Nat.xor_lt_two_pow masked.isLt clear.isLt⟩
  left_inv _ := Fin.ext (by simp)
  right_inv _ := Fin.ext (by simp)

theorem xorEquiv_bits {n : ℕ} (clear pad : Fin (2^n)) (i : ℕ) :
    (xorEquiv clear pad).val.testBit i = Bool.xor (clear.val.testBit i) (pad.val.testBit i) := by
  change (pad.val ^^^ clear.val).testBit i = _
  simp only [Nat.testBit_xor,Bool.xor_comm]

def packedQuotients (quotients : Fin 2 → Fin (2^10)) : MdocAdvice.Value :=
  ⟨(quotients 0).val+2^10*(quotients 1).val,by
    have h0 := (quotients 0).isLt
    have h1 := (quotients 1).isLt
    norm_num at h0 h1 ⊢
    omega⟩

theorem packedQuotients_bits (quotients : Fin 2 → Fin (2^10)) (tree : Fin 2) (i : Fin 10) :
    MdocAdvice.bits (packedQuotients quotients) tree i = (quotients tree).val.testBit i.val := by
  have h := Nat.testBit_two_pow_mul_add (quotients 1).val (quotients 0).isLt
  have hi := i.isLt
  fin_cases tree
  · simpa [MdocAdvice.bits,packedQuotients,Nat.add_comm,hi] using h i.val
  · have hn : ¬10+i.val < 10 := by omega
    simpa [MdocAdvice.bits,packedQuotients,Nat.add_comm,hn] using h (10+i.val)

def rawOtpEquiv : Fin (2^24) ≃ MdocAdvice.Value × Fin 16 :=
  ((finCongr (by norm_num : 2^24 = 16*(2^20))).trans finProdFinEquiv.symm).trans
    (Equiv.prodComm _ _)

theorem rawOtp_low (raw : Fin (2^24)) : (rawOtpEquiv raw).1.val = raw.val % 2^20 := rfl

theorem rawOtp_bits (raw : Fin (2^24)) (tree : Fin 2) (i : Fin 10) :
    MdocAdvice.bits (rawOtpEquiv raw).1 tree i = raw.val.testBit (10*tree.val+i.val) := by
  have ht := tree.isLt
  have hi := i.isLt
  have h : 10*tree.val+i.val < 20 := by omega
  unfold MdocAdvice.bits
  rw [rawOtp_low]
  simpa only [h,decide_true,Bool.true_and] using
    Nat.testBit_mod_two_pow raw.val 20 (10*tree.val+i.val)

end LfzkV2.Current.ZeroKnowledge.Frontend.AdapterBits
