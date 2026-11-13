import LfzkV2.Current.MdocAdvice
import LfzkV2.Current.AdapterTree
import Mathlib.Data.Nat.Bitwise

/-! Canonical little-endian words and the adapter's one-time pads. Each
`Otp<10>` is drawn from exactly two fresh bytes, as `Otp::sample` does, and
masked to its low ten bits. Only those ten bits are committed or used. Keeping
the six unused high bits of each pad as an inert coordinate makes the raw-byte
coupling bijective without assigning a nonuniform distribution to canonical
masked words. -/
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

/-- `MaskedWord::mask`, separately for each tree's word. -/
def xorValue (clear : MdocAdvice.Value) : MdocAdvice.Value ≃ MdocAdvice.Value :=
  Equiv.piCongrRight fun tree => xorEquiv (clear tree)

theorem xorValue_bits (clear pad : MdocAdvice.Value) (tree : Fin 2) (i : Fin 10) :
    MdocAdvice.bits (xorValue clear pad) tree i =
      Bool.xor (MdocAdvice.bits clear tree i) (MdocAdvice.bits pad tree i) :=
  xorEquiv_bits (clear tree) (pad tree) i.val

theorem xorValue_symm_bits (clear masked : MdocAdvice.Value) (tree : Fin 2) (i : Fin 10) :
    MdocAdvice.bits ((xorValue clear).symm masked) tree i =
      Bool.xor (MdocAdvice.bits masked tree i) (MdocAdvice.bits clear tree i) := by
  change ((masked tree).val ^^^ (clear tree).val).testBit i.val = _
  exact Nat.testBit_xor _ _ _

/-- The two raw bytes of one pad, as a little-endian sixteen-bit integer. -/
abbrev RawWord := Fin (2^16)

/-- The six high bits of one pad's raw bytes; they are discarded. -/
abbrev Unused := Fin 2 → Fin (2^6)

/-- One pad's raw bytes: its masked ten-bit value and its discarded bits. -/
def rawWordEquiv : RawWord ≃ MdocAdvice.Word × Fin (2^6) :=
  ((finCongr (by norm_num : 2^16 = 2^6*2^10)).trans finProdFinEquiv.symm).trans
    (Equiv.prodComm _ _)

theorem rawWord_low (raw : RawWord) : (rawWordEquiv raw).1.val = raw.val % 2^10 := rfl

/-- Both pads, in sampling order: exactly two fresh bytes for each word. -/
def rawOtpEquiv : (Fin 2 → RawWord) ≃ MdocAdvice.Value × Unused :=
  (Equiv.piCongrRight fun _ => rawWordEquiv).trans (Equiv.arrowProdEquivProdArrow _ _ _)

theorem rawOtp_bits (raw : Fin 2 → RawWord) (tree : Fin 2) (i : Fin 10) :
    MdocAdvice.bits (rawOtpEquiv raw).1 tree i = (raw tree).val.testBit i.val := by
  unfold MdocAdvice.bits
  change (rawWordEquiv (raw tree)).1.val.testBit i.val = _
  rw [rawWord_low]
  simpa only [i.isLt,decide_true,Bool.true_and] using
    Nat.testBit_mod_two_pow (raw tree).val 10 i.val

end LfzkV2.Current.ZeroKnowledge.Frontend.AdapterBits
