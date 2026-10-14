import JBAgreement.LigeroCode
import LigeroFamily.Soundness.PolicySelectedMCA
import Ligero.V1.Soundness.V1Profile

/-! Shared geometry and checked arithmetic for scalar extraction certificates. -/

namespace Ligero.Examples.Grid

open LigeroFamily

set_option maxHeartbeats 1000000

structure Certificate where
  n : ℕ
  k : ℕ
  d : ℕ
  e : ℕ
  g : ℕ
  m : ℕ
  fieldBits : ℕ
  targetBits : ℕ
  openings : ℕ

  cutoff : ℕ := 0

  localM : ℕ := 0

  fieldOrder : ℕ := 0

abbrev V1Certificate := Certificate
def Certificate.fieldSize (c : Certificate) : ℕ :=
  if c.fieldOrder = 0 then 2 ^ c.fieldBits else c.fieldOrder

def Certificate.lineBound (c : Certificate) : ℕ :=
  SelectedMCA.directLineFailureBound c.m

def Certificate.refinedLocalM (c : Certificate) : ℕ :=
  if c.localM = 0 then c.m else c.localM

def binaryCliqueSearch (n radius g d : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _lo, hi => hi
  | fuel + 1, lo, hi =>
      if lo < hi then
        let mid := (lo + hi) / 2
        if decide (SelectedMCA.DirectCliqueCondition n radius g d mid) then
          binaryCliqueSearch n radius g d fuel lo mid
        else
          binaryCliqueSearch n radius g d fuel (mid + 1) hi
      else hi

def Certificate.integratedLocalM (c : Certificate) (a : ℕ) : ℕ :=
  if 3 * (c.n - a) < c.d then c.m
  else binaryCliqueSearch c.n (c.n - a) c.g c.d 64 3
    (max c.m c.refinedLocalM)

def Certificate.integratedLocalLineBound (c : Certificate) (a : ℕ) : ℕ :=
  SelectedMCA.directLineFailureBound (c.integratedLocalM a)

def Certificate.IntegratedLocalPointValid (c : Certificate) (a : ℕ) : Prop :=
  SelectedMCA.DirectCliqueCondition c.n (c.n - a) c.g c.d
      (c.integratedLocalM a) ∧
    (¬3 * (c.n - a) < c.d →
      ¬SelectedMCA.DirectCliqueCondition c.n (c.n - a) c.g c.d
        (c.integratedLocalM a - 1))

def Certificate.integratedLocalValidBool (c : Certificate) : Bool :=
  (List.range (c.n + 1)).all fun a ↦
    if c.n - c.e ≤ a then
      @decide (c.IntegratedLocalPointValid a) (by
        unfold Certificate.IntegratedLocalPointValid
        infer_instance)
    else true

theorem Certificate.integratedLocalPointValid_of_bool (c : Certificate)
    (h : c.integratedLocalValidBool = true) (a : ℕ)
    (ha : c.n - c.e ≤ a) (han : a ≤ c.n) :
    c.IntegratedLocalPointValid a := by
  unfold Certificate.integratedLocalValidBool at h
  rw [List.all_eq_true] at h
  have hmem : a ∈ List.range (c.n + 1) := by simp; omega
  have hp := h a hmem
  simp only [if_pos ha] at hp
  exact @of_decide_eq_true (c.IntegratedLocalPointValid a) (by
    unfold Certificate.IntegratedLocalPointValid
    infer_instance) hp

def Certificate.listSize (c : Certificate) : ℕ :=
  CodingTheory.InterleavedJohnson.listBound c.n c.d (c.e + c.g)

def Certificate.v1Threshold (c : Certificate) : ℕ :=
  Nat.sqrt (c.n * (2 * c.k - 1)) + 1

def Certificate.optimizedFailureDenominator (c : Certificate) : ℕ :=
  SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator c.fieldSize c.g

def Certificate.johnsonLocalLineBound
    (c : Certificate) (etaBits agreement : ℕ) : ℕ :=
  Nat.ceil (JBAgreement.johnsonThresholdQ c.k c.n (c.n - agreement) etaBits) - 1

namespace V1Certificate

theorem v1JohnsonRange (c : V1Certificate)
    (hkpos : 0 < c.k) (hresponse : 2 * c.k ≤ c.n)
    {F : Type*} [_root_.Field F] {openings w : ℕ}
    (C : MultiplicativeCode F openings w c.n) (hk : C.k = c.k) :
    Ligero.V1.V1JohnsonRange C c.v1Threshold := by
  unfold Certificate.v1Threshold
  apply Ligero.V1.V1JohnsonRange.ofSquare C
    (Nat.sqrt (c.n * (2 * c.k - 1)) + 1)
  · omega
  · rw [hk]
    exact hresponse
  · rw [hk]
    have hsqrt : 2 * c.k - 1 ≤ Nat.sqrt (c.n * (2 * c.k - 1)) := by
      apply Nat.le_sqrt.mpr
      have hcutoff : 2 * c.k - 1 ≤ c.n := by omega
      simpa [Nat.mul_comm] using
        Nat.mul_le_mul_right (2 * c.k - 1) hcutoff
    omega
  · rw [hk]
    simpa [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt (c.n * (2 * c.k - 1))

end V1Certificate

namespace V1Certificate

end V1Certificate

def Certificate.johnsonConditions (c : Certificate) (etaBits : ℕ) : Bool :=
  JBAgreement.johnsonConditionsBool c.n c.k c.e etaBits c.lineBound
      c.fieldSize &&
    (List.range (c.n + 1)).all (fun a ↦
      if c.n - c.e ≤ a then
        JBAgreement.johnsonConditionsBool c.n c.k (c.n - a)
          etaBits (c.johnsonLocalLineBound etaBits a) c.fieldSize
      else true) &&
    (3 * c.g < c.d - c.e) && (c.g + 1 < c.fieldSize) &&
    decide (0 < CodingTheory.InterleavedJohnson.denominator c.n c.d (c.e + c.g))

theorem Certificate.johnsonLineConditions (c : Certificate) {etaBits : ℕ}
    {F : Type*} [_root_.Field F] [Fintype F] [DecidableEq F]
    {C : CodingTheory.LinearCode F c.n}
    (P : JBAgreement.RSPresentation c.n c.k C)
    (hfield : Fintype.card F = c.fieldSize)
    (h : c.johnsonConditions etaBits = true) :
    LigeroFamily.IntegratedSelectedMCALineConditions C c.fieldSize c.e c.g c.d
      c.lineBound (c.johnsonLocalLineBound etaBits) := by
  simp only [Certificate.johnsonConditions, Bool.and_eq_true,
    decide_eq_true_eq] at h
  have hlocal (a : ℕ) (ha : c.n - c.e ≤ a) (han : a ≤ c.n) :
      JBAgreement.johnsonConditionsBool c.n c.k (c.n - a) etaBits
        (c.johnsonLocalLineBound etaBits a) c.fieldSize = true := by
    have hall := h.1.1.1.2
    rw [List.all_eq_true] at hall
    have hmem : a ∈ List.range (c.n + 1) := by simp; omega
    simpa [ha] using hall a hmem
  exact {
    outer := {
      line := JBAgreement.lineFailureBound_of_johnsonConditions P hfield
        (JBAgreement.johnsonConditions_of_bool h.1.1.1.1)
      punctured := ⟨h.1.1.2, h.1.2⟩
      johnson := ⟨h.2⟩ }
    localLine := fun a ha han ↦
      JBAgreement.lineFailureBound_of_johnsonConditions P hfield
        (JBAgreement.johnsonConditions_of_bool (hlocal a ha han))
    local_three_radius := by
      intro a ha han
      have houter := h.1.1.2
      omega }

def Certificate.conditions (c : Certificate) : Prop :=
  IntegratedSelectedMCAParameterConditions c.fieldSize c.n c.e c.g c.d c.m
    c.integratedLocalM

theorem Certificate.conditions_of_checked (c : Certificate)
    (hdirect : SelectedMCA.DirectCliqueCondition c.n c.e c.g c.d c.m)
    (hthree : 3 * c.g < c.d - c.e)
    (hfield : c.g + 1 < c.fieldSize)
    (hdenominator : 0 < CodingTheory.InterleavedJohnson.denominator
      c.n c.d (c.e + c.g))
    (hlocal : c.integratedLocalValidBool = true) : c.conditions := by
  exact {
    toSelectedMCAParameterConditions :=
      ⟨⟨hdirect⟩, ⟨hthree, hfield⟩, ⟨hdenominator⟩⟩
    localDirect := fun a ha han ↦
      (c.integratedLocalPointValid_of_bool hlocal a ha han).1
    local_three_radius := by
      intro a ha han
      omega }

end Ligero.Examples.Grid
