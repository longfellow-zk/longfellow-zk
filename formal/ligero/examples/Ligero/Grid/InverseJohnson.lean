import examples.Ligero.Certificate
import JBAgreement.InverseEtaCertificate

/-! Shared rational Johnson parameter optimization for all verifier variants.
Searches suggest denominators; every returned value and local line bound is
independently checked by the finite certificate before it reaches the IOP. -/
namespace Ligero.Examples.Grid
open LigeroFamily

/-- Geometry-only admissibility for eta = 1 / denominator. -/
def inverseEtaGeometry (n k agreement denominator : ℕ) : Bool :=
  (4 * n ≤ agreement * denominator) &&
    ((k - 1) * n * denominator ^ 2 ≤ (agreement * denominator - 4 * n) ^ 2)

def inverseEtaSearch (n k agreement : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, hi => hi
  | fuel + 1, lo, hi =>
      if lo < hi then
        let mid := (lo + hi) / 2
        if inverseEtaGeometry n k agreement mid then
          inverseEtaSearch n k agreement fuel lo mid
        else inverseEtaSearch n k agreement fuel (mid + 1) hi
      else hi

/-- Candidate least admissible denominator at actual agreement. Its validity
is checked separately; no theorem assumes correctness of the search. -/
def Certificate.inverseEtaDenominator (c : Certificate) (agreement : ℕ) : ℕ :=
  inverseEtaSearch c.n c.k agreement 64 4 c.n

def Certificate.inverseJohnsonLocalLineBound (c : Certificate)
    (denominators : ℕ → ℕ) (agreement : ℕ) : ℕ :=
  Nat.ceil (JBAgreement.johnsonThresholdInverseQ c.k c.n (c.n - agreement)
    (denominators agreement)) - 1

def Certificate.inverseJohnsonConditions (c : Certificate) (outerDenominator : ℕ)
    (denominators : ℕ → ℕ) : Bool :=
  JBAgreement.inverseEtaConditionsBool c.n c.k c.e outerDenominator c.lineBound c.fieldSize &&
    (List.range (c.n + 1)).all (fun a =>
      if c.n - c.e ≤ a then
        JBAgreement.inverseEtaConditionsBool c.n c.k (c.n - a) (denominators a)
          (c.inverseJohnsonLocalLineBound denominators a) c.fieldSize
      else true) &&
    (3 * c.g < c.d - c.e) && (c.g + 1 < c.fieldSize) &&
    decide (0 < CodingTheory.InterleavedJohnson.denominator c.n c.d (c.e + c.g))

/-- The complete checked per-agreement denominator family reaches the same
proximity-gap interface used by V1, V2 and V3. -/
theorem Certificate.inverseJohnsonLineConditions (c : Certificate)
    (outerDenominator : ℕ) (denominators : ℕ → ℕ)
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {C : CodingTheory.LinearCode F c.n}
    (P : JBAgreement.RSPresentation c.n c.k C)
    (hfield : Fintype.card F = c.fieldSize)
    (h : c.inverseJohnsonConditions outerDenominator denominators = true) :
    IntegratedSelectedMCALineConditions C c.fieldSize c.e c.g c.d c.lineBound
      (c.inverseJohnsonLocalLineBound denominators) := by
  simp only [Certificate.inverseJohnsonConditions, Bool.and_eq_true, decide_eq_true_eq] at h
  have hlocal (a : ℕ) (ha : c.n - c.e ≤ a) (han : a ≤ c.n) :
      JBAgreement.inverseEtaConditionsBool c.n c.k (c.n - a) (denominators a)
        (c.inverseJohnsonLocalLineBound denominators a) c.fieldSize = true := by
    have hall := h.1.1.1.2
    rw [List.all_eq_true] at hall
    have hmem : a ∈ List.range (c.n + 1) := by simp; omega
    simpa [ha] using hall a hmem
  exact {
    outer := {
      line := JBAgreement.lineFailureBound_of_inverseEtaConditions P hfield
        (JBAgreement.inverseEtaConditions_of_bool h.1.1.1.1)
      punctured := ⟨h.1.1.2, h.1.2⟩
      johnson := ⟨h.2⟩ }
    localLine := fun a ha han =>
      JBAgreement.lineFailureBound_of_inverseEtaConditions P hfield
        (JBAgreement.inverseEtaConditions_of_bool (hlocal a ha han))
    local_three_radius := by intro a ha han; have := h.1.1.2; omega }
end Ligero.Examples.Grid
