import LfzkV1.SoundnessAudit
import examples.Ligero.Longfellow.OptimizedIOPCertificates

/-!
# Opening tails for the four v7 hash geometries

All calculations are cross-multiplied over natural numbers. The four
puncturing radii are analysis choices. The verifier still opens 132 columns.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace LfzkV1.OpeningGeometry125

open LfzkV1.SoundnessAudit
open Ligero.Examples.Grid (Certificate)
open Ligero.Examples.Grid.LongfellowProfiledExtraction
open Ligero.Examples.Grid.LongfellowProfiledExtraction.Optimized

private def original (i : Fin 4) : Result :=
  match i.val with
  | 0 => v7Hash1_v1
  | 1 => v7Hash2_v1
  | 2 => v7Hash3_v1
  | _ => v7Hash4_v1

def result (i : Fin 4) : Result :=
  let base := original i
  {base with certificate := {
    base.certificate with g := if i.val = 1 then 14 else 15
                          m := 4 * base.certificate.m }}

private abbrev n (i : Fin 4) : ℕ := (result i).certificate.n
private abbrev k (i : Fin 4) : ℕ := (result i).certificate.k
private abbrev openings (i : Fin 4) : ℕ := (result i).certificate.openings
private abbrev punctures (i : Fin 4) : ℕ := (result i).certificate.g

theorem deployedGeometry (i : Fin 4) :
    n i = (v7HashRow i).params.row.n ∧ k i = (v7HashRow i).params.row.k ∧
    openings i = (v7HashRow i).params.row.openings ∧
    (result i).certificate.fieldSize = 2 ^ 128 := by
  fin_cases i <;> decide +kernel

theorem variant (i : Fin 4) : (result i).variant = .v1 := by
  fin_cases i <;> rfl

private def cliqueCheck (n e g d m : ℕ) : Prop :=
  let lo := (m * (n - e)) / n
  let hiCount := (m * (n - e)) % n
  3 ≤ m ∧ n - d < n - e ∧
    (SelectedMCA.directLineOccupancyBound n g - 2) * Nat.fast_choose m 2 / 3 *
        ((n - e) - (n - d)) + Nat.fast_choose m 3 * (n - d) <
      (n - hiCount) * Nat.fast_choose lo 3 + hiCount * Nat.fast_choose (lo + 1) 3

private instance (n e g d m : ℕ) : Decidable (cliqueCheck n e g d m) := by
  unfold cliqueCheck
  infer_instance

private theorem cliqueCheck_iff (n e g d m : ℕ) :
    SelectedMCA.DirectCliqueCondition n e g d m ↔ cliqueCheck n e g d m := by
  simp only [SelectedMCA.DirectCliqueCondition, SelectedMCA.simpleCliqueUpperNat,
    AffineAgreement.balanced_choose_three, cliqueCheck, Nat.choose_eq_fast_choose]

private def fastSearch (n e g d : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _lo, hi => hi
  | fuel + 1, lo, hi =>
    if lo < hi then
      let mid := (lo + hi) / 2
      if cliqueCheck n e g d mid then fastSearch n e g d fuel lo mid
      else fastSearch n e g d fuel (mid + 1) hi
    else hi

private theorem search_eq (n e g d fuel lo hi : ℕ) :
    Ligero.Examples.Grid.binaryCliqueSearch n e g d fuel lo hi = fastSearch n e g d fuel lo hi := by
  induction fuel generalizing lo hi with
  | zero => rfl
  | succ fuel ih =>
    simp only [Ligero.Examples.Grid.binaryCliqueSearch, fastSearch]
    split <;> rename_i h
    · have hprop := cliqueCheck_iff n e g d ((lo + hi) / 2)
      by_cases hmid : cliqueCheck n e g d ((lo + hi) / 2)
      · simp [hmid, hprop.mpr hmid, ih]
      · simp [hmid, hprop.not.mpr hmid, ih]
    · rfl

def fastLocalM (c : Certificate) (a : ℕ) : ℕ :=
  if 3 * (c.n - a) < c.d then c.m
  else fastSearch c.n (c.n - a) c.g c.d 64 3 (max c.m c.refinedLocalM)

private theorem localM_eq (c : Certificate) (a : ℕ) : c.integratedLocalM a = fastLocalM c a := by
  simp only [Certificate.integratedLocalM, fastLocalM, search_eq]

theorem integratedLocalLineBound_eq (c : Certificate) (a : ℕ) :
    c.integratedLocalLineBound a = fastLocalM c a - 1 := by
  simp only [Certificate.integratedLocalLineBound, SelectedMCA.directLineFailureBound, localM_eq]

private def localUpper (c : Certificate) (a : ℕ) : ℕ :=
  if 3 * (c.n - a) < c.d then c.m else max c.m c.refinedLocalM

private theorem fastSearch_valid (n e g d fuel lo hi : ℕ) (h : cliqueCheck n e g d hi) :
    cliqueCheck n e g d (fastSearch n e g d fuel lo hi) := by
  induction fuel generalizing lo hi with
  | zero => exact h
  | succ fuel ih =>
    simp only [fastSearch]
    split
    · split
      · exact ih _ _ ‹cliqueCheck n e g d ((lo + hi) / 2)›
      · exact ih _ _ h
    · exact h

private def checkLocalBlock (c : Certificate) (block : ℕ) : Bool :=
  (List.range 64).all fun j =>
    let a := 64 * block + j
    if c.n - c.e ≤ a ∧ a ≤ c.n then
      decide (cliqueCheck c.n (c.n - a) c.g c.d (localUpper c a))
    else true

private theorem localDirect_of_blocks (c : Certificate)
    (h : (List.range (c.n / 64 + 1)).all (checkLocalBlock c) = true)
    (a : ℕ) (ha : c.n - c.e ≤ a) (hn : a ≤ c.n) :
    SelectedMCA.DirectCliqueCondition c.n (c.n - a) c.g c.d (c.integratedLocalM a) := by
  rw [List.all_eq_true] at h
  have hblock := h (a / 64) (List.mem_range.mpr (by omega))
  unfold checkLocalBlock at hblock
  rw [List.all_eq_true] at hblock
  have hentry := hblock (a % 64) (List.mem_range.mpr (by omega))
  have hvalid : c.n - c.e ≤ a ∧ a ≤ c.n := ⟨ha, hn⟩
  simp only [Nat.div_add_mod, if_pos hvalid, decide_eq_true_eq] at hentry
  rw [cliqueCheck_iff, localM_eq]
  by_cases hb : 3 * (c.n - a) < c.d
  · simpa only [fastLocalM, hb, if_true, localUpper] using hentry
  · simp only [fastLocalM, hb, if_false]
    apply fastSearch_valid
    simpa only [localUpper, hb, if_false] using hentry

theorem parameters (i : Fin 4) : (result i).ParametersValid := by
  let c := (result i).certificate
  have hgeom : 0 < c.k ∧ c.k ≤ c.n ∧ c.d = c.n - c.k + 1 ∧ 2 * c.k ≤ c.n := by
    fin_cases i <;> decide +kernel
  have hmask₁ : c.maskStart ≤ c.v1Threshold := by fin_cases i <;> decide +kernel
  have hmask₂ : 2 * c.k - 1 < c.maskStart := by fin_cases i <;> decide +kernel
  have hmask₃ : CodingTheory.HahnDelsarte.certificateValid c.n c.maskStart
      (2 * c.k - 1) c.hahnMask = true := by
    fin_cases i
    · exact HahnMask.v7Hash1_valid
    · exact HahnMask.v7Hash2_valid
    · exact HahnMask.v7Hash3_valid
    · exact HahnMask.v7Hash4_valid
  have hmask : c.maskValid = true := by simp [Certificate.maskValid, hmask₁, hmask₂, hmask₃]
  have hroute : (result i).route = .triples := by fin_cases i <;> rfl
  simp only [Result.ParametersValid, variant, hroute, if_true]
  refine ⟨hgeom.1, hgeom.2.1, hgeom.2.2.1, hgeom.2.2.2, hmask, ?_⟩
  have hthree : 3 * c.g < c.d - c.e := by fin_cases i <;> decide +kernel
  exact {
    toSelectedMCAParameterConditions :=
      ⟨⟨by rw [cliqueCheck_iff]; fin_cases i <;> decide +kernel⟩,
        ⟨hthree, by fin_cases i <;> decide +kernel⟩,
        ⟨by fin_cases i <;> decide +kernel⟩⟩
    localDirect := localDirect_of_blocks c (by fin_cases i <;> decide +kernel)
    local_three_radius := by
      intro a ha _
      dsimp only [c] at hthree
      omega }

theorem liftCount (i : Fin 4) : (result i).certificate.listSize ≤ 2 := by
  fin_cases i <;> decide +kernel

def secondarySize (i : Fin 4) : ℕ := (n i + (k i - 1)) / 2

theorem uniqueHighResponse (i : Fin 4) :
    secondarySize i + (2 * k i - 1) < 2 * (result i).certificate.maskStart := by
  fin_cases i <;> decide +kernel

theorem ambiguousTail (i : Fin 4) :
    let r := openings i
    let b := r - 2 * punctures i
    2 ^ 202 * ((k i - 1).choose b * (n i - b).choose (r - b)) ≤ (n i).choose r := by
  dsimp only
  simp only [Nat.choose_eq_descFactorial_div_factorial]
  fin_cases i <;> decide +kernel

theorem openingFirstTail (i : Fin 4) :
    let r := openings i
    let b := r - punctures i
    2 ^ 32 * ((secondarySize i).choose b * (n i - b).choose (r - b)) ≤
      (n i).choose r := by
  dsimp only
  simp only [Nat.choose_eq_descFactorial_div_factorial]
  fin_cases i <;> decide +kernel

theorem initialFirstTail (i : Fin 4) :
    2 ^ 108 * (secondarySize i + punctures i).choose (openings i) ≤
      (n i).choose (openings i) := by
  simp only [Nat.choose_eq_descFactorial_div_factorial]
  fin_cases i <;> decide +kernel

end LfzkV1.OpeningGeometry125
