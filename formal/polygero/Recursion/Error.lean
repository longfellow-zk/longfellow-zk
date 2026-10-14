import polygero.Recursion.Certificate

/-! Canonical recursive error and its range; independent of the counting proof. -/

namespace RecursivePolygero.Protocol.ProfileProof
open Finset ProfileAnalysis
attribute [local instance] Classical.propDecidable
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {I : Instance F} {protocol : Protocol I} {p : ProfileCertificate I}

noncomputable def error : {I : Instance F} → {protocol : Protocol I} →
    {p : ProfileCertificate I} → protocol.ProfileProof p → ℚ
  | _, _, _, .terminal p => p.error
  | _, _, _, .step p rest => p.error+(1-p.error)*rest.error

omit [DecidableEq F] in
theorem error_bounds (r : protocol.ProfileProof p) : 0 ≤ r.error ∧ r.error < 1 := by
  induction r with
  | terminal p => exact ⟨p.error_nonneg,p.error_lt_one⟩
  | step p rest ih =>
    have hp0 := p.error_nonneg
    have hp1 : p.error < 1 := p.error_lt_one
    have hc0 := ih.1
    change 0 ≤ p.error+(1-p.error)*rest.error ∧ p.error+(1-p.error)*rest.error < 1
    constructor
    · positivity
    · have := mul_pos (sub_pos.mpr hp1) (sub_pos.mpr ih.2)
      nlinarith


noncomputable def localErrors : {I : Instance F} → {protocol : Protocol I} →
    {p : ProfileCertificate I} → protocol.ProfileProof p → List ℚ
  | _, _, _, .terminal p => [p.error]
  | _, _, _, .step p rest => p.error :: rest.localErrors

omit [Fintype F] [DecidableEq F] in
theorem error_eq_product (r : protocol.ProfileProof p) :
    r.error = 1-(r.localErrors.map (1-·)).prod := by
  induction r with
  | terminal p => simp [error,localErrors]
  | step p rest ih =>
    simp only [error,localErrors,List.map_cons,List.prod_cons,ih]
    ring

omit [DecidableEq F] in
theorem error_le_sum (r : protocol.ProfileProof p) : r.error ≤ r.localErrors.sum := by
  induction r with
  | terminal p => simp [error,localErrors]
  | step p rest ih =>
    have hp := p.error_nonneg
    have hr := rest.error_bounds.1
    simp only [error,localErrors,List.sum_cons]
    nlinarith

end RecursivePolygero.Protocol.ProfileProof
