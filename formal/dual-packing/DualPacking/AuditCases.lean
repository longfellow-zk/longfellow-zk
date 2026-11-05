import DualPacking.ArtinSchreierBackend

/-! # Security regression for the audited simplification

The linear verifier must genuinely allow an inconsistent Frobenius cell. This
example accepts a false target at a particular challenge while the original
Frobenius-checked verifier rejects. Thus the stronger soundness theorem cannot
be inheriting a Frobenius-consistency check hidden in its acceptance predicate.
-/

namespace DualPacking.ArtinSchreier.Audit

open Module
open scoped Classical

variable {K F I : Type*} [Field K] [Fintype K] [Field F] [Fintype F] [Algebra K F]
  [Fintype I] [DecidableEq I]

noncomputable def inconsistentFrobenius (e : Basis I K F) (k : I) : Instance K F I Unit where
  basis := e
  pivot := k
  words := fun _ => 0
  coefficients := fun _ _ => 0
  target := 1
  masks := fun _ => 0
  r := 0
  b := -e.traceDual k

theorem inconsistentFrobenius_false (e : Basis I K F) (k : I) :
    (inconsistentFrobenius e k).target ≠ (inconsistentFrobenius e k).trueValue := by
  simp [Instance.trueValue, value, inconsistentFrobenius, digit]

theorem inconsistentFrobenius_linear_accepts (e : Basis I K F) (k : I) :
    (inconsistentFrobenius e k).nativeLinearVerify (fun _ => 0) (Pi.single k 1) 0 := by
  simp [Instance.nativeLinearVerify, Instance.nativeOne, Instance.nativeTwo,
    Instance.targetCoeff, inconsistentFrobenius, traceF, Pi.single_apply, map_zero, map_one]

theorem inconsistentFrobenius_checked_rejects (e : Basis I K F) (k : I) :
    ¬(inconsistentFrobenius e k).nativeVerify (fun _ => 0) (Pi.single k 1) 0 := by
  intro h
  exact (e.traceDual.ne_zero k) (neg_eq_zero.mp (by simpa [inconsistentFrobenius] using h.2.symm))

end DualPacking.ArtinSchreier.Audit
