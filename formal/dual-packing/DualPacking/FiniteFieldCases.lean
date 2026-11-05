import DualPacking.AuditCases

/-! # A genuine odd-characteristic extension exercises the complete native verifier

This is a degree-six extension of the prime field with five elements. The
Frobenius map fixes embedded base elements and is demonstrably not squaring.
Both honest acceptance and the unchecked-cell adversarial regression are checked.
-/

namespace DualPacking.ArtinSchreier.FiniteFieldCases

open Module
open scoped Classical

local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

abbrev F := GaloisField 5 6

noncomputable local instance : Fintype F := Fintype.ofFinite F

noncomputable def basis : Basis (Fin 6) (ZMod 5) F :=
  (Module.finBasis (ZMod 5) F).reindex (finCongr (GaloisField.finrank 5 (by norm_num)))

noncomputable def honest : Instance (ZMod 5) F (Fin 6) Unit where
  basis := basis
  pivot := 0
  words := fun _ => 0
  coefficients := fun _ _ => 0
  target := 0
  masks := fun _ => 0
  r := algebraMap (ZMod 5) F 2
  b := algebraMap (ZMod 5) F 2

theorem frobenius_not_square :
    frobenius (ZMod 5) F honest.r ≠ honest.r ^ 2 := by
  change frobenius (ZMod 5) F (algebraMap (ZMod 5) F 2) ≠
    (algebraMap (ZMod 5) F 2) ^ 2
  rw [(frobenius (ZMod 5) F).commutes, ← map_pow]
  intro h
  have hbase := (algebraMap (ZMod 5) F).injective h
  norm_num at hbase
  have hval := congrArg ZMod.val hbase
  norm_num [ZMod.val_ofNat] at hval

theorem honest_accepts (delta : Fin 6 → F) :
    honest.nativeLinearVerify honest.honestU delta (honest.honestA delta) := by
  apply honest.native_linear_completeness
  · simp [honest, Instance.trueValue, value, digit]
  · exact (frobenius (ZMod 5) F).commutes 2

noncomputable def malicious : Instance (ZMod 5) F (Fin 6) Unit :=
  Audit.inconsistentFrobenius basis 0

theorem malicious_false : malicious.target ≠ malicious.trueValue :=
  Audit.inconsistentFrobenius_false basis 0

theorem malicious_accepts_one_challenge :
    malicious.nativeLinearVerify (fun _ => 0) (Pi.single 0 1) 0 :=
  Audit.inconsistentFrobenius_linear_accepts basis 0

theorem malicious_rejects_checked :
    ¬malicious.nativeVerify (fun _ => 0) (Pi.single 0 1) 0 :=
  Audit.inconsistentFrobenius_checked_rejects basis 0

/-- Certificate for the same native verifier on this actual odd-characteristic field. -/
theorem malicious_soundness (U : Fin 6 → F) (respondA : (Fin 6 → F) → F) :
    malicious.nativeLinearAcceptanceProbability U respondA ≤ 1 / (5 : ℚ) ^ 6 :=
  linear_soundness_prime_degree_six malicious U respondA malicious_false

end DualPacking.ArtinSchreier.FiniteFieldCases
