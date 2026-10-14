import AffineAgreement.Basic
import Mathlib.Tactic.FieldSimp

/-! The elementary secant identity for affine word lines. -/
namespace AffineAgreement
variable {F : Type*} [Field F] [DecidableEq F]
namespace Internal

omit [DecidableEq F] in
theorem received_secant {n : ℕ} (u v : Word F n) (a b c : F)
    (hab : a ≠ b) :
    affineWord u v c =
      affineWord
        (affineWord u v a - fun i ↦
          a * ((b - a)⁻¹ *
            (affineWord u v b i - affineWord u v a i)))
        (fun i ↦ (b - a)⁻¹ *
          (affineWord u v b i - affineWord u v a i)) c := by
  funext i
  simp only [affineWord, Pi.sub_apply]
  field_simp [sub_ne_zero.mpr hab.symm]
  ring

end Internal
export Internal (received_secant)
end AffineAgreement
