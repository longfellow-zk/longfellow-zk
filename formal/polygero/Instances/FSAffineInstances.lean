import polygero.Recursion.AffineBlock
import polygero.Instances.FSTwoLevel

namespace RecursivePolygero.Instances.FSTwoLevel

open Bcs.AffineBlock FiatShamir.TwoLevel
open scoped Classical

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

def certifiedRate (schedule : Schedule) : Rate :=
  Rate.diagonal (1 / (2^(data schedule).bits : ℚ)) (by positivity)

/-- The two kernel-checked schedules instantiate the interface with
diagonal coefficients 2^-123 and 2^-124, respectively. -/
theorem affine_soundness {I : Instance F} (child : Child I) (schedule : Schedule)
    (h0 : Geometry I (data schedule)) (h1 : Geometry child.instance (childData schedule))
    (hq : Nat.card F = fieldSize) (sigma : I.layer.Statement)
    (hfalse : ∀ witness, ¬ I.layer.satisfies sigma witness)
    {N : ℕ} (tree : Merkle.RandomOracle.Tree (HashInput child) (Answer child) (Proof child) N) :
    Certificate (fun H => accepts child sigma H (tree.run H).1)
      (fun _ => (N : ℚ)) (certifiedRate schedule) := by
  apply Certificate.of_budget _ _ (N : ℚ) (by positivity)
  have h := (certifiedSoundness child schedule h0 h1 hq sigma hfalse tree).trans
    (mul_le_mul_of_nonneg_left (checked schedule).2.2.1 (by positivity))
  simpa only [certifiedRate, Rate.diagonal, add_mul, one_mul, mul_comm, add_comm] using h

end RecursivePolygero.Instances.FSTwoLevel
