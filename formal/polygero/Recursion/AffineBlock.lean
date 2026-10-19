import Bcs.AffineBlock
import polygero.Recursion.FSListBound
import polygero.Benchmarks.FSTwoLevel

/-! Two-level Polygero as an affine block. These are whole-protocol
budget certificates. They retain the proved list-bound coefficient;
no incoming-envelope consumption assumption is silently added. -/

namespace RecursivePolygero.FiatShamir.TwoLevel

open Bcs.AffineBlock ProfileAnalysis Merkle.RandomOracle
open scoped Classical

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {I : Instance F} (child : Child I)
variable (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)

omit [Fintype F] [DecidableEq F] in
theorem listBudget_nonneg : 0 ≤ listBudget child p cp := by
  unfold listBudget
  exact add_nonneg (add_nonneg (add_nonneg (listError_nonneg I p)
    (mul_nonneg (Nat.cast_nonneg _) p.threshold_nonneg))
    (listError_nonneg child.instance cp)) cp.threshold_nonneg

noncomputable def affineRate : Rate :=
  Rate.diagonal (listBudget child p cp) (listBudget_nonneg child p cp)

theorem affine_certificate (hp : p.listBound < Nat.card F) (hcp : cp.listBound < Nat.card F)
    (sigma : I.layer.Statement) {N : ℕ}
    (tree : Tree (HashInput child) (Answer child) (Proof child) N) :
    Certificate (fun H => failure child p cp sigma (fun _ => False) H (tree.run H).1)
      (fun _ => (N : ℚ)) (affineRate child p cp) := by
  apply Certificate.of_budget _ _ (N : ℚ) (by positivity)
  have h := fs_list_bound child p cp hp hcp sigma tree
  simpa only [affineRate, Rate.diagonal, add_mul, one_mul, mul_comm, add_comm] using h

/-- Uniform over every adversary tree and its declared budget. -/
theorem affine_sound (hp : p.listBound < Nat.card F) (hcp : cp.listBound < Nat.card F)
    (sigma : I.layer.Statement) :
    Sound (Context := Σ N, Tree (HashInput child) (Answer child) (Proof child) N)
      (Omega := fun _ => HashInput child → Answer child)
      (fun execution H => failure child p cp sigma (fun _ => False) H (execution.2.run H).1)
      (fun execution _ => (execution.1 : ℚ)) (affineRate child p cp) :=
  fun execution => affine_certificate child p cp hp hcp sigma execution.2

end RecursivePolygero.FiatShamir.TwoLevel

namespace RecursivePolygero.Benchmarks.FSTwoLevel

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

end RecursivePolygero.Benchmarks.FSTwoLevel
