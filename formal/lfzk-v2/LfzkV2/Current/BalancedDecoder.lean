import Bcs.TotalOracle

/-! Finite ideal-sampler bookkeeping.  The raw answer can include a link and
all unused XOF output; only its balanced projection enters a local test. -/
namespace LfzkV2.Current
open Finset
open scoped Classical

variable {Raw Sample : Type} [Fintype Raw] [Fintype Sample]

structure BalancedDecoder (Raw Sample : Type) [Fintype Raw] [Fintype Sample] where
  decode : Raw → Sample
  fiber : ℕ
  fiber_bound : ∀ z, (univ.filter fun raw => decode raw = z).card ≤ fiber
  balanced : fiber * Fintype.card Sample = Fintype.card Raw

theorem BalancedDecoder.bad_card_mul_le (D : BalancedDecoder Raw Sample)
    (bad : Sample → Prop) (numerator denominator : ℕ)
    (hlocal : (univ.filter bad).card * denominator ≤ numerator * Fintype.card Sample) :
    (univ.filter fun raw => bad (D.decode raw)).card * denominator ≤
      numerator * Fintype.card Raw := by
  have h := Bcs.card_decode_le D.decode D.fiber D.fiber_bound bad
    (univ.filter bad).card (by rfl)
  calc
    _ ≤ (D.fiber * (univ.filter bad).card) * denominator := Nat.mul_le_mul_right _ h
    _ = D.fiber * ((univ.filter bad).card * denominator) := by ring
    _ ≤ D.fiber * (numerator * Fintype.card Sample) := Nat.mul_le_mul_left _ hlocal
    _ = numerator * Fintype.card Raw := by rw [← D.balanced]; ring

end LfzkV2.Current
