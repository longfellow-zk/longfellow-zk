import DualPacking.ArtinSchreierMasking
import Mathlib.Data.ZMod.Basic

/-! Joint masking audits include degree one, where there are no free
dependent masks and the trace-zero response space is trivial. -/
noncomputable section
namespace DualPacking.ArtinSchreier.Tests.Masking

open Module
open scoped Classical

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

abbrev K := ZMod 2

def basis : Basis Unit K K := Basis.singleton Unit K

theorem pivot_one : basis () = 1 := Basis.singleton_apply Unit K ()

example (free : {i : Unit // i ≠ ()} → K) :
    Masking.dependent basis () free () = 0 := by
  simp only [Masking.dependent]
  apply Finset.sum_eq_zero
  intro i _
  exact (i.property (Subsingleton.elim _ _)).elim

example : Function.Bijective (Masking.maskMap basis ()) :=
  Masking.maskMap_bijective basis () pivot_one

example (offset : Unit → Masking.TraceZero K K)
    (delta : (Unit → Masking.TraceZero K K) → Unit → K)
    (view : (Unit → Masking.TraceZero K K) × K) :
    Masking.transcriptEquiv basis () pivot_one offset delta
      ((Masking.transcriptEquiv basis () pivot_one offset delta).symm view) = view :=
  (Masking.transcriptEquiv basis () pivot_one offset delta).apply_symm_apply view

#print axioms Masking.maskMap_bijective
#print axioms Masking.transcript_uniform_fiber
#print axioms Masking.honest_transcript

end DualPacking.ArtinSchreier.Tests.Masking
