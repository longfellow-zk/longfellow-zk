import LfzkV2.Current.ZeroKnowledge.FrontendPacking
import DualPacking.Tests.ArtinSchreierMasking

/-! Axiom audit and degree-one boundary of the public forward packing sampler.
The simulator uses field randomness; the inverse is confined to its coupling. -/
noncomputable section
namespace LfzkV2.Current.Tests.ZeroKnowledgePacking

open ZeroKnowledge.Frontend.Packing DualPacking.ArtinSchreier
open scoped Classical

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

abbrev K := ZMod 2

def basis : Module.Basis Unit K K := Module.Basis.singleton Unit K

example (scalar : K) :
    (simulate basis () (0,scalar)).1 = 0 ∧ (simulate basis () (0,scalar)).2 = scalar := by
  constructor
  · exact map_zero (Masking.maskMap basis ())
  · rfl

#print axioms publicEquiv
#print axioms honest_view
#print axioms recovered_constraints
#print axioms sameDistribution

end LfzkV2.Current.Tests.ZeroKnowledgePacking
