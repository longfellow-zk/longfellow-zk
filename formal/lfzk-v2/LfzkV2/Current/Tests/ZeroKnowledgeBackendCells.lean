import LfzkV2.Current.ZeroKnowledge.BackendCells

/-! A selected vector crossing the 265-cell row boundary retains its second
fingerprint mask; padding begins at the very next logical cell. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeBackendCells

open ZeroKnowledge.BackendCells

example (flat : Fin 266 → ZMod 7) : tableau (cells := 264) flat ⟨1,by decide⟩ 0 = flat 265 :=
  primary_read flat 265

example (flat : Fin 266 → ZMod 7) : tableau (cells := 264) flat ⟨1,by decide⟩ 1 = 0 :=
  tail_zero flat ⟨1,by decide⟩ 1 (by decide)

#print axioms primary_read
#print axioms logical_read
#print axioms prime_read
#print axioms prime_logical_read
#print axioms primeRead_flat

end LfzkV2.Current.Tests.ZeroKnowledgeBackendCells
