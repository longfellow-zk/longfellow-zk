import LfzkV2.Current.ZeroKnowledge.FrontendPackingCells

/-! Three private bits cross a degree-two word boundary; the unused fourth
coordinate is fixed to zero. Physical scalar/Frobenius cells stay separate,
and the authenticated source equations use the original pad coordinates. -/
noncomputable section
namespace LfzkV2.Current.Tests.ZeroKnowledgePackingCells

open ZeroKnowledge.Frontend.PackingCells
open scoped Classical

variable {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]

example (basis : Module.Basis (Fin 2) (ZMod 2) F) (bits : Fin 3 → Bool)
    (masks : Fin 1 → F) (random : F) (pads : Fin 1 → F) (selection : Fin 2 → F) :
    Packed.unpack basis (CellLayout.Binary.word 2 2 1)
      (CellLayout.primary (by decide : 0<2) (by decide : 3≤2*2))
      (values (by decide : 0<2) (packedWords basis bits) masks random pads selection) 2 =
        if bits 2 then 1 else 0 :=
  unpack_values (by decide) (by decide) basis bits masks random pads selection 2

example (basis : Module.Basis (Fin 2) (ZMod 2) F) (bits : Fin 3 → Bool) :
    DualPacking.digit basis (packedWords (words := 2) basis bits 1) 1 = 0 :=
  packedWords_zero_tail basis bits 1 1 (by decide)

#print axioms packing_realize
#print axioms freeMaskEquiv_apply
#print axioms unpack_values
#print axioms source_realize
#print axioms source_change_masks
#print axioms simulated_source_rows
#print axioms source_rows

end LfzkV2.Current.Tests.ZeroKnowledgePackingCells
