import LfzkV2.Current.MdocDefaults

namespace LfzkV2.Current.Tests.MdocDefaults

example (g : Geometry) : (MdocDefaults.proof g (ZMod 2)).body.advice = 0 := rfl

example (g : Geometry) (i : Fin 32) :
    (MdocDefaults.proof g (ZMod 2)).finalSeal i = 0 := rfl

example (g : Geometry) :
    (MdocDefaults.proof g (ZMod 2)).body.authentication.frontierLength.val = 0 := rfl

example : MdocDefaults.packing (F := ZMod 2) 1 = () := rfl

#print axioms MdocDefaults.proof

end LfzkV2.Current.Tests.MdocDefaults
