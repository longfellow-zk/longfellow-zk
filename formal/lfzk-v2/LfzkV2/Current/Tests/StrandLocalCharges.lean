import LfzkV2.Current.StrandLocalCharges

namespace LfzkV2.Current.Tests.StrandLocalCharges
open SumcheckV2 LfzkV2.Current.StrandLocalCharges

section Widths
variable {F : Type} {out next mid input checks assertions : ℕ}

-- Entering outputs use the beginning of the layer assertion block.
example (entry : Layered.Entry (Cube out) (Cube next) checks)
    (body : LfzkV2.Native.CircuitLayer (Cube next) (Cube mid) (Fin assertions) F)
    (rest : Layered.Circuit F mid input) (role : Fin (LfzkV2.Replay.vectorSlots assertions)) (offset : ℕ) :
    usedWidth (.entry checks entry (.layer assertions body rest)) (.inr (.inl role)) offset =
      offset+checks+assertions := rfl

-- Input-only assertions share the last combine answer after its scalar.
example (body : LfzkV2.Native.CircuitLayer (Cube out) (Cube mid) (Fin assertions) F)
    (entry : Layered.Entry (Cube mid) (Cube input) checks)
    (role : Fin (LfzkV2.Replay.vectorSlots checks)) :
    usedWidth (.layer assertions body (.entry checks entry .input))
      (.inr (.inr (.inr (.inr (.inl role))))) 0 = 1+checks := rfl

end Widths

-- These are concrete adaptive-runtime statements, not a supplied
-- correspondence certificate or an abstract charge-preservation premise.
#guard_msgs (drop info) in #check StrandLocalCharges.usedWidth_le
#guard_msgs (drop info) in #check StrandLocalCharges.current_samples

/--
info: 'LfzkV2.Current.StrandLocalCharges.application_role_normalize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms StrandLocalCharges.application_role_normalize

/--
info: 'LfzkV2.Current.StrandLocalCharges.application_role_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms StrandLocalCharges.application_role_sum

end LfzkV2.Current.Tests.StrandLocalCharges
