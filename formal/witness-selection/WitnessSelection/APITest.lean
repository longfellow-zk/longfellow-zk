import WitnessSelection
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

namespace WitnessSelection.APITest

local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 101) := ⟨by norm_num⟩

example (a : Coins (ZMod 2) (Fin 3)) (w : Fin 3 → ZMod 2) :
    Function.Bijective (fun m => fingerprint a (w,m)) :=
  (maskTranslation a w).bijective

example (x y : Candidate (ZMod 101) (Fin 3)) (hne : x ≠ y) :
    (collisionCoins x y).card * 101^2 ≤ Fintype.card (Coins (ZMod 101) (Fin 3)) := by
  simpa using pair_collision_card_mul_le x y hne

example (s : Finset (Candidate (ZMod 2) (Fin 0))) :
    (badCoins s).card * 2^2 ≤
      s.card.choose 2 * Fintype.card (Coins (ZMod 2) (Fin 0)) := by
  simpa using list_collision_card_mul_le s

-- With no original cells only the dedicated masks remain. Distinct masks
-- cannot collide, so selection ambiguity is impossible, rather than 1/q².
example (s : Finset (Candidate (ZMod 2) (Fin 0))) : badCoins s = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  obtain ⟨x,_,y,_,hne,hcollision⟩ := (Finset.mem_filter.mp ha).2
  exact hne (same_data_collision a x y (funext fun i => Fin.elim0 i) hcollision)

#guard_msgs (drop info) in #check selected_frontend_decomposition
#guard_msgs (drop info) in #check selected_bad_card_le
#guard_msgs (drop info) in #check Chained.failure_bound
#guard_msgs (drop info) in #check select_valid

/--
info: 'WitnessSelection.pair_collision_card_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms pair_collision_card_mul_le
/--
info: 'WitnessSelection.affine_rows_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms affine_rows_iff
/--
info: 'WitnessSelection.list_collision_card_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms list_collision_card_mul_le
/--
info: 'WitnessSelection.unique_matching_candidate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms unique_matching_candidate
/--
info: 'WitnessSelection.Chained.failure_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms Chained.failure_bound

end WitnessSelection.APITest
