import LfzkV2.Current.StrandRoleSampling

namespace LfzkV2.Current.Tests.StrandRoleSampling
open LfzkV2.Current.StrandRoleSampling

-- The public fragment counts size a single shared vector, not one vector
-- per fragment. A combine also carries the next stage's weights, or the
-- input-only assertions; the prime frontend's last one also reads `eta`.
example : roleKind 16 9 (.assertions .binary 0 [⟨0,3⟩]
    [⟨0,0,2,1⟩,⟨1,0,1,2⟩]) = .binary 9 := rfl

example : roleKind 16 9 (.combine .binary 0 [⟨0,3⟩] [⟨0,0,2,1⟩] false) = .binary 7 := rfl
example : roleKind 16 9 (.combine .prime 0 [⟨0,3⟩] [] false) = .prime 4 := rfl
example : roleKind 16 9 (.combine .prime 0 [⟨0,3⟩] [] true) = .primeEta 4 := rfl
example : roleKind 16 9 (.inputAssertions .prime [⟨0,3⟩]) = .primeEta 3 := rfl

example : roleKind 16 9 (.terminal .prime 0) = .primeNonzero := rfl
example : roleKind 16 9 .conversion = .conversion := rfl
example : roleKind 16 9 .fingerprint = .fingerprints := rfl
example : roleKind 16 9 .rowBatching = .prime 9 := rfl
example : roleKind 16 9 .packing = .binary 16 := rfl
example : roleKind 16 9 .batching = .batching := rfl
example : roleKind 16 9 .opening = .opening := rfl

-- An input-only circuit has no algebraic LayerRole, but its empty public
-- assertion boundary still fits the capacity derived from the circuit.
example {F : Type} {n : ℕ} (side : Side) :
    FrontendSchedule.coordinates (.inputAssertions side []) ≤
      (FrontendSchedule.Plan.input (F := F) (n := n)).capacity :=
  frontend_coordinates_le .input side _ (by simp [Frontend.roles,Frontend.opening,FrontendSchedule.Plan.frontend])

#guard_msgs (drop info) in #check StrandRoleSampling.roleFits

section Factors
variable (B N IB IN RawB RawN Openings : Type) [Field B] [Field N]
variable (binaryCapacity primeCapacity : ℕ)
local notation "Answer" => IdealSamples.Answer B N IB IN RawB RawN Openings binaryCapacity primeCapacity

-- Prime terminal retains exactly one nonzero scalar; the prime frontend's
-- last boundary retains its coordinates and `eta` as that scalar. Conversion
-- retains the joint pair, without an intervening message or extra round.
example (answer : Answer) :
    (factor B N IB IN RawB RawN Openings binaryCapacity primeCapacity .primeNonzero trivial answer).1 =
      (answer .primeNonzero).1 := rfl

example (fits : 0 ≤ primeCapacity) (answer : Answer) :
    (factor B N IB IN RawB RawN Openings binaryCapacity primeCapacity (.primeEta 0) fits answer).1.2 =
      (answer .primeNonzero).1 := rfl

example (answer : Answer) :
    (factor B N IB IN RawB RawN Openings binaryCapacity primeCapacity .conversion trivial answer).1 =
      answer .primeNonzero := rfl

example (answer : Answer) :
    (factor B N IB IN RawB RawN Openings binaryCapacity primeCapacity .fingerprints trivial answer).1 =
      answer .fingerprints := rfl

example (answer : Answer) :
    (factor B N IB IN RawB RawN Openings binaryCapacity primeCapacity .batching trivial answer).1 =
      answer .batching := rfl

end Factors

/--
info: 'LfzkV2.Current.StrandRoleSampling.normalize_binary_role_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms StrandRoleSampling.normalize_binary_role_read

/--
info: 'LfzkV2.Current.StrandRoleSampling.normalize_prime_role_read' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms StrandRoleSampling.normalize_prime_role_read

/--
info: 'LfzkV2.Current.StrandRoleSampling.roleFits' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms StrandRoleSampling.roleFits

end LfzkV2.Current.Tests.StrandRoleSampling
