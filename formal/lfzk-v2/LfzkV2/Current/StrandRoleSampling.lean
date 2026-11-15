import LfzkV2.Current.StrandSampling
import LfzkV2.Current.IdealSamples
import LfzkV2.Current.FrontendSchedule

/-! The physical block sampled at a boundary is a product factor of the
common ideal answer. Frontend blocks use only their public coordinate width;
the remaining vector entries and all other roles are analysis randomness.
Prime terminal reads use one nonzero scalar, the prime frontend's last
boundary also reads `eta` as that scalar after its coordinates, whereas
conversion keeps the two scalars together. No independent physical samples are added.
-/
noncomputable section
namespace LfzkV2.Current.StrandRoleSampling
open Finset IdealSamples
open scoped Classical

section Factors
variable {Whole ComponentValue Used Rest Unused : Type}

/-- Refine one role component without changing the coordinates of other roles. -/
def refine (component : Whole ≃ ComponentValue × Rest)
    (used : ComponentValue ≃ Used × Unused) : Whole ≃ Used × (Unused × Rest) :=
  component.trans ((Equiv.prodCongr used (Equiv.refl Rest)).trans
    (Equiv.prodAssoc Used Unused Rest))

end Factors

/-- The physical shapes used by the runtime. Vector lengths count only this
boundary's reads; the joint factors retain their original field ordering. -/
inductive Kind where
  | binary (count : ℕ)
  | binaryNonzero
  | prime (count : ℕ)
  /-- The prime frontend's last boundary: its coordinates, then `eta`. -/
  | primeEta (count : ℕ)
  | primeNonzero
  | conversion
  | fingerprints
  | batching
  | opening

def roleKind (packingDegree rowCount : ℕ) (role : Role) : Kind :=
  match role with
  | .inputAssertions .binary .. | .assertions .binary .. | .sumcheck .binary .. |
      .combine .binary .. => .binary (FrontendSchedule.coordinates role)
  | .inputAssertions .prime .. | .combine .prime _ _ _ true =>
      .primeEta (FrontendSchedule.coordinates role)
  | .assertions .prime .. | .sumcheck .prime .. | .combine .prime _ _ _ false =>
      .prime (FrontendSchedule.coordinates role)
  | .terminal .binary .. => .binaryNonzero
  | .terminal .prime .. => .primeNonzero
  -- Pure-foreign storage only; absent from the mdoc schedule.
  | .rowBatching => .prime rowCount
  | .packing => .binary packingDegree
  | .conversion => .conversion
  | .fingerprint => .fingerprints
  | .batching => .batching
  | .opening => .opening

section PublicWidths
open FrontendSchedule

theorem stageRoles_coordinates_le {F : Type} {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : Plan F circuit) (side : Side) (first offset : ℕ)
    (role : Role) (member : role ∈ stageRoles side first plan.frontend) :
    coordinates role ≤ plan.capacityFrom offset := by
  induction plan generalizing first offset with
  | input => simp [Plan.frontend, stageRoles] at member
  | inputEntry => simp [Plan.frontend, stageRoles] at member
  | @layer out mid input assertions body rest metadata tail ih =>
      change role ∈ stageRoles side first ⟨⟨[],metadata.fragments,mid⟩ :: tail.frontend.stages,
        tail.frontend.inputEntries⟩ at member
      rw [stageRoles_cons] at member
      change coordinates role ≤ max (offset+assertions) (max 1 (tail.capacityFrom 1))
      have one : 1 ≤ max (offset+assertions) (max 1 (tail.capacityFrom 1)) :=
        (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
      have restBound : tail.capacityFrom 1 ≤ max (offset+assertions) (max 1 (tail.capacityFrom 1)) :=
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
      rcases List.mem_append.mp member with member | member
      · simp only [Stage.roles,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with member | rfl | rfl
        · obtain ⟨round,_,rfl⟩ := List.mem_map.mp member
          exact one
        · exact Nat.zero_le _
        · exact (tail.combineRole_coordinates_le side first).trans restBound
      · exact (ih (first+1) 1 member).trans restBound
  | @entryLayer out next mid input checks assertions entries entry body rest metadata tail ih =>
      change role ∈ stageRoles side first ⟨⟨entries.entries,metadata.fragments,mid⟩ :: tail.frontend.stages,
        tail.frontend.inputEntries⟩ at member
      rw [stageRoles_cons] at member
      change coordinates role ≤ max (offset+checks+assertions) (max 1 (tail.capacityFrom 1))
      have one : 1 ≤ max (offset+checks+assertions) (max 1 (tail.capacityFrom 1)) :=
        (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
      have restBound : tail.capacityFrom 1 ≤ max (offset+checks+assertions) (max 1 (tail.capacityFrom 1)) :=
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
      rcases List.mem_append.mp member with member | member
      · simp only [Stage.roles,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with member | rfl | rfl
        · obtain ⟨round,_,rfl⟩ := List.mem_map.mp member
          exact one
        · exact Nat.zero_le _
        · exact (tail.combineRole_coordinates_le side first).trans restBound
      · exact (ih (first+1) 1 member).trans restBound

/-- The public schedule includes empty assertion boundaries too. Their
width is zero even when there is no retained algebraic failure position. -/
theorem frontend_coordinates_le {F : Type} {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : Plan F circuit) (side : Side)
    (role : Role) (member : role ∈ plan.frontend.roles side) : coordinates role ≤ plan.capacity := by
  rw [roles_eq_stageRoles, List.mem_cons] at member
  rcases member with rfl | member
  · exact plan.opening_role_coordinates_le side
  · exact stageRoles_coordinates_le plan side 0 0 role member

theorem frontend_side (frontend : Frontend) (side : Side) (role : Role)
    (member : role ∈ frontend.roles side) : frontendSide role = some side := by
  rw [roles_eq_stageRoles, List.mem_cons] at member
  rcases member with rfl | member
  · exact Plan.opening_side frontend side
  · obtain ⟨index,_,member⟩ := List.mem_flatMap.mp member
    simp only [Stage.roles,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with member | rfl | rfl
    · obtain ⟨round,_,rfl⟩ := List.mem_map.mp member
      rfl
    · rfl
    · rfl

end PublicWidths

variable (B N IB IN RawBinary RawPrime Openings : Type)
variable [Field B] [Field N]
variable (binaryCapacity primeCapacity : ℕ)

local notation "Answer" => IdealSamples.Answer B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity
local notation "component" => IdealSamples.factor B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity

def Value : Kind → Type
  | .binary count => Fin count → B
  | .binaryNonzero => Linear.TerminalSampling.Nonzero B
  | .prime count => Fin count → N
  | .primeEta count => (Fin count → N) × Linear.TerminalSampling.Nonzero N
  | .primeNonzero => Linear.TerminalSampling.Nonzero N
  | .conversion => Linear.TerminalSampling.Nonzero N × Linear.TerminalSampling.Nonzero N
  | .fingerprints => WitnessSelection.Coins B IB × WitnessSelection.Coins N IN
  | .batching => RawBinary × RawPrime
  | .opening => Openings

abbrev Complement (kind : Component) :=
  (other : {other : Component // other ≠ kind}) →
    IdealSamples.Data B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity other.val

/-- The components other than the prime vector and the prime nonzero pair. -/
abbrev EtaComplement :=
  (other : {other : {other : Component // other ≠ .prime} // other ≠ ⟨.primeNonzero, by decide⟩}) →
    IdealSamples.Data B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity other.val.val

def Unused : Kind → Type
  | .binary count => ((Fin 0 → B) × (Fin (binaryCapacity-(0+count)) → B)) ×
      Complement B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity .binary
  | .binaryNonzero => Complement B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity .binaryNonzero
  | .prime count => ((Fin 0 → N) × (Fin (primeCapacity-(0+count)) → N)) ×
      Complement B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity .prime
  | .primeEta count => ((Fin 0 → N) × (Fin (primeCapacity-(0+count)) → N)) ×
      (Linear.TerminalSampling.Nonzero N × EtaComplement B N IB IN RawBinary RawPrime Openings
        binaryCapacity primeCapacity)
  | .primeNonzero => Linear.TerminalSampling.Nonzero N ×
      Complement B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity .primeNonzero
  | .conversion => Complement B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity .primeNonzero
  | .fingerprints => Complement B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity .fingerprints
  | .batching => Complement B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity .batching
  | .opening => Complement B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity .opening

def Fits : Kind → Prop
  | .binary count => count ≤ binaryCapacity
  | .prime count => count ≤ primeCapacity
  | .primeEta count => count ≤ primeCapacity
  | _ => True

section ScheduleFits
omit [Field B] [Field N]

private theorem frontend_fits {F : Type} {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : FrontendSchedule.Plan F circuit) (side : Side) (degree rowCount : ℕ)
    (capacity : plan.capacity ≤ match side with | .binary => binaryCapacity | .prime => primeCapacity)
    (role : Role) (member : role ∈ plan.frontend.roles side) :
    Fits binaryCapacity primeCapacity (roleKind degree rowCount role) := by
  have width := (frontend_coordinates_le plan side role member).trans capacity
  have owner := frontend_side plan.frontend side role member
  cases role <;> simp only [frontendSide,Option.some.injEq,reduceCtorEq] at owner
  all_goals cases owner
  all_goals first
    | (cases side <;> first | exact width | trivial)
    | (rename_i last; cases side <;> cases last <;> exact width)

/-- Every scheduled block fits the same public capacities already used by
the actual frontend readers. This includes empty rounds and the optional
packing round; no extra schedule-capacity assumption is required. The mdoc
schedule has no row-batching round (pure-foreign storage only), so the
row-count bound `_rowsFit` of the shared sampler interface is not needed. -/
theorem roleFits {BF PF : Type} {bo bi po pi : ℕ}
    {binaryCircuit : Layered.Circuit BF bo bi} {primeCircuit : Layered.Circuit PF po pi}
    (g : Geometry) (binaryPlan : FrontendSchedule.Plan BF binaryCircuit)
    (primePlan : FrontendSchedule.Plan PF primeCircuit)
    (binaryGeometry : binaryPlan.frontend = g.binary) (primeGeometry : primePlan.frontend = g.prime)
    (binaryFits : binaryPlan.capacity ≤ binaryCapacity) (primeFits : primePlan.capacity ≤ primeCapacity)
    (degree rowCount : ℕ) (degreeFits : degree ≤ binaryCapacity) (_rowsFit : rowCount ≤ primeCapacity)
    (index : Fin g.roles.length) :
    Fits binaryCapacity primeCapacity (roleKind degree rowCount (g.roles.get index)) := by
  have member := List.get_mem g.roles index
  generalize actual : g.roles.get index = role at member ⊢
  rw [g.roles_eq] at member
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with ((((rfl | primeMember) | rfl) | binaryMember) | packingMember) | (rfl | rfl)
  · trivial
  · rw [← primeGeometry] at primeMember
    exact frontend_fits binaryCapacity primeCapacity primePlan .prime degree rowCount primeFits _ primeMember
  · trivial
  · rw [← binaryGeometry] at binaryMember
    exact frontend_fits binaryCapacity primeCapacity binaryPlan .binary degree rowCount binaryFits _ binaryMember
  · split_ifs at packingMember
    · cases packingMember
    · have equal := List.mem_singleton.mp packingMember
      rw [equal]
      exact degreeFits
  · trivial
  · trivial

end ScheduleFits

def binary (count : ℕ) (fits : count ≤ binaryCapacity) :=
  refine (component .binary) (IdealProjections.boundedSlice binaryCapacity 0 count (by simpa using fits))

def prime (count : ℕ) (fits : count ≤ primeCapacity) :=
  refine (component .prime) (IdealProjections.boundedSlice primeCapacity 0 count (by simpa using fits))

/-- Exactly the first prime nonzero scalar is used at a terminal boundary.
The second coordinate is reserved for the conversion role. -/
def primeNonzero := refine (component .primeNonzero) (Equiv.refl _)

/-- The prime frontend's last boundary reads its coordinates from the prime
vector and `eta` as the first prime nonzero scalar: two independent factors. -/
def primeEta (count : ℕ) (fits : count ≤ primeCapacity) :
    Answer ≃ ((Fin count → N) × Linear.TerminalSampling.Nonzero N) ×
      (((Fin 0 → N) × (Fin (primeCapacity-(0+count)) → N)) ×
        (Linear.TerminalSampling.Nonzero N × EtaComplement B N IB IN RawBinary RawPrime Openings
          binaryCapacity primeCapacity)) :=
  let first := prime B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity count fits
  let second := Equiv.piSplitAt (⟨.primeNonzero, by decide⟩ : {other : Component // other ≠ .prime})
    (fun other => IdealSamples.Data B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity other.val)
  { toFun := fun answer =>
      let x := first answer
      let y := second x.2.2
      ((x.1,y.1.1),(x.2.1,(y.1.2,y.2)))
    invFun := fun z => first.symm (z.1.1,(z.2.1,second.symm ((z.1.2,z.2.2.1),z.2.2.2)))
    left_inv := by
      intro answer
      simp
    right_inv := by
      rintro ⟨⟨v,e⟩,⟨u,⟨e',rest⟩⟩⟩
      simp }

/-- This supplies the dependent factor required by `StrandSampling.read`
and `oracle_on_success`. Its fit premise is a public coordinate bound. -/
def factor (kind : Kind) (fits : Fits binaryCapacity primeCapacity kind) :
    Answer ≃ Value B N IB IN RawBinary RawPrime Openings kind ×
      Unused B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity kind := by
  cases kind with
  | binary count => exact binary B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity count fits
  | prime count => exact prime B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity count fits
  | primeEta count => exact primeEta B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity count fits
  | binaryNonzero => exact component .binaryNonzero
  | primeNonzero => exact primeNonzero B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity
  | conversion => exact component .primeNonzero
  | fingerprints => exact component .fingerprints
  | batching => exact component .batching
  | opening => exact component .opening

private theorem binary_value (count : ℕ) (fits : count ≤ binaryCapacity) (answer : Answer) (i : Fin count) :
    (binary B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity count fits answer).1 i =
      answer .binary ⟨i.val,by have := i.isLt; omega⟩ := by
  change (IdealProjections.boundedSlice binaryCapacity 0 count (by simpa using fits)
    (answer .binary)).1 i = _
  simpa only [Nat.zero_add] using
    IdealProjections.boundedSlice_apply binaryCapacity 0 count (by simpa using fits) (answer .binary) i

private theorem prime_value (count : ℕ) (fits : count ≤ primeCapacity) (answer : Answer) (i : Fin count) :
    (prime B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity count fits answer).1 i =
      answer .prime ⟨i.val,by have := i.isLt; omega⟩ := by
  change (IdealProjections.boundedSlice primeCapacity 0 count (by simpa using fits)
    (answer .prime)).1 i = _
  simpa only [Nat.zero_add] using
    IdealProjections.boundedSlice_apply primeCapacity 0 count (by simpa using fits) (answer .prime) i

/-- Whole joint factors are retained at fingerprint, conversion, batching and
opening boundaries. In particular both fields' fingerprints share one value. -/
theorem normalize_component (kind : Component) (fallback answer : Answer) :
    StrandSampling.normalize (component kind) fallback answer kind = answer kind :=
  StrandSampling.normalize_value (component kind) fallback answer

theorem normalize_binary (count : ℕ) (fits : count ≤ binaryCapacity)
    (fallback answer : Answer) (i : Fin count) :
    StrandSampling.normalize
      (binary B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity count fits)
      fallback answer .binary ⟨i.val,by have := i.isLt; omega⟩ =
      answer .binary ⟨i.val,by have := i.isLt; omega⟩ := by
  simpa only [binary_value] using congrFun (StrandSampling.normalize_value
    (binary B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity count fits)
    fallback answer) i

theorem normalize_prime (count : ℕ) (fits : count ≤ primeCapacity)
    (fallback answer : Answer) (i : Fin count) :
    StrandSampling.normalize
      (prime B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity count fits)
      fallback answer .prime ⟨i.val,by have := i.isLt; omega⟩ =
      answer .prime ⟨i.val,by have := i.isLt; omega⟩ := by
  simpa only [prime_value] using congrFun (StrandSampling.normalize_value
    (prime B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity count fits)
    fallback answer) i

theorem normalize_primeNonzero (fallback answer : Answer) :
    (StrandSampling.normalize
      (primeNonzero B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity)
      fallback answer .primeNonzero).1 = (answer .primeNonzero).1 :=
  StrandSampling.normalize_value
    (primeNonzero B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity) fallback answer

variable [Fintype B] [Fintype N] [DecidableEq B] [DecidableEq N]
variable [Fintype IB] [Fintype IN] [DecidableEq IB] [DecidableEq IN]
variable [Fintype RawBinary] [Fintype RawPrime] [Fintype Openings]

instance valueFintype (kind : Kind) : Fintype (Value B N IB IN RawBinary RawPrime Openings kind) := by
  cases kind <;> dsimp only [Value] <;> infer_instance

instance unusedFintype (kind : Kind) :
    Fintype (Unused B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity kind) := by
  cases kind <;> dsimp only [Unused,Complement] <;> infer_instance

theorem normalize_binary_read (count : ℕ) (fits : count ≤ binaryCapacity)
    (fallback answer : Answer) (index : ℕ) (inside : index < count) :
    IdealSamples.vectorRead
      (IdealSamples.decoder B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity .binary)
      (StrandSampling.normalize
        (binary B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity count fits)
        fallback answer) index =
      IdealSamples.vectorRead
        (IdealSamples.decoder B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity .binary)
        answer index := by
  have within : index < binaryCapacity := lt_of_lt_of_le inside fits
  simp only [IdealSamples.vectorRead,dif_pos within,IdealSamples.decoder_apply]
  exact normalize_binary B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity
    count fits fallback answer ⟨index,inside⟩

theorem normalize_prime_read (count : ℕ) (fits : count ≤ primeCapacity)
    (fallback answer : Answer) (index : ℕ) (inside : index < count) :
    IdealSamples.vectorRead
      (IdealSamples.decoder B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity .prime)
      (StrandSampling.normalize
        (prime B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity count fits)
        fallback answer) index =
      IdealSamples.vectorRead
        (IdealSamples.decoder B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity .prime)
        answer index := by
  have within : index < primeCapacity := lt_of_lt_of_le inside fits
  simp only [IdealSamples.vectorRead,dif_pos within,IdealSamples.decoder_apply]
  exact normalize_prime B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity
    count fits fallback answer ⟨index,inside⟩

omit [Fintype B] [Fintype N] [DecidableEq B] [DecidableEq N] [Fintype IB] [Fintype IN]
  [DecidableEq IB] [DecidableEq IN] [Fintype RawBinary] [Fintype RawPrime] [Fintype Openings] in
theorem primeEta_vector (count : ℕ) (fits : count ≤ primeCapacity) (answer : Answer) :
    ((primeEta B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity count fits answer).1).1 =
      (prime B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity count fits answer).1 := rfl

omit [Fintype B] [Fintype N] [DecidableEq B] [DecidableEq N] [Fintype IB] [Fintype IN]
  [DecidableEq IB] [DecidableEq IN] [Fintype RawBinary] [Fintype RawPrime] [Fintype Openings] in
theorem primeEta_eta (count : ℕ) (fits : count ≤ primeCapacity) (answer : Answer) :
    ((primeEta B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity count fits answer).1).2 =
      (answer .primeNonzero).1 := rfl

theorem normalize_primeEta_read (count : ℕ) (fits : count ≤ primeCapacity)
    (fallback answer : Answer) (index : ℕ) (inside : index < count) :
    IdealSamples.vectorRead
      (IdealSamples.decoder B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity .prime)
      (StrandSampling.normalize
        (primeEta B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity count fits)
        fallback answer) index =
      IdealSamples.vectorRead
        (IdealSamples.decoder B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity .prime)
        answer index := by
  have within : index < primeCapacity := lt_of_lt_of_le inside fits
  have h := congrArg (fun z => z.1 ⟨index,inside⟩) (StrandSampling.normalize_value
    (primeEta B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity count fits)
    fallback answer)
  simp only [primeEta_vector, prime_value] at h
  simp only [IdealSamples.vectorRead,dif_pos within,IdealSamples.decoder_apply]
  exact h

omit [Fintype B] [Fintype N] [DecidableEq B] [DecidableEq N] [Fintype IB] [Fintype IN]
  [DecidableEq IB] [DecidableEq IN] [Fintype RawBinary] [Fintype RawPrime] [Fintype Openings] in
theorem normalize_primeEta_nonzero (count : ℕ) (fits : count ≤ primeCapacity)
    (fallback answer : Answer) :
    ((StrandSampling.normalize
        (primeEta B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity count fits)
        fallback answer) .primeNonzero).1 = (answer .primeNonzero).1 := by
  have h := congrArg (fun z => z.2) (StrandSampling.normalize_value
    (primeEta B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity count fits)
    fallback answer)
  simpa only [primeEta_eta] using h

theorem normalize_binary_role_read (degree rowCount : ℕ) (role : Role)
    (fits : Fits binaryCapacity primeCapacity (roleKind degree rowCount role))
    (side : frontendSide role = some .binary) (fallback answer : Answer)
    (index : ℕ) (inside : index < FrontendSchedule.coordinates role) :
    IdealSamples.vectorRead (IdealSamples.decoder B N IB IN RawBinary RawPrime Openings
      binaryCapacity primeCapacity .binary)
      (StrandSampling.normalize (factor B N IB IN RawBinary RawPrime Openings
        binaryCapacity primeCapacity (roleKind degree rowCount role) fits) fallback answer) index =
    IdealSamples.vectorRead (IdealSamples.decoder B N IB IN RawBinary RawPrime Openings
      binaryCapacity primeCapacity .binary) answer index := by
  cases role <;> simp only [frontendSide,Option.some.injEq,reduceCtorEq] at side
  all_goals try contradiction
  all_goals subst side
  all_goals exact normalize_binary_read B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity _ fits fallback answer index inside

theorem normalize_prime_role_read (degree rowCount : ℕ) (role : Role)
    (fits : Fits binaryCapacity primeCapacity (roleKind degree rowCount role))
    (side : frontendSide role = some .prime) (fallback answer : Answer)
    (index : ℕ) (inside : index < FrontendSchedule.coordinates role) :
    IdealSamples.vectorRead (IdealSamples.decoder B N IB IN RawBinary RawPrime Openings
      binaryCapacity primeCapacity .prime)
      (StrandSampling.normalize (factor B N IB IN RawBinary RawPrime Openings
        binaryCapacity primeCapacity (roleKind degree rowCount role) fits) fallback answer) index =
    IdealSamples.vectorRead (IdealSamples.decoder B N IB IN RawBinary RawPrime Openings
      binaryCapacity primeCapacity .prime) answer index := by
  cases role <;> simp only [frontendSide,Option.some.injEq,reduceCtorEq] at side
  all_goals try contradiction
  all_goals subst side
  all_goals first
    | exact normalize_prime_read B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity _ fits fallback answer index inside
    | (rename_i last; cases last
       · exact normalize_prime_read B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity _ fits fallback answer index inside
       · exact normalize_primeEta_read B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity _ fits fallback answer index inside)

omit [Fintype B] [Fintype N] [DecidableEq B] [DecidableEq N] [Fintype IB] [Fintype IN]
  [DecidableEq IB] [DecidableEq IN] [Fintype RawBinary] [Fintype RawPrime] [Fintype Openings] in
theorem normalize_binary_role_nonzero (degree rowCount : ℕ) (role : Role)
    (fits : Fits binaryCapacity primeCapacity (roleKind degree rowCount role))
    (side : frontendSide role = some .binary) (terminal : role.domain = .terminal)
    (fallback answer : Answer) :
    (StrandSampling.normalize (factor B N IB IN RawBinary RawPrime Openings
      binaryCapacity primeCapacity (roleKind degree rowCount role) fits) fallback answer) .binaryNonzero =
      answer .binaryNonzero := by
  cases role <;> simp only [Role.domain,reduceCtorEq] at terminal
  rename_i side' stage
  simp only [frontendSide,Option.some.injEq] at side
  subst side'
  exact normalize_component B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity
    .binaryNonzero fallback answer

omit [Fintype B] [Fintype N] [DecidableEq B] [DecidableEq N] [Fintype IB] [Fintype IN]
  [DecidableEq IB] [DecidableEq IN] [Fintype RawBinary] [Fintype RawPrime] [Fintype Openings] in
theorem normalize_prime_role_nonzero (degree rowCount : ℕ) (role : Role)
    (fits : Fits binaryCapacity primeCapacity (roleKind degree rowCount role))
    (side : frontendSide role = some .prime) (terminal : role.domain = .terminal)
    (fallback answer : Answer) :
    ((StrandSampling.normalize (factor B N IB IN RawBinary RawPrime Openings
      binaryCapacity primeCapacity (roleKind degree rowCount role) fits) fallback answer) .primeNonzero).1 =
      (answer .primeNonzero).1 := by
  cases role <;> simp only [Role.domain,reduceCtorEq] at terminal
  rename_i side' stage
  simp only [frontendSide,Option.some.injEq] at side
  subst side'
  exact normalize_primeNonzero B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity
    fallback answer

omit [Fintype B] [Fintype N] [DecidableEq B] [DecidableEq N] [Fintype IB] [Fintype IN]
  [DecidableEq IB] [DecidableEq IN] [Fintype RawBinary] [Fintype RawPrime] [Fintype Openings] in
/-- The prime frontend's last boundary also reads `eta` as its first prime
nonzero scalar. -/
theorem normalize_prime_role_eta (degree rowCount : ℕ) (role : Role)
    (fits : Fits binaryCapacity primeCapacity (roleKind degree rowCount role))
    (last : roleKind degree rowCount role = .primeEta (FrontendSchedule.coordinates role))
    (fallback answer : Answer) :
    ((StrandSampling.normalize (factor B N IB IN RawBinary RawPrime Openings
      binaryCapacity primeCapacity (roleKind degree rowCount role) fits) fallback answer) .primeNonzero).1 =
      (answer .primeNonzero).1 := by
  generalize hk : roleKind degree rowCount role = kind at fits last ⊢
  subst last
  exact normalize_primeEta_nonzero B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity
    _ fits fallback answer

end LfzkV2.Current.StrandRoleSampling
