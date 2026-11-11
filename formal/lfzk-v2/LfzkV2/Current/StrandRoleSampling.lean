import LfzkV2.Current.StrandSampling
import LfzkV2.Current.IdealSamples
import LfzkV2.Current.FrontendSchedule

/-! The physical block sampled at a boundary is a product factor of the
common ideal answer. Frontend blocks use only their public coordinate width;
the remaining vector entries and all other roles are analysis randomness.
Prime terminal/rescaling reads use one nonzero scalar, whereas conversion
keeps the two scalars together. No independent physical samples are added.
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
  | primeNonzero
  | conversion
  | fingerprints
  | batching
  | opening

def roleKind (packingDegree rowCount : ℕ) (role : Role) : Kind :=
  match role with
  | .inputAssertions .binary .. | .assertions .binary .. | .sumcheck .binary .. |
      .combine .binary .. => .binary (FrontendSchedule.coordinates role)
  | .inputAssertions .prime .. | .assertions .prime .. | .sumcheck .prime .. |
      .combine .prime .. => .prime (FrontendSchedule.coordinates role)
  | .terminal .binary .. => .binaryNonzero
  | .terminal .prime .. | .rescaling => .primeNonzero
  | .rowBatching => .prime rowCount
  | .packing => .binary packingDegree
  | .conversion => .conversion
  | .fingerprint => .fingerprints
  | .batching => .batching
  | .opening => .opening

section PublicWidths
open FrontendSchedule

private theorem stage_coordinates_le (stage : Stage) (side : Side) (index : ℕ)
    (inputs : List Entry) (capacity : ℕ)
    (assertions : coordinates (.assertions side index stage.entering stage.fragments) ≤ capacity)
    (one : 1 ≤ capacity) (combine : 1+(inputs.map Entry.outputs).sum ≤ capacity)
    (role : Role) (member : role ∈ stage.roles side index inputs) : coordinates role ≤ capacity := by
  simp only [Stage.roles,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with (rfl | member) | (rfl | rfl)
  · exact assertions
  · obtain ⟨round,_,rfl⟩ := List.mem_map.mp member
    exact one
  · exact Nat.zero_le _
  · exact combine

/-- The public schedule includes empty assertion boundaries too. Their
width is zero even when there is no retained algebraic failure position. -/
theorem frontend_coordinates_le {F : Type} {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : Plan F circuit) (side : Side) (first offset : ℕ)
    (role : Role) (member : role ∈ rolesFrom plan.frontend side first) :
    coordinates role ≤ plan.capacityFrom offset := by
  induction plan generalizing first offset role with
  | input =>
      simp only [Plan.frontend,rolesFrom,List.isEmpty_nil,↓reduceIte,List.mem_singleton] at member
      subst role
      exact Nat.zero_le _
  | inputEntry metadata entry =>
      simp only [Plan.frontend,rolesFrom,List.isEmpty_nil,↓reduceIte,List.mem_singleton] at member
      subst role
      simp only [coordinates,metadata.count,Plan.capacityFrom]
      omega
  | @layer out mid input assertions body rest metadata tail ih =>
      change role ∈ rolesFrom ⟨⟨[],metadata.fragments,mid⟩ :: tail.frontend.stages,tail.frontend.inputEntries⟩ side first at member
      rw [rolesFrom_cons] at member
      change coordinates role ≤ max (offset+assertions) (max 1 (tail.capacityFrom (if FrontendReplay.hasLayers rest then 0 else 1)))
      have head := Nat.le_max_left (offset+assertions) (max 1 (tail.capacityFrom (if FrontendReplay.hasLayers rest then 0 else 1)))
      have one := (Nat.le_max_left 1 (tail.capacityFrom (if FrontendReplay.hasLayers rest then 0 else 1))).trans
        (Nat.le_max_right (offset+assertions) _)
      have restBound := (Nat.le_max_right 1 (tail.capacityFrom (if FrontendReplay.hasLayers rest then 0 else 1))).trans
        (Nat.le_max_right (offset+assertions) _)
      rcases List.mem_append.mp member with member | member
      · apply stage_coordinates_le _ side first _ _ _ one _ role member
        · simpa only [coordinates,List.map_nil,List.sum_nil,Nat.zero_add,metadata.count] using
            (show assertions ≤ offset+assertions by omega).trans head
        · by_cases empty : tail.frontend.stages.isEmpty = true
          · simp only [if_pos empty]
            have noLayers : FrontendReplay.hasLayers rest = false := by rw [tail.hasLayers_eq,empty]; rfl
            rw [noLayers] at restBound ⊢
            exact (tail.input_coordinates_le 1 noLayers).trans restBound
          · simpa only [if_neg empty,List.map_nil,List.sum_nil,Nat.add_zero] using one
      · split_ifs at member with empty
        · cases member
        · exact (ih (first+1) _ role member).trans restBound
  | @entryLayer out next mid input checks assertions entries entry body rest metadata tail ih =>
      change role ∈ rolesFrom ⟨⟨entries.entries,metadata.fragments,mid⟩ :: tail.frontend.stages,tail.frontend.inputEntries⟩ side first at member
      rw [rolesFrom_cons] at member
      change coordinates role ≤ max (offset+checks+assertions) (max 1 (tail.capacityFrom (if FrontendReplay.hasLayers rest then 0 else 1)))
      have head := Nat.le_max_left (offset+checks+assertions) (max 1 (tail.capacityFrom (if FrontendReplay.hasLayers rest then 0 else 1)))
      have one := (Nat.le_max_left 1 (tail.capacityFrom (if FrontendReplay.hasLayers rest then 0 else 1))).trans
        (Nat.le_max_right (offset+checks+assertions) _)
      have restBound := (Nat.le_max_right 1 (tail.capacityFrom (if FrontendReplay.hasLayers rest then 0 else 1))).trans
        (Nat.le_max_right (offset+checks+assertions) _)
      rcases List.mem_append.mp member with member | member
      · apply stage_coordinates_le _ side first _ _ _ one _ role member
        · simpa only [coordinates,entries.count,metadata.count] using
            (show checks+assertions ≤ offset+checks+assertions by omega).trans head
        · by_cases empty : tail.frontend.stages.isEmpty = true
          · simp only [if_pos empty]
            have noLayers : FrontendReplay.hasLayers rest = false := by rw [tail.hasLayers_eq,empty]; rfl
            rw [noLayers] at restBound ⊢
            exact (tail.input_coordinates_le 1 noLayers).trans restBound
          · simpa only [if_neg empty,List.map_nil,List.sum_nil,Nat.add_zero] using one
      · split_ifs at member with empty
        · cases member
        · exact (ih (first+1) _ role member).trans restBound

theorem frontend_side (frontend : Frontend) (side : Side) (role : Role)
    (member : role ∈ frontend.roles side) : frontendSide role = some side := by
  unfold Frontend.roles at member
  split_ifs at member
  · have equal := List.mem_singleton.mp member
    subst role
    rfl
  · obtain ⟨index,_,member⟩ := List.mem_flatMap.mp member
    simp only [Stage.roles,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with (rfl | member) | (rfl | rfl)
    · rfl
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
  | .primeNonzero => Linear.TerminalSampling.Nonzero N
  | .conversion => Linear.TerminalSampling.Nonzero N × Linear.TerminalSampling.Nonzero N
  | .fingerprints => WitnessSelection.Coins B IB × WitnessSelection.Coins N IN
  | .batching => RawBinary × RawPrime
  | .opening => Openings

abbrev Complement (kind : Component) :=
  (other : {other : Component // other ≠ kind}) →
    IdealSamples.Data B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity other.val

def Unused : Kind → Type
  | .binary count => ((Fin 0 → B) × (Fin (binaryCapacity-(0+count)) → B)) ×
      Complement B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity .binary
  | .binaryNonzero => Complement B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity .binaryNonzero
  | .prime count => ((Fin 0 → N) × (Fin (primeCapacity-(0+count)) → N)) ×
      Complement B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity .prime
  | .primeNonzero => Linear.TerminalSampling.Nonzero N ×
      Complement B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity .primeNonzero
  | .conversion => Complement B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity .primeNonzero
  | .fingerprints => Complement B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity .fingerprints
  | .batching => Complement B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity .batching
  | .opening => Complement B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity .opening

def Fits : Kind → Prop
  | .binary count => count ≤ binaryCapacity
  | .prime count => count ≤ primeCapacity
  | _ => True

section ScheduleFits
omit [Field B] [Field N]

private theorem frontend_fits {F : Type} {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : FrontendSchedule.Plan F circuit) (side : Side) (degree rowCount : ℕ)
    (capacity : plan.capacity ≤ match side with | .binary => binaryCapacity | .prime => primeCapacity)
    (role : Role) (member : role ∈ plan.frontend.roles side) :
    Fits binaryCapacity primeCapacity (roleKind degree rowCount role) := by
  have width := (frontend_coordinates_le plan side 0 0 role
    (by simpa only [FrontendSchedule.rolesFrom_zero] using member)).trans capacity
  have owner := frontend_side plan.frontend side role member
  cases role <;> simp only [frontendSide,Option.some.injEq,reduceCtorEq] at owner
  all_goals cases owner; cases side <;> first | exact width | trivial

/-- Every scheduled block fits the same public capacities already used by
the actual frontend readers. This includes empty rounds and the optional
packing round; no extra schedule-capacity assumption is required. -/
theorem roleFits {BF PF : Type} {bo bi po pi : ℕ}
    {binaryCircuit : Layered.Circuit BF bo bi} {primeCircuit : Layered.Circuit PF po pi}
    (g : Geometry) (binaryPlan : FrontendSchedule.Plan BF binaryCircuit)
    (primePlan : FrontendSchedule.Plan PF primeCircuit)
    (binaryGeometry : binaryPlan.frontend = g.binary) (primeGeometry : primePlan.frontend = g.prime)
    (binaryFits : binaryPlan.capacity ≤ binaryCapacity) (primeFits : primePlan.capacity ≤ primeCapacity)
    (degree rowCount : ℕ) (degreeFits : degree ≤ binaryCapacity) (rowsFit : rowCount ≤ primeCapacity)
    (index : Fin g.roles.length) :
    Fits binaryCapacity primeCapacity (roleKind degree rowCount (g.roles.get index)) := by
  have member := List.get_mem g.roles index
  generalize actual : g.roles.get index = role at member ⊢
  rw [g.roles_eq] at member
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with ((((rfl | primeMember) | (rfl | rfl | rfl)) | binaryMember) | packingMember) | (rfl | rfl)
  · trivial
  · rw [← primeGeometry] at primeMember
    exact frontend_fits binaryCapacity primeCapacity primePlan .prime degree rowCount primeFits _ primeMember
  · exact rowsFit
  · trivial
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

/-- Exactly the first prime nonzero scalar is used at a terminal or rescaling
boundary. The second coordinate is reserved for the conversion role. -/
def primeNonzero := refine (component .primeNonzero) (Equiv.refl _)

/-- This supplies the dependent factor required by `StrandSampling.read`
and `oracle_on_success`. Its fit premise is a public coordinate bound. -/
def factor (kind : Kind) (fits : Fits binaryCapacity primeCapacity kind) :
    Answer ≃ Value B N IB IN RawBinary RawPrime Openings kind ×
      Unused B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity kind := by
  cases kind with
  | binary count => exact binary B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity count fits
  | prime count => exact prime B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity count fits
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
  all_goals exact normalize_prime_read B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity _ fits fallback answer index inside

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

end LfzkV2.Current.StrandRoleSampling
