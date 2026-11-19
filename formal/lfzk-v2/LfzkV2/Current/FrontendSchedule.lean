import LfzkV2.Current.FrontendBody
import LfzkV2.Current.FrontendCounting

/-! A public schedule annotation of a normalized algebraic circuit. Component
identifiers remain explicit public metadata: the algebraic circuit does not
contain identifiers from which to invent them. Counts and assertion classes
are checked against the actual circuit syntax. The annotation determines
stage roles and decoder capacity without inspecting any proof or witness. -/
namespace LfzkV2.Current.FrontendSchedule
open SumcheckV2

variable {F : Type}

/-- Component identifiers and their order are fixed setup data. The count
check validates the coefficient count, not identifier or mapping provenance.
The concrete compiler must supply Rust's decreasing-depth order, with supplied
component index as the tie breaker; no semantic certificate about diagnostic
identifiers is part of this annotation. -/
structure EntryMetadata (checks : ℕ) where
  entries : List Entry
  count : (entries.map Entry.outputs).sum = checks

def isQuadratic {Wire : Type} : LfzkV2.Native.AssertionTerm Wire → Bool
  | .quadratic .. => true
  | .linear .. => false

/-- Runtime visits quadratic markers across all fragments, then linear
markers across all fragments. The constructor check prevents a quadratic
assertion from being charged or decoded as a linear marker. Fragment order
and its component/mapping provenance are fixed by public setup, not checked
by the aggregate count or manufactured from the algebraic tensors. -/
structure LayerMetadata {out mid assertions : ℕ}
    (body : LfzkV2.Native.CircuitLayer (Cube out) (Cube mid) (Fin assertions) F) where
  fragments : List Fragment
  count : (fragments.map Fragment.quadraticAssertions).sum +
    (fragments.map Fragment.linearAssertions).sum = assertions
  quadratic_first : ∀ i, isQuadratic (body.assertions i) =
    decide (i.val < (fragments.map Fragment.quadraticAssertions).sum)

/-- The four forms are exactly the normalized circuit grammar. An entry
can precede a layer or the inputs; adjacent entry blocks cannot be supplied.
The concrete public compiler supplies component and fragment metadata in
runtime order; this generic annotation does not verify their provenance. -/
inductive Plan (F : Type) : {out input : ℕ} → Layered.Circuit F out input → Type
  | input {n : ℕ} : Plan F (.input (n := n))
  | inputEntry {out input checks : ℕ}
      (metadata : EntryMetadata checks)
      (entry : Layered.Entry (Cube out) (Cube input) checks) :
      Plan F (.entry checks entry .input)
  | layer {out mid input assertions : ℕ}
      {body : LfzkV2.Native.CircuitLayer (Cube out) (Cube mid) (Fin assertions) F}
      {rest : Layered.Circuit F mid input}
      (metadata : LayerMetadata body) (tail : Plan F rest) :
      Plan F (.layer assertions body rest)
  | entryLayer {out next mid input checks assertions : ℕ}
      (entries : EntryMetadata checks)
      (entry : Layered.Entry (Cube out) (Cube next) checks)
      {body : LfzkV2.Native.CircuitLayer (Cube next) (Cube mid) (Fin assertions) F}
      {rest : Layered.Circuit F mid input}
      (metadata : LayerMetadata body) (tail : Plan F rest) :
      Plan F (.entry checks entry (.layer assertions body rest))

/-- The stage roles from stage number `first`, without the opening boundary;
used when descending into a tail of the circuit. -/
def stageRoles (side : Side) (first : ℕ) (frontend : Frontend) : List Role :=
  (List.finRange frontend.stages.length).flatMap fun i =>
    (frontend.stages.get i).roles side (first+i.val) (frontend.weightsAt (i.val+1))
      (i.val+1 = frontend.stages.length)

theorem roles_eq_stageRoles (frontend : Frontend) (side : Side) :
    frontend.roles side = frontend.opening side :: stageRoles side 0 frontend := by
  simp only [Frontend.roles, stageRoles, Nat.zero_add]

theorem weightsAt_cons (stage : Stage) (tail : List Stage) (inputs : List Entry) (i : ℕ) :
    Frontend.weightsAt ⟨stage :: tail, inputs⟩ (i+1) = Frontend.weightsAt ⟨tail, inputs⟩ i := by
  simp only [Frontend.weightsAt, List.getElem?_cons_succ]

theorem stageRoles_cons (side : Side) (first : ℕ) (stage : Stage) (tail : List Stage)
    (inputs : List Entry) :
    stageRoles side first ⟨stage :: tail, inputs⟩ =
      stage.roles side first (Frontend.weightsAt ⟨tail, inputs⟩ 0) tail.isEmpty ++
        stageRoles side (first+1) ⟨tail, inputs⟩ := by
  simp only [stageRoles, List.length_cons, List.finRange_succ, List.flatMap_cons, List.flatMap_map,
    List.get_cons_zero, Fin.val_zero, Fin.val_succ, Nat.add_zero, weightsAt_cons]
  congr 2
  · cases tail <;> simp
  · funext i
    congr 1
    · omega
    · simp only [decide_eq_decide]
      omega

theorem stage_round (side : Side) (first : ℕ) (stage : Stage) (next : List Entry × List Fragment)
    (last : Bool) (i : Fin stage.rounds) :
    (stage.roles side first next last)[i.val]? = some (.sumcheck side first i.val) := by
  change ((List.range stage.rounds).map (Role.sumcheck side first) ++
    [Role.terminal side first,Role.combine side first next.1 next.2 last])[i.val]? = _
  rw [List.getElem?_append_left (by simp only [List.length_map,List.length_range]; exact i.isLt)]
  simp only [List.getElem?_map,List.getElem?_range i.isLt,Option.map_some]

theorem stage_terminal (side : Side) (first : ℕ) (stage : Stage) (next : List Entry × List Fragment)
    (last : Bool) : (stage.roles side first next last)[stage.rounds]? = some (.terminal side first) := by
  simp [Stage.roles]

theorem stage_combine (side : Side) (first : ℕ) (stage : Stage) (next : List Entry × List Fragment)
    (last : Bool) :
    (stage.roles side first next last)[stage.rounds+1]? =
      some (.combine side first next.1 next.2 last) := by
  simp [Stage.roles]

theorem queryIndex_shift {out input : ℕ} (circuit : Layered.Circuit F out input)
    (role : Layered.Replay.LayerRole circuit) (start : ℕ) :
    FrontendReplay.queryIndex circuit role start = start+FrontendReplay.queryIndex circuit role 0 := by
  induction circuit generalizing start with
  | input => exact Fin.elim0 role
  | entry _ _ _ ih =>
      cases role with
      | inl => rfl
      | inr role => exact ih role start
  | @layer out mid input a body rest ih =>
      rcases role with i | i | i | i | role
      · rfl
      · simp only [FrontendReplay.queryIndex]; omega
      · simp only [FrontendReplay.queryIndex]; omega
      · simp only [FrontendReplay.queryIndex]; omega
      · simp only [FrontendReplay.queryIndex]
        rw [ih role (start+mid+2), ih role (0+mid+2)]
        omega

/-- `head` is the role of the answer that opens this circuit: the frontend's
opening boundary at the top, and the preceding layer's combine below it. All
tests of that answer (entries, assertions, a combine) share the role. -/
def layerLocated {out mid input assertions : ℕ}
    {body : LfzkV2.Native.CircuitLayer (Cube out) (Cube mid) (Fin assertions) F}
    {rest : Layered.Circuit F mid input} (side : Side) (first : ℕ)
    (next : List Entry × List Fragment) (last : Bool) (head : Role)
    (tail : Layered.Replay.LayerRole rest → Role) :
    Layered.Replay.LayerRole (.layer assertions body rest) → Role
  | .inl _ => head
  | .inr (.inl i) => .sumcheck side first i.val
  | .inr (.inr (.inl _)) => .terminal side first
  | .inr (.inr (.inr (.inl _))) => .combine side first next.1 next.2 last
  | .inr (.inr (.inr (.inr role))) => tail role

/-- Ordinary full-field coordinates in one frontend answer. A terminal
answer, and `eta`, instead use the separately counted nonzero sampler. -/
def coordinates : Role → ℕ
  | .inputAssertions _ entries => (entries.map Entry.outputs).sum
  | .assertions _ _ entries fragments => (entries.map Entry.outputs).sum +
      ((fragments.map Fragment.quadraticAssertions).sum + (fragments.map Fragment.linearAssertions).sum)
  | .sumcheck .. => 1
  | .combine _ _ entries fragments _ => 1+((entries.map Entry.outputs).sum +
      ((fragments.map Fragment.quadraticAssertions).sum + (fragments.map Fragment.linearAssertions).sum))
  | _ => 0

/-- An algebraic entry or assertion can share a combine domain. The other
retained tests have exactly their own protocol domain. -/
def CompatibleDomain : Linear.Challenges.Kind → Domain → Prop
  | .terminal, domain => domain = .terminal
  | .ordinary .round, domain => domain = .sumcheck
  | .ordinary .combine, domain => domain = .combine
  | .ordinary (.assertions _), domain => domain = .assertions ∨ domain = .combine
  | .ordinary (.output _), _ => False

namespace Plan

def frontend : {out input : ℕ} → {circuit : Layered.Circuit F out input} → Plan F circuit → Frontend
  | _, _, _, .input => ⟨[],[]⟩
  | _, _, _, .inputEntry metadata _ => ⟨[],metadata.entries⟩
  | _, _, _, .layer (mid := mid) metadata tail =>
      ⟨⟨[],metadata.fragments,mid⟩ :: tail.frontend.stages,tail.frontend.inputEntries⟩
  | _, _, _, .entryLayer (mid := mid) entries _ metadata tail =>
      ⟨⟨entries.entries,metadata.fragments,mid⟩ :: tail.frontend.stages,tail.frontend.inputEntries⟩

/-- The combine role that closes a layer whose tail has plan `tail`. -/
def combineRole {out input : ℕ} {circuit : Layered.Circuit F out input} (tail : Plan F circuit)
    (side : Side) (first : ℕ) : Role :=
  .combine side first (tail.frontend.weightsAt 0).1 (tail.frontend.weightsAt 0).2
    tail.frontend.stages.isEmpty

def locatedRole : {out input : ℕ} → {circuit : Layered.Circuit F out input} →
    Plan F circuit → Side → ℕ → Role → Layered.Replay.LayerRole circuit → Role
  | _, _, _, .input, _, _, _, role => Fin.elim0 role
  | _, _, _, .inputEntry _ _, _, _, head, role =>
      match role with
      | .inl _ => head
      | .inr role => Fin.elim0 role
  | _, _, _, .layer _ tail, side, first, head, role =>
      layerLocated side first (tail.frontend.weightsAt 0) tail.frontend.stages.isEmpty head
        (tail.locatedRole side (first+1) (tail.combineRole side first)) role
  | _, _, _, .entryLayer _ _ _ tail, side, first, head, role =>
      match role with
      | .inl _ => head
      | .inr role => layerLocated side first (tail.frontend.weightsAt 0) tail.frontend.stages.isEmpty
          head (tail.locatedRole side (first+1) (tail.combineRole side first)) role

theorem coalesced {out input : ℕ} {circuit : Layered.Circuit F out input} (plan : Plan F circuit) :
    FrontendReplay.Coalesced circuit := by
  induction plan with
  | input => trivial
  | inputEntry => exact ⟨trivial,trivial⟩
  | layer _ _ ih => exact ih
  | entryLayer _ _ _ _ ih => exact ⟨trivial,ih⟩

/-- Exact maximum coordinate endpoint, including the weights that follow
alpha in each combine answer. Terminal nonzero sampling has its own decoder
law and needs no ordinary coordinate. -/
def capacityFrom : {out input : ℕ} → {circuit : Layered.Circuit F out input} →
    Plan F circuit → ℕ → ℕ
  | _, _, _, .input, offset => offset
  | _, _, _, .inputEntry (checks := checks) _ _, offset => offset+checks
  | _, _, _, .layer (assertions := a) _ tail, offset =>
      max (offset+a) (max 1 (tail.capacityFrom 1))
  | _, _, _, .entryLayer (checks := checks) (assertions := a) _ _ _ tail, offset =>
      max (offset+checks+a) (max 1 (tail.capacityFrom 1))

def capacity {out input : ℕ} {circuit : Layered.Circuit F out input} (plan : Plan F circuit) : ℕ :=
  plan.capacityFrom 0

theorem fits_of_capacityFrom_le {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : Plan F circuit) (offset capacity : ℕ) (h : plan.capacityFrom offset ≤ capacity) :
    FrontendReplay.Fits capacity circuit offset := by
  induction plan generalizing offset with
  | input => trivial
  | inputEntry => exact ⟨h,trivial⟩
  | layer metadata tail ih =>
      exact ⟨(max_le_iff.mp h).1,(max_le_iff.mp (max_le_iff.mp h).2).1,
        ih _ (max_le_iff.mp (max_le_iff.mp h).2).2⟩
  | entryLayer entries entry metadata tail ih =>
      have ha := (max_le_iff.mp h).1
      exact ⟨by omega,ha,(max_le_iff.mp (max_le_iff.mp h).2).1,
        ih _ (max_le_iff.mp (max_le_iff.mp h).2).2⟩

theorem fits {out input : ℕ} {circuit : Layered.Circuit F out input} (plan : Plan F circuit) :
    FrontendReplay.Fits plan.capacity circuit 0 :=
  plan.fits_of_capacityFrom_le 0 plan.capacity le_rfl

theorem hasLayers_eq {out input : ℕ} {circuit : Layered.Circuit F out input} (plan : Plan F circuit) :
    FrontendReplay.hasLayers circuit = !plan.frontend.stages.isEmpty := by
  cases plan <;> rfl

/-- The last answer's used coordinates: alpha after a layer, then the
input-only entries. -/
theorem lastWidth_eq {out input : ℕ} {circuit : Layered.Circuit F out input} (plan : Plan F circuit)
    (offset : ℕ) : FrontendReplay.lastWidth circuit offset =
      (if FrontendReplay.hasLayers circuit then 1 else offset) +
        (plan.frontend.inputEntries.map Entry.outputs).sum := by
  induction plan generalizing offset with
  | input => simp [FrontendReplay.lastWidth, FrontendReplay.hasLayers, frontend]
  | inputEntry metadata entry =>
      simp [FrontendReplay.lastWidth, FrontendReplay.hasLayers, frontend, metadata.count]
  | layer metadata tail ih =>
      rw [FrontendReplay.lastWidth, ih 1]
      simp [FrontendReplay.hasLayers, frontend]
  | entryLayer entries entry metadata tail ih =>
      rw [FrontendReplay.lastWidth, FrontendReplay.lastWidth, ih 1]
      simp [FrontendReplay.hasLayers, frontend]

theorem slots_eq_stageRoles_length {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : Plan F circuit) (side : Side) (first : ℕ) :
    FrontendReplay.slots circuit = (stageRoles side first plan.frontend).length + 1 := by
  induction plan generalizing first with
  | input => rfl
  | inputEntry => rfl
  | @layer out mid input assertions body rest metadata tail ih =>
      change mid+2+FrontendReplay.slots rest = _
      change _ = (stageRoles side first ⟨⟨[],metadata.fragments,mid⟩ :: tail.frontend.stages,
        tail.frontend.inputEntries⟩).length + 1
      rw [stageRoles_cons, List.length_append, Stage.roles_length, ih (first+1)]
      rfl
  | @entryLayer out next mid input checks assertions entries entry body rest metadata tail ih =>
      change mid+2+FrontendReplay.slots rest = _
      change _ = (stageRoles side first ⟨⟨entries.entries,metadata.fragments,mid⟩ :: tail.frontend.stages,
        tail.frontend.inputEntries⟩).length + 1
      rw [stageRoles_cons, List.length_append, Stage.roles_length, ih (first+1)]
      rfl

/-- Entries and fragments contribute coordinates, never extra boundaries.
This includes scalar layers and the one input-only assertion boundary. -/
theorem slots_eq_roles_length {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : Plan F circuit) (side : Side) :
    FrontendReplay.slots circuit = (plan.frontend.roles side).length := by
  rw [roles_eq_stageRoles, List.length_cons]
  exact plan.slots_eq_stageRoles_length side 0

private theorem layer_role_get {out mid input assertions : ℕ}
    {body : LfzkV2.Native.CircuitLayer (Cube out) (Cube mid) (Fin assertions) F}
    {rest : Layered.Circuit F mid input}
    (tail : Plan F rest) (metadata : LayerMetadata body) (entering : List Entry)
    (side : Side) (first : ℕ) (head : Role)
    (htail : ∀ role, (tail.combineRole side first :: stageRoles side (first+1) tail.frontend)[
      FrontendReplay.queryIndex rest role 0]? =
        some (tail.locatedRole side (first+1) (tail.combineRole side first) role))
    (role : Layered.Replay.LayerRole (.layer assertions body rest)) :
    (head :: stageRoles side first ⟨⟨entering,metadata.fragments,mid⟩ :: tail.frontend.stages,
      tail.frontend.inputEntries⟩)[FrontendReplay.queryIndex (.layer assertions body rest) role 0]? =
      some (layerLocated side first (tail.frontend.weightsAt 0) tail.frontend.stages.isEmpty head
        (tail.locatedRole side (first+1) (tail.combineRole side first)) role) := by
  rw [stageRoles_cons]
  have hstage := Stage.roles_length side first ⟨entering,metadata.fragments,mid⟩
    (tail.frontend.weightsAt 0) tail.frontend.stages.isEmpty
  rcases role with i | i | i | i | role
  · rfl
  · simp only [FrontendReplay.queryIndex,layerLocated,Nat.zero_add]
    rw [Nat.add_comm 1 i.val, List.getElem?_cons_succ,
      List.getElem?_append_left (by rw [hstage]; change i.val < mid+2; have := i.isLt; omega)]
    exact stage_round side first ⟨entering,metadata.fragments,mid⟩ _ _ i
  · simp only [FrontendReplay.queryIndex,layerLocated,Nat.zero_add]
    rw [Nat.add_comm 1 mid, List.getElem?_cons_succ,
      List.getElem?_append_left (by rw [hstage]; change mid < mid+2; omega)]
    exact stage_terminal side first ⟨entering,metadata.fragments,mid⟩ _ _
  · simp only [FrontendReplay.queryIndex,layerLocated,Nat.zero_add]
    rw [show mid+2 = (mid+1)+1 by omega, List.getElem?_cons_succ,
      List.getElem?_append_left (by rw [hstage]; change mid+1 < mid+2; omega)]
    exact stage_combine side first ⟨entering,metadata.fragments,mid⟩ _ _
  · simp only [FrontendReplay.queryIndex,layerLocated,Nat.zero_add]
    rw [queryIndex_shift]
    have hcomb : (head :: (Stage.roles side first ⟨entering,metadata.fragments,mid⟩
        (tail.frontend.weightsAt 0) tail.frontend.stages.isEmpty ++
          stageRoles side (first+1) tail.frontend)) =
        (head :: ((List.range mid).map (Role.sumcheck side first) ++ [Role.terminal side first])) ++
          (tail.combineRole side first :: stageRoles side (first+1) tail.frontend) := by
      simp [Stage.roles, combineRole]
    rw [hcomb, List.getElem?_append_right (by simp)]
    simp only [List.length_cons, List.length_append, List.length_map, List.length_range,
      List.length_nil]
    rw [show mid+2+FrontendReplay.queryIndex rest role 0-(mid+(0+1)+1) =
      FrontendReplay.queryIndex rest role 0 by omega]
    exact htail role

/-- Every retained algebraic event lands at its actual grouped role. In
particular the map need not be injective: entry/assertion events share the
opening answer, and a combine shares its answer with the next weights. -/
theorem role_get_queryIndex {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : Plan F circuit) (side : Side) (first : ℕ) (head : Role)
    (role : Layered.Replay.LayerRole circuit) :
    (head :: stageRoles side first plan.frontend)[FrontendReplay.queryIndex circuit role 0]? =
      some (plan.locatedRole side first head role) := by
  induction plan generalizing first head with
  | input => exact Fin.elim0 role
  | inputEntry metadata entry =>
      cases role with
      | inl => rfl
      | inr role => exact Fin.elim0 role
  | layer metadata tail ih =>
      exact layer_role_get tail metadata [] side first head (ih (first+1) _) role
  | entryLayer entries entry metadata tail ih =>
      cases role with
      | inl => rfl
      | inr role => exact layer_role_get tail metadata entries.entries side first head (ih (first+1) _) role

theorem frontend_role_get_queryIndex {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : Plan F circuit) (side : Side) (role : Layered.Replay.LayerRole circuit) :
    (plan.frontend.roles side)[FrontendReplay.queryIndex circuit role 0]? =
      some (plan.locatedRole side 0 (plan.frontend.opening side) role) := by
  rw [roles_eq_stageRoles]
  exact plan.role_get_queryIndex side 0 _ role

def roleIndex {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : Plan F circuit) (side : Side) (role : Layered.Replay.LayerRole circuit) :
    Fin (plan.frontend.roles side).length :=
  ⟨FrontendReplay.queryIndex circuit role 0,by
    rw [← plan.slots_eq_roles_length]
    simpa only [Nat.zero_add] using FrontendReplay.queryIndex_lt circuit role 0⟩

theorem opening_side (frontend : Frontend) (side : Side) :
    frontendSide (frontend.opening side) = some side := by
  unfold Frontend.opening
  split <;> rfl

theorem opening_domain (frontend : Frontend) (side : Side) :
    (frontend.opening side).domain = .assertions := by
  unfold Frontend.opening
  split <;> rfl

/-- The opening answer belongs to the assertion domain at the top and to the
combine domain below it; its tests are entries and assertions only. -/
theorem locatedRole_domain {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : Plan F circuit) (side : Side) (first : ℕ) (head : Role)
    (hhead : head.domain = .assertions ∨ head.domain = .combine)
    (role : Layered.Replay.LayerRole circuit) :
    CompatibleDomain (Layered.Replay.LayerRole.kind circuit role)
      (plan.locatedRole side first head role).domain := by
  induction plan generalizing first head with
  | input => exact Fin.elim0 role
  | inputEntry metadata entry =>
      cases role with
      | inl => exact hhead
      | inr role => exact Fin.elim0 role
  | @layer out mid input assertions body rest metadata tail ih =>
      rcases role with i | i | i | i | role
      · exact hhead
      · rfl
      · rfl
      · rfl
      · exact ih (first+1) _ (Or.inr rfl) role
  | @entryLayer out next mid input checks assertions entries entry body rest metadata tail ih =>
      rcases role with i | i | i | i | i | role
      · exact hhead
      · exact hhead
      · rfl
      · rfl
      · rfl
      · exact ih (first+1) _ (Or.inr rfl) role

/-- The weights read at a circuit's opening answer fit after `offset`. -/
theorem opening_coordinates_le {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : Plan F circuit) (offset : ℕ) :
    offset+((plan.frontend.weightsAt 0).1.map Entry.outputs).sum +
      (((plan.frontend.weightsAt 0).2.map Fragment.quadraticAssertions).sum +
        ((plan.frontend.weightsAt 0).2.map Fragment.linearAssertions).sum) ≤ plan.capacityFrom offset := by
  cases plan with
  | input => simp [frontend, Frontend.weightsAt, capacityFrom]
  | inputEntry metadata entry =>
      simp [frontend, Frontend.weightsAt, capacityFrom, metadata.count]
  | layer metadata tail =>
      simp only [frontend, Frontend.weightsAt, List.getElem?_cons_zero, List.map_nil, List.sum_nil,
        metadata.count, capacityFrom]
      omega
  | entryLayer entries entry metadata tail =>
      simp only [frontend, Frontend.weightsAt, List.getElem?_cons_zero, entries.count,
        metadata.count, capacityFrom]
      omega

theorem combineRole_coordinates_le {out input : ℕ} {circuit : Layered.Circuit F out input}
    (tail : Plan F circuit) (side : Side) (first : ℕ) :
    coordinates (tail.combineRole side first) ≤ tail.capacityFrom 1 := by
  have h := tail.opening_coordinates_le 1
  simp only [combineRole, coordinates]
  omega

theorem opening_role_coordinates_le {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : Plan F circuit) (side : Side) :
    coordinates (plan.frontend.opening side) ≤ plan.capacityFrom 0 := by
  have h := plan.opening_coordinates_le 0
  unfold Frontend.opening
  split
  · next stage hs =>
      simp only [Frontend.weightsAt, hs] at h
      simp only [coordinates]
      omega
  · next hs =>
      simp only [Frontend.weightsAt, hs, List.map_nil, List.sum_nil] at h
      simp only [coordinates]
      omega

/-- Every ordinary coordinate consumed by any actual grouped role fits in
the computed decoder capacity. This is derived from syntax and public counts,
not supplied as a separate schedule or capacity certificate. -/
theorem locatedRole_coordinates_le {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : Plan F circuit) (side : Side) (first offset : ℕ) (head : Role)
    (hhead : coordinates head ≤ plan.capacityFrom offset)
    (role : Layered.Replay.LayerRole circuit) :
    coordinates (plan.locatedRole side first head role) ≤ plan.capacityFrom offset := by
  induction plan generalizing first offset head with
  | input => exact Fin.elim0 role
  | inputEntry metadata entry =>
      cases role with
      | inl => exact hhead
      | inr role => exact Fin.elim0 role
  | @layer _ _ _ a _ _ metadata tail ih =>
      have hone : 1 ≤ max (offset+a) (max 1 (tail.capacityFrom 1)) :=
        (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
      have htail : tail.capacityFrom 1 ≤ max (offset+a) (max 1 (tail.capacityFrom 1)) :=
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
      rcases role with i | i | i | i | role
      · exact hhead
      · exact hone
      · exact Nat.zero_le _
      · exact (tail.combineRole_coordinates_le side first).trans htail
      · exact (ih (first+1) 1 _ (tail.combineRole_coordinates_le side first) role).trans htail
  | @entryLayer _ _ _ _ checks a entries entry _ _ metadata tail ih =>
      have hone : 1 ≤ max (offset+checks+a) (max 1 (tail.capacityFrom 1)) :=
        (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
      have htail : tail.capacityFrom 1 ≤ max (offset+checks+a) (max 1 (tail.capacityFrom 1)) :=
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
      rcases role with i | i | i | i | i | role
      · exact hhead
      · exact hhead
      · exact hone
      · exact Nat.zero_le _
      · exact (tail.combineRole_coordinates_le side first).trans htail
      · exact (ih (first+1) 1 _ (tail.combineRole_coordinates_le side first) role).trans htail

end Plan
end LfzkV2.Current.FrontendSchedule

namespace LfzkV2.Current.Geometry

/-- Prime sumcheck follows the shared fingerprint boundary. -/
def primeStart (_g : Geometry) : ℕ := 1

/-- The conversion boundary separates prime and binary sumcheck. -/
def binaryStart (g : Geometry) : ℕ := (g.prime.roles .prime).length+2

def primeIndex (g : Geometry) (i : Fin (g.prime.roles .prime).length) : Fin g.roles.length :=
  ⟨g.primeStart+i.val,by
    have h := g.roles_length
    have hi := i.isLt
    dsimp only [primeStart]
    omega⟩

def binaryIndex (g : Geometry) (i : Fin (g.binary.roles .binary).length) : Fin g.roles.length :=
  ⟨g.binaryStart+i.val,by
    have h := g.roles_length
    have hi := i.isLt
    dsimp only [binaryStart]
    omega⟩

theorem prime_role_get (g : Geometry) (i : Fin (g.prime.roles .prime).length) :
    g.roles.get (g.primeIndex i) = (g.prime.roles .prime).get i := by
  have hget : g.roles[g.primeStart+i.val]? = some ((g.prime.roles .prime).get i) := by
    have hr : g.roles = [.fingerprint] ++ ((g.prime.roles .prime) ++
      [.conversion] ++ g.binary.roles .binary ++
      (if g.packingDegree = 1 then [] else [.packing]) ++ [.batching,.opening]) := by
      rw [g.roles_eq]
      simp only [List.append_assoc]
    rw [hr,List.getElem?_append_right (by change 1 ≤ 1+i.val; omega)]
    simp only [primeStart,List.length_singleton,Nat.add_sub_cancel_left]
    simp only [List.append_assoc]
    rw [List.getElem?_append_left i.isLt]
    exact List.getElem?_eq_getElem i.isLt
  have h := List.getElem?_eq_getElem (l := g.roles) (g.primeIndex i).isLt
  exact Option.some.inj (h.symm.trans hget)

theorem binary_role_get (g : Geometry) (i : Fin (g.binary.roles .binary).length) :
    g.roles.get (g.binaryIndex i) = (g.binary.roles .binary).get i := by
  let leadingRoles : List Role := [.fingerprint] ++ g.prime.roles .prime ++ [.conversion]
  have hlen : leadingRoles.length = g.binaryStart := by
    simp only [leadingRoles,binaryStart,List.length_append,List.length_cons,List.length_nil]
    omega
  have hr : g.roles = leadingRoles ++ (g.binary.roles .binary ++
      (if g.packingDegree = 1 then [] else [.packing]) ++ [.batching,.opening]) := by
    rw [g.roles_eq]
    simp only [leadingRoles,List.append_assoc]
  have hget : g.roles[g.binaryStart+i.val]? = some ((g.binary.roles .binary).get i) := by
    rw [hr,List.getElem?_append_right (by rw [hlen]; omega),hlen,Nat.add_sub_cancel_left]
    simp only [List.append_assoc]
    rw [List.getElem?_append_left i.isLt]
    exact List.getElem?_eq_getElem i.isLt
  have h := List.getElem?_eq_getElem (l := g.roles) (g.binaryIndex i).isLt
  exact Option.some.inj (h.symm.trans hget)

theorem primeStart_pos (g : Geometry) : 0 < g.primeStart := by change 0 < 1; decide
theorem binaryStart_pos (g : Geometry) : 0 < g.binaryStart := by unfold binaryStart; omega

theorem binary_window (g : Geometry) :
    g.binaryStart+(g.binary.roles .binary).length ≤ g.roles.length := by
  have h := g.roles_length
  unfold binaryStart
  omega

end LfzkV2.Current.Geometry
