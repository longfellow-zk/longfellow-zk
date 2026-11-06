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

/-- The same public frontend role list with an explicit initial stage
number, used when descending into a tail of the circuit. -/
def stageRoles (side : Side) (first : ℕ) (stages : List Stage) (inputs : List Entry) : List Role :=
  (List.finRange stages.length).flatMap fun i =>
    (stages.get i).roles side (first+i.val) (if i.val+1 = stages.length then inputs else [])

def rolesFrom (frontend : Frontend) (side : Side) (first : ℕ) : List Role :=
  if frontend.stages.isEmpty then [.inputAssertions side frontend.inputEntries]
  else stageRoles side first frontend.stages frontend.inputEntries

theorem rolesFrom_zero (frontend : Frontend) (side : Side) :
    rolesFrom frontend side 0 = frontend.roles side := by
  simp only [rolesFrom,stageRoles,Frontend.roles,Nat.zero_add]

theorem stageRoles_cons (side : Side) (first : ℕ) (stage : Stage) (tail : List Stage)
    (inputs : List Entry) :
    stageRoles side first (stage :: tail) inputs =
      stage.roles side first (if tail.isEmpty then inputs else []) ++
        stageRoles side (first+1) tail inputs := by
  simp only [stageRoles,List.length_cons,List.finRange_succ,List.flatMap_cons,List.flatMap_map,
    List.get_cons_zero,Fin.val_zero,Fin.val_succ,Nat.add_zero]
  congr 2
  · split_ifs <;> simp_all
  · funext i
    congr 1
    · omega
    · congr 1
      exact propext (by omega)

theorem rolesFrom_cons (side : Side) (first : ℕ) (stage : Stage) (tail : List Stage)
    (inputs : List Entry) :
    rolesFrom ⟨stage :: tail,inputs⟩ side first =
      stage.roles side first (if tail.isEmpty then inputs else []) ++
        if tail.isEmpty then [] else rolesFrom ⟨tail,inputs⟩ side (first+1) := by
  simp only [rolesFrom,List.isEmpty_cons,Bool.false_eq_true,↓reduceIte,stageRoles_cons]
  by_cases h : tail.isEmpty
  · have he : tail = [] := List.isEmpty_iff.mp h
    subst tail
    rfl
  · simp only [h,Bool.false_eq_true,↓reduceIte]

theorem stage_assertions (side : Side) (first : ℕ) (stage : Stage) (inputs : List Entry) :
    (stage.roles side first inputs)[0]? = some (.assertions side first stage.entering stage.fragments) := rfl

theorem stage_round (side : Side) (first : ℕ) (stage : Stage) (inputs : List Entry)
    (i : Fin stage.rounds) :
    (stage.roles side first inputs)[1+i.val]? = some (.sumcheck side first i.val) := by
  rw [Nat.add_comm 1 i.val]
  change ((List.range stage.rounds).map (Role.sumcheck side first) ++
    [Role.terminal side first,Role.combine side first inputs])[i.val]? = _
  rw [List.getElem?_append_left (by simp only [List.length_map,List.length_range]; exact i.isLt)]
  simp only [List.getElem?_map,List.getElem?_range i.isLt,Option.map_some]

theorem stage_terminal (side : Side) (first : ℕ) (stage : Stage) (inputs : List Entry) :
    (stage.roles side first inputs)[1+stage.rounds]? = some (.terminal side first) := by
  rw [Nat.add_comm 1 stage.rounds]
  simp [Stage.roles]

theorem stage_combine (side : Side) (first : ℕ) (stage : Stage) (inputs : List Entry) :
    (stage.roles side first inputs)[stage.rounds+2]? = some (.combine side first inputs) := by
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
        rw [ih role (if FrontendReplay.hasLayers rest then start+mid+3 else start+mid+2),
          ih role (if FrontendReplay.hasLayers rest then 0+mid+3 else 0+mid+2)]
        split_ifs <;> omega

theorem queryIndex_no_layers {out input : ℕ} (circuit : Layered.Circuit F out input)
    (h : FrontendReplay.hasLayers circuit = false) (role : Layered.Replay.LayerRole circuit) (start : ℕ) :
    FrontendReplay.queryIndex circuit role start = start := by
  induction circuit with
  | input => exact Fin.elim0 role
  | entry _ _ _ ih =>
      cases role with
      | inl => rfl
      | inr role => exact ih h role
  | layer => simp only [FrontendReplay.hasLayers,Bool.true_eq_false] at h

/-- Entry and assertion tests share the first role. At the final layer,
input-entry tests share the combine role instead of introducing another one. -/
def layerLocated {out mid input assertions : ℕ}
    {body : LfzkV2.Native.CircuitLayer (Cube out) (Cube mid) (Fin assertions) F}
    {rest : Layered.Circuit F mid input} (side : Side) (first : ℕ)
    (entering : List Entry) (fragments : List Fragment) (inputs : List Entry)
    (tail : Layered.Replay.LayerRole rest → Role) :
    Layered.Replay.LayerRole (.layer assertions body rest) → Role
  | .inl _ => .assertions side first entering fragments
  | .inr (.inl i) => .sumcheck side first i.val
  | .inr (.inr (.inl _)) => .terminal side first
  | .inr (.inr (.inr (.inl _))) => .combine side first
      (if FrontendReplay.hasLayers rest then [] else inputs)
  | .inr (.inr (.inr (.inr role))) =>
      if FrontendReplay.hasLayers rest then tail role else .combine side first inputs

/-- Ordinary full-field coordinates in one frontend answer. A terminal
answer instead uses the separately counted nonzero sampler. -/
def coordinates : Role → ℕ
  | .inputAssertions _ entries => (entries.map Entry.outputs).sum
  | .assertions _ _ entries fragments => (entries.map Entry.outputs).sum +
      ((fragments.map Fragment.quadraticAssertions).sum + (fragments.map Fragment.linearAssertions).sum)
  | .sumcheck .. => 1
  | .combine _ _ entries => 1+(entries.map Entry.outputs).sum
  | _ => 0

/-- An algebraic entry can share the final combine domain. The other three
retained tests have exactly their own protocol domain. -/
def CompatibleDomain : Linear.Challenges.Kind → Domain → Prop
  | .terminal, domain => domain = .terminal
  | .ordinary .round, domain => domain = .sumcheck
  | .ordinary .combine, domain => domain = .combine
  | .ordinary (.assertions _), domain => domain = .assertions ∨ domain = .combine
  | .ordinary (.output _), _ => False

theorem kind_no_layers {out input : ℕ} (circuit : Layered.Circuit F out input)
    (h : FrontendReplay.hasLayers circuit = false) (role : Layered.Replay.LayerRole circuit) :
    ∃ checks, Layered.Replay.LayerRole.kind circuit role = .ordinary (.assertions checks) := by
  induction circuit with
  | input => exact Fin.elim0 role
  | entry checks _ _ ih =>
      cases role with
      | inl => exact ⟨checks,rfl⟩
      | inr role => exact ih h role
  | layer => simp only [FrontendReplay.hasLayers,Bool.true_eq_false] at h

namespace Plan

def frontend : {out input : ℕ} → {circuit : Layered.Circuit F out input} → Plan F circuit → Frontend
  | _, _, _, .input => ⟨[],[]⟩
  | _, _, _, .inputEntry metadata _ => ⟨[],metadata.entries⟩
  | _, _, _, .layer (mid := mid) metadata tail =>
      ⟨⟨[],metadata.fragments,mid⟩ :: tail.frontend.stages,tail.frontend.inputEntries⟩
  | _, _, _, .entryLayer (mid := mid) entries _ metadata tail =>
      ⟨⟨entries.entries,metadata.fragments,mid⟩ :: tail.frontend.stages,tail.frontend.inputEntries⟩

def locatedRole : {out input : ℕ} → {circuit : Layered.Circuit F out input} →
    Plan F circuit → Side → ℕ → Layered.Replay.LayerRole circuit → Role
  | _, _, _, .input, _, _, role => Fin.elim0 role
  | _, _, _, .inputEntry metadata _, side, _, role =>
      match role with
      | .inl _ => .inputAssertions side metadata.entries
      | .inr role => Fin.elim0 role
  | _, _, _, .layer metadata tail, side, first, role =>
      layerLocated side first [] metadata.fragments tail.frontend.inputEntries
        (tail.locatedRole side (first+1)) role
  | _, _, _, .entryLayer entries _ metadata tail, side, first, role =>
      match role with
      | .inl _ => .assertions side first entries.entries metadata.fragments
      | .inr role => layerLocated side first entries.entries metadata.fragments tail.frontend.inputEntries
          (tail.locatedRole side (first+1)) role

theorem coalesced {out input : ℕ} {circuit : Layered.Circuit F out input} (plan : Plan F circuit) :
    FrontendReplay.Coalesced circuit := by
  induction plan with
  | input => trivial
  | inputEntry => exact ⟨trivial,trivial⟩
  | layer _ _ ih => exact ih
  | entryLayer _ _ _ _ ih => exact ⟨trivial,ih⟩

/-- Exact maximum coordinate endpoint, including the entry coefficients
that follow alpha in the last combine answer. Terminal nonzero sampling has
its own decoder law and needs no ordinary coordinate. -/
def capacityFrom : {out input : ℕ} → {circuit : Layered.Circuit F out input} →
    Plan F circuit → ℕ → ℕ
  | _, _, _, .input, offset => offset
  | _, _, _, .inputEntry (checks := checks) _ _, offset => offset+checks
  | _, _, _, .layer (assertions := a) (rest := rest) _ tail, offset =>
      max (offset+a) (max 1 (tail.capacityFrom (if FrontendReplay.hasLayers rest then 0 else 1)))
  | _, _, _, .entryLayer (checks := checks) (assertions := a) (rest := rest) _ _ _ tail, offset =>
      max (offset+checks+a) (max 1 (tail.capacityFrom (if FrontendReplay.hasLayers rest then 0 else 1)))

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

theorem stage_widths {out input : ℕ} {circuit : Layered.Circuit F out input} (plan : Plan F circuit) :
    plan.frontend.stages.map Stage.rounds = FrontendBody.widths circuit := by
  induction plan with
  | input => rfl
  | inputEntry => rfl
  | layer metadata tail ih => simpa only [frontend,List.map_cons,FrontendBody.widths] using congrArg (List.cons _) ih
  | entryLayer entries entry metadata tail ih =>
      simpa only [frontend,List.map_cons,FrontendBody.widths] using congrArg (List.cons _) ih

theorem hasLayers_eq {out input : ℕ} {circuit : Layered.Circuit F out input} (plan : Plan F circuit) :
    FrontendReplay.hasLayers circuit = !plan.frontend.stages.isEmpty := by
  cases plan <;> rfl

theorem slots_eq_rolesFrom_length {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : Plan F circuit) (side : Side) (first : ℕ) :
    FrontendReplay.slots circuit = (rolesFrom plan.frontend side first).length := by
  induction plan generalizing first with
  | input => rfl
  | inputEntry => rfl
  | @layer out mid input assertions body rest metadata tail ih =>
      change mid+3+(if FrontendReplay.hasLayers rest then FrontendReplay.slots rest else 0) = _
      rw [tail.hasLayers_eq]
      change _ = (rolesFrom ⟨⟨[],metadata.fragments,mid⟩ :: tail.frontend.stages,
        tail.frontend.inputEntries⟩ side first).length
      rw [rolesFrom_cons]
      cases h : tail.frontend.stages.isEmpty <;>
        simp only [Bool.not_false,Bool.not_true,Bool.false_eq_true,↓reduceIte,
          List.length_append,Stage.roles_length,List.length_nil,Nat.add_zero]
      exact congrArg (mid+3+·) (ih (first+1))
  | @entryLayer out next mid input checks assertions entries entry body rest metadata tail ih =>
      change mid+3+(if FrontendReplay.hasLayers rest then FrontendReplay.slots rest else 0) = _
      rw [tail.hasLayers_eq]
      change _ = (rolesFrom ⟨⟨entries.entries,metadata.fragments,mid⟩ :: tail.frontend.stages,
        tail.frontend.inputEntries⟩ side first).length
      rw [rolesFrom_cons]
      cases h : tail.frontend.stages.isEmpty <;>
        simp only [Bool.not_false,Bool.not_true,Bool.false_eq_true,↓reduceIte,
          List.length_append,Stage.roles_length,List.length_nil,Nat.add_zero]
      exact congrArg (mid+3+·) (ih (first+1))

/-- Entries and fragments contribute coordinates, never extra boundaries.
This includes scalar layers and the one input-only assertion boundary. -/
theorem slots_eq_roles_length {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : Plan F circuit) (side : Side) :
    FrontendReplay.slots circuit = (plan.frontend.roles side).length := by
  rw [← rolesFrom_zero]
  exact plan.slots_eq_rolesFrom_length side 0

private theorem layer_role_get {out mid input assertions : ℕ}
    {body : LfzkV2.Native.CircuitLayer (Cube out) (Cube mid) (Fin assertions) F}
    {rest : Layered.Circuit F mid input}
    (tail : Plan F rest) (metadata : LayerMetadata body) (entering : List Entry)
    (side : Side) (first : ℕ)
    (htail : ∀ role, (rolesFrom tail.frontend side (first+1))[
      FrontendReplay.queryIndex rest role 0]? = some (tail.locatedRole side (first+1) role))
    (role : Layered.Replay.LayerRole (.layer assertions body rest)) :
    (rolesFrom ⟨⟨entering,metadata.fragments,mid⟩ :: tail.frontend.stages,
      tail.frontend.inputEntries⟩ side first)[FrontendReplay.queryIndex (.layer assertions body rest) role 0]? =
      some (layerLocated side first entering metadata.fragments tail.frontend.inputEntries
        (tail.locatedRole side (first+1)) role) := by
  rw [rolesFrom_cons]
  have hinputs : (if tail.frontend.stages.isEmpty then tail.frontend.inputEntries else []) =
      (if FrontendReplay.hasLayers rest then [] else tail.frontend.inputEntries) := by
    rw [tail.hasLayers_eq]
    cases tail.frontend.stages.isEmpty <;> rfl
  rcases role with i | i | i | i | role
  · simp only [FrontendReplay.queryIndex,layerLocated]
    rw [List.getElem?_append_left (by rw [Stage.roles_length]; omega)]
    exact stage_assertions side first _ _
  · simp only [FrontendReplay.queryIndex,layerLocated,Nat.zero_add]
    rw [List.getElem?_append_left (by rw [Stage.roles_length]; change 1+i.val < mid+3; have := i.isLt; omega)]
    exact stage_round side first ⟨entering,metadata.fragments,mid⟩ _ i
  · simp only [FrontendReplay.queryIndex,layerLocated,Nat.zero_add]
    rw [List.getElem?_append_left (by rw [Stage.roles_length]; change 1+mid < mid+3; omega)]
    exact stage_terminal side first ⟨entering,metadata.fragments,mid⟩ _
  · simp only [FrontendReplay.queryIndex,layerLocated,Nat.zero_add]
    rw [List.getElem?_append_left (by rw [Stage.roles_length]; change mid+2 < mid+3; omega),stage_combine,hinputs]
  · simp only [FrontendReplay.queryIndex,layerLocated]
    by_cases h : FrontendReplay.hasLayers rest = true
    · have he : tail.frontend.stages.isEmpty = false := by
        rw [tail.hasLayers_eq] at h
        cases hb : tail.frontend.stages.isEmpty <;> simp_all
      simp only [h,he,Bool.false_eq_true,↓reduceIte,Nat.zero_add]
      rw [queryIndex_shift]
      rw [List.getElem?_append_right (by rw [Stage.roles_length]; change mid+3 ≤ mid+3+_; omega)]
      simp only [Stage.roles_length,Nat.add_sub_cancel_left]
      exact htail role
    · have hf : FrontendReplay.hasLayers rest = false := Bool.eq_false_iff.mpr h
      have he : tail.frontend.stages.isEmpty = true := by
        rw [tail.hasLayers_eq] at hf
        cases hb : tail.frontend.stages.isEmpty <;> simp_all
      simp only [hf,he,Bool.false_eq_true,↓reduceIte,Nat.zero_add]
      rw [queryIndex_no_layers rest hf role (mid+2)]
      rw [List.getElem?_append_left (by rw [Stage.roles_length]; change mid+2 < mid+3; omega)]
      exact stage_combine side first ⟨entering,metadata.fragments,mid⟩ _

/-- Every retained algebraic event lands at its actual grouped role. In
particular the map need not be injective: entry/assertion events and the
final combine/input-entry events deliberately share their query. -/
theorem role_get_queryIndex {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : Plan F circuit) (side : Side) (first : ℕ) (role : Layered.Replay.LayerRole circuit) :
    (rolesFrom plan.frontend side first)[FrontendReplay.queryIndex circuit role 0]? =
      some (plan.locatedRole side first role) := by
  induction plan generalizing first with
  | input => exact Fin.elim0 role
  | inputEntry metadata entry =>
      cases role with
      | inl => rfl
      | inr role => exact Fin.elim0 role
  | layer metadata tail ih => exact layer_role_get tail metadata [] side first (ih (first+1)) role
  | entryLayer entries entry metadata tail ih =>
      cases role with
      | inl =>
          change (rolesFrom ⟨⟨entries.entries,metadata.fragments,_⟩ :: tail.frontend.stages,
            tail.frontend.inputEntries⟩ side first)[0]? = _
          rw [rolesFrom_cons,List.getElem?_append_left (by rw [Stage.roles_length]; omega)]
          rfl
      | inr role => exact layer_role_get tail metadata entries.entries side first (ih (first+1)) role

theorem frontend_role_get_queryIndex {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : Plan F circuit) (side : Side) (role : Layered.Replay.LayerRole circuit) :
    (plan.frontend.roles side)[FrontendReplay.queryIndex circuit role 0]? =
      some (plan.locatedRole side 0 role) := by
  rw [← rolesFrom_zero]
  exact plan.role_get_queryIndex side 0 role

def roleIndex {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : Plan F circuit) (side : Side) (role : Layered.Replay.LayerRole circuit) :
    Fin (plan.frontend.roles side).length :=
  ⟨FrontendReplay.queryIndex circuit role 0,by
    rw [← plan.slots_eq_roles_length]
    simpa only [Nat.zero_add] using FrontendReplay.queryIndex_lt circuit role 0⟩

theorem roleIndex_get {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : Plan F circuit) (side : Side) (role : Layered.Replay.LayerRole circuit) :
    (plan.frontend.roles side).get (plan.roleIndex side role) = plan.locatedRole side 0 role := by
  have h := plan.frontend_role_get_queryIndex side role
  have hg := List.getElem?_eq_getElem (l := plan.frontend.roles side) (plan.roleIndex side role).isLt
  exact Option.some.inj (hg.symm.trans h)

theorem locatedRole_side {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : Plan F circuit) (side : Side) (first : ℕ) (role : Layered.Replay.LayerRole circuit) :
    frontendSide (plan.locatedRole side first role) = some side := by
  induction plan generalizing first with
  | input => exact Fin.elim0 role
  | inputEntry metadata entry =>
      cases role with
      | inl => rfl
      | inr role => exact Fin.elim0 role
  | layer metadata tail ih =>
      rcases role with i | i | i | i | role
      all_goals simp only [locatedRole,layerLocated,frontendSide]
      split_ifs
      · exact ih (first+1) role
      · rfl
  | entryLayer entries entry metadata tail ih =>
      rcases role with i | i | i | i | i | role
      all_goals simp only [locatedRole,layerLocated,frontendSide]
      split_ifs
      · exact ih (first+1) role
      · rfl

theorem locatedRole_domain {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : Plan F circuit) (side : Side) (first : ℕ) (role : Layered.Replay.LayerRole circuit) :
    CompatibleDomain (Layered.Replay.LayerRole.kind circuit role)
      (plan.locatedRole side first role).domain := by
  induction plan generalizing first with
  | input => exact Fin.elim0 role
  | inputEntry metadata entry =>
      cases role with
      | inl => exact Or.inl rfl
      | inr role => exact Fin.elim0 role
  | @layer out mid input assertions body rest metadata tail ih =>
      rcases role with i | i | i | i | role
      · exact Or.inl rfl
      · rfl
      · rfl
      · rfl
      · dsimp only [locatedRole,layerLocated,Layered.Replay.LayerRole.kind]
        split_ifs with h
        · exact ih (first+1) role
        · have hf : FrontendReplay.hasLayers rest = false := Bool.eq_false_iff.mpr h
          obtain ⟨checks,hkind⟩ := kind_no_layers rest hf role
          rw [hkind]
          exact Or.inr rfl
  | @entryLayer out next mid input checks assertions entries entry body rest metadata tail ih =>
      rcases role with i | i | i | i | i | role
      · exact Or.inl rfl
      · exact Or.inl rfl
      · rfl
      · rfl
      · rfl
      · dsimp only [locatedRole,layerLocated,Layered.Replay.LayerRole.kind]
        split_ifs with h
        · exact ih (first+1) role
        · have hf : FrontendReplay.hasLayers rest = false := Bool.eq_false_iff.mpr h
          obtain ⟨checks,hkind⟩ := kind_no_layers rest hf role
          rw [hkind]
          exact Or.inr rfl

theorem input_coordinates_le {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : Plan F circuit) (offset : ℕ) (h : FrontendReplay.hasLayers circuit = false) :
    offset+(plan.frontend.inputEntries.map Entry.outputs).sum ≤ plan.capacityFrom offset := by
  cases plan with
  | input => exact le_refl _
  | inputEntry metadata entry =>
      simpa only [frontend,capacityFrom,metadata.count] using (le_refl (offset+_))
  | layer => simp only [FrontendReplay.hasLayers,Bool.true_eq_false] at h
  | entryLayer => simp only [FrontendReplay.hasLayers,Bool.true_eq_false] at h

private theorem layer_coordinates_le {out mid input assertions : ℕ}
    {body : LfzkV2.Native.CircuitLayer (Cube out) (Cube mid) (Fin assertions) F}
    {rest : Layered.Circuit F mid input}
    (tail : Plan F rest) (metadata : LayerMetadata body) (entering : List Entry)
    (side : Side) (first offset : ℕ)
    (htail : ∀ role, coordinates (tail.locatedRole side (first+1) role) ≤
      tail.capacityFrom (if FrontendReplay.hasLayers rest then 0 else 1))
    (role : Layered.Replay.LayerRole (.layer assertions body rest)) :
    coordinates (layerLocated side first entering metadata.fragments tail.frontend.inputEntries
      (tail.locatedRole side (first+1)) role) ≤
      max (offset+(entering.map Entry.outputs).sum+assertions)
        (max 1 (tail.capacityFrom (if FrontendReplay.hasLayers rest then 0 else 1))) := by
  let total := max (offset+(entering.map Entry.outputs).sum+assertions)
    (max 1 (tail.capacityFrom (if FrontendReplay.hasLayers rest then 0 else 1)))
  have hhead : offset+(entering.map Entry.outputs).sum+assertions ≤ total := Nat.le_max_left _ _
  have hone : 1 ≤ total := (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have htailCap : tail.capacityFrom (if FrontendReplay.hasLayers rest then 0 else 1) ≤ total :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hinput (hf : FrontendReplay.hasLayers rest = false) :
      1+(tail.frontend.inputEntries.map Entry.outputs).sum ≤ total := by
    have hi := tail.input_coordinates_le 1 hf
    rw [hf] at htailCap
    exact hi.trans htailCap
  change coordinates (layerLocated side first entering metadata.fragments tail.frontend.inputEntries
    (tail.locatedRole side (first+1)) role) ≤ total
  rcases role with i | i | i | i | role
  · simp only [layerLocated,coordinates,metadata.count]
    omega
  · exact hone
  · exact Nat.zero_le _
  · dsimp only [layerLocated]
    split_ifs with h
    · simpa only [coordinates,List.map_nil,List.sum_nil,Nat.add_zero] using hone
    · exact hinput (Bool.eq_false_iff.mpr h)
  · dsimp only [layerLocated]
    split_ifs with h
    · exact (htail role).trans htailCap
    · exact hinput (Bool.eq_false_iff.mpr h)

/-- Every ordinary coordinate consumed by any actual grouped role fits in
the computed decoder capacity. This is derived from syntax and public counts,
not supplied as a separate schedule or capacity certificate. -/
theorem locatedRole_coordinates_le {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : Plan F circuit) (side : Side) (first offset : ℕ) (role : Layered.Replay.LayerRole circuit) :
    coordinates (plan.locatedRole side first role) ≤ plan.capacityFrom offset := by
  induction plan generalizing first offset with
  | input => exact Fin.elim0 role
  | inputEntry metadata entry =>
      cases role with
      | inl => simp only [locatedRole,coordinates,capacityFrom,metadata.count]; omega
      | inr role => exact Fin.elim0 role
  | layer metadata tail ih =>
      simpa only [locatedRole,capacityFrom,List.map_nil,List.sum_nil,Nat.add_zero] using
        layer_coordinates_le tail metadata [] side first offset (ih (first+1) _) role
  | entryLayer entries entry metadata tail ih =>
      cases role with
      | inl =>
          simp only [locatedRole,coordinates,capacityFrom,entries.count,metadata.count]
          exact (show _ ≤ offset+_+_ by omega).trans (Nat.le_max_left _ _)
      | inr role =>
          simpa only [locatedRole,capacityFrom,entries.count] using
            layer_coordinates_le tail metadata entries.entries side first offset (ih (first+1) _) role

end Plan
end LfzkV2.Current.FrontendSchedule

namespace LfzkV2.Current.Geometry

/-- Prime sumcheck follows the shared fingerprint boundary. -/
def primeStart (_g : Geometry) : ℕ := 1

/-- Three adapter boundaries separate prime and binary sumcheck. -/
def binaryStart (g : Geometry) : ℕ := (g.prime.roles .prime).length+4

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
      [.rowBatching,.rescaling,.conversion] ++ g.binary.roles .binary ++
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
  let leadingRoles : List Role := [.fingerprint] ++ g.prime.roles .prime ++ [.rowBatching,.rescaling,.conversion]
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

theorem prime_window (g : Geometry) :
    g.primeStart+(g.prime.roles .prime).length ≤ g.roles.length := by
  have h := g.roles_length
  unfold primeStart
  omega

theorem binary_window (g : Geometry) :
    g.binaryStart+(g.binary.roles .binary).length ≤ g.roles.length := by
  have h := g.roles_length
  unfold binaryStart
  omega

end LfzkV2.Current.Geometry
