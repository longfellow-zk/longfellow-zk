import LfzkV2.Current.ZeroKnowledge.HonestTranscriptRoles
import LfzkV2.Current.ZeroKnowledge.CompleteFrontendBody
import LfzkV2.Current.ZeroKnowledge.FrontendSimulationWrites

/-! The fresh-write sequence stored by the public frontend simulator is
the prefix of the actual complete-body encoder. The auxiliary writes occur
once at their existing role positions; frontend fragments introduce no extra
message or boundary. This is a static body/schedule identity. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.BodyWrites
open SumcheckV2 ApplicationSetup ConcreteSetup
open scoped Classical
set_option maxHeartbeats 800000
variable {g : Geometry} {fields : Fields} {Advice Authentication : Type}

def pureFresh (body : Body g fields Advice Authentication) (role : Role) : ProtocolWrites.Fresh g fields Advice :=
  { frontend := ProtocolWrites.frontendMessages body role }

def atRole (body : Body g fields Advice Authentication) (index : ℕ) (role : Role) : ProtocolWrites.Fresh g fields Advice where
  fingerprints := if index = g.primeStart then some body.fingerprints else none
  mu := if role = .conversion then some body.mu else none
  advice := if index = g.binaryStart then some body.advice else none
  packingU := if role = .packing then (ProtocolWrites.packingPair body).map Prod.fst else none
  packingA := if role = .batching then (ProtocolWrites.packingPair body).map Prod.snd else none
  frontend := ProtocolWrites.frontendMessages body role
  responses := if role = .opening then some (body.binaryBackend.response,body.primeBackend.response) else none

theorem mapIdx_ofFn {A V : Type} (items : List A) (f : ℕ → A → V) :
    items.mapIdx f = List.ofFn (fun i : Fin items.length => f i.val (items.get i)) := by
  induction items generalizing f with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.mapIdx_cons,List.ofFn_succ,ih,List.get_cons_zero,Fin.val_zero,Fin.val_succ]
      rfl

theorem bodyPrefix (body : Body g fields Advice Authentication) :
    List.ofFn (fun i : Fin g.batchingIndex.val => ProtocolWrites.fresh body
      ⟨i.val,by have := i.isLt; have := g.batchingIndex.isLt; omega⟩) =
      g.backendPrefix.mapIdx (atRole body) := by
  rw [mapIdx_ofFn]
  congr 1
  funext i
  have role : g.roles.get ⟨i.val,by have := i.isLt; have := g.batchingIndex.isLt; omega⟩ = g.backendPrefix.get i := by
    simp only [g.roles_eq_backend,List.get_eq_getElem,List.getElem_append_left i.isLt]
    rfl
  simp only [ProtocolWrites.fresh,atRole,role]

theorem at_frontend (body : Body g fields Advice Authentication) (index : ℕ) (role : Role) (side : Side)
    (owned : frontendSide role = some side) :
    atRole body index role =
      { fingerprints := if index = g.primeStart then some body.fingerprints else none
        advice := if index = g.binaryStart then some body.advice else none
        frontend := ProtocolWrites.frontendMessages body role } := by
  cases role <;> simp only [frontendSide,Option.some.injEq,reduceCtorEq] at owned
  all_goals rfl

theorem first_pure (body : Body g fields Advice Authentication) (frontend : Frontend) (side : Side) :
    (frontend.roles side).head?.map (pureFresh body) = some {} := by
  rcases frontend with ⟨stages,entries⟩
  cases stages with
  | nil => rfl
  | cons head tail =>
      simp only [Frontend.roles,List.isEmpty_cons,Bool.false_eq_true,↓reduceIte,List.length_cons,
        List.finRange_succ,List.flatMap_cons,List.get_cons_zero,Fin.val_zero,Stage.roles,
        List.cons_append,List.head?_cons,Option.map_some,pureFresh,ProtocolWrites.frontendMessages]

theorem mapIdx_ignore {A V : Type} (items : List A) (f : A → V) :
    items.mapIdx (fun _ item => f item) = items.map f := by
  induction items with
  | nil => rfl
  | cons head tail ih => simpa only [List.mapIdx_cons,List.map_cons] using congrArg (List.cons (f head)) ih

theorem carry_first {A V : Type} (items : List A) (ordinary : A → V) (pending : V)
    (nonempty : items ≠ []) :
    items.mapIdx (fun index item => if index = 0 then pending else ordinary item) =
      pending :: (items.map ordinary).tail := by
  cases items with
  | nil => contradiction
  | cons head tail =>
      simp only [List.mapIdx_cons,List.map_cons,List.tail_cons]
      simp only [Nat.add_eq_zero_iff,one_ne_zero,and_false,↓reduceIte,mapIdx_ignore]

theorem frontend_nonempty (body : Body g fields Advice Authentication) (frontend : Frontend) (side : Side) :
    frontend.roles side ≠ [] := by
  intro empty
  have first := first_pure body frontend side
  rw [empty] at first
  cases first

theorem first_get (body : Body g fields Advice Authentication) (frontend : Frontend) (side : Side)
    (positive : 0 < (frontend.roles side).length) :
    pureFresh body (frontend.roles side)[0] = {} := by
  have first := first_pure body frontend side
  rw [List.head?_eq_getElem?,List.getElem?_eq_getElem positive,Option.map_some] at first
  exact Option.some.inj first

theorem prime_map (body : Body g fields Advice Authentication) :
    (g.prime.roles .prime).mapIdx (fun i role => atRole body (i+1) role) =
      ({ fingerprints := some body.fingerprints } : ProtocolWrites.Fresh g fields Advice) ::
        ((g.prime.roles .prime).map (pureFresh body)).tail := by
  rw [← carry_first _ (pureFresh body) _ (frontend_nonempty body g.prime .prime)]
  apply List.mapIdx_eq_mapIdx_iff.mpr
  intro i bound
  have owned := RuntimeRoles.frontend_side .prime g.prime ((g.prime.roles .prime)[i]) (List.getElem_mem bound)
  rw [at_frontend body (i+1) _ .prime owned]
  have advice : i+1 ≠ g.binaryStart := by unfold Geometry.binaryStart; omega
  by_cases zero : i = 0
  · subst i
    have empty := congrArg ProtocolWrites.Fresh.frontend (first_get body g.prime .prime bound)
    simp only [pureFresh] at empty
    simp only [Geometry.primeStart,Nat.zero_add,↓reduceIte,if_neg advice,empty]
  · have fingerprints : i+1 ≠ g.primeStart := by unfold Geometry.primeStart; omega
    simp only [if_neg zero,if_neg fingerprints,if_neg advice,pureFresh]

theorem binary_map (body : Body g fields Advice Authentication) :
    (g.binary.roles .binary).mapIdx (fun i role => atRole body (i+g.binaryStart) role) =
      ({ advice := some body.advice } : ProtocolWrites.Fresh g fields Advice) ::
        ((g.binary.roles .binary).map (pureFresh body)).tail := by
  rw [← carry_first _ (pureFresh body) _ (frontend_nonempty body g.binary .binary)]
  apply List.mapIdx_eq_mapIdx_iff.mpr
  intro i bound
  have owned := RuntimeRoles.frontend_side .binary g.binary ((g.binary.roles .binary)[i]) (List.getElem_mem bound)
  rw [at_frontend body (i+g.binaryStart) _ .binary owned]
  have fingerprints : i+g.binaryStart ≠ g.primeStart := by unfold Geometry.binaryStart Geometry.primeStart; omega
  by_cases zero : i = 0
  · subst i
    simp only [Nat.zero_add] at fingerprints
    have empty := congrArg ProtocolWrites.Fresh.frontend (first_get body g.binary .binary bound)
    simp only [pureFresh] at empty
    simp only [Nat.zero_add,↓reduceIte,if_neg fingerprints,empty]
  · have advice : i+g.binaryStart ≠ g.binaryStart := by omega
    simp only [if_neg zero,if_neg fingerprints,if_neg advice,pureFresh]

def leading (g : Geometry) : List Role :=
  [.fingerprint] ++ g.prime.roles .prime ++ [.rowBatching,.rescaling,.conversion]

theorem leading_length (g : Geometry) : (leading g).length = g.binaryStart := by
  simp only [leading,List.length_append,List.length_cons,List.length_nil,Geometry.binaryStart]
  omega

theorem leading_map (body : Body g fields Advice Authentication) :
    (leading g).mapIdx (atRole body) =
      [WriteLog.empty] ++ ({ fingerprints := some body.fingerprints } :: ((g.prime.roles .prime).map (pureFresh body)).tail) ++
        [WriteLog.empty,WriteLog.empty,{ mu := some body.mu }] := by
  have positive : 0 < (g.prime.roles .prime).length :=
    List.length_pos_iff.mpr (frontend_nonempty body g.prime .prime)
  simp only [leading,List.mapIdx_append,List.mapIdx_cons,List.mapIdx_nil,
    List.length_cons,List.length_nil,List.length_append]
  rw [prime_map]
  simp (disch := omega) [atRole,Geometry.primeStart,Geometry.binaryStart,ProtocolWrites.frontendMessages,WriteLog.empty]
  exact ⟨⟨frontend_nonempty body g.prime .prime,by omega⟩,by omega,by omega,by omega⟩

theorem backend_map (body : Body g fields Advice Authentication) (packing : g.packingDegree ≠ 1) :
    g.backendPrefix.mapIdx (atRole body) =
      [WriteLog.empty] ++ ({ fingerprints := some body.fingerprints } :: ((g.prime.roles .prime).map (pureFresh body)).tail) ++
        [WriteLog.empty,WriteLog.empty,{ mu := some body.mu }] ++
        ({ advice := some body.advice } :: ((g.binary.roles .binary).map (pureFresh body)).tail) ++
        [{ packingU := (ProtocolWrites.packingPair body).map Prod.fst }] := by
  have roles : g.backendPrefix = leading g ++ g.binary.roles .binary ++ [.packing] := by
    simp only [Geometry.backendPrefix,leading,if_neg packing]
  rw [roles,List.mapIdx_append,List.mapIdx_append,leading_map,leading_length,binary_map]
  simp only [List.length_append,leading_length,List.mapIdx_cons,List.mapIdx_nil,Nat.zero_add]
  have positive : 0 < (g.binary.roles .binary).length :=
    List.length_pos_iff.mpr (frontend_nonempty body g.binary .binary)
  have notPrime : g.binaryStart+(g.binary.roles .binary).length ≠ g.primeStart := by
    unfold Geometry.primeStart Geometry.binaryStart
    omega
  have notBinary : g.binaryStart+(g.binary.roles .binary).length ≠ g.binaryStart := by omega
  simp only [atRole,if_neg notPrime,if_neg notBinary,ProtocolWrites.frontendMessages,
    reduceCtorEq,↓reduceIte,List.append_assoc]

section Mdoc
variable {B Key Base C : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
local notation "P" => Adapter.Mdoc.P
variable (binary : BinaryCircuit B) (prime : PrimePublic P 768)
variable (primePlan : FrontendSchedule.Plan P prime.circuit)
local notation "G" => CompleteSimulation.geometry binary prime primePlan

def rawWrites (result : CompleteSimulation.RawResult binary prime primePlan Key Base C) :
    List (CompleteSimulation.Fresh binary prime primePlan) :=
  [WriteLog.empty] ++
    WriteLog.snapshots .prime (Equiv.refl P) { fingerprints := some result.fingerprints }
      (Prefix.circuit primePlan result.primePayload false) ++
    [WriteLog.empty,WriteLog.empty,{ mu := some result.mu }] ++
    WriteLog.snapshots .binary (Equiv.refl B) { advice := some result.advice }
      (Prefix.circuit binary.plan result.binaryPayload false) ++
    [{ packingU := some result.packing.1 }]

omit [Fintype B] [DecidableEq B] in
theorem raw_bodyPrefix (root : Digest) (result : CompleteSimulation.RawResult binary prime primePlan Key Base C) :
    List.ofFn (fun i : Fin (G).batchingIndex.val => ProtocolWrites.fresh
      (CompleteFrontendBody.rawBody binary prime primePlan root result)
      ⟨i.val,by have := i.isLt; have := (G).batchingIndex.isLt; omega⟩) =
        rawWrites binary prime primePlan result := by
  let body := CompleteFrontendBody.rawBody binary prime primePlan root result
  have packing : (G).packingDegree ≠ 1 := by change (128 : ℕ) ≠ 1; decide
  have primeMap :
      (primePlan.frontend.roles .prime).map
          (fun role => WriteLog.withMessage .prime (Equiv.refl P) {}
            (Prefix.roleWrite (CompleteShape.bodyEquiv primePlan result.primePayload) role)) =
        (primePlan.frontend.roles .prime).map (pureFresh body) := by
    apply List.map_congr_left
    intro role member
    exact Prefix.role_snapshot body .prime role (RuntimeRoles.frontend_side .prime primePlan.frontend role member)
  have binaryMap :
      (binary.plan.frontend.roles .binary).map
          (fun role => WriteLog.withMessage .binary (Equiv.refl B) {}
            (Prefix.roleWrite (CompleteShape.bodyEquiv binary.plan result.binaryPayload) role)) =
        (binary.plan.frontend.roles .binary).map (pureFresh body) := by
    apply List.map_congr_left
    intro role member
    exact Prefix.role_snapshot body .binary role (RuntimeRoles.frontend_side .binary binary.plan.frontend role member)
  have primeSnap := Prefix.circuit_snapshots .prime (Equiv.refl P) primePlan result.primePayload
    ({ fingerprints := some result.fingerprints } : CompleteSimulation.Fresh binary prime primePlan)
  have binarySnap := Prefix.circuit_snapshots .binary (Equiv.refl B) binary.plan result.binaryPayload
    ({ advice := some result.advice } : CompleteSimulation.Fresh binary prime primePlan)
  rw [primeMap] at primeSnap
  rw [binaryMap] at binarySnap
  rw [bodyPrefix,backend_map body packing]
  change [WriteLog.empty] ++
      ({ fingerprints := some result.fingerprints } :: ((primePlan.frontend.roles .prime).map (pureFresh body)).tail) ++
      [WriteLog.empty,WriteLog.empty,{ mu := some result.mu }] ++
      ({ advice := some result.advice } :: ((binary.plan.frontend.roles .binary).map (pureFresh body)).tail) ++
      [{ packingU := some result.packing.1 }] = _
  rw [← primeSnap,← binarySnap]
  rfl

omit [Fintype B] [DecidableEq B] in
theorem raw_pending (root : Digest) (result : CompleteSimulation.RawResult binary prime primePlan Key Base C) :
    ProtocolWrites.fresh (CompleteFrontendBody.rawBody binary prime primePlan root result) (G).batchingIndex =
      { packingA := some result.packing.2 } := by
  have packing : binary.description.degree ≠ 1 := by change (128 : ℕ) ≠ 1; decide
  have counter : (G).batchingIndex.val = (primePlan.frontend.roles .prime).length+(binary.plan.frontend.roles .binary).length+5 := by
    simp only [Geometry.batchingIndex,Geometry.backendPrefix,CompleteSimulation.geometry,ConcreteSetup.geometry,
      if_neg packing,List.length_append,List.length_cons,List.length_nil]
    omega
  have notPrime : (G).batchingIndex.val ≠ (G).primeStart := by rw [counter]; change _ ≠ 1; omega
  have notBinary : (G).batchingIndex.val ≠ (G).binaryStart := by
    rw [counter]
    change _ ≠ (primePlan.frontend.roles .prime).length+4
    omega
  simp only [ProtocolWrites.fresh,Geometry.get_batchingIndex,if_neg notPrime,if_neg notBinary,
    ProtocolWrites.frontendMessages,reduceCtorEq,↓reduceIte]
  rfl

variable (samples : ConcreteMetadata.Samples B C)
variable (base : CompleteSimulation.BaseWriter binary prime primePlan (Base := Base) (C := C))
variable (H : CompleteSimulation.Point binary prime primePlan (Key := Key) (Base := Base) → Digest × C)

omit [DecidableEq B] in
theorem simulated_bodyPrefix (root : Digest) (context : Key) (coins : CompleteSimulation.Coins binary prime) :
    SimulationWrites.writes binary prime primePlan coins =
      List.ofFn (fun i : Fin (G).batchingIndex.val => ProtocolWrites.fresh
        (CompleteFrontendBody.body binary prime primePlan root
          (CompleteSimulation.simulate binary prime primePlan samples base H context coins))
        ⟨i.val,by have := i.isLt; have := (G).batchingIndex.isLt; omega⟩) := by
  rw [CompleteFrontendBody.body,raw_bodyPrefix]
  rfl

end Mdoc

end LfzkV2.Current.ZeroKnowledge.Frontend.BodyWrites
