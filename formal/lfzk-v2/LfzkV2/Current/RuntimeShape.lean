import LfzkV2.Current.FrontendTopology
import LfzkV2.Current.ApplicationViews

/-! One trusted public binary template determines the schedule and decoder
capacity of every generated adapter instance. Only coefficients depend on
conversion challenges and masked advice; all metadata is retained exactly. -/
noncomputable section
namespace LfzkV2.Current.RuntimeShape
open Application ApplicationSetup ApplicationViews ApplicationOracle RecursivePolygero SumcheckV2

section Transfer
variable {B C : Type} [Field B] [Fintype B] [Algebra (ZMod 2) B] {shared maskBits adviceBits : ℕ}
variable (binary : BinaryPublic B shared maskBits adviceBits)
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable (prime : PrimePublic N shared) (generator : Bˣ)
variable (template : FrontendSchedule.Plan B binary.template)

/-- This is the template's supplied metadata on the actual generated circuit.
It does not replace component identifiers or infer fragment provenance. -/
def binaryPlan (packet : AdapterPacket binary prime C) :
    FrontendSchedule.Plan B (packet.setup generator).circuit :=
  binary.planFromTemplate template (packet.powers generator)
    (generator^(-(Adapter.Mdoc.primeOrder : ℤ))) packet.masked (packet.targets generator)

theorem binaryPlan_frontend (packet : AdapterPacket binary prime C) :
    (binaryPlan binary prime generator template packet).frontend = template.frontend :=
  binary.planFromTemplate_frontend template _ _ _ _

theorem binaryPlan_capacity (packet : AdapterPacket binary prime C) :
    (binaryPlan binary prime generator template packet).capacity = template.capacity :=
  binary.planFromTemplate_capacity template _ _ _ _

end Transfer

theorem adapter_get (g : Geometry) (i : Fin 3) :
    g.roles[ApplicationPrefix.rowBatchingIndex g+i.val]? =
      some (([Role.rowBatching,.rescaling,.conversion]).get i) := by
  let leading := [.fingerprint] ++ g.prime.roles .prime
  have hlength : leading.length = ApplicationPrefix.rowBatchingIndex g := by
    simp only [leading,List.length_append,List.length_singleton,ApplicationPrefix.rowBatchingIndex,
      Geometry.primeStart]
  have hroles : g.roles = leading ++
      ([.rowBatching,.rescaling,.conversion] ++ g.binary.roles .binary ++
        (if g.packingDegree = 1 then [] else [.packing]) ++ [.batching,.opening]) := by
    rw [g.roles_eq]
    simp only [leading,List.append_assoc]
  rw [hroles,List.getElem?_append_right (by rw [hlength]; omega),hlength,Nat.add_sub_cancel_left]
  simp only [List.append_assoc]
  rw [List.getElem?_append_left (show i.val < ([Role.rowBatching,.rescaling,.conversion]).length from i.isLt)]
  exact List.getElem?_eq_getElem i.isLt

theorem packing_get (g : Geometry) (nontrivial : g.packingDegree ≠ 1) :
    g.roles[ApplicationPrefix.packingIndex g]? = some .packing := by
  let leading := [.fingerprint] ++ g.prime.roles .prime ++ [.rowBatching,.rescaling,.conversion] ++
    g.binary.roles .binary
  have hlength : leading.length = ApplicationPrefix.packingIndex g := by
    simp only [leading,List.length_append,List.length_cons,List.length_nil,
      ApplicationPrefix.packingIndex,Geometry.binaryStart]
    omega
  have hroles : g.roles = leading ++ [.packing,.batching,.opening] := by
    rw [g.roles_eq]
    simp only [leading,if_neg nontrivial,List.append_assoc]
    rfl
  rw [hroles,List.getElem?_append_right (by rw [hlength]),hlength,Nat.sub_self]
  rfl

theorem stage_side (side : Side) (index : ℕ) (stage : Stage) (entries : List Entry)
    (role : Role) (h : role ∈ stage.roles side index entries) : frontendSide role = some side := by
  simp only [Stage.roles,List.mem_append,List.mem_cons,List.not_mem_nil,
    or_false,List.mem_map] at h
  rcases h with (rfl | ⟨i,_,rfl⟩) | rfl | rfl <;> rfl

theorem frontend_side (side : Side) (frontend : Frontend) (role : Role)
    (h : role ∈ frontend.roles side) : frontendSide role = some side := by
  by_cases empty : frontend.stages.isEmpty
  · simp only [Frontend.roles,empty,↓reduceIte,List.mem_singleton] at h
    subst role
    rfl
  · simp only [Frontend.roles,empty,Bool.false_eq_true,↓reduceIte,List.mem_flatMap] at h
    obtain ⟨i,_,h⟩ := h
    exact stage_side side i.val (frontend.stages.get i) _ role h
end LfzkV2.Current.RuntimeShape
