import LfzkV2.Current.ApplicationViews

/-! Role positions of the fixed public schedule. The binary circuit and its
plan are fixed; adapter challenges and masked words change only virtual
definitions, never the schedule or the decoder capacity. -/
noncomputable section
namespace LfzkV2.Current.RuntimeShape
open Application ApplicationSetup ApplicationViews ApplicationOracle RecursivePolygero SumcheckV2

/-- The two adapter boundaries directly follow the prime frontend; mixed
storage has no row-batching round. -/
theorem adapter_get (g : Geometry) (i : Fin 2) :
    g.roles[ApplicationPrefix.rescalingIndex g+i.val]? =
      some (([Role.rescaling,.conversion]).get i) := by
  let leading := [.fingerprint] ++ g.prime.roles .prime
  have hlength : leading.length = ApplicationPrefix.rescalingIndex g := by
    simp only [leading,List.length_append,List.length_singleton,ApplicationPrefix.rescalingIndex,
      Geometry.primeStart]
  have hroles : g.roles = leading ++
      ([.rescaling,.conversion] ++ g.binary.roles .binary ++
        (if g.packingDegree = 1 then [] else [.packing]) ++ [.batching,.opening]) := by
    rw [g.roles_eq]
    simp only [leading,List.append_assoc]
  rw [hroles,List.getElem?_append_right (by rw [hlength]; omega),hlength,Nat.add_sub_cancel_left]
  simp only [List.append_assoc]
  rw [List.getElem?_append_left (show i.val < ([Role.rescaling,.conversion]).length from i.isLt)]
  exact List.getElem?_eq_getElem i.isLt

theorem packing_get (g : Geometry) (nontrivial : g.packingDegree ≠ 1) :
    g.roles[ApplicationPrefix.packingIndex g]? = some .packing := by
  let leading := [.fingerprint] ++ g.prime.roles .prime ++ [.rescaling,.conversion] ++
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
