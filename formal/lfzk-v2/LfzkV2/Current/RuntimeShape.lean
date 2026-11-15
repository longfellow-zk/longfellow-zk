import LfzkV2.Current.ApplicationViews

/-! Role positions of the fixed public schedule. The binary circuit and its
plan are fixed; adapter challenges and masked words change only virtual
definitions, never the schedule or the decoder capacity. -/
noncomputable section
namespace LfzkV2.Current.RuntimeShape
open Application ApplicationSetup ApplicationViews ApplicationOracle RecursivePolygero SumcheckV2

/-- The prime frontend's last boundary, which also draws `eta`, sits at the
rescaling index. -/
theorem prime_last_get (g : Geometry) :
    g.roles[ApplicationPrefix.rescalingIndex g]? = some (g.prime.lastRole .prime) := by
  have hpos := ApplicationPrefix.prime_roles_pos g
  have hroles : g.roles = [.fingerprint] ++ (g.prime.roles .prime ++
      ([.conversion] ++ g.binary.roles .binary ++
        (if g.packingDegree = 1 then [] else [.packing]) ++ [.batching,.opening])) := by
    rw [g.roles_eq]
    simp only [List.append_assoc]
  rw [hroles, List.getElem?_append_right (by
    simp only [List.length_singleton, ApplicationPrefix.rescalingIndex, Geometry.primeStart]; omega)]
  simp only [List.length_singleton, ApplicationPrefix.rescalingIndex, Geometry.primeStart]
  rw [show 1+(g.prime.roles .prime).length-1-1 = (g.prime.roles .prime).length-1 by omega,
    List.getElem?_append_left (by omega), List.getElem?_eq_getElem (by omega)]
  simp [Frontend.lastRole, List.getLast_eq_getElem]

/-- Mixed storage has no row-batching round: the adapter's conversion
boundary directly follows the prime frontend. -/
theorem conversion_get (g : Geometry) :
    g.roles[ApplicationPrefix.conversionIndex g]? = some .conversion := by
  let leading := [.fingerprint] ++ g.prime.roles .prime
  have hlength : leading.length = ApplicationPrefix.conversionIndex g := by
    simp only [leading,List.length_append,List.length_singleton,ApplicationPrefix.conversionIndex,
      Geometry.primeStart]
  have hroles : g.roles = leading ++
      ([.conversion] ++ g.binary.roles .binary ++
        (if g.packingDegree = 1 then [] else [.packing]) ++ [.batching,.opening]) := by
    rw [g.roles_eq]
    simp only [leading,List.append_assoc]
  rw [hroles,List.getElem?_append_right (by rw [hlength]),hlength,Nat.sub_self]
  rfl

theorem packing_get (g : Geometry) (nontrivial : g.packingDegree ≠ 1) :
    g.roles[ApplicationPrefix.packingIndex g]? = some .packing := by
  let leading := [.fingerprint] ++ g.prime.roles .prime ++ [.conversion] ++
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

theorem stage_side (side : Side) (index : ℕ) (stage : Stage) (next : List Entry × List Fragment)
    (last : Bool) (role : Role) (h : role ∈ stage.roles side index next last) :
    frontendSide role = some side := by
  rcases Stage.mem_roles h with ⟨_,_,rfl⟩ | rfl | rfl <;> rfl

theorem frontend_side (side : Side) (frontend : Frontend) (role : Role)
    (h : role ∈ frontend.roles side) : frontendSide role = some side := by
  rcases Frontend.mem_roles h with rfl | ⟨i,h⟩
  · rcases Frontend.opening_cases side frontend with ⟨_,he⟩ | ⟨_,he⟩ <;> rw [he] <;> rfl
  · exact stage_side side i.val (frontend.stages.get i) _ _ role h
end LfzkV2.Current.RuntimeShape
