import LfzkV2.Current.Prefix

/-! The joint backend occupies the final two ordinary boundaries. Neither
frontend contributes a batching or opening role, and the final seal has its
own constructor rather than an ordinary protocol role. These structural facts
keep the application and backend charges disjoint. -/
namespace LfzkV2.Current

namespace Stage

@[simp] theorem batching_not_mem (side : Side) (index : ℕ) (stage : Stage)
    (entries : List Entry) : .batching ∉ stage.roles side index entries := by
  simp [roles]

@[simp] theorem opening_not_mem (side : Side) (index : ℕ) (stage : Stage)
    (entries : List Entry) : .opening ∉ stage.roles side index entries := by
  simp [roles]

end Stage

namespace Frontend

@[simp] theorem batching_not_mem (side : Side) (frontend : Frontend) :
    .batching ∉ frontend.roles side := by
  by_cases h : frontend.stages.isEmpty
  · simp [roles, h]
  · simp only [roles, h, Bool.false_eq_true, ↓reduceIte, List.mem_flatMap]
    rintro ⟨i,_,hi⟩
    exact Stage.batching_not_mem _ _ _ _ hi

@[simp] theorem opening_not_mem (side : Side) (frontend : Frontend) :
    .opening ∉ frontend.roles side := by
  by_cases h : frontend.stages.isEmpty
  · simp [roles, h]
  · simp only [roles, h, Bool.false_eq_true, ↓reduceIte, List.mem_flatMap]
    rintro ⟨i,_,hi⟩
    exact Stage.opening_not_mem _ _ _ _ hi

end Frontend

namespace Geometry

/-- All boundaries preceding the one joint backend. -/
def backendPrefix (g : Geometry) : List Role :=
  [.fingerprint] ++ g.prime.roles .prime ++ [.rowBatching,.rescaling,.conversion] ++
    g.binary.roles .binary ++ (if g.packingDegree = 1 then [] else [.packing])

theorem roles_eq_backend (g : Geometry) :
    g.roles = g.backendPrefix ++ [.batching,.opening] := by
  rw [g.roles_eq]
  simp only [backendPrefix, List.append_assoc]

@[simp] theorem backendPrefix_batching_not_mem (g : Geometry) :
    .batching ∉ g.backendPrefix := by
  by_cases h : g.packingDegree = 1 <;> simp [backendPrefix, h]

@[simp] theorem backendPrefix_opening_not_mem (g : Geometry) :
    .opening ∉ g.backendPrefix := by
  by_cases h : g.packingDegree = 1 <;> simp [backendPrefix, h]

theorem roles_length_backend (g : Geometry) : g.roles.length = g.backendPrefix.length+2 := by
  rw [g.roles_eq_backend]
  simp

def batchingIndex (g : Geometry) : Fin g.roles.length :=
  ⟨g.backendPrefix.length, by rw [g.roles_length_backend]; omega⟩

def openingIndex (g : Geometry) : Fin g.roles.length :=
  ⟨g.backendPrefix.length+1, by rw [g.roles_length_backend]; omega⟩

@[simp] theorem batchingIndex_val (g : Geometry) :
    g.batchingIndex.val = g.backendPrefix.length := rfl

@[simp] theorem openingIndex_val (g : Geometry) :
    g.openingIndex.val = g.batchingIndex.val+1 := rfl

theorem batchingIndex_next (g : Geometry) : g.batchingIndex.val+1 < g.roles.length :=
  g.openingIndex.isLt

theorem batchingIndex_add_two (g : Geometry) : g.batchingIndex.val+2 = g.roles.length :=
  g.roles_length_backend.symm

theorem openingIndex_last (g : Geometry) : g.openingIndex.val+1 = g.roles.length := by
  rw [g.openingIndex_val]
  exact g.batchingIndex_add_two

@[simp] theorem batchingIndex_ne_openingIndex (g : Geometry) : g.batchingIndex ≠ g.openingIndex := by
  intro h
  have hv := congrArg Fin.val h
  simp only [openingIndex_val] at hv
  omega

@[simp] theorem get_batchingIndex (g : Geometry) : g.roles.get g.batchingIndex = .batching := by
  simp [List.get_eq_getElem, batchingIndex, g.roles_eq_backend]

@[simp] theorem get_openingIndex (g : Geometry) : g.roles.get g.openingIndex = .opening := by
  simp [List.get_eq_getElem, openingIndex, g.roles_eq_backend]

theorem get_eq_batching_iff (g : Geometry) (i : Fin g.roles.length) :
    g.roles.get i = .batching ↔ i = g.batchingIndex := by
  constructor
  · intro hi
    by_cases hbefore : i.val < g.backendPrefix.length
    · have hget : g.roles.get i = g.backendPrefix.get ⟨i.val,hbefore⟩ := by
        simp only [List.get_eq_getElem, g.roles_eq_backend,
          List.getElem_append_left hbefore]
      have hmem := List.get_mem g.backendPrefix ⟨i.val,hbefore⟩
      rw [← hget, hi] at hmem
      exact (g.backendPrefix_batching_not_mem hmem).elim
    · have hlt := i.isLt
      have hlen := g.roles_length_backend
      have hcases : i.val = g.backendPrefix.length ∨ i.val = g.backendPrefix.length+1 := by omega
      rcases hcases with heq | heq
      · apply Fin.ext
        exact heq
      · have hi' : i = g.openingIndex := Fin.ext heq
        subst i
        have hfalse : Role.opening = .batching := g.get_openingIndex.symm.trans hi
        cases hfalse
  · rintro rfl
    exact g.get_batchingIndex

theorem get_eq_opening_iff (g : Geometry) (i : Fin g.roles.length) :
    g.roles.get i = .opening ↔ i = g.openingIndex := by
  constructor
  · intro hi
    by_cases hbefore : i.val < g.backendPrefix.length
    · have hget : g.roles.get i = g.backendPrefix.get ⟨i.val,hbefore⟩ := by
        simp only [List.get_eq_getElem, g.roles_eq_backend,
          List.getElem_append_left hbefore]
      have hmem := List.get_mem g.backendPrefix ⟨i.val,hbefore⟩
      rw [← hget, hi] at hmem
      exact (g.backendPrefix_opening_not_mem hmem).elim
    · have hlt := i.isLt
      have hlen := g.roles_length_backend
      have hcases : i.val = g.backendPrefix.length ∨ i.val = g.backendPrefix.length+1 := by omega
      rcases hcases with heq | heq
      · have hi' : i = g.batchingIndex := Fin.ext heq
        subst i
        have hfalse : Role.batching = .opening := g.get_batchingIndex.symm.trans hi
        cases hfalse
      · apply Fin.ext
        exact heq
  · rintro rfl
    exact g.get_openingIndex

end Geometry
end LfzkV2.Current
