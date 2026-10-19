import polygero.Local.GrindingAlgebra

/-! Explicit three-region geometry in the verified n=8192, k=512 setting.
All region cardinalities and query masses are proved without enumeration. -/
namespace RecursivePolygero.ProfileAnalysis.GrindingGeometry
open Finset LigeroFamily Local Local.Polygero Counting
open scoped Classical
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

private def commonEmbedding : Fin 511 ↪ Fin 8192 where
  toFun j := ⟨j.val, by omega⟩
  inj' := by
    intro x y h
    have hv := congrArg (fun j : Fin 8192 => j.val) h
    exact Fin.ext hv

private def blockEmbedding (i : Fin 3) : Fin 2560 ↪ Fin 8192 where
  toFun j := ⟨511 + 2560*i.val + j.val, by have := i.isLt; omega⟩
  inj' := by
    intro x y h
    have hv := congrArg (fun j : Fin 8192 => j.val) h
    change 511 + 2560*i.val + x.val = 511 + 2560*i.val + y.val at hv
    apply Fin.ext
    omega

def common : Finset (Fin 8192) := univ.map commonEmbedding

def block (i : Fin 3) : Finset (Fin 8192) := univ.map (blockEmbedding i)

def region (i : Fin 3) : Finset (Fin 8192) := common ∪ block i

def spare : Fin 8192 := ⟨8191, by decide⟩

theorem mem_common (j : Fin 8192) : j ∈ common ↔ j.val < 511 := by
  constructor
  · intro h
    obtain ⟨i, _, rfl⟩ := mem_map.mp h
    exact i.isLt
  · intro h
    exact mem_map.mpr ⟨⟨j.val,h⟩, mem_univ _, Fin.ext rfl⟩

theorem mem_block (i : Fin 3) (j : Fin 8192) :
    j ∈ block i ↔ 511 + 2560*i.val ≤ j.val ∧ j.val < 511 + 2560*(i.val+1) := by
  constructor
  · intro h
    obtain ⟨k, _, rfl⟩ := mem_map.mp h
    change 511 + 2560*i.val ≤ 511 + 2560*i.val + k.val ∧
      511 + 2560*i.val + k.val < 511 + 2560*(i.val+1)
    have := k.isLt
    omega
  · rintro ⟨hlo, hhi⟩
    refine mem_map.mpr ⟨⟨j.val-(511+2560*i.val), by omega⟩, mem_univ _, ?_⟩
    apply Fin.ext
    change 511 + 2560*i.val + (j.val-(511+2560*i.val)) = j.val
    omega

@[simp] theorem common_card : common.card = 511 := by simp [common]
@[simp] theorem block_card (i : Fin 3) : (block i).card = 2560 := by simp [block]

theorem common_disjoint_block (i : Fin 3) : Disjoint common (block i) := by
  apply disjoint_left.mpr
  intro j ha hb
  have h₀ := (mem_common j).mp ha
  have h₁ := (mem_block i j).mp hb
  omega

@[simp] theorem region_card (i : Fin 3) : (region i).card = 3071 := by
  rw [region, card_union_of_disjoint (common_disjoint_block i), common_card, block_card]

theorem region_avoids_spare (i : Fin 3) : spare ∉ region i := by
  intro h
  rcases mem_union.mp h with h | h
  · have hh := (mem_common spare).mp h
    norm_num [spare] at hh
  · have hh := (mem_block i spare).mp h
    have := i.isLt
    simp only [spare] at hh
    omega

noncomputable def label (values : Fin 3 → F) (j : Fin 8192) : F :=
  if j.val < 3071 then values 0 else if j.val < 5631 then values 1 else values 2

omit [Field F] [Fintype F] [DecidableEq F] in
theorem label_agrees (values : Fin 3 → F) (i : Fin 3) (j : Fin 8192)
    (hj : j ∈ region i) : j ∈ common ∨ label values j = values i := by
  rcases mem_union.mp hj with h | h
  · exact Or.inl h
  · right
    have hh := (mem_block i j).mp h
    fin_cases i <;> dsimp at hh ⊢
    · exact if_pos (by omega)
    · unfold label
      rw [if_neg (by omega), if_pos (by omega)]
    · unfold label
      rw [if_neg (by omega), if_neg (by omega)]

/-- The exact sampling probability of a successful parent query. -/
theorem region_query_mean (i : Fin 3) (t : ℕ) :
    mean (fun q : QuerySet 8192 t => indicator (q.coordinates ⊆ region i)) =
      (Nat.choose 3071 t : ℚ) / Nat.choose 8192 t := by
  rw [mean_indicator]
  calc
    _ = ((queriesWithin (r := t) (region i)).card : ℚ) / Fintype.card (QuerySet 8192 t) := by
      congr 1
      congr 1
      congr 1
      ext q
      simp [queriesWithin]
    _ = _ := by rw [card_queriesWithin, region_card, QuerySet.fintype_card]

end RecursivePolygero.ProfileAnalysis.GrindingGeometry
