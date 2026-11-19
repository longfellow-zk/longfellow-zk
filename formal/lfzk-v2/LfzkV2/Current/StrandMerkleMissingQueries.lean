import Merkle.Indexed.Path
import Merkle.ExtractionROM
import TranscriptV2.UnqueriedAnswer

/-! Fresh authentication hits along one selected column path. Selection may
use the actual opening PRF answer, but cannot use a Merkle hash answer. The
query table is retained in the original program's output, so changing a
missing coordinate leaves both that table and the submitted proof fixed. -/
namespace LfzkV2.Current.StrandMerkleMissingQueries
open Merkle Merkle.Indexed Merkle.RandomOracle TranscriptV2 Bcs.TotalOracle Bcs.FiniteProbability
open scoped Classical

variable {Salt M D Enc Out : Type} {n : ℕ}

structure SelectedPath extends MH.OpeningClaim n Salt M D where
  root : D
  column : Fin n
  opened : column ∈ I
  cut : List (Enc × D)

def vertex (path : SelectedPath (n := n) (Salt := Salt) (M := M) (D := D) (Enc := Enc))
    (slot : Fin (Heap.heapDepth n+1)) : ℕ :=
  (Heap.ancestors (n+path.column.val)).getD slot.val 1

theorem vertex_positive (path : SelectedPath (n := n) (Salt := Salt) (M := M) (D := D) (Enc := Enc))
    (slot : Fin (Heap.heapDepth n+1)) : 0 < vertex path slot := by
  unfold vertex
  rw [List.getD_eq_getElem?_getD]
  cases found : (Heap.ancestors (n+path.column.val))[slot.val]? with
  | none => decide
  | some value => exact (Heap.mem_ancestors.mp (List.mem_of_getElem? found)).1

theorem vertex_mem (path : SelectedPath (n := n) (Salt := Salt) (M := M) (D := D) (Enc := Enc))
    (slot : Fin (Heap.heapDepth n+1)) : vertex path slot ∈ Heap.pathOf n path.column := by
  unfold vertex
  rw [List.getD_eq_getElem?_getD]
  cases found : (Heap.ancestors (n+path.column.val))[slot.val]? with
  | none => exact Heap.root_mem_pathOf n path.column
  | some value => exact List.mem_toFinset.mpr (List.mem_of_getElem? found)

theorem vertex_covers (path : SelectedPath (n := n) (Salt := Salt) (M := M) (D := D) (Enc := Enc))
    (value : ℕ) (member : value ∈ Heap.pathOf n path.column) :
    ∃ slot, vertex path slot = value := by
  have inList : value ∈ Heap.ancestors (n+path.column.val) := List.mem_toFinset.mp member
  obtain ⟨i,within,same⟩ := List.getElem_of_mem inList
  have length : (Heap.ancestors (n+path.column.val)).length ≤ Heap.heapDepth n+1 := by
    rw [← List.toFinset_card_of_nodup (Heap.ancestors_nodup _)]
    exact Heap.pathOf_card_le_heapDepth n path.column
  refine ⟨⟨i,lt_of_lt_of_le within length⟩,?_⟩
  exact (List.getElem_eq_getD 1).symm.trans same

variable [DecidableEq D] [Inhabited D] [DecidableEq Enc]
variable (codec : Codec Salt M D Enc) (dec : RoleDecoders codec)

omit [DecidableEq D] [DecidableEq Enc] in
/-- Equal opening claims produce the same path query. Membership proofs
are evidence only; callers need not unfold the concrete application to
transport an opened path across a decoded-claim equality. -/
theorem claim_pathInput_congr (first second : MH.OpeningClaim n Salt M D)
    (same : first = second) (column : Fin n) (firstOpened : column ∈ first.I)
    (secondOpened : column ∈ second.I) (H : Enc → D) (vertex : ℕ) :
    pathInput codec first.I first.a first.pf column firstOpened H vertex =
      pathInput codec second.I second.a second.pf column secondOpened H vertex := by
  cases same
  rfl

def IsMerkleInput (input : Enc) : Prop :=
  (∃ value, input = codec.leafEnc value) ∨ ∃ index children, input = codec.nodeEnc index children

def point (path : SelectedPath (n := n) (Salt := Salt) (M := M) (D := D) (Enc := Enc))
    (H : Enc → D) (slot : Fin (Heap.heapDepth n+1)) : Enc :=
  pathInput codec path.I path.a path.pf path.column path.opened H (vertex path slot)

omit [DecidableEq D] [DecidableEq Enc] in
theorem point_isMerkle (path : SelectedPath (n := n) (Salt := Salt) (M := M) (D := D) (Enc := Enc))
    (H : Enc → D) (slot : Fin (Heap.heapDepth n+1)) : IsMerkleInput codec (point codec path H slot) := by
  unfold point pathInput
  split
  · exact Or.inr ⟨_,_,rfl⟩
  · exact Or.inl ⟨_,rfl⟩

variable (select : Out → (Enc → D) →
  SelectedPath (n := n) (Salt := Salt) (M := M) (D := D) (Enc := Enc))

def chosen (result : Out) (H : Enc → D) (slot : Fin (Heap.heapDepth n+1)) : Enc × D :=
  let path := select result H
  (point codec path H slot,(label dec path.cut path.root (vertex path slot)).getD default)

variable (separated : Separated codec n)
variable (independent : ∀ result H H' input, IsMerkleInput codec input → AgreeOff input H H' →
  select result H = select result H')

include separated independent in
omit [DecidableEq Enc] in
theorem chosen_off (result : Out) (H H' : Enc → D)
    (slot : Fin (Heap.heapDepth n+1))
    (agree : AgreeOff (chosen codec dec select result H slot).1 H H') :
    chosen codec dec select result H slot = chosen codec dec select result H' slot := by
  have same := independent result H H' _ (point_isMerkle codec (select result H) H slot) agree
  unfold chosen
  rw [← same]
  apply Prod.ext
  · exact pathInput_off codec _ _ _ _ _ separated H H' _ (vertex_positive _ slot) agree
  · rfl

/-- A receiving hit expressed solely in the original observation. Its
target is the committed root or a child named in the extraction cut. -/
def OriginalHit (trace cut : List (Enc × D)) (root : D) : Prop :=
  ∃ input answer, (input,answer) ∈ trace ∧ (input,answer) ∉ cut ∧ IsMerkleInput codec input ∧
    (answer = root ∨ ∃ index raw digest children,
      (raw,digest) ∈ cut ∧ dec.nodeDec index raw = some children ∧
        (answer = children.1 ∨ answer = children.2))


section Restriction
variable {P : Type} [DecidableEq P]
variable (encode : P → Enc) (decode : Enc → P)

/-- Restrict the same selected path to a finite oracle window. An address
outside the window contributes no event. Such an address cannot occur on an
accepted verifier path covered by that window; rejected fallback paths need
no additional support or fictitious oracle queries. -/
def restrictedChosen (result : Out) (G : P → D)
    (slot : Fin (Heap.heapDepth n+1)) : Option (P × D) :=
  let pair := chosen codec dec select result (G ∘ decode) slot
  if encode (decode pair.1) = pair.1 then some (decode pair.1,pair.2) else none

variable (fiber : ∀ input, IsMerkleInput codec input → encode (decode input) = input →
  ∀ other, decode other = decode input → other = input)

include separated independent fiber in
omit [DecidableEq P] in
theorem restrictedChosen_off (result : Out) (G G' : P → D)
    (slot : Fin (Heap.heapDepth n+1)) (point : P) (target : D)
    (selected : restrictedChosen codec dec select encode decode result G slot = some (point,target))
    (agree : AgreeOff point G G') :
    restrictedChosen codec dec select encode decode result G' slot = some (point,target) := by
  let pair := chosen codec dec select result (G ∘ decode) slot
  change (if encode (decode pair.1) = pair.1 then some (decode pair.1,pair.2) else none) =
    some (point,target) at selected
  have represented : encode (decode pair.1) = pair.1 := by
    by_contra absent
    rw [if_neg absent] at selected
    cases selected
  have address : decode pair.1 = point := by
    have same : some (decode pair.1,pair.2) = some (point,target) := by
      simpa only [if_pos represented] using selected
    exact congrArg Prod.fst (Option.some.inj same)
  have rawAgree : AgreeOff pair.1 (G ∘ decode) (G' ∘ decode) := by
    intro raw different
    apply agree
    intro same
    apply different
    exact fiber pair.1 (point_isMerkle codec _ _ slot) represented raw (same.trans address.symm)
  have unchanged := chosen_off codec dec select separated independent result
    (G ∘ decode) (G' ∘ decode) slot rawAgree
  change (if encode (decode (chosen codec dec select result (G' ∘ decode) slot).1) =
    (chosen codec dec select result (G' ∘ decode) slot).1 then
      some (decode (chosen codec dec select result (G' ∘ decode) slot).1,
        (chosen codec dec select result (G' ∘ decode) slot).2) else none) = _
  rw [← unchanged]
  exact selected

variable {budget : ℕ} (finiteProgram : Tree P D Out budget)

/-- The finite representation preserves the existing deterministic
failure cover. Only inputs on the one selected path need representation. -/
theorem disagreement_restricted_cover [Inhabited M]
    (G : P → D)
    (represented : let result := finiteProgram.run G
      let path := select result.1 (G ∘ decode)
      ∀ slot, encode (decode (point codec path (G ∘ decode) slot)) = point codec path (G ∘ decode) slot)
    (unique : let result := finiteProgram.run G
      MH.CollisionFree (select result.1 (G ∘ decode)).cut)
    (accepted : let result := finiteProgram.run G
      let path := select result.1 (G ∘ decode)
      Accepts (codec.withOracle (G ∘ decode)) n path.root path.I path.a path.pf)
    (different : let result := finiteProgram.run G
      let path := select result.1 (G ∘ decode)
      messages dec path.cut path.root n path.column ≠ path.a path.column) :
    (let result := finiteProgram.run G
      let path := select result.1 (G ∘ decode)
      OriginalHit codec dec (result.2.map fun qa => (encode qa.1,qa.2)) path.cut path.root) ∨
      ∃ slot, UnqueriedAnswer.PartialHit
        (fun result H => restrictedChosen codec dec select encode decode result H slot)
        finiteProgram G := by
  let result := finiteProgram.run G
  let path := select result.1 (G ∘ decode)
  obtain ⟨position,member,missing,target⟩ := Merkle.Indexed.disagreement_hit codec dec
    path.I path.a path.pf path.column path.opened (G ∘ decode) path.cut path.root unique accepted different
  obtain ⟨slot,same⟩ := vertex_covers path position member
  rw [← same] at missing target
  let input := point codec path (G ∘ decode) slot
  have answerMissing : (input,G (decode input)) ∉ path.cut := by
    rw [← pathInput_answer codec path.I path.a path.pf path.column path.opened (G ∘ decode)
      (vertex path slot) (by rwa [same])] at missing
    exact missing
  by_cases wasQueried : decode input ∈ seen finiteProgram G
  · apply Or.inl
    refine ⟨input,G (decode input),?_,answerMissing,point_isMerkle codec path _ slot,?_⟩
    · obtain ⟨⟨raw,answer⟩,present,equal⟩ := List.mem_map.mp (List.mem_toFinset.mp wasQueried)
      change raw = decode input at equal
      have value := Tree.trace_sound finiteProgram G _ present
      exact List.mem_map.mpr ⟨(raw,answer),present,Prod.ext
        ((congrArg encode equal).trans (represented slot)) (value.trans (congrArg G equal))⟩
    · rcases label_named codec dec path.cut path.root (G (decode input)) (vertex path slot) target with root | child
      · exact Or.inl root
      · obtain ⟨raw,answer,children,old,decoded,equal⟩ := child
        exact Or.inr ⟨vertex path slot/2,raw,answer,children,old,decoded,equal⟩
  · apply Or.inr
    refine ⟨slot,decode input,G (decode input),?_,?_,rfl⟩
    · simp only [restrictedChosen,chosen,if_pos (represented slot)]
      change some (decode input,(label dec path.cut path.root (vertex path slot)).getD default) = _
      rw [target]
      rfl
    · exact wasQueried

variable [Fintype P] [Fintype D]

include separated independent fiber in
/-- The byte-level path bound survives finite address restriction. The
finite window's size and the number of verifier queries do not enter it. -/
theorem restricted_any_hit_density_le :
    density (fun G => ∃ slot,
      UnqueriedAnswer.PartialHit
        (fun result H => restrictedChosen codec dec select encode decode result H slot)
        finiteProgram G) ≤ (Heap.heapDepth n+1 : ℚ) / Fintype.card D := by
  calc
    _ ≤ ∑ slot, density (UnqueriedAnswer.PartialHit
        (fun result H => restrictedChosen codec dec select encode decode result H slot)
        finiteProgram) := density_union_le _ _ (fun _ hit => hit)
    _ ≤ ∑ _slot : Fin (Heap.heapDepth n+1), (1 / (Fintype.card D : ℚ)) := by
      apply Finset.sum_le_sum
      intro slot _
      apply UnqueriedAnswer.partial_density_le
      intro result G G' point target selected agree
      exact restrictedChosen_off codec dec select separated independent encode decode fiber
        result G G' slot point target selected agree
    _ = _ := by simp [div_eq_mul_inv,Nat.cast_add]

end Restriction

end LfzkV2.Current.StrandMerkleMissingQueries
