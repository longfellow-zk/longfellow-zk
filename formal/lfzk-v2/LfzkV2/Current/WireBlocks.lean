import LfzkV2.Current.ProtocolWrites

/-! The public shape of a transcript format and the role index facts its
packets use: the public input counts and field zeros (`Shape`), the
boundaries where a frontend starts (`startAt`), and that every scheduled
role's stage and round lie inside the public schedule (`role_valid`). -/
noncomputable section
namespace LfzkV2.Current.WireBlocks
open scoped Classical

/-- Counts are fixed by the public circuit/layout. They are not redundant
lengths in the proof. The remaining counts are public allocation sizes,
each within a u64. -/
structure Shape (g : Geometry) (fields : Fields) where
  binaryPublic : ℕ
  primePublic : ℕ
  primeInputs : ℕ
  sharedBits : ℕ
  packingInputs : ℕ
  binary128Packing : Bool
  zero : (side : Side) → fields side
  sliceFits : ∀ count ∈ [primeInputs,sharedBits+1,packingInputs,g.packingDegree,
      g.rowDimension+g.maskingDegree,2*g.rowDimension], count < 2^64

inductive Start where
  | none | prime | binary
  deriving DecidableEq

def startAt (g : Geometry) (i : Fin g.roles.length) : Start :=
  if i.val = g.primeStart then .prime else if i.val = g.binaryStart then .binary else .none

/-- The single A response, absent at degree one. -/
def PackingA (g : Geometry) (fields : Fields) : Type := if g.packingDegree = 1 then Unit else fields .binary

private def FrontendValid (frontend : Frontend) (side : Side) : Role → Prop
  | .inputAssertions participant _ => participant = side
  | .assertions participant stage .. => participant = side ∧ stage < frontend.stages.length
  | .sumcheck participant stage round => participant = side ∧
      ∃ hs : stage < frontend.stages.length, round < (frontend.stages.get ⟨stage,hs⟩).rounds
  | .terminal participant stage | .combine participant stage .. =>
      participant = side ∧ stage < frontend.stages.length
  | _ => False

private theorem frontend_valid (frontend : Frontend) (side : Side) (role : Role)
    (h : role ∈ frontend.roles side) : FrontendValid frontend side role := by
  rcases Frontend.mem_roles h with rfl | ⟨i,hr⟩
  · rcases Frontend.opening_cases side frontend with ⟨_,he⟩ | ⟨hpos,he⟩
    · rw [he]
      rfl
    · rw [he]
      exact ⟨rfl,hpos⟩
  · rcases Stage.mem_roles hr with ⟨round,hround,rfl⟩ | rfl | rfl
    · exact ⟨rfl,i.isLt,hround⟩
    · exact ⟨rfl,i.isLt⟩
    · exact ⟨rfl,i.isLt⟩

def ValidRole (g : Geometry) : Role → Prop
  | .sumcheck side stage round =>
      ∃ hs : stage < (g.frontend side).stages.length,
        round < ((g.frontend side).stages.get ⟨stage,hs⟩).rounds
  | .terminal side stage | .combine side stage .. => stage < (g.frontend side).stages.length
  | .packing => g.packingDegree ≠ 1
  | _ => True

private theorem prime_role_valid (g : Geometry) (role : Role) (h : role ∈ g.prime.roles .prime) :
    ValidRole g role := by
  have hf := frontend_valid g.prime .prime role h
  cases role with
  | sumcheck side stage round => rcases hf with ⟨rfl,hf⟩; exact hf
  | terminal side stage => rcases hf with ⟨rfl,hf⟩; exact hf
  | combine side stage entries fragments last => rcases hf with ⟨rfl,hf⟩; exact hf
  | packing => exact False.elim hf
  | _ => trivial

private theorem binary_role_valid (g : Geometry) (role : Role) (h : role ∈ g.binary.roles .binary) :
    ValidRole g role := by
  have hf := frontend_valid g.binary .binary role h
  cases role with
  | sumcheck side stage round => rcases hf with ⟨rfl,hf⟩; exact hf
  | terminal side stage => rcases hf with ⟨rfl,hf⟩; exact hf
  | combine side stage entries fragments last => rcases hf with ⟨rfl,hf⟩; exact hf
  | packing => exact False.elim hf
  | _ => trivial

/-- Every ordinary frontend message is indexed inside its actual public
stage, and packing occurs only when its degree is greater than one. -/
theorem role_valid (g : Geometry) (i : Fin g.roles.length) : ValidRole g (g.roles.get i) := by
  let role := g.roles.get i
  have h : role ∈ g.roles := List.get_mem g.roles i
  change ValidRole g role
  rw [g.roles_eq] at h
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at h
  rcases h with hfp | hp | hconv | hb | hpack | hbatch | hopen
  · rw [hfp]; trivial
  · exact prime_role_valid g _ hp
  · rw [hconv]; trivial
  · exact binary_role_valid g _ hb
  · by_cases he : g.packingDegree = 1
    · simp only [if_pos he,List.not_mem_nil] at hpack
    · have hr : role = .packing := by
        simpa only [if_neg he,List.mem_cons,List.not_mem_nil,or_false] using hpack
      rw [hr]
      exact he
  · rw [hbatch]; trivial
  · rw [hopen]; trivial

end LfzkV2.Current.WireBlocks
