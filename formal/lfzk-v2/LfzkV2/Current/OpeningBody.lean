import LfzkV2.Current.Opening
import LfzkV2.Current.ApplicationStatement
import LfzkV2.Joint.Pair.Basic

/-! The physical opening layout used by the runtime: `u, m, witness, fstar`
inside each participant, binary before prime inside the one tuple leaf.
All rows, nonce bytes and frontier nodes come from the actual proof body.
Only the sampled column positions are supplied by transcript replay. -/
namespace LfzkV2.Current.OpeningBody
open RecursivePolygero LigeroFamily RecursivePolygero.Local.Polygero

def rowIndex (rows : ℕ) : (Fin 2 ⊕ Fin rows ⊕ Fin 1) ≃ Fin (rows+3) :=
  ((Equiv.refl (Fin 2)).sumCongr finSumFinEquiv).trans
    (finSumFinEquiv.trans (finCongr (by omega)))

/-- This is an explicit physical order, not an arbitrary finite enumeration.
The two checked mask rows precede every ordinary witness row. -/
def leafEquiv (F : Type) (rows : ℕ) :
    (Fin (rows+3) → F) ≃ MerkleCompiler.Leaf F rows 0 where
  toFun values := ({
    core := fun block => match block with
      | .linear => fun i => values (rowIndex rows (.inr (.inl i)))
      | .left | .right | .output => Fin.elim0
    checkedMask := fun kind => match kind with
      | .vCoefficient => values (rowIndex rows (.inl 0))
      | .zRCoefficient => values (rowIndex rows (.inl 1)) },
    values (rowIndex rows (.inr (.inr 0))))
  invFun leaf i := match (rowIndex rows).symm i with
    | .inl j => if j = 0 then leaf.1.checkedMask .vCoefficient else leaf.1.checkedMask .zRCoefficient
    | .inr (.inl j) => leaf.1.core .linear j
    | .inr (.inr _) => leaf.2
  left_inv values := by
    funext i
    obtain ⟨j, rfl⟩ := (rowIndex rows).surjective i
    rcases j with j | j | j
    · fin_cases j <;> simp [Equiv.symm_apply_apply]
    · simp only [Equiv.symm_apply_apply]
    · fin_cases j
      simp only [Equiv.symm_apply_apply]
      rfl
  right_inv leaf := by
    apply Prod.ext
    · apply congrArg₂ Column.mk
      · funext block i
        cases block with
        | linear => simp only [Equiv.symm_apply_apply]
        | left => exact Fin.elim0 i
        | right => exact Fin.elim0 i
        | output => exact Fin.elim0 i
      · funext kind
        cases kind <;> simp [Equiv.symm_apply_apply]
    · simp only [Equiv.symm_apply_apply]

theorem leaf_witness {F : Type} {rows : ℕ} (values : Fin (rows+3) → F) (i : Fin rows) :
    (leafEquiv F rows values).1.core .linear i = values ⟨i.val+2, by have := i.isLt; omega⟩ := by
  change values (rowIndex rows (.inr (.inl i))) = _
  congr 1
  apply Fin.ext
  change 2+i.val = i.val+2
  omega

theorem leaf_masks {F : Type} {rows : ℕ} (values : Fin (rows+3) → F) :
    (leafEquiv F rows values).1.checkedMask .vCoefficient = values ⟨0, by omega⟩ ∧
      (leafEquiv F rows values).1.checkedMask .zRCoefficient = values ⟨1, by omega⟩ :=
  ⟨rfl, rfl⟩

theorem leaf_proximity {F : Type} {rows : ℕ} (values : Fin (rows+3) → F) :
    (leafEquiv F rows values).2 = values ⟨rows+2, by omega⟩ := by
  change values (rowIndex rows (.inr (.inr 0))) = _
  congr 1
  apply Fin.ext
  change 2+(rows+0) = rows+2
  omega

/-- The parser checks queries times tree depth, and the serialized count
is a four-byte unsigned integer. Both bounds apply before node allocation. -/
def frontierCapacity (g : Geometry) : ℕ :=
  min (2^32-1) (g.openings*(Nat.clog 2 g.columns+1))

/-- Authentication has one common nonce vector and one common frontier.
The length is the actual serialized count; the vector has exactly that
length, with no padding. Its public parser bound makes the proof space finite.
The context is checked against the public joint commitment context. -/
structure Authentication (g : Geometry) where
  context : Digest
  nonce : Fin g.openings → MerkleNonce
  frontierLength : Fin (frontierCapacity g+1)
  frontier : Fin frontierLength.val → Digest

noncomputable instance (g : Geometry) : Fintype (Authentication g) := by
  classical
  apply Fintype.ofInjective (fun a : Authentication g =>
    (a.context,a.nonce,(⟨a.frontierLength,a.frontier⟩ :
      (length : Fin (frontierCapacity g+1)) × (Fin length.val → Digest))))
  intro a b h
  cases a
  cases b
  cases h
  rfl

variable {g : Geometry} {fields : Fields} {Advice : Type} {k s n t : ℕ}

def participantLeaf (P : Joint.Participant k s n t) (side : Side)
    (field : fields side → P.Carrier) (hrows : g.dataRows side = P.backend.nw)
    (values : Fin (g.dataRows side+3) → fields side) : P.Leaf :=
  let physical : Fin (P.backend.nw+3) → P.Carrier :=
    fun i => field (values (Fin.cast (by rw [hrows]) i))
  cast (by change MerkleCompiler.Leaf P.Carrier P.backend.nw 0 =
      MerkleCompiler.Leaf P.Carrier P.backend.nw P.backend.nq; rw [P.linearOnly])
    (leafEquiv P.Carrier P.backend.nw physical)

def raw (P R : Joint.Participant k s n t)
    (binary : fields .binary → P.Carrier) (prime : fields .prime → R.Carrier)
    (hB : g.dataRows .binary = P.backend.nw) (hN : g.dataRows .prime = R.backend.nw)
    (hopenings : g.openings = t)
    (proof : Proof g fields Advice (Authentication g)) :
    OrderedOpening.Raw t MerkleNonce (Joint.Pair.family P R).Leaf Digest where
  values j := (piFinTwoEquiv _).symm
    (participantLeaf P .binary binary hB (fun i => proof.body.binaryBackend.rows i (Fin.cast hopenings.symm j)),
     participantLeaf R .prime prime hN (fun i => proof.body.primeBackend.rows i (Fin.cast hopenings.symm j)))
  nonce j := proof.body.authentication.nonce (Fin.cast hopenings.symm j)
  frontier := List.ofFn proof.body.authentication.frontier

theorem raw_nonce (P R : Joint.Participant k s n t)
    (binary : fields .binary → P.Carrier) (prime : fields .prime → R.Carrier)
    (hB : g.dataRows .binary = P.backend.nw) (hN : g.dataRows .prime = R.backend.nw)
    (hopenings : g.openings = t)
    (proof : Proof g fields Advice (Authentication g)) (j : Fin t) :
    (raw P R binary prime hB hN hopenings proof).nonce j =
      proof.body.authentication.nonce (Fin.cast hopenings.symm j) := rfl

end LfzkV2.Current.OpeningBody

namespace LfzkV2.Current.OpeningBody
open Merkle RecursivePolygero
variable {g : Geometry} {fields : Fields} {k s n t : ℕ}
/-- The existing scalar/row decoder is invertible, including its physical
u,m,witness,fstar row order. No field cell is invented by a parser cache. -/
def participantEquiv (side : Side) (Q : Joint.Participant k s n t)
    (field : fields side ≃ Q.Carrier) (hrows : g.dataRows side = Q.backend.nw) :
    (Fin (g.dataRows side+3) → fields side) ≃ Q.Leaf :=
  ((Equiv.arrowCongr (finCongr (congrArg (fun rows => rows+3) hrows)) field).trans
    (OpeningBody.leafEquiv Q.Carrier Q.backend.nw)).trans
      (Equiv.cast (by change MerkleCompiler.Leaf Q.Carrier Q.backend.nw 0 =
        MerkleCompiler.Leaf Q.Carrier Q.backend.nw Q.backend.nq; rw [Q.linearOnly]))

theorem participantEquiv_apply (side : Side) (Q : Joint.Participant k s n t)
    (field : fields side ≃ Q.Carrier) (hrows : g.dataRows side = Q.backend.nw)
    (values : Fin (g.dataRows side+3) → fields side) :
    participantEquiv side Q field hrows values = OpeningBody.participantLeaf Q side field hrows values := rfl


end LfzkV2.Current.OpeningBody
