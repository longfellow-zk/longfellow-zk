import LfzkV2.Current.ZeroKnowledge.CompleteOpening
import LfzkV2.Current.BackendBody
import LfzkV2.Current.ProtocolWrites
import LfzkV2.Current.ZeroKnowledge.CompleteTerminalBody

/-! Construct the terminal body fields from actual tuple columns and honest
authentication. Both full response arrays are encoded by the inverse runtime
decoder. Opened rows preserve the sampled order in both participants. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.CompleteBody

open Merkle Merkle.MH RecursivePolygero LigeroFamily
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice : Type} {k s n t : ℕ}
variable (P R : Joint.Participant k s n t)
variable (binary : fields .binary ≃ P.Carrier) (prime : fields .prime ≃ R.Carrier)
variable (hB : g.dataRows .binary = P.backend.nw) (hN : g.dataRows .prime = R.backend.nw)
variable (hopenings : g.openings = t)

private theorem raw_ext {Nonce Leaf D : Type} {queries : ℕ}
    (first second : OrderedOpening.Raw queries Nonce Leaf D)
    (values : first.values = second.values) (nonce : first.nonce = second.nonce)
    (frontier : first.frontier = second.frontier) : first = second := by
  cases first
  cases second
  cases values
  cases nonce
  cases frontier
  rfl

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

def binaryRows (indices : Fin t ↪ Fin n) (columns : Fin n → (Joint.Pair.family P R).Leaf) :
    Fin (g.dataRows .binary+3) → Fin g.openings → fields .binary := fun row query =>
  (participantEquiv .binary P binary hB).symm
    ((piFinTwoEquiv _ (columns (indices (Fin.cast hopenings query)))).1) row

def primeRows (indices : Fin t ↪ Fin n) (columns : Fin n → (Joint.Pair.family P R).Leaf) :
    Fin (g.dataRows .prime+3) → Fin g.openings → fields .prime := fun row query =>
  (participantEquiv .prime R prime hN).symm
    ((piFinTwoEquiv _ (columns (indices (Fin.cast hopenings query)))).2) row

variable {Enc : Type}
variable (scheme : Scheme (Fin n × Digest) (Joint.Pair.family P R).Leaf Digest Enc)
variable (indices : Fin t ↪ Fin n) (nonces : Fin n → Digest)
variable (columns : Fin n → (Joint.Pair.family P R).Leaf)

def frontier : List Digest :=
  (CompleteOpening.raw scheme (fun i nonce => (i,nonce)) indices nonces columns).frontier

def authentication (context : Digest)
    (capacity : (frontier P R scheme indices nonces columns).length ≤ OpeningBody.frontierCapacity g) :
    OpeningBody.Authentication g where
  context := context
  nonce query := nonces (indices (Fin.cast hopenings query))
  frontierLength := ⟨(frontier P R scheme indices nonces columns).length,by omega⟩
  frontier i := (frontier P R scheme indices nonces columns)[i.val]

def fill (body : Body g fields Advice (OpeningBody.Authentication g))
    (responses : Response g (fields .binary) × Response g (fields .prime)) (context : Digest)
    (capacity : (frontier P R scheme indices nonces columns).length ≤ OpeningBody.frontierCapacity g) :
    Body g fields Advice (OpeningBody.Authentication g) :=
  { body with
    binaryBackend := ⟨responses.1,binaryRows P R binary hB hopenings indices columns⟩
    primeBackend := ⟨responses.2,primeRows P R prime hN hopenings indices columns⟩
    authentication := authentication P R hopenings scheme indices nonces columns context capacity }

/-- Equality of the committed tuple columns transports the complete
authentication body. The frontier bound is a proof, so it contributes no
additional data or compatibility condition. -/
theorem fill_congr_columns (other : Fin n → (Joint.Pair.family P R).Leaf)
    (same : columns = other)
    (body : Body g fields Advice (OpeningBody.Authentication g))
    (responses : Response g (fields .binary) × Response g (fields .prime)) (context : Digest)
    (capacity : (frontier P R scheme indices nonces columns).length ≤ OpeningBody.frontierCapacity g)
    (otherCapacity : (frontier P R scheme indices nonces other).length ≤ OpeningBody.frontierCapacity g) :
    fill P R binary prime hB hN hopenings scheme indices nonces columns body responses context capacity =
      fill P R binary prime hB hN hopenings scheme indices nonces other body responses context otherCapacity := by
  cases same
  rfl

theorem fill_congr (other : Fin n → (Joint.Pair.family P R).Leaf) (same : columns = other)
    (body otherBody : Body g fields Advice (OpeningBody.Authentication g))
    (retained : CompleteTerminal.fill body otherBody = otherBody)
    (responses : Response g (fields .binary) × Response g (fields .prime)) (context : Digest)
    (capacity : (frontier P R scheme indices nonces columns).length ≤ OpeningBody.frontierCapacity g)
    (otherCapacity : (frontier P R scheme indices nonces other).length ≤ OpeningBody.frontierCapacity g) :
    fill P R binary prime hB hN hopenings scheme indices nonces columns body responses context capacity =
      fill P R binary prime hB hN hopenings scheme indices nonces other otherBody responses context otherCapacity := by
  cases same
  have transported := congrArg
    (fun source => fill P R binary prime hB hN hopenings scheme indices nonces columns source responses context capacity)
    retained
  exact transported

/-- Filling the terminal data retains every earlier body field. This form
lets runtime proofs use the terminal abstraction without reopening the
record or its row and frontier encoders. -/
theorem terminal_fill (body : Body g fields Advice (OpeningBody.Authentication g))
    (responses : Response g (fields .binary) × Response g (fields .prime)) (context : Digest)
    (capacity : (frontier P R scheme indices nonces columns).length ≤ OpeningBody.frontierCapacity g) :
    CompleteTerminal.fill body
        (fill P R binary prime hB hN hopenings scheme indices nonces columns body responses context capacity) =
      fill P R binary prime hB hN hopenings scheme indices nonces columns body responses context capacity := rfl

theorem response_fill (body : Body g fields Advice (OpeningBody.Authentication g))
    (responses : Response g (fields .binary) × Response g (fields .prime)) (context : Digest)
    (capacity : (frontier P R scheme indices nonces columns).length ≤ OpeningBody.frontierCapacity g) :
    ((fill P R binary prime hB hN hopenings scheme indices nonces columns body responses context capacity).binaryBackend.response,
      (fill P R binary prime hB hN hopenings scheme indices nonces columns body responses context capacity).primeBackend.response) =
      responses := rfl

theorem fresh_before (body : Body g fields Advice (OpeningBody.Authentication g))
    (responses : Response g (fields .binary) × Response g (fields .prime)) (context : Digest)
    (capacity : (frontier P R scheme indices nonces columns).length ≤ OpeningBody.frontierCapacity g)
    (i : Fin g.roles.length) (before : i.val < g.openingIndex.val) :
    ProtocolWrites.fresh
        (fill P R binary prime hB hN hopenings scheme indices nonces columns body responses context capacity) i =
      ProtocolWrites.fresh body i := by
  have notOpening : g.roles.get i ≠ .opening := by
    intro atOpening
    have same := (g.get_eq_opening_iff i).mp atOpening
    subst i
    exact Nat.lt_irrefl _ before
  simp only [ProtocolWrites.fresh,notOpening,if_false,fill,ProtocolWrites.packingPair,
    ProtocolWrites.frontendMessages,Body.frontend]

theorem raw_fill (body : Body g fields Advice (OpeningBody.Authentication g))
    (responses : Response g (fields .binary) × Response g (fields .prime)) (context : Digest)
    (capacity : (frontier P R scheme indices nonces columns).length ≤ OpeningBody.frontierCapacity g)
    (finalSeal : Digest) :
    OpeningBody.raw P R binary prime hB hN hopenings
      ⟨fill P R binary prime hB hN hopenings scheme indices nonces columns body responses context capacity,finalSeal⟩ =
      CompleteOpening.raw scheme (fun i nonce => (i,nonce)) indices nonces columns := by
  apply raw_ext
  · funext query
    change (piFinTwoEquiv (fun i : Fin 2 => ((Joint.Pair.family P R).participant i).Leaf)).symm
      (OpeningBody.participantLeaf P .binary binary hB
        ((participantEquiv .binary P binary hB).symm
          ((piFinTwoEquiv _ (columns (indices (Fin.cast hopenings (Fin.cast hopenings.symm query))))).1)),
       OpeningBody.participantLeaf R .prime prime hN
        ((participantEquiv .prime R prime hN).symm
          ((piFinTwoEquiv _ (columns (indices (Fin.cast hopenings (Fin.cast hopenings.symm query))))).2))) = _
    rw [← participantEquiv_apply,← participantEquiv_apply,
      Equiv.apply_symm_apply,Equiv.apply_symm_apply]
    simp only [Fin.cast_cast,Fin.cast_refl,id_eq,Prod.eta,Equiv.symm_apply_apply]
    rfl
  · funext query
    change nonces (indices (Fin.cast hopenings (Fin.cast hopenings.symm query))) = nonces (indices query)
    simp only [Fin.cast_cast,Fin.cast_refl,id_eq]
  · change List.ofFn (fun i : Fin (frontier P R scheme indices nonces columns).length =>
        (frontier P R scheme indices nonces columns)[i.val]) = _
    exact List.ofFn_getElem

end LfzkV2.Current.ZeroKnowledge.CompleteBody
