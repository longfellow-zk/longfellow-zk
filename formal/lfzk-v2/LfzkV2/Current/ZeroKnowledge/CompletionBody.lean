import LfzkV2.Current.ZeroKnowledge.CompletePublicBody

/-! The sampled-order row encoder and decoder are inverses for every
authentication payload, independently of the Merkle hashing convention. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.CompletePublicBody
open Merkle.MH RecursivePolygero LigeroFamily

variable {g : Geometry} {fields : Fields} {Advice : Type} {k s n t : ℕ}
variable (P R : Joint.Participant k s n t)
variable (binary : fields .binary ≃ P.Carrier) (prime : fields .prime ≃ R.Carrier)
variable (hB : g.dataRows .binary = P.backend.nw) (hN : g.dataRows .prime = R.backend.nw)
variable (hopenings : g.openings = t)

private theorem raw_extensionality {Nonce Leaf D : Type} {queries : ℕ}
    (first second : OrderedOpening.Raw queries Nonce Leaf D)
    (values : first.values = second.values) (nonce : first.nonce = second.nonce)
    (frontier : first.frontier = second.frontier) : first = second := by
  cases first
  cases second
  cases values
  cases nonce
  cases frontier
  rfl

theorem raw_fill (body : Body g fields Advice (OpeningBody.Authentication g))
    (responses : Response g (fields .binary) × Response g (fields .prime))
    (raw : OrderedOpening.Raw t MerkleNonce (Joint.Pair.family P R).Leaf Digest)
    (context : Digest) (capacity : raw.frontier.length ≤ OpeningBody.frontierCapacity g)
    (finalSeal : Digest) :
    OpeningBody.raw P R binary prime hB hN hopenings
      ⟨fill P R binary prime hB hN hopenings body responses raw context capacity,finalSeal⟩ = raw := by
  have values : ∀ query,
      (OpeningBody.raw P R binary prime hB hN hopenings
        ⟨fill P R binary prime hB hN hopenings body responses raw context capacity,finalSeal⟩).values query =
      raw.values query := by
    intro query
    change (piFinTwoEquiv (fun i : Fin 2 => ((Joint.Pair.family P R).participant i).Leaf)).symm
      (OpeningBody.participantLeaf P .binary binary hB
        ((CompleteBody.participantEquiv .binary P binary hB).symm
          ((piFinTwoEquiv _ (raw.values (Fin.cast hopenings (Fin.cast hopenings.symm query)))).1)),
       OpeningBody.participantLeaf R .prime prime hN
        ((CompleteBody.participantEquiv .prime R prime hN).symm
          ((piFinTwoEquiv _ (raw.values (Fin.cast hopenings (Fin.cast hopenings.symm query)))).2))) = _
    rw [← CompleteBody.participantEquiv_apply,← CompleteBody.participantEquiv_apply,
      Equiv.apply_symm_apply,Equiv.apply_symm_apply]
    simp only [Fin.cast_cast,Fin.cast_refl,id_eq,Prod.eta,Equiv.symm_apply_apply]
  have nonce : ∀ query,
      (OpeningBody.raw P R binary prime hB hN hopenings
        ⟨fill P R binary prime hB hN hopenings body responses raw context capacity,finalSeal⟩).nonce query =
      raw.nonce query := by
    intro query
    change raw.nonce (Fin.cast hopenings (Fin.cast hopenings.symm query)) = raw.nonce query
    simp only [Fin.cast_cast,Fin.cast_refl,id_eq]
  have frontier :
      (OpeningBody.raw P R binary prime hB hN hopenings
        ⟨fill P R binary prime hB hN hopenings body responses raw context capacity,finalSeal⟩).frontier =
      raw.frontier := by
    exact List.ofFn_getElem
  exact raw_extensionality _ _ (funext values) (funext nonce) frontier

end LfzkV2.Current.ZeroKnowledge.CompletePublicBody
