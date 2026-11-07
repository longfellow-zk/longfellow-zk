import Merkle.Hiding

/-! Prior queries are fixed before the fresh commitment nonces and labels.
They may have selected the public request and hence every committed message.
These counts hold for each such prior state, without conditioning on the
eventual commitment root.  The label tape used here is the independent tape
in the causal refresh coupling; it is not the unreindexed honest label array.

A prior leaf hit guesses one nonce.  A prior internal-node hit pins two
distinct child labels.  These are separate from collisions among the honest
commitment's own hash inputs, which the Merkle hiding analysis already costs. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.MerklePriorHits

open Merkle Merkle.MH Merkle.RandomOracle Finset
open scoped Classical

variable {Salt Message Digest Enc : Type}

theorem leaves_card_le [Fintype Salt] [DecidableEq Salt] [DecidableEq Enc]
    (codec : Codec Salt Message Digest Enc) (injective : codec.Inj)
    (n : ℕ) (messages : Fin n → Message) (prior : Finset Enc) :
    (univ.filter fun nonce : Fin n → Salt =>
      ∃ i : Fin n, codec.leafEnc (nonce i,messages i) ∈ prior).card ≤
      n * (prior.card * Fintype.card Salt ^ (n-1)) := by
  apply nonceGuess_card_le codec n messages
  intro i a b same
  exact congrArg Prod.fst (injective.leaf same)

abbrev Node (n : ℕ) := {v : Fin n // 0 < v.val}

theorem node_card (n : ℕ) : Fintype.card (Node n) = n-1 := by
  rw [Fintype.card_subtype]
  have eq : (univ.filter fun v : Fin n => 0 < v.val) =
      univ.filter (fun v : Fin n => v.val ≠ 0) := by
    ext v
    simp only [mem_filter,mem_univ,true_and]
    omega
  rw [eq]
  by_cases positive : 0 < n
  · have eq' : (univ.filter fun v : Fin n => v.val ≠ 0) = univ.erase ⟨0,positive⟩ := by
      ext v
      simp [Fin.ext_iff]
    rw [eq']
    simp
  · have zero : n = 0 := by omega
    subst n
    simp

def left (n T : ℕ) (fits : 2*n-1 ≤ T) (v : Node n) : Fin T :=
  ⟨2*n-1-2*v.val.val,by have := v.property; have := v.val.isLt; omega⟩

def right (n T : ℕ) (fits : 2*n-1 ≤ T) (v : Node n) : Fin T :=
  ⟨2*n-2-2*v.val.val,by have := v.property; have := v.val.isLt; omega⟩

theorem children_ne (n T : ℕ) (fits : 2*n-1 ≤ T) (v : Node n) :
    left n T fits v ≠ right n T fits v := by
  intro same
  have values := congrArg Fin.val same
  have positive := v.property
  have bounded := v.val.isLt
  simp only [left,right] at values
  omega

/-- Every fixed prior input pins both child labels of a matching internal
node.  The encoding need only be injective within the internal-node role;
no disjointness from leaf encodings is assumed. -/
theorem nodes_card_le [Fintype Digest] [DecidableEq Digest] [DecidableEq Enc]
    (codec : Codec Salt Message Digest Enc) (injective : codec.Inj)
    (n T : ℕ) (fits : 2*n-1 ≤ T) (prior : Finset Enc) :
    (univ.filter fun labels : Fin T → Digest =>
      ∃ v : Node n, codec.nodeEnc
        (labels (left n T fits v),labels (right n T fits v)) ∈ prior).card ≤
      ((n-1)*prior.card) * Fintype.card Digest ^ (T-2) := by
  let family : Finset (Node n × Enc) := univ ×ˢ prior
  have counted := answerTape_determinedFamily₂_card_le T family
    (fun entry => left n T fits entry.1) (fun entry => right n T fits entry.1)
    (fun entry _ => children_ne n T fits entry.1)
    (fun entry labels => codec.nodeEnc
      (labels (left n T fits entry.1),labels (right n T fits entry.1)) = entry.2)
    (by
      intro entry _ a b _ ha hb
      exact Prod.mk.inj (injective.node (ha.trans hb.symm)))
  have same : (univ.filter fun labels : Fin T → Digest =>
      ∃ v : Node n, codec.nodeEnc
        (labels (left n T fits v),labels (right n T fits v)) ∈ prior) =
      univ.filter (fun labels : Fin T → Digest => ∃ entry ∈ family,
        codec.nodeEnc (labels (left n T fits entry.1),labels (right n T fits entry.1)) =
          entry.2) := by
    ext labels
    simp only [mem_filter,mem_univ,true_and,family,mem_product]
    constructor
    · rintro ⟨v,member⟩
      exact ⟨(v,_),member,rfl⟩
    · rintro ⟨⟨v,query⟩,member,same⟩
      exact ⟨v,same ▸ member⟩
  rw [same]
  calc
    _ ≤ family.card * Fintype.card Digest ^ (T-2) := counted
    _ = _ := by simp only [family,card_product,card_univ,node_card]

end LfzkV2.Current.ZeroKnowledge.MerklePriorHits
