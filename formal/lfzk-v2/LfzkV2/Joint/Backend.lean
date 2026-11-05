import LfzkV2.Joint.Participant

/-!
# One column tree for an ordered family of fields

A leaf contains one typed column per participant. Authentication explains the
entire tuple at once. Every arithmetic verifier receives the same query set;
no independence between their acceptance events is asserted or required.
-/

namespace LfzkV2.Joint

open RecursivePolygero LigeroFamily Merkle Merkle.MH
open scoped Classical

structure Family (k s n t : ℕ) where
  count : ℕ
  nonempty : 0 < count
  participant : Fin count → Participant k s n t

namespace Family

variable {k s n t : ℕ} (G : Family k s n t)

abbrev Index := Fin G.count
abbrev Statement := (i : G.Index) → (G.participant i).Statement
abbrev Witness := (i : G.Index) → (G.participant i).Witness
abbrev Oracle := (i : G.Index) → (G.participant i).Oracle
abbrev Coin := (i : G.Index) → (G.participant i).Coin
abbrev Response := (i : G.Index) → (G.participant i).Response
abbrev Leaf := (i : G.Index) → (G.participant i).Leaf
abbrev Opening (Q : QuerySet n t) := (i : G.Index) → (G.participant i).Opening Q

noncomputable def columnsEquiv : G.Oracle ≃ (Fin n → G.Leaf) where
  toFun W j i := (G.participant i).columnsEquiv (W i) j
  invFun a i := (G.participant i).columnsEquiv.symm (fun j => a j i)
  left_inv W := by funext i; exact (G.participant i).columnsEquiv.symm_apply_apply (W i)
  right_inv a := by
    funext j i
    exact congrFun ((G.participant i).columnsEquiv.apply_symm_apply (fun j => a j i)) j

noncomputable def compiler (ht : 0 < t) :
    Bcs.Compiler G.Statement G.Oracle G.Coin G.Response (QuerySet n t) G.Opening G.Leaf n where
  protocol :=
    { language := fun σ => ∀ i, ∃ w, (G.participant i).backend.layer.satisfies (σ i) w
      openOracle W Q i := ((G.participant i).compiler ht).protocol.openOracle (W i) Q
      verify σ coin response Q opening := decide (∀ i,
        ((G.participant i).compiler ht).protocol.verify (σ i) (coin i) (response i) Q (opening i) = true) }
  columns := G.columnsEquiv
  indices Q := Q.coordinates
  indices_nonempty Q := Finset.card_pos.mp (by simpa only [QuerySet.card_coordinates] using ht)
  open_congr first second Q hagree := by
    funext i
    apply ((G.participant i).compiler ht).open_congr
    intro j hj
    rw [(G.participant i).compiler_indices ht] at hj
    rw [(G.participant i).compiler_columns ht]
    exact congrFun (hagree j hj) i

noncomputable def Verify (σ : G.Statement) (W : G.Oracle) (coin : G.Coin)
    (response : G.Response) (Q : QuerySet n t) : Prop :=
  ∀ i, (G.participant i).backend.layer.verify (σ i) (W i) (coin i) (response i)
    ((G.participant i).localQuery Q)

theorem compiler_verify (ht : 0 < t) (σ : G.Statement) (W : G.Oracle)
    (coin : G.Coin) (response : G.Response) (Q : QuerySet n t) :
    (G.compiler ht).protocol.verify σ coin response Q
      ((G.compiler ht).protocol.openOracle W Q) = true ↔ G.Verify σ W coin response Q := by
  simp only [compiler, decide_eq_true_eq, Verify]
  exact forall_congr' (fun i => (G.participant i).compiler_verify ht _ _ _ _ _)

/-- One explained opening transfers every field check to the same extracted
column tuple. There is one commitment-extraction event, not one per field. -/
theorem verify_of_accepts (ht : 0 < t) {Salt D Enc : Type} [Inhabited D]
    (scheme : Scheme Salt G.Leaf D Enc) (σ : G.Statement) (root : D)
    (coin : G.Coin) (response : G.Response) (Q : QuerySet n t)
    (claim : OpeningClaim n Salt G.Leaf D) (W : G.Oracle)
    (hagree : ∀ j ∈ claim.I, G.columnsEquiv W j = claim.a j)
    (haccept : (G.compiler ht).Accepts scheme σ root coin response Q claim) :
    G.Verify σ W coin response Q :=
  (G.compiler_verify ht σ W coin response Q).mp
    ((G.compiler ht).verify_of_accepts scheme σ root coin response Q claim W hagree haccept)

noncomputable def extractedOracle {Salt D Enc : Type}
    [DecidableEq D] [Inhabited D] [Inhabited Salt] [Inhabited G.Leaf]
    {codec : Codec Salt G.Leaf D Enc} (dec : RoleDecoders codec)
    (root : D) (trace : List (Enc × D)) : G.Oracle :=
  G.columnsEquiv.symm (((extract dec n root trace).map Extracted.message).getD default)

theorem verify_of_extraction (ht : 0 < t) {Salt D Enc : Type}
    [DecidableEq D] [Inhabited D] [Inhabited Salt] [Inhabited G.Leaf]
    {codec : Codec Salt G.Leaf D Enc} (dec : RoleDecoders codec)
    (scheme : Scheme Salt G.Leaf D Enc) (σ : G.Statement) (root : D)
    (trace : List (Enc × D)) (coin : G.Coin) (response : G.Response) (Q : QuerySet n t)
    (claim : OpeningClaim n Salt G.Leaf D) (e : Extracted n Salt G.Leaf D)
    (hext : extract dec n root trace = some e)
    (hagree : ∀ j ∈ claim.I, e.message j = claim.a j)
    (haccept : (G.compiler ht).Accepts scheme σ root coin response Q claim) :
    G.Verify σ (G.extractedOracle dec root trace) coin response Q := by
  apply G.verify_of_accepts ht scheme σ root coin response Q claim _ _ haccept
  intro j hj
  simpa only [extractedOracle, Equiv.apply_symm_apply, hext, Option.map_some, Option.getD_some]
    using hagree j hj

/-- The fixed family is formed before any backend response or query. Each
field retains its own candidate list even though authentication is shared. -/
noncomputable def Candidates (W : G.Oracle) (cutoff : G.Index → ℕ) :=
  (i : G.Index) → ↥(Counting.committedCandidates (G.participant i).backend (W i) (cutoff i))

noncomputable instance candidatesFintype (W : G.Oracle) (cutoff : G.Index → ℕ) :
    Fintype (G.Candidates W cutoff) := inferInstanceAs (Fintype ((i : G.Index) →
      ↥(Counting.committedCandidates (G.participant i).backend (W i) (cutoff i))))

theorem candidates_card (W : G.Oracle) (cutoff : G.Index → ℕ) :
    Fintype.card (G.Candidates W cutoff) = ∏ i,
      (Counting.committedCandidates (G.participant i).backend (W i) (cutoff i)).card := by
  rw [← Nat.card_eq_fintype_card]
  unfold Candidates
  rw [Nat.card_pi]
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe]

end Family
end LfzkV2.Joint
