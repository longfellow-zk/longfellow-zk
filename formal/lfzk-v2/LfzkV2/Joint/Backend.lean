import LfzkV2.Joint.Participant
import polygero.Local.CommittedCandidates

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

/-- The fixed family is formed before any backend response or query. Each
field retains its own candidate list even though authentication is shared. -/
noncomputable def Candidates (W : G.Oracle) (cutoff : G.Index → ℕ) :=
  (i : G.Index) → ↥(Counting.committedCandidates (G.participant i).backend (W i) (cutoff i))

noncomputable instance candidatesFintype (W : G.Oracle) (cutoff : G.Index → ℕ) :
    Fintype (G.Candidates W cutoff) := inferInstanceAs (Fintype ((i : G.Index) →
      ↥(Counting.committedCandidates (G.participant i).backend (W i) (cutoff i))))

end Family
end LfzkV2.Joint
