import LfzkV2.Current.Replay

/-! Ordinary replay depends only on the public context and the block
builders already reached. Terminal proof data may differ; its final-seal
input is deliberately outside this congruence. -/
namespace LfzkV2.Current.Replay.Encoding
variable {g : Geometry} {F : Fields} {Advice Authentication Context Block C : Type}
variable (e : Encoding g F Advice Authentication Context Block C)

private theorem stateAt_congr (first second : Output g F Advice Authentication)
    (index : ℕ) (inside : index < g.roles.length)
    (history : History Context Block Digest index) (answers : Fin index → C)
    (same : e.block first ⟨index,inside⟩ answers = e.block second ⟨index,inside⟩ answers) :
    e.stateAt first index (Nat.le_of_lt inside) history answers =
      e.stateAt second index (Nat.le_of_lt inside) history answers := by
  simp only [stateAt,dif_pos inside]
  rw [same]

/-- The proof payloads may differ after the requested boundary. Only the
context and the actual blocks up to that boundary must agree, for every
strict earlier challenge history. -/
theorem replay_eq_of_blocks (initial : Digest) (first second : Output g F Advice Authentication)
    (H : Point g F Advice Authentication Context Block → Digest × C)
    (index : ℕ) (inside : index < g.roles.length)
    (context : e.context first = e.context second)
    (blocks : ∀ (i : Fin g.roles.length), i.val ≤ index → ∀ past,
      e.block first i past = e.block second i past) :
    ((e.chain initial).replay first H index) = ((e.chain initial).replay second H index) := by
  induction index with
  | zero =>
      change e.stateAt first 0 (Nat.zero_le _) (e.context first) Fin.elim0 =
        e.stateAt second 0 (Nat.zero_le _) (e.context second) Fin.elim0
      rw [context]
      exact stateAt_congr e first second 0 inside _ _ (blocks ⟨0,inside⟩ (le_refl _) _)
  | succ index ih =>
      have earlier : index < g.roles.length := by omega
      simp only [TranscriptV2.Chain.replay,dif_pos earlier]
      rw [ih earlier (fun i bound => blocks i (by omega))]
      have rank := (e.chain initial).point_rank second H (Nat.le_of_lt earlier)
      change Input.rank (((e.chain initial).replay second H index).point) = index at rank
      generalize same : ((e.chain initial).replay second H index) = state
      rw [same] at rank
      rcases state with ⟨point,answers⟩
      cases point with
      | round i history block =>
          change i.val = index at rank
          exact stateAt_congr e first second (i.val+1) (by omega) _ _
            (blocks ⟨i.val+1,by omega⟩ (by change i.val+1 ≤ index+1; omega) _)
      | finalSeal history body =>
          change g.roles.length = index at rank
          omega

end LfzkV2.Current.Replay.Encoding
