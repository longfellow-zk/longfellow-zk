import LfzkV2.Current.Replay
import LfzkV2.Current.QueryAnswers

/-! A later replay input contains the exact earlier query inputs, not merely
their counters. This lets early witness selection be reconstructed at every
later boundary without consulting any future message. -/
namespace LfzkV2.Current

namespace Input
variable {roles : List Role} {Context Block Link Body : Type}

/-- Recover an earlier boundary, allowing the current boundary itself. The
result is determined by the preimage; no oracle access is involved. -/
def atRank (point : Input roles Context Block Link Body) (n : ℕ) :
    Option (Input roles Context Block Link Body) :=
  if h : n < point.rank then some (point.priorPoints ⟨n,h⟩)
  else if n = point.rank then some point else none

theorem previous_rank {n : ℕ} {hn : n ≤ roles.length}
    {history : History Context Block Link n} {ancestor : Input roles Context Block Link Body}
    (h : previous n hn history = some ancestor) : n = ancestor.rank+1 := by
  cases n with
  | zero => simp [previous] at h
  | succ n =>
      have he := Option.some.inj h
      rw [← he]
      rfl

theorem priorPoints_parent {child ancestor : Input roles Context Block Link Body}
    (hp : child.parent = some ancestor) (i : Fin ancestor.rank) :
    child.priorPoints ⟨i.val, by have := parent_rank hp; omega⟩ = ancestor.priorPoints i := by
  have aux (n : ℕ) (hn : n ≤ roles.length) (history : History Context Block Link n)
      (h : previous n hn history = some ancestor) :
      historyPoints n hn history ⟨i.val, by have := i.isLt; have := previous_rank h; omega⟩ =
        ancestor.priorPoints i := by
    cases n with
    | zero => simp [previous] at h
    | succ n =>
      have he : (.round ⟨n, by omega⟩ history.1 history.2.1 :
          Input roles Context Block Link Body) = ancestor := Option.some.inj h
      subst ancestor
      change Fin n at i
      change historyPoints (n+1) hn history i.castSucc = historyPoints n _ history.1 i
      simp only [historyPoints, Fin.snoc_castSucc]
  cases child with
  | round j history block => exact aux j.val (by omega) history hp
  | finalSeal history body => exact aux roles.length (by rfl) history hp

theorem priorPoints_last {child ancestor : Input roles Context Block Link Body}
    (hp : child.parent = some ancestor) :
    child.priorPoints ⟨ancestor.rank, by have := parent_rank hp; omega⟩ = ancestor := by
  have aux (n : ℕ) (hn : n ≤ roles.length) (history : History Context Block Link n)
      (h : previous n hn history = some ancestor) :
      historyPoints n hn history ⟨ancestor.rank, by have := previous_rank h; omega⟩ = ancestor := by
    cases n with
    | zero => simp [previous] at h
    | succ n =>
      have he : (.round ⟨n, by omega⟩ history.1 history.2.1 :
          Input roles Context Block Link Body) = ancestor := Option.some.inj h
      subst ancestor
      change historyPoints (n+1) hn history (Fin.last n) = _
      simp only [historyPoints, Fin.snoc_last]
  cases child with
  | round j history block => exact aux j.val (by omega) history hp
  | finalSeal history body => exact aux roles.length (by rfl) history hp

end Input

namespace Replay.Encoding
variable {g : Geometry} {F : Fields} {Advice Authentication Context Block C : Type}
variable (e : Encoding g F Advice Authentication Context Block C)

theorem point_priorPoints (initialLink : Digest) (proof : Output g F Advice Authentication)
    (H : Point g F Advice Authentication Context Block → Digest × C)
    (n : ℕ) (hn : n ≤ g.roles.length) (j : Fin n) :
    ((e.chain initialLink).point proof H n).priorPoints
      ⟨j.val, by
        have hr := (e.chain initialLink).point_rank proof H hn
        change Input.rank _ = n at hr
        rw [hr]
        exact j.isLt⟩ =
      (e.chain initialLink).point proof H j.val := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
      have hp := (e.chain initialLink).point_parent proof H (show n < g.roles.length by omega)
      have hr := (e.chain initialLink).point_rank proof H (show n ≤ g.roles.length by omega)
      change Input.rank _ = n at hr
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simpa only [Fin.val_last, hr] using Input.priorPoints_last hp
      · have h := Input.priorPoints_parent hp ⟨i.val, by rw [hr]; exact i.isLt⟩
        exact h.trans (ih (by omega) i)

theorem point_atRank (initialLink : Digest) (proof : Output g F Advice Authentication)
    (H : Point g F Advice Authentication Context Block → Digest × C)
    (n j : ℕ) (hn : n ≤ g.roles.length) (hj : j ≤ n) :
    ((e.chain initialLink).point proof H n).atRank j =
      some ((e.chain initialLink).point proof H j) := by
  have hr := (e.chain initialLink).point_rank proof H hn
  change Input.rank _ = n at hr
  by_cases hlt : j < n
  · simp only [Input.atRank, hr, dif_pos hlt]
    exact congrArg some (e.point_priorPoints initialLink proof H n hn ⟨j,hlt⟩)
  · have he : j = n := by omega
    subst j
    simp [Input.atRank, hr]

theorem point_answersWith (initialLink : Digest) (proof : Output g F Advice Authentication)
    (H : Point g F Advice Authentication Context Block → Digest × C)
    (n j : ℕ) (hn : n ≤ g.roles.length) (hj : j ≤ n) (fallback : C) :
    ((e.chain initialLink).point proof H n).answersWith H
        (H ((e.chain initialLink).point proof H n)).2 fallback j =
      (H ((e.chain initialLink).point proof H j)).2 := by
  have hr := (e.chain initialLink).point_rank proof H hn
  change Input.rank _ = n at hr
  by_cases hlt : j < n
  · simp only [Input.answersWith, completeAnswers, hr, dif_pos hlt, Input.priorAnswers]
    exact congrArg (fun p => (H p).2) (e.point_priorPoints initialLink proof H n hn ⟨j,hlt⟩)
  · have he : j = n := by omega
    subst j
    simp [Input.answersWith, completeAnswers, hr]

end Replay.Encoding
end LfzkV2.Current
