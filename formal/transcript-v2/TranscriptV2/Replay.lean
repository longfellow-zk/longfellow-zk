import TranscriptV2.Links

/-! Deterministic verification replay. State can retain earlier answers while
oracle inputs bind prefixes and links. The laws below enforce parent recovery,
actual-link feedback and increasing ranks. Binding the actual canonical messages
and final proof body is a separate encoding correspondence obligation. -/
namespace TranscriptV2
open Finset Bcs.TotalOracle Merkle.RandomOracle
open scoped Classical

structure Chain (P Link C Out : Type) (R : ℕ) extends Links P Link where
  State : Type
  rank : P → ℕ
  initial : Out → State
  input : State → P
  advance : Out → Fin R → State → (Link × C) → State
  initial_rank : ∀ out, rank (input (initial out)) = 0
  advance_rank : ∀ out i s a, rank (input s) = i.val →
    rank (input (advance out i s a)) = i.val+1
  advance_parent : ∀ out i s a, rank (input s) = i.val →
    parent (input (advance out i s a)) = some (input s)
  advance_link : ∀ out i s a, rank (input s) = i.val →
    claimed (input (advance out i s a)) = a.1
  finalSeal : Out → Link

variable {P Link C Out : Type} {R : ℕ}

namespace Chain
variable (M : Chain P Link C Out R)

def replay (out : Out) (H : P → Link × C) : ℕ → M.State
  | 0 => M.initial out
  | n+1 => if hn : n < R then
      let s := replay out H n
      M.advance out ⟨n,hn⟩ s (H (M.input s))
    else replay out H n

def point (out : Out) (H : P → Link × C) (n : ℕ) : P := M.input (M.replay out H n)
def finalSealPoint (out : Out) (H : P → Link × C) : P := M.point out H R

theorem point_rank (out : Out) (H : P → Link × C) {n : ℕ} (hn : n ≤ R) :
    M.rank (M.point out H n) = n := by
  induction n with
  | zero => exact M.initial_rank out
  | succ n ih =>
    have hlt : n < R := by omega
    have h := M.advance_rank out ⟨n,hlt⟩ (M.replay out H n) (H (M.point out H n))
      (ih (by omega))
    simpa [point, replay, hlt] using h

theorem point_parent (out : Out) (H : P → Link × C) {n : ℕ} (hn : n < R) :
    M.parent (M.point out H (n+1)) = some (M.point out H n) := by
  have h := M.advance_parent out ⟨n,hn⟩ (M.replay out H n) (H (M.point out H n))
    (M.point_rank out H (by omega))
  simpa [point, replay, hn] using h

theorem point_link (out : Out) (H : P → Link × C) {n : ℕ} (hn : n < R) :
    M.claimed (M.point out H (n+1)) = (H (M.point out H n)).1 := by
  have h := M.advance_link out ⟨n,hn⟩ (M.replay out H n) (H (M.point out H n))
    (M.point_rank out H (by omega))
  simpa [point, replay, hn] using h

theorem replay_congr_prefix (out : Out) (H H' : P → Link × C) (n : ℕ)
    (h : ∀ k < n, H (M.point out H k) = H' (M.point out H k)) :
    M.replay out H n = M.replay out H' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hs := ih (fun k hk => h k (by omega))
    by_cases hn : n < R
    · simp only [replay, dif_pos hn]
      have ha := h n (by omega)
      dsimp [point] at ha
      rw [← hs, ha]
    · simpa only [replay, dif_neg hn] using hs

/-- Recomputing the final input never reads the oracle at that input: all
earlier points have smaller counters. This also holds for zero-round proofs. -/
theorem finalSealPoint_off (out : Out) {H H' : P → Link × C}
    (h : AgreeOff (M.finalSealPoint out H) H H') :
    M.finalSealPoint out H = M.finalSealPoint out H' := by
  apply congrArg M.input
  apply M.replay_congr_prefix
  intro k hk
  apply h
  intro heq
  have h₁ := M.point_rank out H (show k ≤ R by omega)
  have h₂ := M.point_rank out H (show R ≤ R by rfl)
  dsimp [finalSealPoint] at heq
  rw [heq] at h₁
  omega

theorem points_injective (out : Out) (H : P → Link × C) :
    Function.Injective (fun i : Fin (R+1) => M.point out H i.val) := by
  intro i j hij
  change M.point out H i.val = M.point out H j.val at hij
  apply Fin.ext
  have h₁ := M.point_rank out H (show i.val ≤ R by omega)
  have h₂ := M.point_rank out H (show j.val ≤ R by omega)
  rw [hij] at h₁
  omega

end Chain

end TranscriptV2
