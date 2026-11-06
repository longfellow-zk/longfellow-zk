import SumcheckV2.FiatShamir
import TranscriptV2.Charging

/-! Adaptive total-oracle accounting for ordinary quadratic sumcheck. The
search may query arbitrary points in any order, repeat queries, and explore
branches. Full-parent feedback and the final
seal discharge charging. Canonical preimage/schema and local algebraic replay
are the explicit representation/reduction contracts below. -/
namespace SumcheckV2.Chained
open Finset Bcs.TotalOracle Merkle.RandomOracle
open scoped Classical

variable {F P Link Rest Out : Type} [Field F]

abbrev Answer (Link Rest F : Type) := Link × (Rest × F)

def badAt (pts : PrefixPoints P)
    (data : (p : P) → (Fin (pts.slot p) → Answer Link Rest F) → RoundData F)
    (p : P) (H : P → Answer Link Rest F) (a : Answer Link Rest F) : Prop :=
  let d := data p (pts.chal H p)
  BadRoundEvent d.truth d.message d.claim a.2.2

theorem badAt_off (pts : PrefixPoints P)
    (data : (p : P) → (Fin (pts.slot p) → Answer Link Rest F) → RoundData F)
    (p : P) (H H' : P → Answer Link Rest F) (h : AgreeOff p H H') (a : Answer Link Rest F) :
    badAt pts data p H a → badAt pts data p H' a := by
  simpa only [badAt, pts.chal_congr h] using id

theorem badAt_card_le [Fintype F] [DecidableEq F] [Fintype Link] [Fintype Rest]
    (pts : PrefixPoints P)
    (data : (p : P) → (Fin (pts.slot p) → Answer Link Rest F) → RoundData F)
    (hdegree : ∀ p pref, (data p pref).truth.natDegree ≤ 2)
    (p : P) (H : P → Answer Link Rest F) :
    (univ.filter (badAt pts data p H)).card ≤
      Fintype.card Link * (Fintype.card Rest * 2) := by
  let d := data p (pts.chal H p)
  have heq : (univ.filter (badAt pts data p H)) = (univ : Finset Link) ×ˢ
      ((univ : Finset Rest) ×ˢ (univ.filter fun z => BadRoundEvent d.truth d.message d.claim z)) := by
    ext a
    rcases a with ⟨link, rest, z⟩
    simp [badAt, d]
  rw [heq, card_product, card_univ, card_product, card_univ]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
    (bad_round_roots d.truth d.message d.claim (hdegree p (pts.chal H p))))

/-- Ordinary sumcheck supplies the local reduction from its incoming claims,
true sums and the two evaluation updates. This is verifier/algebraic replay;
it does not assert anything about when the adversary queried these points. -/
def ofRoundReplay {R : ℕ} (M : TranscriptV2.Chain P Link (Rest × F) Out R)
    (pts : PrefixPoints P)
    (data : (p : P) → (Fin (pts.slot p) → Answer Link Rest F) → RoundData F)
    (Failure : Out → (P → Answer Link Rest F) → Prop)
    (claims truths : Out → (P → Answer Link Rest F) → ℕ → F)
    (hstart : ∀ out H, Failure out H → claims out H 0 ≠ truths out H 0)
    (hfinish : ∀ out H, Failure out H → claims out H R = truths out H R)
    (hreplay : ∀ out H n, n < R →
      let p := M.point out H n
      let d := data p (pts.chal H p)
      d.claim = claims out H n ∧ projectiveSum d.truth = truths out H n ∧
      check_round d.claim d.message (H p).2.2 = claims out H (n+1) ∧
      d.truth.eval (H p).2.2 = truths out H (n+1))
    (hseal : ∀ out H, Failure out H → (H (M.finalSealPoint out H)).1 = M.finalSeal out) :
    TranscriptV2.Reduction M (badAt pts data) Failure where
  exists_bad_point := by
    intro out H hf
    by_contra hbad
    have hfalse : ∀ n ≤ R, claims out H n ≠ truths out H n := by
      intro n
      induction n with
      | zero => intro _; exact hstart out H hf
      | succ n ih =>
          intro hn heq
          have hprior := ih (by omega)
          obtain ⟨hc,ht,hcnext,htnext⟩ := hreplay out H n (by omega)
          apply hbad
          refine ⟨n, by omega, ?_⟩
          change BadRoundEvent _ _ _ _
          exact ⟨by simpa only [hc, ht] using hprior, hcnext.trans (heq.trans htnext.symm)⟩
    exact hfalse R le_rfl (hfinish out H hf)
  final_seal_valid := hseal

/-- One quadratic-root charge per actually queried point. The only additional
chain charge is for guessed predecessor links or an unqueried final seal. -/
theorem failure_bound [Fintype F] [DecidableEq F] [Fintype P] [DecidableEq P]
    [Fintype Link] [Nonempty Link] [DecidableEq Link]
    [Fintype Rest] [Nonempty Rest] [DecidableEq Rest]
    {R fuel Q : ℕ} (M : TranscriptV2.Chain P Link (Rest × F) Out R)
    (pts : PrefixPoints P)
    (data : (p : P) → (Fin (pts.slot p) → Answer Link Rest F) → RoundData F)
    (hdegree : ∀ p pref, (data p pref).truth.natDegree ≤ 2)
    (Failure : Out → (P → Answer Link Rest F) → Prop)
    (reduction : TranscriptV2.Reduction M (badAt pts data) Failure)
    (tree : Tree P (Answer Link Rest F) Out fuel)
    (hbudget : ∀ H, (TranscriptV2.seen tree H).card ≤ Q) :
    ((univ.filter fun H => Failure (tree.run H).1 H).card : ℚ) /
      (Fintype.card (Answer Link Rest F) : ℚ)^Fintype.card P ≤
      (2*Q : ℚ) / Fintype.card F + (Q+1 : ℚ) / Fintype.card Link := by
  have hlocal (p : P) (H : P → Answer Link Rest F) :
      (univ.filter (badAt pts data p H)).card * Fintype.card F ≤
        2 * Fintype.card (Answer Link Rest F) := by
    calc
      _ ≤ (Fintype.card Link * (Fintype.card Rest * 2)) * Fintype.card F :=
        Nat.mul_le_mul_right _ (badAt_card_le pts data hdegree p H)
      _ = _ := by simp only [Answer, Fintype.card_prod]; ring
  simpa only [Nat.cast_ofNat, mul_comm (Q : ℚ) 2] using reduction.failure_ratio_le tree hbudget
    (badAt_off pts data) (by positivity) hlocal

end SumcheckV2.Chained
