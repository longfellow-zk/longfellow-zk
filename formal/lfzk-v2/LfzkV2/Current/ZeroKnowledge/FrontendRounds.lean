import LfzkV2.Layered.Prover
import SumcheckV2.AdaptiveTerminalMasking
import LfzkV2.PolygeroZk

/-! Stateful simulation of the current coefficient-masked sumcheck rounds.
The reader sees only public state and messages. It may implement a fixed
Fiat--Shamir oracle, including all preceding prefix/link information; it
never receives the clear witness tables. Two coefficients are bound together
before their one challenge. The pad/message map is triangular and invertible
even when every challenge depends on the earlier transmitted messages. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend
open SumcheckV2
open scoped Classical

variable {F State : Type} [Field F]

structure Reader (F State : Type) [Field F] where
  round : State → RoundPoly F → F × State
  terminal : State → F → {r : F // r ≠ 0} × State
  combine : State → F × F → F × State

def coefficientEquiv (F : Type) : (F × F) ≃ RoundPoly F where
  toFun v := ⟨v.1,v.2⟩
  invFun p := (p.c0,p.c1)
  left_inv _ := rfl
  right_inv _ := rfl

instance [Fintype F] : Fintype (RoundPoly F) :=
  Fintype.ofEquiv (F × F) (coefficientEquiv F)

@[simp] theorem mask_mask (p pad : RoundPoly F) : mask p (mask p pad) = pad := by
  cases p
  cases pad
  simp [mask]

def realRounds (reader : Reader F State) : {n : ℕ} →
    (Cube n → F) → (Cube n → F) → State → (Fin n → RoundPoly F) → Fin n → RoundPoly F
  | 0, _, _, _, _ => Fin.elim0
  | n+1, q, w, state, pads =>
      let message := mask (honestMessage q w) (pads 0)
      let answer := reader.round state message
      Fin.cons message (realRounds reader (fold q answer.1) (fold w answer.1) answer.2
        (fun i : Fin n => pads i.succ))

def recoverRounds (reader : Reader F State) : {n : ℕ} →
    (Cube n → F) → (Cube n → F) → State → (Fin n → RoundPoly F) → Fin n → RoundPoly F
  | 0, _, _, _, _ => Fin.elim0
  | n+1, q, w, state, messages =>
      let answer := reader.round state (messages 0)
      Fin.cons (mask (honestMessage q w) (messages 0))
        (recoverRounds reader (fold q answer.1) (fold w answer.1) answer.2
          (fun i : Fin n => messages i.succ))

theorem recover_real (reader : Reader F State) {n : ℕ}
    (q w : Cube n → F) (state : State) (pads : Fin n → RoundPoly F) :
    recoverRounds reader q w state (realRounds reader q w state pads) = pads := by
  induction n generalizing state with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
      simp only [realRounds,recoverRounds,Fin.cons_zero,Fin.cons_succ,mask_mask,ih]
      exact Fin.cons_self_tail pads

theorem real_recover (reader : Reader F State) {n : ℕ}
    (q w : Cube n → F) (state : State) (messages : Fin n → RoundPoly F) :
    realRounds reader q w state (recoverRounds reader q w state messages) = messages := by
  induction n generalizing state with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
      simp only [recoverRounds,realRounds,Fin.cons_zero,Fin.cons_succ,mask_mask,ih]
      exact Fin.cons_self_tail messages

def roundsEquiv (reader : Reader F State) {n : ℕ}
    (q w : Cube n → F) (state : State) : (Fin n → RoundPoly F) ≃ (Fin n → RoundPoly F) where
  toFun := realRounds reader q w state
  invFun := recoverRounds reader q w state
  left_inv := recover_real reader q w state
  right_inv := real_recover reader q w state

/-- Public replay of just the round messages. The final scalars and private
pads play no role in challenge generation. -/
def readRounds (reader : Reader F State) : {n : ℕ} → State →
    (Fin n → RoundPoly F) → (Fin n → F) × State
  | 0, state, _ => (Fin.elim0,state)
  | n+1, state, messages =>
      let answer := reader.round state (messages 0)
      let tail := readRounds reader answer.2 (fun i : Fin n => messages i.succ)
      (Fin.cons answer.1 tail.1,tail.2)

/-- The recovered pads unmask precisely the numerical prover's honest
round polynomials at the public replay's adaptive challenge sequence. -/
theorem rounds_clear (reader : Reader F State) {n : ℕ}
    (q w : Cube n → F) (state : State) (pads : Fin n → RoundPoly F) :
    let messages := realRounds reader q w state pads
    List.ofFn (fun i => unmask (messages i) (pads i)) =
      honestMessages q w (readRounds reader state messages).1 := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      simp only [realRounds,readRounds,Fin.cons_zero,Fin.cons_succ,List.ofFn_succ,
        unmask_mask,honestMessages]
      congr 1
      exact ih _ _ _ _

theorem recovered_rounds_clear (reader : Reader F State) {n : ℕ}
    (q w : Cube n → F) (state : State) (messages : Fin n → RoundPoly F) :
    List.ofFn (fun i => unmask (messages i) (recoverRounds reader q w state messages i)) =
      honestMessages q w (readRounds reader state messages).1 := by
  have h := rounds_clear reader q w state (recoverRounds reader q w state messages)
  simpa only [real_recover] using h

/-- Exactly one honest pad vector yields each arbitrary sampled round
message vector. This includes scalar layers, whose vector is empty. -/
theorem rounds_uniform_fiber [Fintype F] (reader : Reader F State) {n : ℕ}
    (q w : Cube n → F) (state : State) (messages : Fin n → RoundPoly F) :
    (Finset.univ.filter fun pads => realRounds reader q w state pads = messages).card = 1 := by
  have heq : (Finset.univ.filter fun pads => realRounds reader q w state pads = messages) =
      {recoverRounds reader q w state messages} := by
    ext pads
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
    exact (roundsEquiv reader q w state).apply_eq_iff_eq_symm_apply
  rw [heq,Finset.card_singleton]

end LfzkV2.Current.ZeroKnowledge.Frontend
