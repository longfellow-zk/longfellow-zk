import Sumcheck.Round

/-!
# The sumcheck chain

`verify_multi_round` iterates `check_round_c`, and this file is its two directions.

* **Soundness** (`sumcheck_multi_reduction`): if the verifier accepts a run started from a false
  claim, then either the claim it ends on is wrong, or some round was a lucky guess.
* **Completeness** (`sumcheck_multi_completeness`): an honest prover starting from the true claim
  is accepted, and the verifier ends on `get_last_eval` — the last true polynomial at its own
  challenge.  No degree bound and no field-size condition appear; completeness is unconditional.

The two are not symmetric and both are needed: soundness bounds a cheating prover, while a hiding
argument needs to know *which* value an honest run closes on.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Sumcheck

open Polynomial

variable {F : Type} [Field F] [DecidableEq F] {d : ℕ} [Interp F d]

def multi_round_bad_event {F : Type} [Field F] {d : ℕ} [Interp F d] : List (Polynomial F) → List (RoundPoly F d) → List F → Prop
  | (P::Ps), (p::ps), (r::rs) => BadRoundEvent P p r ∨ multi_round_bad_event Ps ps rs
  | _, _, _ => False

def verify_multi_round {F : Type} [Field F] [DecidableEq F] {d : ℕ} [Interp F d] (claim_start : F) (polys : List (RoundPoly F d)) (challenges : List F) : Option F :=
  match polys, challenges with
  | [], [] => some claim_start
  | p :: ps, r :: rs =>
      match check_round_c claim_start p r with
      | some next_claim => verify_multi_round next_claim ps rs
      | none => none
  | _, _ => none

def consistent_true_polys {F : Type} [Field F] : List (Polynomial F) → List F → Prop
  | (P1::P2::Ps), (r::rs) => P2.eval 0 + P2.eval 1 = P1.eval r ∧ consistent_true_polys (P2::Ps) rs
  | _, _ => True

def get_last_eval {F : Type} [Field F] : List (Polynomial F) → List F → Option F
  | [P], [r] => some (P.eval r)
  | (_::Ps), (_::rs) => get_last_eval Ps rs
  | _, _ => none

/--
`sumcheck_multi_reduction` establishes the core soundness reduction across multiple rounds of the sumcheck protocol.
It proves that if a verifier accepts a sequence of round polynomials and challenges resulting in a final claim (`verify_multi_round = some claim_out`), but the initial claim is false relative to the true polynomials, then one of two things must happen:
1. The final extracted claim `claim_out` does not match the final evaluation of the true polynomials.
2. The prover was "lucky" and a bad event occurred in at least one of the rounds (`multi_round_bad_event`).
-/
theorem sumcheck_multi_reduction {F : Type} [Field F] [DecidableEq F] {d : ℕ} [Interp F d]
    (P_trues : List (Polynomial F)) (polys : List (RoundPoly F d)) (challenges : List F)
    (claim_in claim_out : F) :
    verify_multi_round claim_in polys challenges = some claim_out →
    List.length P_trues = List.length polys →
    List.length challenges = List.length polys →
    consistent_true_polys P_trues challenges →
    polys ≠ [] →
    (claim_in ≠ P_trues.head!.eval 0 + P_trues.head!.eval 1) →
    (get_last_eval P_trues challenges = some claim_out → False) ∨
    multi_round_bad_event P_trues polys challenges := by
  induction polys generalizing claim_in P_trues challenges
  case nil =>
    intros _ _ _ _ h_nil _
    contradiction
  case cons p ps ih =>
    intro h_ver h_len1 h_len2 h_cons h_nnil h_false
    cases P_trues with
    | nil => contradiction
    | cons P Ps =>
      cases challenges with
      | nil => contradiction
      | cons r rs =>
        dsimp [verify_multi_round] at h_ver
        cases h_check : check_round_c claim_in p r
        · rw [h_check] at h_ver; contradiction
        · next claim_next =>
          rw [h_check] at h_ver
          have h_step := sumcheck_step_reduction P p claim_in claim_next r h_check h_false
          cases h_step with
          | inr h_bad =>
            right
            dsimp [multi_round_bad_event]
            left
            exact h_bad
          | inl h_claim_next_false =>
            cases ps with
            | nil =>
              cases rs with
              | nil =>
                dsimp [verify_multi_round] at h_ver
                injection h_ver with h_eq
                subst h_eq
                left
                cases Ps with
                | nil =>
                  dsimp [get_last_eval]
                  intro h_eq2
                  injection h_eq2 with h_eq3
                  rw [h_eq3] at h_claim_next_false
                  contradiction
                | cons P2 Ps2 =>
                  -- Ps length is 0 because h_len1 says (P::Ps).length = [p].length = 1
                  cases h_len1
              | cons r2 rs2 =>
                cases h_len2
            | cons p2 ps2 =>
              cases rs with
              | nil => cases h_len2
              | cons r2 rs2 =>
                cases Ps with
                | nil => cases h_len1
                | cons P2 Ps2 =>
                  have h_cons2 : consistent_true_polys (P::P2::Ps2) (r::r2::rs2) := h_cons
                  have h_P2_start : P2.eval 0 + P2.eval 1 = P.eval r := h_cons2.1
                  have h_next_false : claim_next ≠ P2.eval 0 + P2.eval 1 := by
                    rw [h_P2_start]
                    exact h_claim_next_false
                  have h_len1_next : (P2::Ps2).length = (p2::ps2).length := Nat.succ.inj h_len1
                  have h_len2_next : (r2::rs2).length = (p2::ps2).length := Nat.succ.inj h_len2
                  have h_ih := ih (P2::Ps2) (r2::rs2) claim_next h_ver h_len1_next h_len2_next h_cons2.2 (by aesop) h_next_false
                  cases h_ih with
                  | inl h_left =>
                    left
                    exact h_left
                  | inr h_right =>
                    right
                    dsimp [multi_round_bad_event]
                    right
                    exact h_right


/-!
## The other direction: completeness

`sumcheck_multi_reduction` is the soundness half — if the verifier accepts a *false* claim then
some round was lucky.  Nothing so far says the verifier accepts an *honest* run at all, and the
hiding side needs exactly that: `HonestFinalClaim` (`ZkSim.lean`) asks what claim the rounds
close on when the prover is honest.

`HonestRounds` says the transmitted triples agree with the true polynomials where the verifier
looks: at `0`, at `1`, and at the round's own challenge.  Under it the round checks pass by
`check_round_c`'s test and the chain telescopes down to `get_last_eval`.
-/

/-- The transmitted round polynomials agree with the true ones at the three points the
verifier reads: `0`, `1`, and the challenge.  This is the negation of `BadRoundEvent`'s first
conjunct, round by round, plus agreement at the challenge. -/
def HonestRounds {F : Type} [Field F] {d : ℕ} [Interp F d] :
    List (Polynomial F) → List (RoundPoly F d) → List F → Prop
  | (P :: Ps), (p :: ps), (r :: rs) =>
      (p.eval0 = P.eval 0 ∧ p.eval1 = P.eval 1 ∧ p.eval_lagrange r = P.eval r)
        ∧ HonestRounds Ps ps rs
  | [], [], [] => True
  | _, _, _ => False

/--
**Sumcheck completeness, multi-round.**

An honest prover starting from the true claim is accepted, and the claim the verifier ends on
is the last true polynomial at its own challenge — `get_last_eval`.

The two hypotheses are exactly the honest prover's own properties: `hcons` is
`consistent_generate` (each true polynomial's hypercube sum is the previous one's value at the
challenge) and `hstart` says the run starts from the true claim.  Note that no degree bound and
no field-size condition appear: completeness is unconditional.
-/
theorem sumcheck_multi_completeness {F : Type} [Field F] [DecidableEq F] {d : ℕ} [Interp F d] :
    ∀ (P_trues : List (Polynomial F)) (polys : List (RoundPoly F d)) (challenges : List F)
      (claim_in : F),
      HonestRounds P_trues polys challenges →
      consistent_true_polys P_trues challenges →
      polys ≠ [] →
      claim_in = P_trues.head!.eval 0 + P_trues.head!.eval 1 →
      verify_multi_round claim_in polys challenges = get_last_eval P_trues challenges := by
  intro P_trues
  induction P_trues with
  | nil => intro polys challenges claim_in hh _ _ _; cases polys <;> cases challenges <;> simp_all [HonestRounds]
  | cons P Pt ih =>
    intro polys challenges claim_in hh hcons _ hstart
    cases polys with
    | nil => exact absurd hh (by simp [HonestRounds])
    | cons p pt =>
      cases challenges with
      | nil => exact absurd hh (by simp [HonestRounds])
      | cons r rt =>
        obtain ⟨⟨h0, h1, hr⟩, hrest⟩ := hh
        -- the round check passes: the transmitted `p(0) + p(1)` is the incoming claim
        have hcheck : check_round_c claim_in p r = some (p.eval_lagrange r) := by
          rw [check_round_c, if_pos]
          simp only [beq_iff_eq, h0, h1]
          simpa using hstart.symm
        rw [verify_multi_round, hcheck, hr]
        cases pt with
        | nil =>
          -- one round left: `Pt` and `rt` are empty too, and the chain ends here
          cases Pt with
          | nil => cases rt with
            | nil => rfl
            | cons _ _ => exact absurd hrest (by simp [HonestRounds])
          | cons _ _ => exact absurd hrest (by simp [HonestRounds])
        | cons p' pt' =>
          cases Pt with
          | nil => exact absurd hrest (by simp [HonestRounds])
          | cons P' Pt' =>
            cases rt with
            | nil => exact absurd hrest (by simp [HonestRounds])
            | cons r' rt' =>
              -- the next claim is the true one, by `consistent_true_polys`
              rw [consistent_true_polys] at hcons
              -- with two or more rounds left, `get_last_eval` just drops the head
              have hgle : get_last_eval (P :: P' :: Pt') (r :: r' :: rt')
                  = get_last_eval (P' :: Pt') (r' :: rt') := rfl
              rw [hgle]
              exact ih (p' :: pt') (r' :: rt') (P.eval r) hrest hcons.2 (by simp)
                (by simpa using hcons.1.symm)

end Sumcheck
