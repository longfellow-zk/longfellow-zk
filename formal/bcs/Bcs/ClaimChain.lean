import Bcs.RoundByRound

/-!
# State functions that track a claim

`Bcs.Rbr` takes its state function abstract: `doomed j` is any predicate of the first `j` answers.
Real protocols do not present one that way.  A sumcheck-style protocol carries a **claim**, each
round transforms it, and "doomed" means the claim is wrong — for every candidate the extractor
offers.  This file is that shape, and it exists to prove one thing generically:

> **the extractor's candidate list costs exactly one factor of its size, at every round.**

That is `gero`'s `CPArg.RBRSound.list_union_bound` for the two-block case; here it is the `T`-round
tape version, and it falls out of a union bound over candidates because a state function emits no
message and so there is no pigeonhole to pay for.  At Ligero V3's certified parameters the list size
is `4` (`../longfellow-nizk-plan.md` §6), so this costs two bits.

## The shape

A `ClaimChain` is an initial state, a per-slot transition, and a notion of the state being wrong for
a candidate:

* `step i pref c` may read the answers before slot `i` as well as the answer at it.  That is what
  carries the **prover's messages**: under Fiat--Shamir an accepting proof's round-`i` message is a
  function of the challenge prefix, so a transition that reads the prefix is reading the messages
  too.  Nothing about the prover has to be assumed here; the prefix-dependence is in the type;
* `Wrong cand s` is per-candidate, and `doomed` is `∀ cand, Wrong cand s`.  Quantifying inside the
  state function rather than outside is what makes the list factor a union bound instead of a
  pigeonhole.

`state` is total — it clamps at `T` rather than carrying a proof that `j ≤ T` — which keeps
`doomed`'s type exactly `Rbr`'s and avoids proof-carrying arguments in every rewrite.

## What a caller supplies

`toRbr` takes three things, and each is where a real protocol's content goes:

* `wrong_init` — extraction failing means the initial claim is wrong for every candidate.  For
  Longfellow this is "no candidate satisfies the circuit", which is a function of the commitment and
  the circuit alone, hence available before any challenge;
* `budget` — the per-round, **per-candidate** escape count.  `Lfzk.RbrBudgets` is exactly this list
  for Longfellow's rounds;
* `right_of_accepts` — an accepting run's final claim is right for some candidate.  This is the only
  place the verifier enters.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bcs

open Finset
open scoped Classical

/-! ## Restricting a prefix -/

section Restrict

variable {C : Type}

/-- Drop the last answer of a prefix. -/
def dropLast {j : ℕ} (pref : Fin (j + 1) → C) : Fin j → C :=
  fun k => pref ⟨k.val, by omega⟩

/-- The last answer of a prefix. -/
def lastOf {j : ℕ} (pref : Fin (j + 1) → C) : C := pref ⟨j, by omega⟩

@[simp] theorem dropLast_extend {j : ℕ} (pref : Fin j → C) (c : C) :
    dropLast (extend pref c) = pref := by
  funext k
  have hk : k.val < j := k.isLt
  simp only [dropLast, extend, dif_pos hk]

@[simp] theorem lastOf_extend {j : ℕ} (pref : Fin j → C) (c : C) :
    lastOf (extend pref c) = c := by
  have hj : ¬ (j < j) := by omega
  simp only [lastOf, extend, dif_neg hj]

end Restrict

/-! ## The notion -/

/--
**A claim carried along a tape.**

`S` is the state — a claim, or a tuple of claims and the layer position — and `Cand` indexes the
extractor's candidate list.  `step i` reads the prefix as well as slot `i`, which is how the
prover's messages enter without being assumed about.
-/
structure ClaimChain (C : Type) (T : ℕ) (S Cand : Type) where
  /-- The claim the run starts from. -/
  init : S
  /-- Slot `i`'s transition.  May read the earlier answers, hence the prover's messages. -/
  step : ∀ i : Fin T, (Fin i.val → C) → C → S → S
  /-- The state is wrong for this candidate. -/
  Wrong : Cand → S → Prop

namespace ClaimChain

variable {C S Cand : Type} {T : ℕ}

/-- The state after the first `j` answers.  Clamped past `T`, which never arises: `Rbr` only ever
evaluates the state function at `j ≤ T`. -/
def state (ch : ClaimChain C T S Cand) : ∀ (j : ℕ), (Fin j → C) → S
  | 0, _ => ch.init
  | (j + 1), pref =>
      if h : j < T then
        ch.step ⟨j, h⟩ (dropLast pref) (lastOf pref) (ch.state j (dropLast pref))
      else
        ch.state j (dropLast pref)

/-- **One step.**  Extending a prefix by one answer applies that slot's transition. -/
theorem state_extend (ch : ClaimChain C T S Cand) (i : Fin T) (pref : Fin i.val → C) (c : C) :
    ch.state (i.val + 1) (extend pref c) = ch.step i pref c (ch.state i.val pref) := by
  rw [state]
  simp only [dif_pos i.isLt, dropLast_extend, lastOf_extend]

/-- Doom: the state is wrong for **every** candidate.  Quantifying inside is what makes the list
cost a union bound rather than a pigeonhole. -/
def doomed (ch : ClaimChain C T S Cand) (j : ℕ) (pref : Fin j → C) : Prop :=
  ∀ cand : Cand, ch.Wrong cand (ch.state j pref)

/--
**The list factor, once.**

If from a wrong state at most `b` answers make it right *for one candidate*, then at most
`|Cand| * b` answers make it right for some candidate.  A union bound over the list — and that is
the whole cost of a list-valued extractor in a round-by-round argument, at every round and at any
depth.
-/
theorem doom_preserved_of_perCandidate [Fintype C] [Fintype Cand]
    (ch : ClaimChain C T S Cand) (b : ℕ) (i : Fin T) (pref : Fin i.val → C)
    (hb : ∀ cand : Cand, ch.Wrong cand (ch.state i.val pref) →
      (univ.filter fun c : C =>
        ¬ ch.Wrong cand (ch.step i pref c (ch.state i.val pref))).card ≤ b)
    (hdoom : ch.doomed i.val pref) :
    (univ.filter fun c : C => ¬ ch.doomed (i.val + 1) (extend pref c)).card
      ≤ Fintype.card Cand * b := by
  classical
  refine le_trans (Finset.card_le_card (t := univ.biUnion fun cand : Cand =>
      univ.filter fun c : C =>
        ¬ ch.Wrong cand (ch.step i pref c (ch.state i.val pref))) ?_) ?_
  · intro c hc
    simp only [mem_filter, mem_univ, true_and, doomed, not_forall] at hc
    obtain ⟨cand, hcand⟩ := hc
    rw [state_extend] at hcand
    exact Finset.mem_biUnion.mpr ⟨cand, mem_univ _, mem_filter.mpr ⟨mem_univ _, hcand⟩⟩
  · calc (univ.biUnion fun cand : Cand => univ.filter fun c : C =>
            ¬ ch.Wrong cand (ch.step i pref c (ch.state i.val pref))).card
        ≤ ∑ cand : Cand, (univ.filter fun c : C =>
            ¬ ch.Wrong cand (ch.step i pref c (ch.state i.val pref))).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _cand : Cand, b := Finset.sum_le_sum (fun cand _ => hb cand (hdoom cand))
      _ = Fintype.card Cand * b := by simp [Finset.sum_const]

/--
**A claim chain is a round-by-round argument.**

The three hypotheses are the protocol's content; everything else is the machinery above.  Note that
`budget` is stated **per candidate** — the caller never has to think about the list — and that
`beta` therefore already carries the `|Cand|` factor.
-/
def toRbr [Fintype C] [Fintype Cand] (ch : ClaimChain C T S Cand)
    {Accepts : (Fin T → C) → Prop} {Fails : Prop} (b : Fin T → ℕ)
    (wrong_init : Fails → ∀ cand : Cand, ch.Wrong cand ch.init)
    (budget : ∀ (i : Fin T) (pref : Fin i.val → C) (cand : Cand),
      ch.Wrong cand (ch.state i.val pref) →
      (univ.filter fun c : C =>
        ¬ ch.Wrong cand (ch.step i pref c (ch.state i.val pref))).card ≤ b i)
    (right_of_accepts : ∀ tape : Fin T → C, Accepts tape →
      ∃ cand : Cand, ¬ ch.Wrong cand (ch.state T (trunc tape T le_rfl))) :
    Rbr C T Accepts Fails where
  doomed := ch.doomed
  beta i := Fintype.card Cand * b i
  doomed_start hfail pt := by
    intro cand
    have : ch.state 0 pt = ch.init := rfl
    rw [this]
    exact wrong_init hfail cand
  doom_preserved i pref hdoom :=
    ch.doom_preserved_of_perCandidate (b i) i pref (fun cand => budget i pref cand) hdoom
  accepts_undoomed tape hacc := by
    obtain ⟨cand, hcand⟩ := right_of_accepts tape hacc
    exact fun hdoom => hcand (hdoom cand)

/--
**The bound a caller wants, in one call.**

```
Pr[ the verifier accepts  ∧  extraction fails ]  ≤  |Cand| · (∑ i, b i) / |C|
```

with `b` the per-round, per-candidate escape budget.  The `|Cand|` is the list factor, and it is a
single factor rather than one per round.
-/
theorem claimChain_ratio_le [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand]
    (ch : ClaimChain C T S Cand) {Accepts : (Fin T → C) → Prop} {Fails : Prop} (b : Fin T → ℕ)
    (wrong_init : Fails → ∀ cand : Cand, ch.Wrong cand ch.init)
    (budget : ∀ (i : Fin T) (pref : Fin i.val → C) (cand : Cand),
      ch.Wrong cand (ch.state i.val pref) →
      (univ.filter fun c : C =>
        ¬ ch.Wrong cand (ch.step i pref c (ch.state i.val pref))).card ≤ b i)
    (right_of_accepts : ∀ tape : Fin T → C, Accepts tape →
      ∃ cand : Cand, ¬ ch.Wrong cand (ch.state T (trunc tape T le_rfl)))
    (hT : 1 ≤ T) :
    ((univ.filter fun tape : Fin T → C => Accepts tape ∧ Fails).card : ℚ)
        / (Fintype.card C : ℚ) ^ T
      ≤ ((Fintype.card Cand * ∑ i, b i : ℕ) : ℚ) / (Fintype.card C : ℚ) := by
  have h := (ch.toRbr b wrong_init budget right_of_accepts).toCore.rbr_ratio_le hT
  have hsum : ∑ i, (ch.toRbr b wrong_init budget right_of_accepts).toCore.beta i
      = Fintype.card Cand * ∑ i, b i := by
    simp [toRbr, Rbr.toCore, Finset.mul_sum]
  rwa [hsum] at h

end ClaimChain

/-! ## Non-vacuity

The guessing game again, this time as a claim chain: the state is "has the secret been hit", the one
candidate is wrong while it has not, and the budget is one answer per round.  It gives back
`guessing_card_le`'s bound, which is what a witness for this interface should do.
-/

section GuessingChain

variable {C : Type} [Fintype C] [DecidableEq C]

/-- The guessing game as a claim chain: `Bool` state, one candidate, budget one. -/
def guessingChain (T : ℕ) (secret : C) : ClaimChain C T Bool Unit where
  init := false
  step _ _ c s := s || (c = secret)
  Wrong _ s := s = false

/-- The per-round budget is one: only `secret` itself changes the state. -/
theorem guessingChain_budget (T : ℕ) (secret : C) (i : Fin T) (pref : Fin i.val → C)
    (cand : Unit) (hw : (guessingChain T secret).Wrong cand
      ((guessingChain T secret).state i.val pref)) :
    (univ.filter fun c : C => ¬ (guessingChain T secret).Wrong cand
      ((guessingChain T secret).step i pref c
        ((guessingChain T secret).state i.val pref))).card ≤ 1 := by
  classical
  refine le_trans (Finset.card_le_card (t := ({secret} : Finset C)) ?_) (by simp)
  intro c hc
  simp only [mem_filter, mem_univ, true_and, guessingChain, Bool.or_eq_false_iff,
    decide_eq_false_iff_not, not_and, not_not] at hc
  simp only [Finset.mem_singleton]
  exact hc hw

end GuessingChain

end Bcs
