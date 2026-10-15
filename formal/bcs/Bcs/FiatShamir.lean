import Bcs.RoundByRound
import Merkle.LazyTape

/-!
# Fiat--Shamir: the grinding adversary

`Bcs.Rbr` is the *sequential* round-by-round notion — the tape slots are the protocol's rounds in
order, so the prover gets one draw per round and cannot retry.  This file removes that.  A
Fiat--Shamir prover is an adaptive oracle program: it queries the challenge hash at as many partial
transcripts as its budget allows and keeps whichever answer suits it.  What that buys it, and what it
costs, is what `Bcs.RbrCore` was built to express and what `Rbr` could not.

## Why this is a `RbrCore` and not an `Rbr`

`Rbr` needs a **monotone state**: doomed at the start, undoomed at the end, hence shed at one slot.
A grinding adversary has no such state.  Slot `j` holds the answer to whichever partial transcript it
asked `j`-th, and slot `j+1` holds the answer to a *different* transcript, so there is nothing to
shed.  The right bad event is per-slot and local:

> the query made at slot `j` was already lost, and its answer recovered it.

That is a `Bcs.RbrCore.bad` — a function of the first `j` answers and the `j`-th — and it is
prefix-measurable for a reason that is not obvious and had to be proved:
`Merkle.RandomOracle.slotQuery_eq`, that **the query occupying slot `j` is a function of the slots below
it**.  An adaptive adversary chooses what to ask from what it has been told, and at slot `j` it has
been told slots `0 … j-1`.

## Why doom is a function of the query alone

In Fiat--Shamir a query point *is* a transcript prefix.  So "this partial transcript is lost" is a
predicate on the query, with no history argument — which is what makes `DoomedQuery : Q → Prop` the
right type and keeps `Escapes : Q → C → Prop` a per-query root count.  Nothing here is specific to
Longfellow: `DoomedQuery` is whatever the protocol's state function says, and `Escapes q` is its
escape set at that transcript.

## The one field that is not a count

`chain` is the deterministic content: an accepting proof on which extraction failed queried some
doomed point and got a recovering answer.  It is the grinding analogue of `Rbr`'s
`accepts_undoomed`, and it is where a protocol's own reasoning goes — the Fiat--Shamir verifier
recomputes every challenge as a hash of its prefix, so an accepting proof's challenges are answers at
points *someone* queried; a point the adversary never queried is charged separately, at `1/|C|` per
round, by the usual fresh-hit argument.

`toRbrCore` is the conversion, and its content is turning "some **queried point**" into "some
**slot**".  That step is `slotQuery_eq` and nothing else.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bcs

open Finset Merkle.RandomOracle
open scoped Classical

/--
**A grinding Fiat--Shamir adversary, round by round.**

`adversary` is the adaptive program; `T` bounds the tape and `t` its query budget.  `DoomedQuery` and
`Escapes` are the protocol's state function, read at a query point — which under Fiat--Shamir is a
transcript prefix, hence carries its own history.
-/
structure Grinding (C : Type) [Fintype C] (Q A : Type) [DecidableEq Q] (t T : ℕ)
    (Accepts : (Fin T → C) → Prop) (Fails : Prop) where
  /-- The adaptive program, making at most `t` queries. -/
  adversary : Tree Q C A t
  /-- The answer an out-of-range slot would give; `Merkle.lazyRun_slot_lt` shows it is never read. -/
  dflt : C
  /-- The partial transcript at this query point is already lost. -/
  DoomedQuery : Q → Prop
  /-- The answers at this point that recover it. -/
  Escapes : Q → C → Prop
  /-- The per-query escape budget. -/
  beta : ℕ
  /-- From a lost point, at most `beta` answers recover.  This is the protocol's round bound. -/
  escape_bound : ∀ q : Q, DoomedQuery q →
    (univ.filter fun c : C => Escapes q c).card ≤ beta
  /-- **The deterministic core.**  An accepting run on which extraction failed queried a lost point
  and got a recovering answer.  See the module docstring for what supplies it. -/
  chain : ∀ tape : Fin T → C, Accepts tape → Fails →
    ∃ (j : Fin T) (q : Q),
      (lazyRun tape dflt adversary []).2.1[j.val]? = some q ∧
        DoomedQuery q ∧ Escapes q (tape j)

namespace Grinding

variable {C Q A : Type} [Fintype C] [DecidableEq Q] {t T : ℕ}
variable {Accepts : (Fin T → C) → Prop} {Fails : Prop}

/--
**A grinding adversary is a round-by-round argument.**

The bad event at slot `j` is "the query made there was lost and its answer recovered it", which is a
function of the prefix because `slotQuery_eq` says the query is.  Every slot carries the
same budget, so `RbrCore.rbr_ratio_le` gives `T * beta / |C|`.
-/
noncomputable def toRbrCore (G : Grinding C Q A t T Accepts Fails) :
    RbrCore C T Accepts Fails where
  bad j pref c :=
    ∃ q : Q, slotQuery (T := T) G.dflt G.adversary pref = some q ∧
      G.DoomedQuery q ∧ G.Escapes q c
  beta _ := G.beta
  bad_card j pref := by
    classical
    by_cases hex : ∃ q : Q,
        slotQuery (T := T) G.dflt G.adversary pref = some q ∧ G.DoomedQuery q
    · -- the slot's query is a lost point: its escape set is the budget
      obtain ⟨q, hq, hdoom⟩ := hex
      refine le_trans (Finset.card_le_card (t := univ.filter fun c : C => G.Escapes q c) ?_)
        (G.escape_bound q hdoom)
      intro c hc
      simp only [mem_filter, mem_univ, true_and] at hc ⊢
      obtain ⟨q', hq', -, hesc⟩ := hc
      exact (Option.some.inj (hq'.symm.trans hq)) ▸ hesc
    · -- either the adversary made no `j`-th distinct query, or that query was not lost
      refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
      intro c hc
      simp only [mem_filter, mem_univ, true_and] at hc
      obtain ⟨q', hq', hd, -⟩ := hc
      exact absurd ⟨q', hq', hd⟩ hex
  escape_of_accepts tape hacc hfail := by
    obtain ⟨j, q, hseen, hdoom, hesc⟩ := G.chain tape hacc hfail
    refine ⟨j, q, ?_, hdoom, hesc⟩
    rw [show Sumcheck.extract_prefix tape j
        = (fun i : Fin j.val => tape ⟨i.val, lt_trans i.isLt j.isLt⟩) from rfl]
    rw [slotQuery_eq G.dflt G.adversary (le_of_lt j.isLt) tape]
    exact hseen

/--
**The grinding bound.**

```
Pr[ the verifier accepts  ∧  extraction fails ]  ≤  T * beta / |C|
```

`T` is the tape length: the adversary's `t` queries plus whatever the verifier recomputes.  Read as
an absolute probability the factor `T` looks like a loss, and it is not — security is advantage per
unit of work and the adversary spent `T` to get it, so `advantage / work ≤ beta / |C|`, the
round-by-round error itself.  `../extractor-plan.md` §5.1 settles that convention for this repo.
-/
theorem grinding_ratio_le [DecidableEq C] [Nonempty C]
    (G : Grinding C Q A t T Accepts Fails) (hT : 1 ≤ T) :
    ((univ.filter fun tape : Fin T → C => Accepts tape ∧ Fails).card : ℚ)
        / (Fintype.card C : ℚ) ^ T
      ≤ ((T * G.beta : ℕ) : ℚ) / (Fintype.card C : ℚ) := by
  have h := G.toRbrCore.rbr_ratio_le hT
  have hsum : ∑ _i : Fin T, G.beta = T * G.beta := by simp [Finset.sum_const]
  rw [show (G.toRbrCore).beta = fun _ : Fin T => G.beta from rfl, hsum] at h
  exact h

end Grinding

end Bcs
