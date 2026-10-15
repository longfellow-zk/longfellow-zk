import Bcs.Counting
import Sumcheck.Grinding
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order

/-!
# Round-by-round soundness against a grinding adversary

`Bcs.Soundness` compiles a public-coin IPCP with a Merkle commitment while keeping the verifier's coins **external**; this file removes that, at the
one price a non-interactive prover can pay: it may **grind**, re-deriving challenges as often as
its hash budget allows.

## No protocol structure, deliberately

A round-by-round argument needs three things: a marker saying whether a partial transcript is
already lost, a bound on how often a fresh challenge escapes that marker, and the fact that an
accepting transcript is not lost.  None of the three needs a protocol *object* — they are all
statements about the tape of challenges the run consumed.  So this file takes `Accepts` abstract,
exactly as `lfzk`'s `accepts` is abstract, and indexes the state function by *how much of the tape
it reads*: prefix-measurability is a typing fact rather than a hypothesis, since a predicate given
only the first `j` answers cannot mention slot `j` or later.

The plan for this file originally carried an `L`-round `MultiRound` protocol record with
`Ch : Fin L → Type`, `Msg : Fin L → Type` and a `verify` field.  It is not here: no theorem needed
it, and adding it would only oblige a caller to *also* prove that its abstract `Accepts` agrees
with the record's `verify` — work with no result attached.  Rounds whose challenges have different
types are handled by `card_preimage_le_of_balanced` instead, which is both cheaper and more
faithful; see the section on it below.

## Two notions, and which one is the grinding one

The counting needs only this much: a per-slot bad event, a budget for it, and the fact that an
accepting-and-failing tape hits it somewhere.  That is `RbrCore`, and it is what `rbr_card_le`
consumes.  Its `escape_of_accepts` field is a *field*, not a theorem, precisely because how one
proves it depends on what the adversary is allowed to do.

`Rbr` is the sufficient condition for the **sequential** reading, where the tape slots *are* the
protocol's challenge rounds in order: a monotone state function that starts doomed and is not
doomed at the end must have been shed at one slot (`Rbr.exists_escape`), and `Rbr.toCore` packages
that.  At `T = L` this is round-by-round soundness of the interactive protocol, restated so that
each round's error is charged separately instead of being summed up front.

**It is not yet the grinding bound, and lengthening the tape does not make it one.**  A grinding
adversary re-derives challenges by querying the oracle at many partial transcripts; in the lazy
model each distinct query consumes the next slot, so the bad event at slot `i` is "*the query made
at slot `i`* was doomed and its answer escaped".  That is a `RbrCore`, with `bad i` reading the
adversary's history (slots `< i`) to find which query it made — but it is *not* an `Rbr`, because
the query at slot `i+1` is a different transcript from the query at slot `i`, so there is no
monotone state to shed and `exists_escape` proves the wrong thing.  Discharging
`escape_of_accepts` for a grinding adversary needs the adversary's query tree and the verifier's
recomputation, which is the Fiat--Shamir analogue of `Bcs.Adversary` that `Bcs.Soundness` does not
have.  `../longfellow-nizk-plan.md` §3 tracks that as Phase 3c.

So: the counting layer is grinding-ready, the sequential instance is proved, and the reduction from
a grinding adversary to a `RbrCore` is the outstanding piece.  When it lands, the bound reads
`(∑ i, beta i) / |C|` over a tape of length `T = t + L`, i.e. `T · max beta / |C|` — and the factor
`T` is not a loss, because security is advantage per unit of work and the adversary spent `T` to
get it (`../extractor-plan.md` §5.1 settles that convention for the repo).  The per-slot `beta` is
kept per-slot rather than collapsed to a max because a real protocol's rounds have genuinely
different densities.

## What is proved

* `RbrCore` — the counting interface: a per-slot bad event, its budget, and the escape fact;
* `rbr_card_le` — the count, `(∑ i, beta i) * |C|^(T-1)` accepting tapes;
* `rbr_ratio_le` — the same as a probability, `(∑ i, beta i) / |C|`;
* `Rbr`, `Rbr.exists_escape`, `Rbr.toCore` — the sequential sufficient condition and its proof;
* `card_preimage_le_of_balanced` — the bridge from a budget over the *challenge space* to one over
  the oracle's *answer* space, for a decoder that is at most `k`-to-one.  This is what lets one
  linearly ordered tape of digests carry rounds whose challenges have different types, and it is
  where a non-uniform sampler's bias would show up rather than being assumed away.

## What is not here

The oracle is **fixed**: `Fails` is a proposition, not a function of the tape, because the
commitment is built before any challenge is drawn and so is constant along this one.
`rbr_card_le_prod` lifts that to a family, one `Rbr` per commitment, which is the protocol-agnostic
half of a composed bound.

The other half — the price of the commitment itself — is *not* here and is not a lemma away.
`Bcs.Soundness`'s `drop_explains_card_le` pays it, but over `(Fin T → D) × (Challenge × Query)`,
where the adversary is **handed** one challenge and one query (`A.openingStage omega.2.1
omega.2.2`).  A Fiat--Shamir adversary is handed nothing.  Composing therefore needs a
Fiat--Shamir analogue of `Bcs.Adversary` — a change to `Compiled.lean`, `Transcript.lean` and
`Extractor.lean` — which is the same missing ingredient as the grinding reduction above.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bcs

open Finset
open scoped Classical

/-! ## Prefixes of a tape -/

section Prefixes

variable {C : Type}

/-- The first `j` slots of a tape, for `j` within the tape.  Proof-carrying in `hj`, which costs
nothing: `Fin`'s bound is a proposition, so two truncations at the same `j` are definitionally
equal. -/
def trunc {T : ℕ} (tape : Fin T → C) (j : ℕ) (hj : j ≤ T) : Fin j → C :=
  fun k => tape ⟨k.val, lt_of_lt_of_le k.isLt hj⟩

/-- One more slot on the end of a prefix. -/
def extend {j : ℕ} (pref : Fin j → C) (c : C) : Fin (j + 1) → C :=
  fun k => if h : k.val < j then pref ⟨k.val, h⟩ else c

/-- Truncating to `i` is `Sumcheck`'s prefix extraction, so the counting lemmas apply on the
nose. -/
theorem trunc_eq_extract_prefix {T : ℕ} (tape : Fin T → C) (i : Fin T) :
    trunc tape i.val (le_of_lt i.isLt) = Sumcheck.extract_prefix tape i := rfl

/-- Truncating one slot further is the prefix extended by that slot. -/
theorem trunc_succ {T : ℕ} (tape : Fin T → C) (i : Fin T) :
    trunc tape (i.val + 1) i.isLt
      = extend (Sumcheck.extract_prefix tape i) (tape i) := by
  funext k
  rcases lt_or_ge k.val i.val with hk | hk
  · simp only [trunc, extend, dif_pos hk]
    rfl
  · have hki : k.val = i.val := by omega
    have hnot : ¬ k.val < i.val := by omega
    simp only [trunc, extend, dif_neg hnot]
    congr 1
    exact Fin.ext hki

end Prefixes

/-! ## The counting interface -/

/--
**What the count needs, and nothing more.**

`bad i` is the event at slot `i`, given as a function of the first `i` answers and the `i`-th — so
prefix-measurability is a typing fact, not a hypothesis.  `escape_of_accepts` is the deterministic
content: an accepting tape on which extraction failed hits some slot's bad event.  It is a *field*
because how one proves it is exactly what distinguishes the sequential reading (`Rbr` below) from
the grinding one (see the module docstring).
-/
structure RbrCore (C : Type) [Fintype C] (T : ℕ) (Accepts : (Fin T → C) → Prop)
    (Fails : Prop) where
  /-- The bad event at slot `i`, reading the first `i` answers and the `i`-th. -/
  bad : ∀ i : Fin T, (Fin i.val → C) → C → Prop
  /-- The per-slot budget. -/
  beta : Fin T → ℕ
  /-- From any history, at most `beta i` answers at slot `i` are bad. -/
  bad_card : ∀ (i : Fin T) (pref : Fin i.val → C),
    (univ.filter fun c : C => bad i pref c).card ≤ beta i
  /-- An accepting tape on which extraction failed is bad at some slot. -/
  escape_of_accepts : ∀ tape : Fin T → C, Accepts tape → Fails →
    ∃ i : Fin T, bad i (Sumcheck.extract_prefix tape i) (tape i)

namespace RbrCore

variable {C : Type} [Fintype C] {T : ℕ} {Accepts : (Fin T → C) → Prop} {Fails : Prop}

/--
**The count.**  At most `(∑ i, beta i) * |C|^(T-1)` of the `|C|^T` tapes both make the verifier
accept and leave extraction failing.

`Sumcheck.tape_bad_card_le` does all of it; the only content here is that the accepting-and-failing
tapes are a subset of the bad ones, which is `escape_of_accepts`.
-/
theorem rbr_card_le [DecidableEq C] (R : RbrCore C T Accepts Fails) :
    (univ.filter fun tape : Fin T → C => Accepts tape ∧ Fails).card
      ≤ (∑ i, R.beta i) * Fintype.card C ^ (T - 1) := by
  classical
  refine le_trans (Finset.card_le_card ?_)
    (Sumcheck.tape_bad_card_le R.beta (fun i pref c => R.bad i pref c) R.bad_card)
  intro tape htape
  simp only [mem_filter, mem_univ, true_and] at htape ⊢
  exact R.escape_of_accepts tape htape.1 htape.2

/--
**The same bound as a probability.**  Over the uniform tape,

```
Pr[ the verifier accepts  ∧  extraction fails ]  ≤  (∑ i, beta i) / |C|
```
-/
theorem rbr_ratio_le [DecidableEq C] [Nonempty C] (R : RbrCore C T Accepts Fails) (hT : 1 ≤ T) :
    ((univ.filter fun tape : Fin T → C => Accepts tape ∧ Fails).card : ℚ)
        / (Fintype.card C : ℚ) ^ T
      ≤ ((∑ i, R.beta i : ℕ) : ℚ) / (Fintype.card C : ℚ) := by
  classical
  have hCpos : (0 : ℚ) < (Fintype.card C : ℚ) := by
    have hpos : 0 < Fintype.card C := Fintype.card_pos
    exact_mod_cast hpos
  have hpow : (Fintype.card C : ℚ) ^ T
      = (Fintype.card C : ℚ) ^ (T - 1) * (Fintype.card C : ℚ) := by
    rw [← pow_succ]
    congr 1
    omega
  have hnum : ((univ.filter fun tape : Fin T → C => Accepts tape ∧ Fails).card : ℚ)
      ≤ ((∑ i, R.beta i : ℕ) : ℚ) * (Fintype.card C : ℚ) ^ (T - 1) := by
    exact_mod_cast R.rbr_card_le
  rw [hpow, div_le_div_iff₀ (mul_pos (pow_pos hCpos (T - 1)) hCpos) hCpos]
  calc ((univ.filter fun tape : Fin T → C => Accepts tape ∧ Fails).card : ℚ) *
        (Fintype.card C : ℚ)
      ≤ (((∑ i, R.beta i : ℕ) : ℚ) * (Fintype.card C : ℚ) ^ (T - 1)) *
          (Fintype.card C : ℚ) := by gcongr
    _ = ((∑ i, R.beta i : ℕ) : ℚ) *
          ((Fintype.card C : ℚ) ^ (T - 1) * (Fintype.card C : ℚ)) := by ring

end RbrCore

/-! ## The sequential sufficient condition -/



/--
**Round-by-round soundness against a grinding adversary.**

`C` is the challenge-oracle's answer type, `T` the number of answers the run consumes,
`Accepts` the compiled verifier's decision on a tape, and `Fails` the statement that extraction
from the (fixed) committed oracle produced no witness.

The three fields are the classical obligations:

* `doomed_start` — extraction failing means the empty transcript is already lost.  For a
  list-valued extractor this is *every* candidate failing, and that is where the list factor
  enters: `beta` must bound the escape count for the whole list at once, which costs one factor of
  the list size and no more (`gero`'s `CPArg.RBRSound.list_union_bound` settles that a state
  function, emitting no message, has no pigeonhole);
* `doom_preserved` — from a lost prefix, at most `beta i` of the `|C|` answers at slot `i` recover.
  Nothing is assumed about the prover's message: `doomed (i+1)` is applied to the extended prefix
  and quantified over all of `C`, so a message chosen after seeing slot `i` is already covered;
* `accepts_undoomed` — an accepting run is not lost at the end.  This is the only place the
  verifier enters, and it is the round-by-round replacement for "the verifier's final check".
-/
structure Rbr (C : Type) [Fintype C] (T : ℕ) (Accepts : (Fin T → C) → Prop)
    (Fails : Prop) where
  /-- The state function, reading exactly the first `j` slots. -/
  doomed : ∀ j : ℕ, (Fin j → C) → Prop
  /-- The per-slot escape budget. -/
  beta : Fin T → ℕ
  /-- Extraction failure dooms the empty transcript. -/
  doomed_start : Fails → ∀ pt : Fin 0 → C, doomed 0 pt
  /-- Doom preservation: from a doomed prefix, at most `beta i` answers escape. -/
  doom_preserved : ∀ (i : Fin T) (pref : Fin i.val → C), doomed i.val pref →
    (univ.filter fun c : C => ¬ doomed (i.val + 1) (extend pref c)).card ≤ beta i
  /-- An accepting tape is not doomed at the end. -/
  accepts_undoomed : ∀ tape : Fin T → C, Accepts tape → ¬ doomed T (trunc tape T le_rfl)

namespace Rbr

variable {C : Type} [Fintype C] {T : ℕ} {Accepts : (Fin T → C) → Prop} {Fails : Prop}

/--
**The deterministic core.**  A tape whose empty prefix is doomed and whose full length is not
escaped doom at exactly one slot: there is an `i` with the prefix before `i` doomed and the prefix
through `i` not.

No counting, no probability — this is a statement about a single tape, and it is what turns
"the verifier accepted" into "some one round got lucky".  The proof is the least `j` at which doom
has been shed.
-/
theorem exists_escape (R : Rbr C T Accepts Fails) (tape : Fin T → C)
    (h0 : R.doomed 0 (trunc tape 0 (Nat.zero_le T)))
    (hend : ¬ R.doomed T (trunc tape T le_rfl)) :
    ∃ i : Fin T, R.doomed i.val (Sumcheck.extract_prefix tape i) ∧
      ¬ R.doomed (i.val + 1) (extend (Sumcheck.extract_prefix tape i) (tape i)) := by
  -- strong induction on the first length at which doom is gone
  have key : ∀ j : ℕ, ∀ hj : j ≤ T, ¬ R.doomed j (trunc tape j hj) →
      ∃ i : Fin T, R.doomed i.val (Sumcheck.extract_prefix tape i) ∧
        ¬ R.doomed (i.val + 1) (extend (Sumcheck.extract_prefix tape i) (tape i)) := by
    intro j
    induction j with
    | zero => exact fun hj hnot => absurd h0 hnot
    | succ m ih =>
      intro hj hnot
      have hm : m ≤ T := by omega
      by_cases hdoom : R.doomed m (trunc tape m hm)
      · -- doom is shed exactly at slot `m`
        have hmT : m < T := by omega
        refine ⟨⟨m, hmT⟩, ?_, ?_⟩
        · rw [← trunc_eq_extract_prefix tape ⟨m, hmT⟩]
          exact hdoom
        · rw [← trunc_succ tape ⟨m, hmT⟩]
          exact hnot
      · exact ih hm hdoom
  exact key T le_rfl hend

/--
**The sequential reading is a `RbrCore`.**  The bad event at slot `i` is "doomed before, undoomed
after", its budget is doom preservation, and `escape_of_accepts` is `exists_escape`.

Everything the count needs is therefore available from `Rbr`, and `RbrCore.rbr_card_le` /
`RbrCore.rbr_ratio_le` apply.
-/
def toCore (R : Rbr C T Accepts Fails) : RbrCore C T Accepts Fails where
  bad i pref c := R.doomed i.val pref ∧ ¬ R.doomed (i.val + 1) (extend pref c)
  beta := R.beta
  bad_card i pref := by
    classical
    by_cases hdoom : R.doomed i.val pref
    · refine le_trans (Finset.card_le_card ?_) (R.doom_preserved i pref hdoom)
      intro c hc
      simp only [mem_filter, mem_univ, true_and] at hc ⊢
      exact hc.2
    · -- empty; bound it through `∅` rather than by rewriting, because the goal's `Finset.filter`
      -- carries its own `DecidablePred` instance and a hand-written copy does not match it
      refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
      intro c hc
      simp only [mem_filter, mem_univ, true_and] at hc
      exact absurd hc.1 hdoom
  escape_of_accepts tape hacc hfail :=
    R.exists_escape tape (R.doomed_start hfail _) (R.accepts_undoomed tape hacc)


end Rbr

/-! ## One tape, differently-typed rounds

A protocol's rounds do not all draw from the same set: Longfellow's draw from `F × F`, from `F`,
from a Ligero challenge space and from an `r`-subset of `n` columns.  `RbrCore` is stated over a
single answer type `C` because the count needs a linear order on the slots, and a tuple of tapes
has none.

The bridge is the one the implementation itself uses: the oracle answers in `C` — digests — and each
round **decodes** its digest into the challenge it needs.  A budget over the challenge space then
pulls back to a budget over `C`, multiplied by how many digests can decode to one challenge.  Two
things this buys over assuming a typed oracle per round:

* it is what the deployed system does, so there is no idealisation to name;
* a decoder that is *not* balanced — an `r`-subset sampled by drawing indices and deduplicating,
  say — shows up as a larger `k`, rather than being assumed away.  The bias is in the constant.
-/

section Decode

/--
**Pulling a budget back along a decoder.**  If at most `k` answers decode to any one challenge,
then a bad set of `b` challenges is bad for at most `k * b` answers.

`k = |C| / |Y|` for a balanced decoder, which is the case worth quoting; the statement is an
inequality so that an unbalanced sampler is expressible rather than excluded.
-/
theorem card_preimage_le_of_balanced {C Y : Type} [Fintype C] [DecidableEq Y]
    (decode : C → Y) (k : ℕ) (hbal : ∀ y : Y, (univ.filter fun c : C => decode c = y).card ≤ k)
    (Bad : Finset Y) :
    (univ.filter fun c : C => decode c ∈ Bad).card ≤ k * Bad.card := by
  classical
  have hsplit : (univ.filter fun c : C => decode c ∈ Bad)
      = Bad.biUnion (fun y => univ.filter fun c : C => decode c = y) := by
    ext c
    simp only [mem_filter, mem_univ, true_and, Finset.mem_biUnion]
    exact ⟨fun h => ⟨decode c, h, rfl⟩, fun ⟨y, hy, hc⟩ => hc ▸ hy⟩
  rw [hsplit]
  calc (Bad.biUnion fun y => univ.filter fun c : C => decode c = y).card
      ≤ ∑ y ∈ Bad, (univ.filter fun c : C => decode c = y).card := Finset.card_biUnion_le
    _ ≤ ∑ _y ∈ Bad, k := Finset.sum_le_sum (fun y _ => hbal y)
    _ = k * Bad.card := by simp [Finset.sum_const, mul_comm]

/--
**The per-round budget, in the shape `RbrCore.bad_card` wants.**  A bad set given as a *predicate*
on challenges, of size at most `b`, is bad for at most `k * b` oracle answers.

This is the form every round of a real protocol arrives in: the protocol-level count says "at most
two challenges are roots of this difference", and what the tape count needs is "at most `2k`
answers decode to one".
-/
theorem card_decode_le {C Y : Type} [Fintype C] [Fintype Y] [DecidableEq Y]
    (decode : C → Y) (k : ℕ) (hbal : ∀ y : Y, (univ.filter fun c : C => decode c = y).card ≤ k)
    (Pred : Y → Prop) (b : ℕ) (hb : (univ.filter Pred).card ≤ b) :
    (univ.filter fun c : C => Pred (decode c)).card ≤ k * b := by
  classical
  refine le_trans (Finset.card_le_card (t := univ.filter fun c : C =>
      decode c ∈ univ.filter Pred) ?_) ?_
  · intro c hc
    simp only [mem_filter, mem_univ, true_and] at hc ⊢
    exact hc
  · exact le_trans (card_preimage_le_of_balanced decode k hbal _)
      (Nat.mul_le_mul_left k hb)

end Decode

/-! ## Fixing the commitment

The composed sample space is `Pre × (Fin T → C)`: everything the commitment stage decided, then
the challenge tape.  `Rbr` fixes the commitment, so a composed bound needs one `Rbr` per `Pre` and
a sum over `Pre`.  That sum is the *whole* of the "fix the commitment tape" half of the double
count, and it is protocol-agnostic, so it belongs here rather than at any instantiation.

What is **not** here is the other half, the price of the commitment itself.  `Bcs.Soundness`'s
`drop_explains_card_le` pays it, but it is stated over `(Fin T → D) × (Challenge × Query)` — the
*interactive* sample space, where the adversary is **handed** one challenge and one query
(`A.openingStage omega.2.1 omega.2.2`).  A Fiat--Shamir adversary is not handed coins; it derives
them from a tape and may re-derive them.  So composing this with `merkle` is not a reuse of
`drop_explains_card_le`: it needs a Fiat--Shamir analogue of `Bcs.Adversary` first, which is a
change to `Compiled.lean`, `Transcript.lean` and `Extractor.lean` rather than a new lemma.  That is
the next piece of work, and `longfellow-nizk-plan.md` §3 records it.
-/

section Composed

variable {Pre C : Type} [Fintype Pre] [Fintype C] [DecidableEq C] {T : ℕ}

/--
**Slicing on the commitment.**  Given one round-by-round argument per commitment — the state
function may depend on the commitment, and the escape budgets may too — the composed count is the
worst budget times the tape volume times the number of commitments.

`beta` is taken as a single bound over all commitments rather than per-commitment, because that is
what a parameter table quotes: the budgets come from the code parameters, not from the adversary's
commitment.
-/
theorem rbr_card_le_prod {Accepts : Pre × (Fin T → C) → Prop} {Fails : Pre → Prop}
    (R : ∀ pre : Pre, Rbr C T (fun tape => Accepts (pre, tape)) (Fails pre))
    (bound : ℕ) (hbound : ∀ pre, (∑ i, (R pre).beta i) ≤ bound) :
    (univ.filter fun omega : Pre × (Fin T → C) => Accepts omega ∧ Fails omega.1).card
      ≤ Fintype.card Pre * (bound * Fintype.card C ^ (T - 1)) := by
  classical
  rw [card_filter_prod_fst (fun omega : Pre × (Fin T → C) => Accepts omega ∧ Fails omega.1)]
  calc ∑ pre : Pre, (univ.filter fun tape : Fin T → C =>
          Accepts (pre, tape) ∧ Fails pre).card
      ≤ ∑ _pre : Pre, bound * Fintype.card C ^ (T - 1) :=
        Finset.sum_le_sum (fun pre _ =>
          le_trans (R pre).toCore.rbr_card_le (Nat.mul_le_mul_right _ (hbound pre)))
    _ = Fintype.card Pre * (bound * Fintype.card C ^ (T - 1)) := by
        simp [Finset.sum_const]

/-- **The composed bound as a probability**: `bound / |C|`, uniformly in the commitment. -/
theorem rbr_ratio_le_prod [Nonempty Pre] [Nonempty C]
    {Accepts : Pre × (Fin T → C) → Prop} {Fails : Pre → Prop}
    (R : ∀ pre : Pre, Rbr C T (fun tape => Accepts (pre, tape)) (Fails pre))
    (bound : ℕ) (hbound : ∀ pre, (∑ i, (R pre).beta i) ≤ bound) (hT : 1 ≤ T) :
    ((univ.filter fun omega : Pre × (Fin T → C) => Accepts omega ∧ Fails omega.1).card : ℚ)
        / (Fintype.card Pre * (Fintype.card C : ℚ) ^ T)
      ≤ (bound : ℚ) / (Fintype.card C : ℚ) := by
  classical
  have hCpos : (0 : ℚ) < (Fintype.card C : ℚ) := by
    have hpos : 0 < Fintype.card C := Fintype.card_pos
    exact_mod_cast hpos
  have hPpos : (0 : ℚ) < (Fintype.card Pre : ℚ) := by
    have hpos : 0 < Fintype.card Pre := Fintype.card_pos
    exact_mod_cast hpos
  have hpow : (Fintype.card C : ℚ) ^ T
      = (Fintype.card C : ℚ) ^ (T - 1) * (Fintype.card C : ℚ) := by
    rw [← pow_succ]
    congr 1
    omega
  have hnum : ((univ.filter fun omega : Pre × (Fin T → C) =>
        Accepts omega ∧ Fails omega.1).card : ℚ)
      ≤ (Fintype.card Pre : ℚ) * ((bound : ℚ) * (Fintype.card C : ℚ) ^ (T - 1)) := by
    exact_mod_cast rbr_card_le_prod R bound hbound
  rw [hpow, div_le_div_iff₀ (mul_pos hPpos (mul_pos (pow_pos hCpos (T - 1)) hCpos)) hCpos]
  calc ((univ.filter fun omega : Pre × (Fin T → C) =>
          Accepts omega ∧ Fails omega.1).card : ℚ) * (Fintype.card C : ℚ)
      ≤ ((Fintype.card Pre : ℚ) * ((bound : ℚ) * (Fintype.card C : ℚ) ^ (T - 1))) *
          (Fintype.card C : ℚ) := by gcongr
    _ = (bound : ℚ) * ((Fintype.card Pre : ℚ) *
          ((Fintype.card C : ℚ) ^ (T - 1) * (Fintype.card C : ℚ))) := by ring

end Composed

/-! ## Non-vacuity

`Rbr` is a bundle of hypotheses, so it is worth knowing that it is inhabited and that its
conclusion says something.  The witness is the guessing game: a secret answer, a tape of `T`
tries, and doom meaning "no try has hit the secret yet".  It is the smallest object with the right
shape — an adversary that grinds, and a per-slot escape budget of one — and it exercises `extend`
and `trunc`.
-/

section Guessing

variable {C : Type} [Fintype C] [DecidableEq C]

/-- **The guessing game as a round-by-round instance.**  The verifier accepts a tape one of whose
slots is `secret`; a prefix is doomed while it has missed. -/
def guessingRbr (T : ℕ) (secret : C) :
    Rbr C T (fun tape => ∃ k : Fin T, tape k = secret) True where
  doomed j pref := ∀ k : Fin j, pref k ≠ secret
  beta _ := 1
  doomed_start _ _ := fun k => absurd k.isLt (by omega)
  doom_preserved i pref hdoom := by
    -- from a prefix that has missed, only `secret` itself escapes
    refine le_trans (Finset.card_le_card (t := ({secret} : Finset C)) ?_) (by simp)
    intro c hc
    simp only [mem_filter, mem_univ, true_and, not_forall, not_not] at hc
    obtain ⟨k, hk⟩ := hc
    rcases lt_or_ge k.val i.val with hlt | hge
    · exact absurd (by simpa [extend, dif_pos hlt] using hk) (hdoom ⟨k.val, hlt⟩)
    · have : ¬ k.val < i.val := by omega
      simp only [extend, dif_neg this] at hk
      simp [hk]
  accepts_undoomed tape hacc := by
    obtain ⟨k, hk⟩ := hacc
    exact fun hdoom => hdoom k hk

/-- **The conclusion is not vacuous**: at most `T * |C|^(T-1)` of the `|C|^T` tapes contain the
secret.  That is the grinding shape — `T` tries at a `1/|C|` chance each — and it is sharp up to
the union bound's own slack, the true count being `|C|^T - (|C|-1)^T`. -/
theorem guessing_card_le (T : ℕ) (secret : C) :
    (univ.filter fun tape : Fin T → C => (∃ k : Fin T, tape k = secret) ∧ True).card
      ≤ T * Fintype.card C ^ (T - 1) := by
  have h := (guessingRbr T secret).toCore.rbr_card_le
  simpa [guessingRbr, Rbr.toCore, Finset.sum_const, mul_comm] using h

end Guessing

end Bcs
