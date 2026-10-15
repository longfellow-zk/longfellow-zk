import Bcs.RecomputedRbr

/-!
# Fiat–Shamir on message prefixes: a total random oracle, counted point by point

`Bcs.TranscriptGrinding` and `Bcs.CtxGrinding` model a verifier whose round-`k` hash input carries
the **raw answers of the earlier rounds**, so that "this transcript prefix is lost" is a function of
the hash input alone and the bad event at a lazy-tape slot reads only the slots below it.  The
deployed Longfellow transcript (`rust/runtime/random/src/transcript.rs`, `lib/random/transcript.h`)
does not do that: it is one SHA-256 running state, messages are absorbed, and a challenge is a PRF
expansion of the current digest that is **not** re-absorbed.  Round `k`'s challenge is a function of
the message prefix alone.  Translating a deployed adversary into the raw-answer model costs a factor
`L` (the number of rounds) on the query count: to ask a raw-answer point the model adversary must
first know, hence ask, every earlier round.  This file removes that factor.

## Why the lazy tape is the wrong sample space here

With prefix-only hash inputs the bad event at round `k`'s point `q` reads the answers at `q`'s
ancestors (the hash inputs of rounds `< k` of the same message prefix), which the adversary need not
have asked before `q`.  On a lazy tape (`Merkle.RandomOracle.lazyRun`) an ancestor's answer sits at
its first-occurrence slot, and **that slot is chosen by the adversary after it has seen `q`'s
answer** (it decides how many other fresh points to ask first).  So "fix every slot but `q`'s and
count `q`'s answers" fails pointwise: holding the other slots fixed, the adversary can steer which
fixed slot value becomes the ancestor's answer, one choice per answer at `q`, and the escape count at
`q` multiplies by the number of slots it can steer to.  The bound is still true on average, but
proving it on the lazy tape is the lazy/eager sampling equivalence.

This file therefore counts over the **total** random oracle `H : Q → C` on a finite domain of hash
inputs: the textbook random oracle, a uniformly random function.  Coordinates are points, fixed in
advance, so "the whole oracle except `q`'s coordinate" is a well-defined sample-space slice
whatever the adversary does.

## What is proved

* `card_coord_mul`, `card_coord_le`, `card_coord_le_const` — **one coordinate held out**: if the bad
  event at coordinate `i` reads the oracle only off `i` (`AgreeOff`), then
  `#{H | bad H (H i)} · |C| = ∑ H, #{c | bad H c}`, so a per-slice bound `β` gives
  `#{H | bad H (H i)} ≤ β · |C|^(|ι|−1)`.  `card_exists_coord_le` is the union over coordinates
  with weights that may read the whole oracle (`∑ i, wt i H ≤ B` on every oracle).
* `mem_queried_iff`, `run_eq_of_not_mem` — **whether a run asks `x` does not depend on `H x`**, and a
  run that does not ask `x` does not depend on `H x` at all.
* `CtxGrinding` — the counting structure: an `N`-query adversary against `H`, a verifier recomputing
  round `k` at `hashInput out k` (**no challenge argument**), hash inputs with ancestors
  (`PrefixPoints`), a commitment context fixed off each point (`ctxAt_off`), and a per-point bad event
  reading the point's ancestors' answers (its *own* coordinates).  A point is **charged** when the
  adversary asks it or it is one of the verifier's `L` points (`Charged`); that event does not read
  the point's coordinate (`charged_off`), and on every oracle at most `N + L` points are charged.
  `CtxGrinding.card_mul_le`:
  `#E · |C| ≤ (N · βmax + ∑ k, slotBeta k) · |C|^|Q|` for every event `E` implying a round-level bad
  event — the bound of `Bcs.TranscriptGrinding.ratio_le_weighted`, now with `N` counting
  prefix-only hash queries.
* `Grinding` — the sequential round-by-round form: a state function per proof and per point
  (`doomed`, `doomedAt`) linked at the verifier's points by `hstate`.  `Grinding.ofRbr` builds it from
  any family of `Bcs.Rbr`s indexed by the messages a proof or a point carries (so from any
  `Bcs.ClaimChain` through `ClaimChain.toRbr`).  `roundBad_of_accepts` is the chain — the
  first-occurrence analogue of `Bcs.TranscriptGrinding.exists_bad_slot`: an accepting failing oracle
  sheds doom at some round `k`, and round `k`'s point, judged at its ancestors' answers, is bad at
  its own answer.  `Grinding.ratio_le` is the probability form.

## What is a modelling choice

The random oracle is a uniformly random function on the finite type `Q` of hash inputs; `Q`
finite is the only structural assumption (deployed messages are bounded byte strings).  Whether `Q`
is all of a type or an enumeration of the relevant points is the instantiation's business.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bcs.TotalOracle

open Finset Merkle.RandomOracle
open scoped Classical

/-- **Two oracles agree off a point.** -/
def AgreeOff {ι C : Type} (i : ι) (H H' : ι → C) : Prop := ∀ j, j ≠ i → H j = H' j

theorem AgreeOff.symm {ι C : Type} {i : ι} {H H' : ι → C} (h : AgreeOff i H H') :
    AgreeOff i H' H :=
  fun j hj => (h j hj).symm

theorem agreeOff_update {ι C : Type} [DecidableEq ι] (i : ι) (H : ι → C) (c : C) :
    AgreeOff i H (Function.update H i c) :=
  fun _ hj => (Function.update_of_ne hj c H).symm

/-- Write `c` at coordinate `i` and return the value it replaced.  An involution of
`(ι → C) × C`. -/
def swapCoord {ι C : Type} [DecidableEq ι] (i : ι) (p : (ι → C) × C) : (ι → C) × C :=
  (Function.update p.1 i p.2, p.1 i)

theorem swapCoord_swapCoord {ι C : Type} [DecidableEq ι] (i : ι) (p : (ι → C) × C) :
    swapCoord i (swapCoord i p) = p := by
  obtain ⟨H, c⟩ := p
  simp [swapCoord]

/-! ## 1. One coordinate held out -/

section Count

variable {ι C : Type} [Fintype ι] [DecidableEq ι] [Fintype C]

/--
**Counting with coordinate `i` held out.**  If the bad event at `i` reads the oracle only off `i`,
then the oracles bad at their own answer at `i`, times `|C|`, are the pairs (oracle, answer) that
are bad — i.e. for each setting of the other coordinates, the bad answers at `i`.
-/
theorem card_coord_mul (i : ι) (bad : (ι → C) → C → Prop)
    (hoff : ∀ H H' : ι → C, AgreeOff i H H' → ∀ c, bad H c → bad H' c) :
    (univ.filter fun H : ι → C => bad H (H i)).card * Fintype.card C
      = ∑ H : ι → C, (univ.filter fun c : C => bad H c).card := by
  rw [← card_filter_prod_fst (fun p : (ι → C) × C => bad p.1 p.2)]
  have hB : (univ.filter fun H : ι → C => bad H (H i)).card * Fintype.card C
      = (univ.filter fun p : (ι → C) × C => bad p.1 (p.1 i)).card := by
    rw [card_filter_prod_fst (fun p : (ι → C) × C => bad p.1 (p.1 i)), Finset.card_filter,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun H _ => ?_
    by_cases h : bad H (H i)
    · simp [h]
    · simp [h]
  rw [hB]
  refine Finset.card_nbij' (swapCoord i) (swapCoord i) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hp ⊢
    obtain ⟨H, c⟩ := p
    show bad (Function.update H i c) (H i)
    exact hoff _ _ (agreeOff_update i H c) _ hp
  · intro p hp
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hp ⊢
    obtain ⟨H, c⟩ := p
    show bad (Function.update H i c) ((Function.update H i c) i)
    rw [Function.update_self]
    exact hoff _ _ (agreeOff_update i H c) _ hp
  · intro p _
    exact swapCoord_swapCoord i p
  · intro p _
    exact swapCoord_swapCoord i p

/-- **Coordinate `i` held out, with a weight per slice.** -/
theorem card_coord_le (i : ι) (bad : (ι → C) → C → Prop)
    (hoff : ∀ H H' : ι → C, AgreeOff i H H' → ∀ c, bad H c → bad H' c)
    (wt : (ι → C) → ℕ) (hlocal : ∀ H, (univ.filter fun c : C => bad H c).card ≤ wt H) :
    (univ.filter fun H : ι → C => bad H (H i)).card * Fintype.card C ≤ ∑ H : ι → C, wt H := by
  rw [card_coord_mul i bad hoff]
  exact Finset.sum_le_sum fun H _ => hlocal H

/-- **Coordinate `i` held out, with a uniform budget**: `#{H | bad H (H i)} ≤ β · |C|^(|ι| − 1)`. -/
theorem card_coord_le_const [Nonempty C] (i : ι) (bad : (ι → C) → C → Prop)
    (hoff : ∀ H H' : ι → C, AgreeOff i H H' → ∀ c, bad H c → bad H' c)
    (β : ℕ) (hlocal : ∀ H, (univ.filter fun c : C => bad H c).card ≤ β) :
    (univ.filter fun H : ι → C => bad H (H i)).card
      ≤ β * Fintype.card C ^ (Fintype.card ι - 1) := by
  have h := card_coord_le i bad hoff (fun _ => β) hlocal
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, smul_eq_mul] at h
  have hι : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
  have hC : 0 < Fintype.card C := Fintype.card_pos
  have hpow : Fintype.card C ^ Fintype.card ι
      = Fintype.card C ^ (Fintype.card ι - 1) * Fintype.card C := by
    rw [← pow_succ]; congr 1; omega
  rw [hpow] at h
  have h' : (univ.filter fun H : ι → C => bad H (H i)).card * Fintype.card C
      ≤ β * Fintype.card C ^ (Fintype.card ι - 1) * Fintype.card C :=
    le_of_le_of_eq h (by ring)
  exact Nat.le_of_mul_le_mul_right h' hC

/--
**Every coordinate, with weights that may read the whole oracle.**  If coordinate `i`'s bad answers
on each slice are at most `wt i H`, and every oracle's weights sum to at most `B`, then

```text
#{ oracles bad at some coordinate's own answer } · |C|  ≤  B · |C|^|ι|.
```
-/
theorem card_exists_coord_le (bad : ι → (ι → C) → C → Prop)
    (hoff : ∀ i (H H' : ι → C), AgreeOff i H H' → ∀ c, bad i H c → bad i H' c)
    (wt : ι → (ι → C) → ℕ) (hlocal : ∀ i H, (univ.filter fun c : C => bad i H c).card ≤ wt i H)
    (B : ℕ) (htotal : ∀ H : ι → C, ∑ i, wt i H ≤ B) :
    (univ.filter fun H : ι → C => ∃ i, bad i H (H i)).card * Fintype.card C
      ≤ B * Fintype.card C ^ Fintype.card ι := by
  have hunion : (univ.filter fun H : ι → C => ∃ i, bad i H (H i))
      = univ.biUnion fun i : ι => univ.filter fun H : ι → C => bad i H (H i) := by
    ext H
    simp
  rw [hunion]
  calc (univ.biUnion fun i : ι => univ.filter fun H : ι → C => bad i H (H i)).card
        * Fintype.card C
      ≤ (∑ i : ι, (univ.filter fun H : ι → C => bad i H (H i)).card) * Fintype.card C :=
        Nat.mul_le_mul_right _ card_biUnion_le
    _ = ∑ i : ι, (univ.filter fun H : ι → C => bad i H (H i)).card * Fintype.card C := by
        rw [Finset.sum_mul]
    _ ≤ ∑ i : ι, ∑ H : ι → C, wt i H :=
        Finset.sum_le_sum fun i _ => card_coord_le i (bad i) (hoff i) (wt i) (hlocal i)
    _ = ∑ H : ι → C, ∑ i : ι, wt i H := Finset.sum_comm
    _ ≤ ∑ _H : ι → C, B := Finset.sum_le_sum fun H _ => htotal H
    _ = B * Fintype.card C ^ Fintype.card ι := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, smul_eq_mul, mul_comm]

/-- **The count as a probability**: `Pr[E] ≤ B / |C|`. -/
theorem ratio_exists_coord_le [Nonempty C] (E : (ι → C) → Prop) [DecidablePred E] (bad : ι → (ι → C) → C → Prop)
    (hE : ∀ H, E H → ∃ i, bad i H (H i))
    (hoff : ∀ i (H H' : ι → C), AgreeOff i H H' → ∀ c, bad i H c → bad i H' c)
    (wt : ι → (ι → C) → ℕ) (hlocal : ∀ i H, (univ.filter fun c : C => bad i H c).card ≤ wt i H)
    (B : ℕ) (htotal : ∀ H : ι → C, ∑ i, wt i H ≤ B) :
    ((univ.filter E).card : ℚ) / (Fintype.card C : ℚ) ^ Fintype.card ι
      ≤ (B : ℚ) / (Fintype.card C : ℚ) := by
  have hC : (0 : ℚ) < (Fintype.card C : ℚ) := by exact_mod_cast Fintype.card_pos
  have hsub : (univ.filter E).card
      ≤ (univ.filter fun H : ι → C => ∃ i, bad i H (H i)).card := by
    refine Finset.card_le_card fun H hH => ?_
    simp only [mem_filter, mem_univ, true_and] at hH ⊢
    exact hE H hH
  have hnat := le_trans (Nat.mul_le_mul_right (Fintype.card C) hsub)
    (card_exists_coord_le bad hoff wt hlocal B htotal)
  have hq : ((univ.filter E).card : ℚ) * (Fintype.card C : ℚ)
      ≤ (B : ℚ) * (Fintype.card C : ℚ) ^ Fintype.card ι := by exact_mod_cast hnat
  rw [div_le_div_iff₀ (pow_pos hC _) hC]
  exact hq

end Count

/-! ## 2. Runs against a total oracle -/

section Run

variable {Q C A : Type}

/-- The points a run against the oracle `H` asks, in order, repeats included. -/
def queried {fuel : ℕ} (t : Tree Q C A fuel) (H : Q → C) : List Q := (t.run H).2.map Prod.fst

@[simp] theorem queried_done {fuel : ℕ} (a : A) (H : Q → C) :
    queried (Tree.done (fuel := fuel) a : Tree Q C A fuel) H = [] := rfl

theorem queried_query {fuel : ℕ} (q : Q) (next : C → Tree Q C A fuel) (H : Q → C) :
    queried (Tree.query q next) H = q :: queried (next (H q)) H := rfl

/-- At most `fuel` queries. -/
theorem queried_length_le : ∀ {fuel : ℕ} (t : Tree Q C A fuel) (H : Q → C),
    (queried t H).length ≤ fuel
  | _, .done _, _ => by simp
  | _, .query q next, H => by
      rw [queried_query, List.length_cons]
      have := queried_length_le (next (H q)) H
      omega

/-- **Whether a run asks `x` does not depend on the answer at `x`**: up to the first time it asks
`x`, the run sees only answers off `x`. -/
theorem mem_queried_iff {fuel : ℕ} (t : Tree Q C A fuel) (x : Q) {H H' : Q → C}
    (h : AgreeOff x H H') : x ∈ queried t H ↔ x ∈ queried t H' := by
  induction t with
  | done a => simp
  | query q next ih =>
      rw [queried_query, queried_query, List.mem_cons, List.mem_cons]
      by_cases hq : x = q
      · simp [hq]
      · rw [← h q (Ne.symm hq)]
        exact or_congr_right (ih (H q))

/-- **A run that does not ask `x` does not depend on the answer at `x`.** -/
theorem run_eq_of_not_mem {fuel : ℕ} (t : Tree Q C A fuel) (x : Q) {H H' : Q → C}
    (h : AgreeOff x H H') (hx : x ∉ queried t H) : t.run H' = t.run H :=
  Tree.run_congr_on_trace t H H' fun qa hqa => by
    have hne : qa.1 ≠ x := fun he => hx (List.mem_map.mpr ⟨qa, hqa, he⟩)
    rw [← h qa.1 hne]
    exact (Tree.trace_sound t H qa hqa).symm

end Run

/-! ## 3. Hash inputs that are message prefixes -/

/-- **Prefix-structured hash inputs**: each point is drawn for a round (`slot`), and its ancestors
`anc q j` (`j < slot q`) are the hash inputs of the earlier rounds of the same message prefix.  No
point is its own ancestor. -/
structure PrefixPoints (Q : Type) where
  /-- The round a point is drawn for. -/
  slot : Q → ℕ
  /-- The hash input of round `j` of the same message prefix. -/
  anc : Q → ℕ → Q
  /-- No point is its own ancestor. -/
  anc_ne : ∀ (q : Q) (j : ℕ), j < slot q → anc q j ≠ q

namespace PrefixPoints

variable {Q C : Type}

/-- **The challenges a point's round is judged at**: the oracle's answers at its ancestors, each at
its own coordinate. -/
def chal (P : PrefixPoints Q) (H : Q → C) (q : Q) : Fin (P.slot q) → C :=
  fun j => H (P.anc q j.val)

/-- A point's ancestors' answers do not read the point's own coordinate. -/
theorem chal_congr (P : PrefixPoints Q) {q : Q} {H H' : Q → C} (h : AgreeOff q H H') :
    P.chal H q = P.chal H' q := by
  funext j
  exact h _ (P.anc_ne q j.val j.isLt)

end PrefixPoints

/-! ## 4. The count, with a commitment context -/

/--
**A prefix-only Fiat–Shamir adversary against a total random oracle, with the commitment context
read off the oracle.**

* `adversary` asks at most `N` points of `H` and outputs a proof;
* the verifier recomputes round `k`'s challenge as `H (hashInput out k)` — a function of the proof
  alone, no earlier challenge enters the hash input;
* `pts` gives each point its round and its ancestors;
* `key q` is the commitment a point names and `ctxAt H k` that commitment's context on oracle `H`;
  `ctxAt_off`: **the context of the key a point names does not read the point's coordinate**;
* `Bad κ x pref c` is the bad event at point `x` in context `κ`, with `pref` the answers at `x`'s
  ancestors and `c` the answer at `x`, and `beta x` its budget.
-/
structure CtxGrinding (C : Type) [Fintype C] (Q Out Key K : Type) [DecidableEq Q] (N L : ℕ) where
  /-- The adversary: an adaptive program making at most `N` queries. -/
  adversary : Tree Q C Out N
  /-- Round `k`'s hash input, from the proof alone. -/
  hashInput : Out → ℕ → Q
  /-- The rounds and ancestors of the hash inputs. -/
  pts : PrefixPoints Q
  /-- The commitment a point names. -/
  key : Q → Key
  /-- The commitment context of a key, on a whole oracle. -/
  ctxAt : (Q → C) → Key → K
  /-- **The context is fixed off the point.** -/
  ctxAt_off : ∀ (H H' : Q → C) (x : Q), AgreeOff x H H' → ctxAt H' (key x) = ctxAt H (key x)
  /-- The bad event at a point, in a context, at its ancestors' answers and its own. -/
  Bad : K → (x : Q) → (Fin (pts.slot x) → C) → C → Prop
  /-- The per-point budget; it may read the point, not the context. -/
  beta : Q → ℕ
  /-- In every context and at every ancestor answers, at most `beta x` answers are bad at `x`. -/
  bad_bound : ∀ (κ : K) (x : Q) (pref : Fin (pts.slot x) → C),
    (univ.filter fun c : C => Bad κ x pref c).card ≤ beta x

namespace CtxGrinding

variable {C Q Out Key K : Type} [Fintype C] [DecidableEq Q] {N L : ℕ}
variable (G : CtxGrinding C Q Out Key K N L)

/-- The adversary's proof on an oracle. -/
def proof (H : Q → C) : Out := (G.adversary.run H).1

/-- Round `k`'s hash input at the proof. -/
def point (H : Q → C) (k : ℕ) : Q := G.hashInput (G.proof H) k

/-- **The verifier's challenges**: the oracle at each round's point. -/
def challenges (H : Q → C) : Fin L → C := fun k => H (G.point H k.val)

/-- **The round-level bad event**: some round's point, in the context of its key and at its
ancestors' answers, is bad at its own answer. -/
def RoundBad (H : Q → C) : Prop :=
  ∃ k : Fin L, G.Bad (G.ctxAt H (G.key (G.point H k.val))) (G.point H k.val)
    (G.pts.chal H (G.point H k.val)) (H (G.point H k.val))

/-- **A charged point**: the adversary asks it, or it is one of the verifier's `L` points. -/
def Charged (x : Q) (H : Q → C) : Prop :=
  x ∈ queried G.adversary H ∨ ∃ k : Fin L, G.point H k.val = x

/-- A proof that does not read `x`'s coordinate. -/
theorem proof_off {x : Q} {H H' : Q → C} (h : AgreeOff x H H') (hx : x ∉ queried G.adversary H) :
    G.proof H' = G.proof H := by
  unfold proof
  rw [run_eq_of_not_mem G.adversary x h hx]

/-- **Being charged does not read the point's coordinate.** -/
theorem charged_off {x : Q} {H H' : Q → C} (h : AgreeOff x H H') (hc : G.Charged x H) :
    G.Charged x H' := by
  by_cases hq : x ∈ queried G.adversary H
  · exact Or.inl ((mem_queried_iff G.adversary x h).mp hq)
  · rcases hc with hq' | ⟨k, hk⟩
    · exact absurd hq' hq
    · refine Or.inr ⟨k, ?_⟩
      unfold point at hk ⊢
      rw [G.proof_off h hq]
      exact hk

/-- The bad event at point `x`: charged, and bad in its context at its ancestors' answers. -/
def slotBad (x : Q) (H : Q → C) (c : C) : Prop :=
  G.Charged x H ∧ G.Bad (G.ctxAt H (G.key x)) x (G.pts.chal H x) c

theorem slotBad_off (x : Q) (H H' : Q → C) (h : AgreeOff x H H') (c : C) (hb : G.slotBad x H c) :
    G.slotBad x H' c := by
  refine ⟨G.charged_off h hb.1, ?_⟩
  rw [G.ctxAt_off H H' x h, ← G.pts.chal_congr h]
  exact hb.2

/-- The point's weight on an oracle: its budget if charged, else nothing. -/
noncomputable def weight (x : Q) (H : Q → C) : ℕ := if G.Charged x H then G.beta x else 0

theorem slotBad_card (x : Q) (H : Q → C) :
    (univ.filter fun c : C => G.slotBad x H c).card ≤ G.weight x H := by
  unfold weight
  by_cases hc : G.Charged x H
  · rw [if_pos hc]
    refine le_trans (Finset.card_le_card ?_) (G.bad_bound (G.ctxAt H (G.key x)) x (G.pts.chal H x))
    intro c hcm
    simp only [mem_filter, mem_univ, true_and] at hcm ⊢
    exact hcm.2
  · rw [if_neg hc]
    refine le_of_eq (Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr ?_))
    intro c _ hb
    exact hc hb.1

/--
**Each oracle's total weight.**  The charged points are the adversary's queries — at most `N`, each
at most `βmax` — and the verifier's `L` points, round `i`'s at most `slotBeta i`.
-/
theorem total_weight_le [Fintype Q] (betaMax : ℕ) (hmax : ∀ x : Q, G.beta x ≤ betaMax)
    (slotBeta : Fin L → ℕ) (hslot : ∀ (out : Out) (i : Fin L), G.beta (G.hashInput out i.val) ≤ slotBeta i)
    (H : Q → C) :
    ∑ x : Q, G.weight x H ≤ N * betaMax + ∑ i, slotBeta i := by
  have hw : ∑ x : Q, G.weight x H = ∑ x ∈ univ.filter (fun x => G.Charged x H), G.beta x := by
    rw [Finset.sum_filter]
    rfl
  set A := (queried G.adversary H).toFinset with hA
  set V := (univ : Finset (Fin L)).image fun i => G.point H i.val with hV
  have hsub : univ.filter (fun x => G.Charged x H) ⊆ A ∪ V := by
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    rcases hx with hq | ⟨k, hk⟩
    · exact mem_union_left _ (List.mem_toFinset.mpr hq)
    · exact mem_union_right _ (mem_image.mpr ⟨k, mem_univ _, hk⟩)
  have hAle : ∑ x ∈ A, G.beta x ≤ N * betaMax := by
    refine le_trans (Finset.sum_le_card_nsmul A G.beta betaMax fun x _ => hmax x) ?_
    rw [smul_eq_mul]
    exact Nat.mul_le_mul_right _
      (le_trans (List.toFinset_card_le _) (queried_length_le G.adversary H))
  have hVle : ∑ x ∈ V, G.beta x ≤ ∑ i, slotBeta i :=
    le_trans (Finset.sum_image_le_of_nonneg fun _ _ => Nat.zero_le _)
      (Finset.sum_le_sum fun i _ => hslot _ i)
  have hunion := Finset.sum_union_inter (s₁ := A) (s₂ := V) (f := G.beta)
  calc ∑ x : Q, G.weight x H = ∑ x ∈ univ.filter (fun x => G.Charged x H), G.beta x := hw
    _ ≤ ∑ x ∈ A ∪ V, G.beta x := Finset.sum_le_sum_of_subset hsub
    _ ≤ ∑ x ∈ A, G.beta x + ∑ x ∈ V, G.beta x := by omega
    _ ≤ N * betaMax + ∑ i, slotBeta i := Nat.add_le_add hAle hVle

/-- **A round-level bad event is a point-level one**, at a charged point: the verifier's. -/
theorem exists_slotBad (H : Q → C) (h : G.RoundBad H) : ∃ x : Q, G.slotBad x H (H x) := by
  obtain ⟨k, hk⟩ := h
  exact ⟨G.point H k.val, Or.inr ⟨k, rfl⟩, hk⟩

/--
**The count.**  Every event `E` that implies a round-level bad event satisfies

```text
#E · |C|  ≤  (N · βmax  +  ∑ k, slotBeta k) · |C|^|Q|,
```

i.e. `Pr[E] ≤ (N · βmax + ∑ k, slotBeta k) / |C|`.  `N` counts the adversary's queries at
prefix-only hash inputs.
-/
theorem card_mul_le [Fintype Q] [DecidableEq C] (betaMax : ℕ) (hmax : ∀ x : Q, G.beta x ≤ betaMax)
    (slotBeta : Fin L → ℕ)
    (hslot : ∀ (out : Out) (i : Fin L), G.beta (G.hashInput out i.val) ≤ slotBeta i)
    (E : (Q → C) → Prop) [DecidablePred E] (hE : ∀ H, E H → G.RoundBad H) :
    (univ.filter E).card * Fintype.card C
      ≤ (N * betaMax + ∑ i, slotBeta i) * Fintype.card C ^ Fintype.card Q := by
  refine le_trans (Nat.mul_le_mul_right _ (Finset.card_le_card (t := univ.filter fun H : Q → C =>
      ∃ x, G.slotBad x H (H x)) ?_))
    (card_exists_coord_le G.slotBad G.slotBad_off G.weight G.slotBad_card _
      (G.total_weight_le betaMax hmax slotBeta hslot))
  intro H hH
  simp only [mem_filter, mem_univ, true_and] at hH ⊢
  exact G.exists_slotBad H (hE H hH)

/-- **The probability form.** -/
theorem ratio_le [Fintype Q] [DecidableEq C] [Nonempty C] (betaMax : ℕ)
    (hmax : ∀ x : Q, G.beta x ≤ betaMax) (slotBeta : Fin L → ℕ)
    (hslot : ∀ (out : Out) (i : Fin L), G.beta (G.hashInput out i.val) ≤ slotBeta i)
    (E : (Q → C) → Prop) [DecidablePred E] (hE : ∀ H, E H → G.RoundBad H) :
    ((univ.filter E).card : ℚ) / (Fintype.card C : ℚ) ^ Fintype.card Q
      ≤ ((N * betaMax + ∑ i, slotBeta i : ℕ) : ℚ) / (Fintype.card C : ℚ) := by
  have hC : (0 : ℚ) < (Fintype.card C : ℚ) := by exact_mod_cast Fintype.card_pos
  have hq : ((univ.filter E).card : ℚ) * (Fintype.card C : ℚ)
      ≤ ((N * betaMax + ∑ i, slotBeta i : ℕ) : ℚ) * (Fintype.card C : ℚ) ^ Fintype.card Q := by
    exact_mod_cast G.card_mul_le betaMax hmax slotBeta hslot E hE
  rw [div_le_div_iff₀ (pow_pos hC _) hC]
  exact hq

end CtxGrinding

/-! ## 5. The sequential round-by-round form -/

/-- Reading a prefix of length `m` as one of length `k`, when `m = k`. -/
theorem prefix_cast {C : Type} (P : (j : ℕ) → (Fin j → C) → Prop) (f : ℕ → C) {m k : ℕ}
    (h : m = k) : P m (fun j : Fin m => f j.val) ↔ P k (fun j : Fin k => f j.val) := by
  subst h
  rfl

/-- …and extended by one answer. -/
theorem prefix_cast_extend {C : Type} (P : (j : ℕ) → (Fin j → C) → Prop) (f : ℕ → C) (c : C)
    {m k : ℕ} (h : m = k) :
    P (m + 1) (extend (fun j : Fin m => f j.val) c) ↔ P (k + 1) (extend (fun j : Fin k => f j.val) c) := by
  subst h
  rfl

/--
**A prefix-only grinding adversary against an `L`-round protocol with a sequential state function.**

`doomed out` is the protocol's state function at a proof; `doomedAt q` the state function at the
messages point `q` carries.  The one link is `hstate`: round `k`'s hash input carries the proof's
messages through round `k`, so the two state functions agree through length `k + 1`.  `hslot` and
`hanc` say round `k`'s point is drawn for round `k` and its ancestors are the earlier rounds' points.
Nothing is assumed about the adversary.
-/
structure Grinding (C : Type) [Fintype C] (Q Out : Type) [DecidableEq Q] (N L : ℕ)
    (VerAccepts : Out → (Fin L → C) → Prop) (Fails : Prop) where
  /-- The adversary: an adaptive program making at most `N` queries. -/
  adversary : Tree Q C Out N
  /-- Round `k`'s hash input, from the proof alone. -/
  hashInput : Out → ℕ → Q
  /-- The rounds and ancestors of the hash inputs. -/
  pts : PrefixPoints Q
  /-- The state function at a proof. -/
  doomed : Out → (j : ℕ) → (Fin j → C) → Prop
  /-- Extraction failing dooms the empty transcript, at every proof. -/
  doomed_start : Fails → ∀ (out : Out) (pt : Fin 0 → C), doomed out 0 pt
  /-- An accepting run is not doomed at the end. -/
  accepts_undoomed : ∀ (out : Out) (ch : Fin L → C), VerAccepts out ch →
    ¬ doomed out L (trunc ch L le_rfl)
  /-- The state function at the messages a point carries. -/
  doomedAt : Q → (j : ℕ) → (Fin j → C) → Prop
  /-- The per-point escape budget. -/
  beta : Q → ℕ
  /-- From a doomed prefix at a point's round, at most `beta q` answers escape. -/
  escape_bound : ∀ (q : Q) (pref : Fin (pts.slot q) → C), doomedAt q (pts.slot q) pref →
    (univ.filter fun c : C => ¬ doomedAt q (pts.slot q + 1) (extend pref c)).card ≤ beta q
  /-- Round `k`'s point is drawn for round `k`. -/
  hslot : ∀ (out : Out) (k : ℕ), k < L → pts.slot (hashInput out k) = k
  /-- Its ancestors are the earlier rounds' points. -/
  hanc : ∀ (out : Out) (k j : ℕ), j < k → k < L → pts.anc (hashInput out k) j = hashInput out j
  /-- **The link**: at round `k`'s point the two state functions agree through length `k + 1`. -/
  hstate : ∀ (out : Out) (k : ℕ), k < L → ∀ j, j ≤ k + 1 → ∀ p : Fin j → C,
    doomedAt (hashInput out k) j p ↔ doomed out j p

namespace Grinding

variable {C Q Out : Type} [Fintype C] [DecidableEq Q] {N L : ℕ}
variable {VerAccepts : Out → (Fin L → C) → Prop} {Fails : Prop}
variable (G : Grinding C Q Out N L VerAccepts Fails)

/-- The count with no context: the bad event at a point is "doomed at its ancestors' answers,
escaped at its own". -/
def toCtx : CtxGrinding C Q Out Unit Unit N L where
  adversary := G.adversary
  hashInput := G.hashInput
  pts := G.pts
  key _ := ()
  ctxAt _ _ := ()
  ctxAt_off _ _ _ _ := rfl
  Bad _ x pref c := G.doomedAt x (G.pts.slot x) pref ∧
    ¬ G.doomedAt x (G.pts.slot x + 1) (extend pref c)
  beta := G.beta
  bad_bound _ x pref := by
    by_cases hd : G.doomedAt x (G.pts.slot x) pref
    · refine le_trans (Finset.card_le_card ?_) (G.escape_bound x pref hd)
      intro c hc
      simp only [mem_filter, mem_univ, true_and] at hc ⊢
      exact hc.2
    · refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
      intro c hc
      simp only [mem_filter, mem_univ, true_and] at hc
      exact absurd hc.1 hd

/-- The verifier's decision at the adversary's proof and the oracle's answers at its points. -/
def Accepts (H : Q → C) : Prop := VerAccepts (G.toCtx.proof H) (G.toCtx.challenges H)

/-- The state function at one proof, as a `Bcs.Rbr` with the trivial budget; only its
`exists_escape` is used. -/
def seqRbr (out : Out) : Rbr C L (VerAccepts out) Fails where
  doomed := G.doomed out
  beta _ := Fintype.card C
  doomed_start hf pt := G.doomed_start hf out pt
  doom_preserved _ _ _ := card_le_univ _
  accepts_undoomed ch hacc := G.accepts_undoomed out ch hacc

/--
**The chain.**  On an accepting oracle where extraction failed, some round's point, judged at its
ancestors' answers — each read at its own coordinate — is doomed, and its own answer escapes.

`Rbr.exists_escape` finds the round `k` at which the proof's state function, at the verifier's
challenges, is shed; at round `k`'s point the ancestors' answers *are* the earlier challenges
(`hanc`) and the point's state function is the proof's (`hstate`).
-/
theorem roundBad_of_accepts (H : Q → C) (hacc : G.Accepts H) (hfail : Fails) :
    G.toCtx.RoundBad H := by
  set out := G.toCtx.proof H with hout
  set ch := G.toCtx.challenges H with hch
  obtain ⟨k, hd, he⟩ := (G.seqRbr out).exists_escape ch
    (G.doomed_start hfail out _) (G.accepts_undoomed out ch hacc)
  refine ⟨k, ?_⟩
  set p := G.hashInput out k.val with hp
  have hs : G.pts.slot p = k.val := G.hslot out k.val k.isLt
  have hpre : (fun j : Fin k.val => H (G.pts.anc p j.val)) = Sumcheck.extract_prefix ch k := by
    funext j
    show H (G.pts.anc p j.val) = H (G.hashInput out j.val)
    rw [hp, G.hanc out k.val j.val j.isLt k.isLt]
  have hck : H p = ch k := rfl
  show G.doomedAt p (G.pts.slot p) (fun j => H (G.pts.anc p j.val)) ∧
    ¬ G.doomedAt p (G.pts.slot p + 1) (extend (fun j => H (G.pts.anc p j.val)) (H p))
  rw [prefix_cast (G.doomedAt p) (fun j => H (G.pts.anc p j)) hs,
    prefix_cast_extend (G.doomedAt p) (fun j => H (G.pts.anc p j)) (H p) hs, hpre, hck,
    G.hstate out k.val k.isLt k.val (Nat.le_succ _),
    G.hstate out k.val k.isLt (k.val + 1) le_rfl]
  exact ⟨hd, he⟩

/--
**The sequential count**, over the total oracle:

```text
#{ H : the verifier accepts the recomputed challenges  ∧  extraction fails } · |C|
    ≤  (N · βmax  +  ∑ k, slotBeta k) · |C|^|Q|
```
-/
theorem card_mul_le [Fintype Q] [DecidableEq C] (betaMax : ℕ) (hmax : ∀ x : Q, G.beta x ≤ betaMax)
    (slotBeta : Fin L → ℕ)
    (hslot : ∀ (out : Out) (i : Fin L), G.beta (G.hashInput out i.val) ≤ slotBeta i)
    (E : (Q → C) → Prop) [DecidablePred E] (hE : ∀ H, E H → G.Accepts H) (hfail : Fails) :
    (univ.filter E).card * Fintype.card C
      ≤ (N * betaMax + ∑ i, slotBeta i) * Fintype.card C ^ Fintype.card Q :=
  G.toCtx.card_mul_le betaMax hmax slotBeta hslot E fun H hH =>
    G.roundBad_of_accepts H (hE H hH) hfail

/--
**The sequential bound**:

```text
Pr_H[ the verifier accepts the recomputed challenges  ∧  extraction fails ]
    ≤  (N · βmax  +  ∑ k, slotBeta k) / |C|.
```

The adversary's `N` prefix-only queries pay the worst budget, the verifier's `L` points their own
round's.  At `N = 0` this is the sequential round-by-round sum.
-/
theorem ratio_le [Fintype Q] [DecidableEq C] [Nonempty C] (betaMax : ℕ)
    (hmax : ∀ x : Q, G.beta x ≤ betaMax) (slotBeta : Fin L → ℕ)
    (hslot : ∀ (out : Out) (i : Fin L), G.beta (G.hashInput out i.val) ≤ slotBeta i) :
    ((univ.filter fun H : Q → C => G.Accepts H ∧ Fails).card : ℚ)
        / (Fintype.card C : ℚ) ^ Fintype.card Q
      ≤ ((N * betaMax + ∑ i, slotBeta i : ℕ) : ℚ) / (Fintype.card C : ℚ) := by
  by_cases hfail : Fails
  · exact G.toCtx.ratio_le betaMax hmax slotBeta hslot _ fun H hH =>
      G.roundBad_of_accepts H hH.1 hfail
  · rw [Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun H _ hH => hfail hH.2)]
    simp only [Nat.cast_zero, zero_div]
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/--
**From any family of `Bcs.Rbr`s.**  `R ms` is the protocol's sequential round-by-round analysis at
the message reading `ms`; a proof carries `msgsOf out` and a point `msgsAt q`.  `hstate` says round
`k`'s point carries the proof's messages through round `k`, as far as the state function reads
them.  Every `Bcs.ClaimChain` gives such a family through `ClaimChain.toRbr`.
-/
def ofRbr {Msgs : Type} {Acc : Msgs → (Fin L → C) → Prop} (R : ∀ ms : Msgs, Rbr C L (Acc ms) Fails)
    (adversary : Tree Q C Out N) (hashInput : Out → ℕ → Q) (pts : PrefixPoints Q)
    (msgsOf : Out → Msgs) (msgsAt : Q → Msgs) (hslotlt : ∀ q : Q, pts.slot q < L)
    (hslot : ∀ (out : Out) (k : ℕ), k < L → pts.slot (hashInput out k) = k)
    (hanc : ∀ (out : Out) (k j : ℕ), j < k → k < L → pts.anc (hashInput out k) j = hashInput out j)
    (hstate : ∀ (out : Out) (k : ℕ), k < L → ∀ j, j ≤ k + 1 → ∀ p : Fin j → C,
      (R (msgsAt (hashInput out k))).doomed j p ↔ (R (msgsOf out)).doomed j p) :
    Grinding C Q Out N L (fun out => Acc (msgsOf out)) Fails where
  adversary := adversary
  hashInput := hashInput
  pts := pts
  doomed out := (R (msgsOf out)).doomed
  doomed_start hf out pt := (R (msgsOf out)).doomed_start hf pt
  accepts_undoomed out ch hacc := (R (msgsOf out)).accepts_undoomed ch hacc
  doomedAt q := (R (msgsAt q)).doomed
  beta q := (R (msgsAt q)).beta ⟨pts.slot q, hslotlt q⟩
  escape_bound q pref hd := (R (msgsAt q)).doom_preserved ⟨pts.slot q, hslotlt q⟩ pref hd
  hslot := hslot
  hanc := hanc
  hstate := hstate

end Grinding

end Bcs.TotalOracle
