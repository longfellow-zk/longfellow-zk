import Bcs.FiatShamir
import Merkle.TreeCompose
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Action.Defs

/-!
# Fiat–Shamir over an `L`-round transcript, against a grinding adversary

`Bcs.Grinding` turns a grinding adversary into a `Bcs.RbrCore`, but it takes the deterministic
content — `chain`, "an accepting failing run queried a doomed point and got an escaping answer" — as
a field.  This file proves `chain` for a protocol of `L` challenge rounds whose verifier
**recomputes every challenge**, starting from the protocol's ordinary *sequential* state function.

## The execution

The adversary is an adaptive program `adversary : Tree Q C Out N` against the challenge oracle.  It
makes at most `N` queries at whatever points it likes and outputs a proof `out`.  The verifier then
recomputes the `L` challenges in order: round `k`'s challenge is the oracle's answer at the hash
input `hashInput out k cp`, where `cp` holds the raw answers of rounds `< k`.  `execution` is the two
phases glued with `Tree.bind`, so it is one tree of fuel `L + N` on one lazy-sampling tape, and every
challenge the verifier uses is the first-occurrence answer at its point.  This is
`Bcs.RecomputedGrinding.verifierTree`'s pattern at `L` rounds instead of two.

## The state function is per proof, the bad event is per point

`doomed out j cp` is the sequential state function of the protocol run with the proof's messages:
an ordinary round-by-round state function, at a fixed proof.  The bad event the count needs is
local to a query point: `DoomedQuery q` and `Escapes q c`.  The one obligation linking them is
`link`: at a verifier hash input, the sequential doom-then-escape step **is** the point's bad event.
That is what makes Fiat–Shamir work for a round-by-round protocol: a hash input is a transcript
prefix, so it carries everything the state function reads.

Because the bad event reads the query point alone, the order in which the adversary asked the
points does not matter.  An adversary that guessed round `k-1`'s answer and asked round `k`'s point
first has asked the very point the verifier recomputes, at the slot where that point's answer
lives.  No reverse-order event has to be charged separately, unlike `Bcs.RecomputedGrinding`'s
`EarlySecond`, whose *graded* bad event spans two points.

## What is proved

* `lazyRun_rounds` — the recomputation's output and its exact trace;
* `TranscriptGrinding.exists_bad_slot` — the chain: an accepting failing tape has a slot whose
  query is a doomed point and whose answer escapes;
* `TranscriptGrinding.toGrinding` — so the adversary is a `Bcs.Grinding`, hence a `Bcs.RbrCore`;
  `ratio_le_uniform` is `(L + N) · βmax / |C|` on a tape of length `L + N`;
* `weighted_tape_card_le` — the per-slot count with a **prefix-dependent** budget, which `RbrCore`
  (one number per slot) cannot express;
* `TranscriptGrinding.ratio_le_weighted` — the sharper bound
  `(N · βmax + ∑ k, slotBeta k) / |C|`: the adversary's `N` own queries pay the worst point's
  budget, and the verifier's `L` recomputations pay their own round's budget.  At `N = 0` this is
  the sequential round-by-round sum.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bcs

open Finset Merkle.RandomOracle
open scoped Classical

/-! ## The verifier's recomputation -/

namespace Recompute

variable {Q C : Type} [DecidableEq Q]

/-- The verifier's recomputation of rounds `k, …, k + r - 1`: ask round `k`'s hash input at the
answers so far, record the answer at index `k`, and continue.  The answers are carried as a total
function `ℕ → C`, so no prefix type has to be cast; `vq k` is handed only the first `k`. -/
def rounds (vq : (k : ℕ) → (Fin k → C) → Q) : (r k : ℕ) → (ℕ → C) → Tree Q C (ℕ → C) r
  | 0, _, acc => .done acc
  | r + 1, k, acc => .query (vq k fun i => acc i.val) fun c =>
      rounds vq r (k + 1) (Function.update acc k c)

/--
**The recomputation, lazily.**  Its output agrees with the starting answers below `k`, and its trace
is exactly one entry per round, `(vq i (out ↾ i), out i)`, for `i = k, …, k + r - 1`.

So round `i`'s challenge is the answer recorded at round `i`'s hash input, and that input is formed
from the *final* answers of the earlier rounds.
-/
theorem lazyRun_rounds {T : ℕ} (tape : Fin T → C) (dflt : C) (vq : (k : ℕ) → (Fin k → C) → Q) :
    ∀ (r k : ℕ) (acc : ℕ → C) (seen : List Q),
      (∀ i, i < k → (lazyRun tape dflt (rounds vq r k acc) seen).1 i = acc i) ∧
      (lazyRun tape dflt (rounds vq r k acc) seen).2.2 =
        (List.range' k r).map fun i =>
          (vq i fun j => (lazyRun tape dflt (rounds vq r k acc) seen).1 j.val,
            (lazyRun tape dflt (rounds vq r k acc) seen).1 i)
  | 0, k, acc, seen => by
      refine ⟨fun _ _ => rfl, ?_⟩
      simp [rounds]
  | r + 1, k, acc, seen => by
      rw [rounds, lazyRun_query]
      dsimp only
      generalize (if (vq k fun i => acc i.val) ∈ seen then seen
        else seen ++ [vq k fun i => acc i.val]) = seen'
      generalize tapeAt tape dflt (seen'.idxOf (vq k fun i => acc i.val)) = y
      obtain ⟨h1, h2⟩ := lazyRun_rounds tape dflt vq r (k + 1) (Function.update acc k y) seen'
      set out := lazyRun tape dflt (rounds vq r (k + 1) (Function.update acc k y)) seen'
      have hbelow : ∀ i, i < k → out.1 i = acc i := by
        intro i hi
        rw [h1 i (by omega), Function.update_of_ne (by omega)]
      refine ⟨hbelow, ?_⟩
      rw [List.range'_succ, List.map_cons, h2]
      congr 2
      · congr 1
        funext j
        exact (hbelow j.val j.isLt).symm
      · rw [h1 k (by omega), Function.update_self]

end Recompute

/-! ## The execution: search, then recompute -/

section Execution

variable {Q C Out : Type} [DecidableEq Q] {N L T : ℕ}

/-- The adversary's search, then the verifier's recomputation of all `L` rounds at its output, as
one tree on one lazy-sampling tape.  The output is the proof and the recomputed answers. -/
def execution (adversary : Tree Q C Out N) (hashInput : Out → (k : ℕ) → (Fin k → C) → Q)
    (dflt : C) (L : ℕ) : Tree Q C (Out × (ℕ → C)) (L + N) :=
  adversary.bind fun out =>
    (Recompute.rounds (hashInput out) L 0 fun _ => dflt).map fun acc => (out, acc)

/-- **The execution, lazily**: the search's run, then the recomputation's run from the search's
seen-list, with the traces concatenated. -/
theorem lazyRun_execution (tape : Fin T → C) (dflt : C) (adversary : Tree Q C Out N)
    (hashInput : Out → (k : ℕ) → (Fin k → C) → Q) :
    lazyRun tape dflt (execution adversary hashInput dflt L) [] =
      (((lazyRun tape dflt adversary []).1,
          (lazyRun tape dflt (Recompute.rounds (hashInput (lazyRun tape dflt adversary []).1) L 0
            fun _ => dflt) (lazyRun tape dflt adversary []).2.1).1),
        (lazyRun tape dflt (Recompute.rounds (hashInput (lazyRun tape dflt adversary []).1) L 0
            fun _ => dflt) (lazyRun tape dflt adversary []).2.1).2.1,
        (lazyRun tape dflt adversary []).2.2 ++
          (lazyRun tape dflt (Recompute.rounds (hashInput (lazyRun tape dflt adversary []).1) L 0
            fun _ => dflt) (lazyRun tape dflt adversary []).2.1).2.2) := by
  rw [execution, lazyRun_bind, lazyRun_map]

end Execution

/-! ## The structure -/

/--
**A grinding adversary against an `L`-round protocol whose verifier recomputes its challenges.**

`VerAccepts out ch` is the verifier's decision on proof `out` at challenge answers `ch`.  The
adversary and the hash inputs are data; the rest is the protocol's round-by-round content:

* `doomed`, `doomed_start`, `accepts_undoomed` — the sequential state function at each proof,
  with the two classical obligations;
* `DoomedQuery`, `Escapes`, `beta`, `escape_bound` — the bad event at a query point and its
  per-point budget;
* `link` — at the verifier's own hash input, a sequential escape is the point's bad event.

Nothing about the adversary is assumed: `link` and `escape_bound` quantify over all proofs, prefixes
and points.
-/
structure TranscriptGrinding (C : Type) [Fintype C] (Q Out : Type) [DecidableEq Q] (N L : ℕ)
    (VerAccepts : Out → (Fin L → C) → Prop) (Fails : Prop) where
  /-- The adversary's search: an adaptive program making at most `N` queries. -/
  adversary : Tree Q C Out N
  /-- The answer an out-of-range slot would give; never read once the tape fits. -/
  dflt : C
  /-- Round `k`'s hash input: the transcript prefix the verifier hashes, read from the proof and the
  raw answers of the earlier rounds. -/
  hashInput : Out → (k : ℕ) → (Fin k → C) → Q
  /-- The sequential state function at a proof. -/
  doomed : Out → (j : ℕ) → (Fin j → C) → Prop
  /-- Extraction failing dooms the empty transcript, at every proof. -/
  doomed_start : Fails → ∀ (out : Out) (pt : Fin 0 → C), doomed out 0 pt
  /-- An accepting run is not doomed at the end. -/
  accepts_undoomed : ∀ (out : Out) (ch : Fin L → C), VerAccepts out ch →
    ¬ doomed out L (trunc ch L le_rfl)
  /-- The partial transcript at this point is already lost. -/
  DoomedQuery : Q → Prop
  /-- The answers at this point that recover it. -/
  Escapes : Q → C → Prop
  /-- The per-point escape budget. -/
  beta : Q → ℕ
  /-- From a lost point, at most `beta q` answers recover. -/
  escape_bound : ∀ q : Q, DoomedQuery q → (univ.filter fun c : C => Escapes q c).card ≤ beta q
  /-- **The link.**  At round `k`'s hash input, a sequential escape is the point's bad event. -/
  link : ∀ (out : Out) (k : ℕ) (cp : Fin k → C) (c : C), k < L →
    doomed out k cp → ¬ doomed out (k + 1) (extend cp c) →
      DoomedQuery (hashInput out k cp) ∧ Escapes (hashInput out k cp) c

namespace TranscriptGrinding

variable {C Q Out : Type} [Fintype C] [DecidableEq Q] {N L T : ℕ}
variable {VerAccepts : Out → (Fin L → C) → Prop} {Fails : Prop}
variable (G : TranscriptGrinding C Q Out N L VerAccepts Fails)

/-- The whole execution. -/
def exec : Tree Q C (Out × (ℕ → C)) (L + N) := execution G.adversary G.hashInput G.dflt L

/-- The proof and the recomputed answers on a tape. -/
def output (tape : Fin T → C) : Out × (ℕ → C) := (lazyRun tape G.dflt G.exec []).1

/-- The recomputed challenge answers, as the verifier reads them. -/
def challenges (tape : Fin T → C) : Fin L → C := fun i => (G.output tape).2 i.val

/-- **The real acceptance event**: the verifier's decision at the proof and the recomputed
challenges. -/
def Accepts (tape : Fin T → C) : Prop := VerAccepts (G.output tape).1 (G.challenges tape)

/-- The sequential state function at one proof, as a `Bcs.Rbr` with the trivial budget.  Only its
`exists_escape` is used. -/
def seqRbr (out : Out) : Rbr C L (VerAccepts out) Fails where
  doomed := G.doomed out
  beta _ := Fintype.card C
  doomed_start hf pt := G.doomed_start hf out pt
  doom_preserved _ _ _ := card_le_univ _
  accepts_undoomed ch hacc := G.accepts_undoomed out ch hacc

/-- Every verifier hash input is recorded, with its recomputed answer, in the execution's trace. -/
theorem verifier_entry_mem (tape : Fin T → C) (k : ℕ) (hk : k < L) :
    (G.hashInput (G.output tape).1 k (fun j : Fin k => (G.output tape).2 j.val),
        (G.output tape).2 k) ∈ (lazyRun tape G.dflt G.exec []).2.2 := by
  have hrun := lazyRun_execution (L := L) tape G.dflt G.adversary G.hashInput
  have hout : G.output tape = ((lazyRun tape G.dflt G.adversary []).1,
      (lazyRun tape G.dflt
        (Recompute.rounds (G.hashInput (lazyRun tape G.dflt G.adversary []).1) L 0
          fun _ => G.dflt) (lazyRun tape G.dflt G.adversary []).2.1).1) := by
    rw [output, exec, hrun]
  rw [exec, hrun, hout]
  refine List.mem_append_right _ ?_
  rw [(Recompute.lazyRun_rounds tape G.dflt _ L 0 _ _).2]
  exact List.mem_map.mpr ⟨k, List.mem_range'.mpr ⟨k, by omega, by omega⟩, rfl⟩

/--
**The chain.**  On an accepting tape where extraction failed, some slot's query is a doomed point
and the tape's answer there escapes.

`Rbr.exists_escape` finds the round `k` at which the sequential state function, at the adversary's
own proof and the recomputed challenges, is shed; `link` turns that into the bad event at round
`k`'s hash input; and `Merkle.RandomOracle.lazyRun_trace_slot` places that input at a tape slot
whose answer *is* round `k`'s challenge, because the verifier read it from the oracle.
-/
theorem exists_bad_slot (hfuel : L + N ≤ T) (tape : Fin T → C) (hacc : G.Accepts tape)
    (hfail : Fails) :
    ∃ (j : Fin T) (q : Q), (lazyRun tape G.dflt G.exec []).2.1[j.val]? = some q ∧
      G.DoomedQuery q ∧ G.Escapes q (tape j) := by
  classical
  set out := (G.output tape).1
  set ch := G.challenges tape
  obtain ⟨k, hdoom, hesc⟩ := (G.seqRbr out).exists_escape ch
    (G.doomed_start hfail out _) (G.accepts_undoomed out ch hacc)
  obtain ⟨hdq, hesq⟩ := G.link out k.val (Sumcheck.extract_prefix ch k) (ch k) k.isLt hdoom hesc
  -- the verifier's round-`k` entry, and where it sits on the tape
  have hmem := G.verifier_entry_mem tape k.val k.isLt
  obtain ⟨hseen, hval⟩ := lazyRun_trace_slot tape G.dflt G.exec [] _ hmem
  set q := G.hashInput out k.val (fun j : Fin k.val => (G.output tape).2 j.val)
  have hlt : (lazyRun tape G.dflt G.exec []).2.1.idxOf q < T := by
    have h := lazyRun_slot_lt tape G.dflt G.exec [] q hseen
    simp only [List.length_nil, Nat.zero_add] at h
    omega
  refine ⟨⟨_, hlt⟩, q, List.getElem?_idxOf hseen, hdq, ?_⟩
  have htape : tape ⟨_, hlt⟩ = ch k := by
    show tape ⟨_, hlt⟩ = (G.output tape).2 k.val
    have hval' : (G.output tape).2 k.val
        = tapeAt tape G.dflt ((lazyRun tape G.dflt G.exec []).2.1.idxOf q) := hval
    rw [hval', tapeAt, dif_pos hlt]
  rw [htape]
  exact hesq

/-! ### The uniform bound, through `Bcs.Grinding` -/

/--
**The adversary is a `Bcs.Grinding`**, hence (`Grinding.toRbrCore`) a `Bcs.RbrCore` whose bad event
at slot `j` is "the query made at slot `j` is a doomed point and its answer escapes".  The budget is
uniform: the worst point's.
-/
noncomputable def toGrinding (betaMax : ℕ) (hmax : ∀ q : Q, G.beta q ≤ betaMax)
    (hfuel : L + N ≤ T) : Grinding C Q (Out × (ℕ → C)) (L + N) T G.Accepts Fails where
  adversary := G.exec
  dflt := G.dflt
  DoomedQuery := G.DoomedQuery
  Escapes := G.Escapes
  beta := betaMax
  escape_bound q hq := le_trans (G.escape_bound q hq) (hmax q)
  chain tape hacc hfail := G.exists_bad_slot hfuel tape hacc hfail

/-- **The uniform grinding bound**: `T · βmax / |C|` over a tape of length `T ≥ L + N`. -/
theorem ratio_le_uniform [DecidableEq C] [Nonempty C] (betaMax : ℕ)
    (hmax : ∀ q : Q, G.beta q ≤ betaMax) (hfuel : L + N ≤ T) (hT : 1 ≤ T) :
    ((univ.filter fun tape : Fin T → C => G.Accepts tape ∧ Fails).card : ℚ)
        / (Fintype.card C : ℚ) ^ T
      ≤ ((T * betaMax : ℕ) : ℚ) / (Fintype.card C : ℚ) :=
  (G.toGrinding betaMax hmax hfuel).grinding_ratio_le hT

end TranscriptGrinding

/-! ## A per-slot count with a prefix-dependent budget

`RbrCore` carries one budget per slot.  Under grinding the point a slot holds is a function of the
prefix, and so is its budget: a slot holding a sumcheck point pays `2/|F|`, one holding a Ligero
point pays a cover ratio.  `weighted_tape_card_le` is `Sumcheck.tape_bad_card_le` with the budget
allowed to read the prefix, and the price of that is that the total is bounded *per tape*
(`htotal`) rather than summed over slots up front.
-/

section Weighted

variable {C : Type} [Fintype C] [DecidableEq C]

/-- Summing a function of the slot-`i` prefix over all tapes: every prefix extends to
`|C|^(T-1-i) · |C|` tapes. -/
theorem sum_tape_prefix {T : ℕ} (i : Fin T) (f : (Fin i.val → C) → ℕ) :
    ∑ tape : Fin T → C, f (Sumcheck.extract_prefix tape i)
      = Fintype.card C ^ (T - 1 - i.val) * Fintype.card C * ∑ pref : Fin i.val → C, f pref := by
  classical
  rw [← Finset.sum_fiberwise univ
    (fun tape : Fin T → C => (Sumcheck.extract_prefix tape i, tape i))]
  have hfib : ∀ y : (Fin i.val → C) × C,
      ∑ tape ∈ univ.filter (fun tape : Fin T → C =>
          (Sumcheck.extract_prefix tape i, tape i) = y), f (Sumcheck.extract_prefix tape i)
        = Fintype.card C ^ (T - 1 - i.val) * f y.1 := by
    intro y
    rw [Finset.sum_congr rfl (g := fun _ => f y.1) (by
      intro tape htape
      simp only [mem_filter, mem_univ, true_and] at htape
      rw [← htape])]
    rw [sum_const, smul_eq_mul]
    congr 1
    have h := Sumcheck.card_fiber_eq T i y
    convert h using 2
    ext tape
    simp [Prod.ext_iff]
  rw [Finset.sum_congr rfl fun y _ => hfib y, ← Finset.mul_sum, Fintype.sum_prod_type]
  simp only [sum_const, card_univ, smul_eq_mul]
  rw [← Finset.mul_sum, mul_assoc]

/-- **One slot, with a prefix-dependent budget.**  The bad tapes at slot `i`, times `|C|`, are at
most the total budget over tapes. -/
theorem slot_weighted_card_le {T : ℕ} (i : Fin T) (P : (Fin i.val → C) → C → Prop)
    (wt : (Fin i.val → C) → ℕ)
    (hlocal : ∀ pref, (univ.filter fun c : C => P pref c).card ≤ wt pref) :
    (univ.filter fun tape : Fin T → C => P (Sumcheck.extract_prefix tape i) (tape i)).card
        * Fintype.card C
      ≤ ∑ tape : Fin T → C, wt (Sumcheck.extract_prefix tape i) := by
  classical
  rw [sum_tape_prefix]
  have hcount := Sumcheck.card_filter_prefix_r T i P
  have hpairs : (univ.filter fun pr : (Fin i.val → C) × C => P pr.1 pr.2).card
      ≤ ∑ pref, wt pref := by
    rw [card_filter_prod_fst]
    exact Finset.sum_le_sum fun pref _ => hlocal pref
  calc (univ.filter fun tape : Fin T → C => P (Sumcheck.extract_prefix tape i) (tape i)).card
        * Fintype.card C
      = (univ.filter fun pr : (Fin i.val → C) × C => P pr.1 pr.2).card
          * Fintype.card C ^ (T - 1 - i.val) * Fintype.card C := by
        rw [← hcount]
    _ ≤ (∑ pref, wt pref) * Fintype.card C ^ (T - 1 - i.val) * Fintype.card C := by gcongr
    _ = Fintype.card C ^ (T - 1 - i.val) * Fintype.card C * ∑ pref, wt pref := by ring

/--
**Every slot, with a prefix-dependent budget.**  If slot `i`'s bad answers at prefix `pref` are at
most `wt i pref`, and every tape's slot budgets sum to at most `B`, then

```
#{tapes bad at some slot} · |C|  ≤  B · |C|^T,     i.e.   Pr[bad somewhere] ≤ B / |C|.
```
-/
theorem weighted_tape_card_le {T : ℕ} (P : ∀ i : Fin T, (Fin i.val → C) → C → Prop)
    (wt : ∀ i : Fin T, (Fin i.val → C) → ℕ)
    (hlocal : ∀ i pref, (univ.filter fun c : C => P i pref c).card ≤ wt i pref) (B : ℕ)
    (htotal : ∀ tape : Fin T → C, ∑ i, wt i (Sumcheck.extract_prefix tape i) ≤ B) :
    (univ.filter fun tape : Fin T → C =>
        ∃ i, P i (Sumcheck.extract_prefix tape i) (tape i)).card * Fintype.card C
      ≤ B * Fintype.card C ^ T := by
  classical
  have hunion : (univ.filter fun tape : Fin T → C =>
        ∃ i, P i (Sumcheck.extract_prefix tape i) (tape i))
      = univ.biUnion fun i : Fin T =>
          univ.filter fun tape : Fin T → C => P i (Sumcheck.extract_prefix tape i) (tape i) := by
    ext tape
    simp
  rw [hunion]
  calc (univ.biUnion fun i : Fin T =>
          univ.filter fun tape : Fin T → C =>
            P i (Sumcheck.extract_prefix tape i) (tape i)).card * Fintype.card C
      ≤ (∑ i : Fin T, (univ.filter fun tape : Fin T → C =>
          P i (Sumcheck.extract_prefix tape i) (tape i)).card) * Fintype.card C :=
        Nat.mul_le_mul_right _ card_biUnion_le
    _ = ∑ i : Fin T, (univ.filter fun tape : Fin T → C =>
          P i (Sumcheck.extract_prefix tape i) (tape i)).card * Fintype.card C := by
        rw [Finset.sum_mul]
    _ ≤ ∑ i : Fin T, ∑ tape : Fin T → C, wt i (Sumcheck.extract_prefix tape i) :=
        Finset.sum_le_sum fun i _ => slot_weighted_card_le i (P i) (wt i) (hlocal i)
    _ = ∑ tape : Fin T → C, ∑ i : Fin T, wt i (Sumcheck.extract_prefix tape i) :=
        Finset.sum_comm
    _ ≤ ∑ _tape : Fin T → C, B := Finset.sum_le_sum fun tape _ => htotal tape
    _ = B * Fintype.card C ^ T := by
        rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, smul_eq_mul, mul_comm]

/-- **The weighted count as a probability**: `B / |C|`. -/
theorem weighted_tape_ratio_le [Nonempty C] {T : ℕ} (E : (Fin T → C) → Prop)
    [DecidablePred E] (P : ∀ i : Fin T, (Fin i.val → C) → C → Prop)
    (hE : ∀ tape, E tape → ∃ i, P i (Sumcheck.extract_prefix tape i) (tape i))
    (wt : ∀ i : Fin T, (Fin i.val → C) → ℕ)
    (hlocal : ∀ i pref, (univ.filter fun c : C => P i pref c).card ≤ wt i pref) (B : ℕ)
    (htotal : ∀ tape : Fin T → C, ∑ i, wt i (Sumcheck.extract_prefix tape i) ≤ B) :
    ((univ.filter E).card : ℚ) / (Fintype.card C : ℚ) ^ T ≤ (B : ℚ) / (Fintype.card C : ℚ) := by
  classical
  have hC : (0 : ℚ) < (Fintype.card C : ℚ) := by exact_mod_cast Fintype.card_pos
  have hsub : (univ.filter E).card ≤ (univ.filter fun tape : Fin T → C =>
      ∃ i, P i (Sumcheck.extract_prefix tape i) (tape i)).card := by
    apply Finset.card_le_card
    intro tape htape
    simp only [mem_filter, mem_univ, true_and] at htape ⊢
    exact hE tape htape
  have hnat := le_trans (Nat.mul_le_mul_right (Fintype.card C) hsub)
    (weighted_tape_card_le P wt hlocal B htotal)
  have hq : ((univ.filter E).card : ℚ) * (Fintype.card C : ℚ)
      ≤ (B : ℚ) * (Fintype.card C : ℚ) ^ T := by exact_mod_cast hnat
  rw [div_le_div_iff₀ (pow_pos hC T) hC]
  exact hq

end Weighted

/-! ## The sharper grinding bound: each slot pays its own point's budget -/

section ListSum

variable {Q : Type}

/-- A slot sum over a list that fits in the tape is the list's sum. -/
theorem sum_slots_eq_list_sum {T : ℕ} (l : List Q) (hl : l.length ≤ T) (b : Q → ℕ) :
    ∑ j : Fin T, (l[j.val]?).elim 0 b = (l.map b).sum := by
  rw [Fin.sum_univ_eq_sum_range (fun j => (l[j]?).elim 0 b) T,
    ← Finset.sum_range_add_sum_Ico _ hl]
  have htail : ∑ j ∈ Finset.Ico l.length T, (l[j]?).elim 0 b = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [List.getElem?_eq_none (Finset.mem_Ico.mp hj).1]
    rfl
  rw [htail, add_zero, ← Fin.sum_univ_eq_sum_range (fun j => (l[j]?).elim 0 b) l.length]
  have hhead : ∀ j : Fin l.length, (l[j.val]?).elim 0 b = b l[j] := by
    intro j
    rw [List.getElem?_eq_getElem j.isLt]
    rfl
  rw [Finset.sum_congr rfl fun j _ => hhead j, ← List.sum_ofFn]
  congr 1
  conv_rhs => rw [← List.ofFn_getElem (xs := l), List.map_ofFn]
  rfl

end ListSum

namespace TranscriptGrinding

variable {C Q Out : Type} [Fintype C] [DecidableEq Q] {N L T : ℕ}
variable {VerAccepts : Out → (Fin L → C) → Prop} {Fails : Prop}
variable (G : TranscriptGrinding C Q Out N L VerAccepts Fails)

/-- The budget of the point at slot `j`, read off the prefix; `0` if the execution makes no `j`-th
distinct query. -/
noncomputable def slotWeight (j : Fin T) (pref : Fin j.val → C) : ℕ :=
  (slotQuery (T := T) G.dflt G.exec pref).elim 0 G.beta

/-- The bad event at slot `j`, read off the prefix and the slot's answer. -/
def slotBad (j : Fin T) (pref : Fin j.val → C) (c : C) : Prop :=
  ∃ q : Q, slotQuery (T := T) G.dflt G.exec pref = some q ∧ G.DoomedQuery q ∧ G.Escapes q c

theorem slotBad_card (j : Fin T) (pref : Fin j.val → C) :
    (univ.filter fun c : C => G.slotBad j pref c).card ≤ G.slotWeight j pref := by
  classical
  unfold slotWeight
  rcases hq : slotQuery (T := T) G.dflt G.exec pref with _ | q
  · refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
    intro c hc
    simp only [mem_filter, mem_univ, true_and, slotBad] at hc
    rw [hq] at hc
    obtain ⟨_, h, -⟩ := hc
    cases h
  · by_cases hdoom : G.DoomedQuery q
    · refine le_trans (Finset.card_le_card (t := univ.filter fun c : C => G.Escapes q c) ?_)
        (G.escape_bound q hdoom)
      intro c hc
      simp only [mem_filter, mem_univ, true_and, slotBad] at hc ⊢
      rw [hq] at hc
      obtain ⟨q', hq', -, hesc⟩ := hc
      cases hq'
      exact hesc
    · refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
      intro c hc
      simp only [mem_filter, mem_univ, true_and, slotBad] at hc
      rw [hq] at hc
      obtain ⟨q', hq', hd, -⟩ := hc
      cases hq'
      exact absurd hd hdoom

/-- `slotQuery` at a slot of a real tape is that slot's entry in the run's seen-list. -/
theorem slotQuery_at (tape : Fin T → C) (j : Fin T) :
    slotQuery (T := T) G.dflt G.exec (Sumcheck.extract_prefix tape j)
      = (lazyRun tape G.dflt G.exec []).2.1[j.val]? := by
  rw [show Sumcheck.extract_prefix tape j
      = (fun l : Fin j.val => tape ⟨l.val, lt_trans l.isLt j.isLt⟩) from rfl]
  exact slotQuery_eq G.dflt G.exec (le_of_lt j.isLt) tape

/--
**Each tape's total budget.**  The execution's distinct queries are the search's — at most `N`, each
at most `βmax` — followed by recomputed points not asked before, each a round-`i` hash input at the
final answers, and at most one per round.  So the slot budgets sum to `N · βmax + ∑ i, slotBeta i`.
-/
theorem total_weight_le (betaMax : ℕ) (hmax : ∀ q : Q, G.beta q ≤ betaMax)
    (slotBeta : Fin L → ℕ)
    (hslot : ∀ (out : Out) (i : Fin L) (cp : Fin i.val → C),
      G.beta (G.hashInput out i.val cp) ≤ slotBeta i)
    (hfuel : L + N ≤ T) (tape : Fin T → C) :
    ∑ j : Fin T, G.slotWeight j (Sumcheck.extract_prefix tape j)
      ≤ N * betaMax + ∑ i, slotBeta i := by
  classical
  -- the two phases' seen-lists
  set search := lazyRun tape G.dflt G.adversary []
  set verif := lazyRun tape G.dflt
    (Recompute.rounds (G.hashInput search.1) L 0 fun _ => G.dflt) search.2.1
  have hrun := lazyRun_execution (L := L) tape G.dflt G.adversary G.hashInput
  have hfinal : (lazyRun tape G.dflt G.exec []).2.1 = verif.2.1 := by rw [exec, hrun]
  have hlenF : verif.2.1.length ≤ T := by
    have h := lazyRun_seen_length_le tape G.dflt G.exec []
    rw [hfinal] at h
    simp only [List.length_nil, Nat.zero_add] at h
    omega
  have hlenS : search.2.1.length ≤ N := by
    have h := lazyRun_seen_length_le tape G.dflt G.adversary []
    simpa using h
  obtain ⟨rest, hrest⟩ := lazyRun_seen_prefix tape G.dflt
    (Recompute.rounds (G.hashInput search.1) L 0 fun _ => G.dflt) search.2.1
  have hnodup : verif.2.1.Nodup := by
    rw [← hfinal]
    exact lazyRun_seen_nodup tape G.dflt G.exec [] List.nodup_nil
  rw [← hrest] at hnodup
  obtain ⟨-, hnodupR, hdisj⟩ := List.nodup_append.mp hnodup
  -- rewrite the slot sum as a list sum over the final seen-list
  have hsum : ∑ j : Fin T, G.slotWeight j (Sumcheck.extract_prefix tape j)
      = (verif.2.1.map G.beta).sum := by
    rw [← sum_slots_eq_list_sum verif.2.1 hlenF G.beta]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [slotWeight, G.slotQuery_at tape j, hfinal]
  rw [hsum, ← hrest, List.map_append, List.sum_append]
  refine Nat.add_le_add ?_ ?_
  · -- the search's own queries
    refine le_trans (List.sum_le_card_nsmul _ betaMax ?_) ?_
    · intro x hx
      obtain ⟨q, -, rfl⟩ := List.mem_map.mp hx
      exact hmax q
    · rw [List.length_map, smul_eq_mul]
      exact Nat.mul_le_mul_right _ hlenS
  · -- the recomputed points the search had not asked: one per round
    have hverif := Recompute.lazyRun_rounds tape G.dflt (G.hashInput search.1) L 0
      (fun _ => G.dflt) search.2.1
    set pts : Finset Q := univ.image fun i : Fin L =>
      G.hashInput search.1 i.val fun j : Fin i.val => verif.1 j.val
    have hsub : rest.toFinset ⊆ pts := by
      intro x hx
      have hxR : x ∈ rest := List.mem_toFinset.mp hx
      have hxF : x ∈ verif.2.1 := by rw [← hrest]; exact List.mem_append_right _ hxR
      have hxS : x ∉ search.2.1 := fun hS => hdisj x hS x hxR rfl
      obtain ⟨y, hy⟩ := lazyRun_mem_trace_of_mem_seen tape G.dflt _ search.2.1 x hxF hxS
      rw [hverif.2] at hy
      obtain ⟨i, hi, hxy⟩ := List.mem_map.mp hy
      have hiL : i < L := by
        have := (List.mem_range'.mp hi)
        omega
      refine Finset.mem_image.mpr ⟨⟨i, hiL⟩, mem_univ _, ?_⟩
      exact (congrArg Prod.fst hxy)
    rw [← List.sum_toFinset G.beta hnodupR]
    calc ∑ x ∈ rest.toFinset, G.beta x
        ≤ ∑ x ∈ pts, G.beta x := Finset.sum_le_sum_of_subset hsub
      _ ≤ ∑ i : Fin L, G.beta (G.hashInput search.1 i.val fun j : Fin i.val => verif.1 j.val) :=
          Finset.sum_image_le_of_nonneg fun _ _ => Nat.zero_le _
      _ ≤ ∑ i, slotBeta i := Finset.sum_le_sum fun i _ => hslot _ i _

/--
**The sharper grinding bound.**

```
Pr[ the verifier accepts the recomputed transcript  ∧  extraction fails ]
    ≤  (N · βmax  +  ∑ i, slotBeta i) / |C|
```

`slotBeta i` bounds round `i`'s hash inputs.  The adversary's `N` own queries can sit at any point
and pay the worst budget; the verifier's `L` recomputations each pay their own round's.  At `N = 0`
the right-hand side is the sequential round-by-round sum.  No union over the adversary's choice of
*which* round to grind is paid twice: a point occupies one slot (`lazyRun_seen_nodup`).
-/
theorem ratio_le_weighted [DecidableEq C] [Nonempty C] (betaMax : ℕ)
    (hmax : ∀ q : Q, G.beta q ≤ betaMax) (slotBeta : Fin L → ℕ)
    (hslot : ∀ (out : Out) (i : Fin L) (cp : Fin i.val → C),
      G.beta (G.hashInput out i.val cp) ≤ slotBeta i)
    (hfuel : L + N ≤ T) :
    ((univ.filter fun tape : Fin T → C => G.Accepts tape ∧ Fails).card : ℚ)
        / (Fintype.card C : ℚ) ^ T
      ≤ ((N * betaMax + ∑ i, slotBeta i : ℕ) : ℚ) / (Fintype.card C : ℚ) := by
  classical
  refine weighted_tape_ratio_le (fun tape : Fin T → C => G.Accepts tape ∧ Fails) G.slotBad ?_
    G.slotWeight G.slotBad_card _ (G.total_weight_le betaMax hmax slotBeta hslot hfuel)
  intro tape htape
  obtain ⟨j, q, hseen, hdoom, hesc⟩ := G.exists_bad_slot hfuel tape htape.1 htape.2
  exact ⟨j, q, by rw [G.slotQuery_at tape j]; exact hseen, hdoom, hesc⟩

/-- The count form of `ratio_le_weighted`, for slicing over a commitment. -/
theorem card_mul_le_weighted [DecidableEq C] (betaMax : ℕ)
    (hmax : ∀ q : Q, G.beta q ≤ betaMax) (slotBeta : Fin L → ℕ)
    (hslot : ∀ (out : Out) (i : Fin L) (cp : Fin i.val → C),
      G.beta (G.hashInput out i.val cp) ≤ slotBeta i)
    (hfuel : L + N ≤ T) (E : (Fin T → C) → Prop) [DecidablePred E]
    (hE : ∀ tape, E tape → G.Accepts tape)
    (hfail : Fails) :
    (univ.filter E).card * Fintype.card C
      ≤ (N * betaMax + ∑ i, slotBeta i) * Fintype.card C ^ T := by
  classical
  refine le_trans (Nat.mul_le_mul_right _ (Finset.card_le_card (t := univ.filter fun tape =>
      ∃ j, G.slotBad j (Sumcheck.extract_prefix tape j) (tape j)) ?_))
    (weighted_tape_card_le G.slotBad G.slotWeight G.slotBad_card _
      (G.total_weight_le betaMax hmax slotBeta hslot hfuel))
  intro tape htape
  simp only [mem_filter, mem_univ, true_and] at htape ⊢
  obtain ⟨j, q, hseen, hdoom, hesc⟩ := G.exists_bad_slot hfuel tape (hE tape htape) hfail
  exact ⟨j, q, by rw [G.slotQuery_at tape j]; exact hseen, hdoom, hesc⟩

end TranscriptGrinding

end Bcs
