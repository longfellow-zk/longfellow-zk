import Bcs.RecomputedRbr

/-!
# Fiat–Shamir with the commitment context read off the tape

`Bcs.TranscriptGrinding` charges each slot of the challenge tape with the bad event of the point
queried there, and that bad event reads **the point alone**: one commitment is fixed before the
search, so "this transcript prefix is lost" needs nothing else.  An adversary that may re-commit has
no such fixed commitment.  A point names its commitment — its root is part of the hash input — but
what the root *commits to* is whatever the Merkle extractor reads off the hash queries made so far,
and that is a function of the run, not of the point.

This file is `TranscriptGrinding`'s count with that context made explicit.

* `key q` is what the point names (a root, or a pair of roots), and `ctxAt tape k` the commitment
  context of key `k` on a tape: for a Merkle commitment, the extracted leaves.
* `ctxAt_congr` is the one obligation on it: **the context of the point at slot `j` is a function of
  the slots below `j`.**  For the Merkle context this holds because the extraction is taken from the
  hash queries made before the *first* query naming the root, which is at or before slot `j`.
* `Bad κ q c` is the bad event at a point in context `κ`; `beta q` its budget, which may read the
  point (its role) but not the context.

The per-slot event is "the point at slot `j`, in the context read off slots `< j`, is bad at the
tape's answer", and the count is `Bcs.weighted_tape_card_le` again.  The chain is supplied at the
level of the verifier's rounds (`RoundBad`): *some* recomputed round's point is bad in its context at
its recomputed answer.  A protocol whose state function is sequential gets it from `Rbr.exists_escape`;
a protocol that composes several bad events (the two-field MAC) supplies the case split.

## What is proved

* `CtxGrinding.exists_bad_slot` — a round-level bad event is a slot-level one;
* `CtxGrinding.card_mul_le` — `#E · |C| ≤ (N · βmax + ∑ k, slotBeta k) · |C|^T`;
* `CtxGrinding.ratio_le` — its probability form.

The weights are `TranscriptGrinding`'s, so the total-weight bound is reused verbatim
(`toTranscript`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bcs

open Finset Merkle.RandomOracle
open scoped Classical

/--
**A grinding adversary whose points are judged in a tape-read commitment context.**

The search, its default answer and the verifier's hash inputs are data, as in
`TranscriptGrinding`; `key`, `ctxAt` and `ctxAt_congr` say what commitment a point names and when that
commitment is fixed; `Bad`, `beta`, `bad_bound` are the per-point bad event and its budget.  Nothing
is assumed about the adversary.
-/
structure CtxGrinding (C : Type) [Fintype C] (Q Out Key K : Type) [DecidableEq Q] (N L T : ℕ) where
  /-- The adversary's search: an adaptive program making at most `N` queries. -/
  adversary : Tree Q C Out N
  /-- The answer an out-of-range slot would give; never read once the tape fits. -/
  dflt : C
  /-- Round `k`'s hash input, read from the proof and the raw answers of the earlier rounds. -/
  hashInput : Out → (k : ℕ) → (Fin k → C) → Q
  /-- The commitment a point names. -/
  key : Q → Key
  /-- The commitment context of a key, on a whole challenge tape. -/
  ctxAt : (Fin T → C) → Key → K
  /-- **The context is fixed in time.**  The context of the key of the point queried at slot `j` is
  the same on every tape that agrees below `j`. -/
  ctxAt_congr : ∀ (tape tape' : Fin T → C) (j : Fin T) (q : Q),
    (lazyRun tape dflt (execution adversary hashInput dflt L) []).2.1[j.val]? = some q →
    (∀ i : Fin T, i.val < j.val → tape i = tape' i) →
    ctxAt tape' (key q) = ctxAt tape (key q)
  /-- The bad event at a point in a context. -/
  Bad : K → Q → C → Prop
  /-- The per-point budget; it may read the point, not the context. -/
  beta : Q → ℕ
  /-- In every context, at most `beta q` answers are bad at `q`. -/
  bad_bound : ∀ (κ : K) (q : Q), (univ.filter fun c : C => Bad κ q c).card ≤ beta q

namespace CtxGrinding

variable {C Q Out Key K : Type} [Fintype C] [DecidableEq Q] {N L T : ℕ}
variable (G : CtxGrinding C Q Out Key K N L T)

/-- The whole execution: the search, then the verifier's recomputation. -/
def exec : Tree Q C (Out × (ℕ → C)) (L + N) := execution G.adversary G.hashInput G.dflt L

/-- The proof and the recomputed answers on a tape. -/
def output (tape : Fin T → C) : Out × (ℕ → C) := (lazyRun tape G.dflt G.exec []).1

/-- The recomputed challenge answers. -/
def challenges (tape : Fin T → C) : Fin L → C := fun i => (G.output tape).2 i.val

/-- Round `k`'s hash input at the proof and the recomputed earlier answers. -/
def point (tape : Fin T → C) (k : Fin L) : Q :=
  G.hashInput (G.output tape).1 k.val fun j : Fin k.val => (G.output tape).2 j.val

/-- **The round-level bad event**: some recomputed round's point is bad, in the context of its key,
at its recomputed answer. -/
def RoundBad (tape : Fin T → C) : Prop :=
  ∃ k : Fin L, G.Bad (G.ctxAt tape (G.key (G.point tape k))) (G.point tape k) (G.challenges tape k)

/-- The same search and hash inputs as a `TranscriptGrinding` with nothing doomed.  Only its
execution, slot weights and total-weight bound are used. -/
def toTranscript : TranscriptGrinding C Q Out N L (fun _ _ => False) False where
  adversary := G.adversary
  dflt := G.dflt
  hashInput := G.hashInput
  doomed _ _ _ := False
  doomed_start h := h.elim
  accepts_undoomed _ _ h := h.elim
  DoomedQuery _ := False
  Escapes _ _ := False
  beta := G.beta
  escape_bound _ h := h.elim
  link _ _ _ _ _ h := h.elim

theorem toTranscript_exec : G.toTranscript.exec = G.exec := rfl

/-- The bad event at slot `j`, read off the prefix and the slot's answer: the point at slot `j`, in
the context the prefix (padded) gives its key. -/
def slotBad (j : Fin T) (pref : Fin j.val → C) (c : C) : Prop :=
  ∃ q : Q, slotQuery (T := T) G.dflt G.exec pref = some q ∧
    G.Bad (G.ctxAt (pad (T := T) G.dflt pref) (G.key q)) q c

theorem slotBad_card (j : Fin T) (pref : Fin j.val → C) :
    (univ.filter fun c : C => G.slotBad j pref c).card ≤ G.toTranscript.slotWeight j pref := by
  classical
  show _ ≤ (slotQuery (T := T) G.dflt G.exec pref).elim 0 G.beta
  rcases hq : slotQuery (T := T) G.dflt G.exec pref with _ | q
  · refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
    intro c hc
    simp only [mem_filter, mem_univ, true_and, slotBad] at hc
    rw [hq] at hc
    obtain ⟨_, h, -⟩ := hc
    cases h
  · refine le_trans (Finset.card_le_card ?_)
      (G.bad_bound (G.ctxAt (pad (T := T) G.dflt pref) (G.key q)) q)
    intro c hc
    simp only [mem_filter, mem_univ, true_and, slotBad] at hc ⊢
    rw [hq] at hc
    obtain ⟨q', hq', hbad⟩ := hc
    cases hq'
    exact hbad

/--
**The chain, at the slot level.**  If some recomputed round's point is bad in its context, then
some slot's query is bad in the context its prefix gives.

The verifier's round-`k` point sits at a tape slot whose answer is round `k`'s challenge
(`TranscriptGrinding.verifier_entry_mem`, `lazyRun_trace_slot`); `ctxAt_congr` moves the context from
the whole tape to the padded prefix below that slot.
-/
theorem exists_bad_slot (hfuel : L + N ≤ T) (tape : Fin T → C) (h : G.RoundBad tape) :
    ∃ j : Fin T, G.slotBad j (Sumcheck.extract_prefix tape j) (tape j) := by
  classical
  obtain ⟨k, hbad⟩ := h
  have hmem := G.toTranscript.verifier_entry_mem tape k.val k.isLt
  obtain ⟨hseen, hval⟩ := lazyRun_trace_slot tape G.dflt G.exec [] _ hmem
  set q := G.point tape k with hqdef
  have hlt : (lazyRun tape G.dflt G.exec []).2.1.idxOf q < T := by
    have h := lazyRun_slot_lt tape G.dflt G.exec [] q hseen
    simp only [List.length_nil, Nat.zero_add] at h
    omega
  set j : Fin T := ⟨_, hlt⟩
  have hget : (lazyRun tape G.dflt G.exec []).2.1[j.val]? = some q := List.getElem?_idxOf hseen
  have htape : tape j = G.challenges tape k := by
    show tape j = (G.output tape).2 k.val
    have hval' : (G.output tape).2 k.val
        = tapeAt tape G.dflt ((lazyRun tape G.dflt G.exec []).2.1.idxOf q) := hval
    rw [hval', tapeAt, dif_pos hlt]
  have hctx : G.ctxAt (pad (T := T) G.dflt (Sumcheck.extract_prefix tape j)) (G.key q)
      = G.ctxAt tape (G.key q) :=
    G.ctxAt_congr tape _ j q hget fun i hi => by
      rw [pad_agree G.dflt _ i hi]
      rfl
  refine ⟨j, q, ?_, ?_⟩
  · rw [show Sumcheck.extract_prefix tape j
        = (fun l : Fin j.val => tape ⟨l.val, lt_trans l.isLt j.isLt⟩) from rfl]
    rw [slotQuery_eq G.dflt G.exec (le_of_lt j.isLt) tape]
    exact hget
  · rw [hctx, htape]
    exact hbad

/--
**The count.**  Every event `E` that forces a round-level bad event satisfies

```text
#E · |C|  ≤  (N · βmax  +  ∑ k, slotBeta k) · |C|^T
```

`slotBeta k` bounds round `k`'s hash inputs; the adversary's `N` own queries pay the worst point's
budget.  The weights are the context-free `TranscriptGrinding` weights, so each slot pays once, at
its point's budget, whatever context the point is judged in.
-/
theorem card_mul_le [DecidableEq C] (betaMax : ℕ) (hmax : ∀ q : Q, G.beta q ≤ betaMax)
    (slotBeta : Fin L → ℕ)
    (hslot : ∀ (out : Out) (i : Fin L) (cp : Fin i.val → C),
      G.beta (G.hashInput out i.val cp) ≤ slotBeta i)
    (hfuel : L + N ≤ T) (E : (Fin T → C) → Prop) [DecidablePred E]
    (hE : ∀ tape, E tape → G.RoundBad tape) :
    (univ.filter E).card * Fintype.card C
      ≤ (N * betaMax + ∑ i, slotBeta i) * Fintype.card C ^ T := by
  classical
  refine le_trans (Nat.mul_le_mul_right _ (Finset.card_le_card (t := univ.filter fun tape =>
      ∃ j, G.slotBad j (Sumcheck.extract_prefix tape j) (tape j)) ?_))
    (weighted_tape_card_le G.slotBad G.toTranscript.slotWeight G.slotBad_card _
      (G.toTranscript.total_weight_le betaMax hmax slotBeta hslot hfuel))
  intro tape htape
  simp only [mem_filter, mem_univ, true_and] at htape ⊢
  exact G.exists_bad_slot hfuel tape (hE tape htape)

/-- **The probability form**: `(N · βmax + ∑ k, slotBeta k) / |C|`. -/
theorem ratio_le [DecidableEq C] [Nonempty C] (betaMax : ℕ) (hmax : ∀ q : Q, G.beta q ≤ betaMax)
    (slotBeta : Fin L → ℕ)
    (hslot : ∀ (out : Out) (i : Fin L) (cp : Fin i.val → C),
      G.beta (G.hashInput out i.val cp) ≤ slotBeta i)
    (hfuel : L + N ≤ T) (E : (Fin T → C) → Prop) [DecidablePred E]
    (hE : ∀ tape, E tape → G.RoundBad tape) :
    ((univ.filter E).card : ℚ) / (Fintype.card C : ℚ) ^ T
      ≤ ((N * betaMax + ∑ i, slotBeta i : ℕ) : ℚ) / (Fintype.card C : ℚ) := by
  have hC : (0 : ℚ) < (Fintype.card C : ℚ) := by exact_mod_cast Fintype.card_pos
  have hnat := G.card_mul_le betaMax hmax slotBeta hslot hfuel E hE
  have hq : ((univ.filter E).card : ℚ) * (Fintype.card C : ℚ)
      ≤ ((N * betaMax + ∑ i, slotBeta i : ℕ) : ℚ) * (Fintype.card C : ℚ) ^ T := by
    exact_mod_cast hnat
  rw [div_le_div_iff₀ (pow_pos hC T) hC]
  exact hq

end CtxGrinding

end Bcs
