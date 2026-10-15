import Bcs.CtxGrinding
import Bcs.Soundness
import Merkle.TwoOracle

/-!
# Commitments made at any time: Merkle extraction for a re-committing Fiat–Shamir prover

`Bcs.Adversary`, `Bcs.StagedAdversary` and `Bcs.LigeroFSAdversary` all fix the commitment with a
separate commit tree run before any challenge-oracle query.  A real Fiat–Shamir prover need not:
one adaptive program may build many Merkle trees, hash each root for its first challenge, and keep
the root whose challenge suits it.  This file handles that program.

## The execution

The prover is one `TwoOracleTree body` interleaving at most `tA` Merkle-oracle queries (left) with
at most `N` challenge-oracle queries (right), and outputs a proof.  The verifier recomputes `L`
challenge rounds at hash inputs read off the proof (`joint`), then checks the Merkle opening against
the proof's root.  Fixing the Merkle tape gives a challenge-oracle tree (the Fiat–Shamir side);
fixing the challenge tape gives a Merkle-oracle tree (`merkleRun`); `TwoOracleTree`'s coherence makes
them one execution.

## When a commitment is made

A point names a key (`key`), the verifier's points name the proof's key (`hkey`), and a key names a
root (`rootOf`).  The commitment a key refers to is fixed at the **first challenge-oracle query naming
it**: `cutIdx` is that query's index among the distinct challenge queries, `stopAt` truncates the
program there, and `cutTrace` is the Merkle trace up to that point.  The extractor reads the root
from `cutTrace`.  Two facts make this the right cut:

* **it is fixed before the point is answered** (`ctxAt_congr`): the cut trace of the key of the point
  at challenge slot `j` reads challenge slots `< j` only.  This is what `Bcs.CtxGrinding` needs;
* **it is a prefix of the Merkle run** (`stop_seen_prefix`), so `Merkle.MH`'s generic cover applies to
  it as a commitment stage, wherever in the run it ends.

## The Merkle count

`merkle_card_le`: on every challenge tape, the Merkle tapes on which the verifier's Merkle check (a
program of `fc` queries; `fc = 2n` for one opening) accepts the proof's opening but the cut-trace
extraction does not explain it number at most

```text
adaptiveNumerator fc tA (L + N) · |D|^(T−1)
  = ( tA(tA−1)/2  +  (fc + tA)(2tA + 1)  +  (fc + tA)(L + N) ) · |D|^(T−1).
```

At `fc = 2n` the first two terms are the single-commitment numerator `merkleExtractionNumerator n tA 0`;
the third is what re-committing costs: a fresh query landing on the root of **some** cut, one target
per distinct challenge query per eligible slot.  A commitment collision is one event for all cuts
(they are prefixes of one trace), and the children labels of every cut are labels of the one
adversary run, so neither of the first two terms is multiplied by the number of cuts.  The number of
commitments the prover makes never appears.

`ratio_le` composes this with `Bcs.CtxGrinding` at every Merkle tape; `ratio_le_two` does the same
for two roots named by one key (two Merkle trees under one hash, one cut).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bcs.AdaptiveCommit

open Finset Merkle Merkle.MH Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree

/-! ## 1. Stopping at the `i`-th distinct challenge query -/

section Stop

variable {QL DL QR DR A : Type} [DecidableEq QR]

/-- **The program up to its `i`-th distinct right query.**  `seen` tracks the distinct right queries
so far — a function of the queries alone, so the truncation is syntactic.  At the `i`-th fresh right
query the program stops, before it is answered, and returns that query. -/
def stopAt (i : ℕ) : {l r : ℕ} → TwoOracleTree QL DL QR DR A l r → List QR →
    TwoOracleTree QL DL QR DR (Option QR) l r
  | _, _, .done _, _ => .done none
  | _, _, .queryLeft q next, seen => .queryLeft q fun y => stopAt i (next y) seen
  | _, _, .queryRight q next, seen =>
      if q ∉ seen ∧ seen.length = i then .done (some q)
      else .queryRight q fun y => stopAt i (next y) (if q ∈ seen then seen else seen ++ [q])

/-- **Challenge side.**  With the Merkle tape fixed, the truncated program's distinct challenge
queries are the first `i` of the whole program's, and it returns the `i`-th. -/
theorem lazyRun_fixLeft_stopAt [DecidableEq QL] {TL TR : ℕ} (mt : Fin TL → DL) (dL : DL)
    (ct : Fin TR → DR) (dR : DR) (i : ℕ) :
    ∀ {l r : ℕ} (τ : TwoOracleTree QL DL QR DR A l r) (sL : List QL) (sR : List QR),
      sR.length ≤ i →
      (lazyRun ct dR (fixLeft mt dL (stopAt i τ sR) sL) sR).2.1
          = (lazyRun ct dR (fixLeft mt dL τ sL) sR).2.1.take i ∧
        (lazyRun ct dR (fixLeft mt dL (stopAt i τ sR) sL) sR).1
          = (lazyRun ct dR (fixLeft mt dL τ sL) sR).2.1[i]? := by
  intro l r τ
  induction τ with
  | done a =>
      intro sL sR h
      simp only [stopAt, fixLeft, lazyRun_done]
      exact ⟨(List.take_of_length_le h).symm, (List.getElem?_eq_none h).symm⟩
  | queryLeft q next ih =>
      intro sL sR h
      simp only [stopAt, fixLeft]
      exact ih _ _ _ h
  | queryRight q next ih =>
      intro sL sR h
      by_cases hstop : q ∉ sR ∧ sR.length = i
      · simp only [stopAt, if_pos hstop, fixLeft, lazyRun_done]
        rw [lazyRun_query]
        dsimp only
        rw [if_neg hstop.1]
        obtain ⟨rest, hrest⟩ := lazyRun_seen_prefix ct dR
          (fixLeft mt dL (next (tapeAt ct dR ((sR ++ [q]).idxOf q))) sL) (sR ++ [q])
        rw [← hrest, ← hstop.2]
        refine ⟨?_, ?_⟩
        · rw [List.append_assoc, List.take_left]
        · rw [List.append_assoc, List.getElem?_append_right le_rfl, Nat.sub_self]
          rfl
      · simp only [stopAt, if_neg hstop, fixLeft]
        rw [lazyRun_query, lazyRun_query]
        dsimp only
        have hlen : (if q ∈ sR then sR else sR ++ [q]).length ≤ i := by
          by_cases hq : q ∈ sR
          · rw [if_pos hq]; exact h
          · rw [if_neg hq, List.length_append, List.length_singleton]
            have : sR.length ≠ i := fun he => hstop ⟨hq, he⟩
            omega
        exact ih _ _ _ hlen

/-- **Merkle side.**  With the challenge tape fixed, the truncated program's Merkle queries are a
prefix of the whole program's. -/
theorem lazyRun_fixRight_stopAt_prefix [DecidableEq QL] {TL TR : ℕ} (mt : Fin TL → DL) (dL : DL)
    (ct : Fin TR → DR) (dR : DR) (i : ℕ) :
    ∀ {l r : ℕ} (τ : TwoOracleTree QL DL QR DR A l r) (sR : List QR) (sL : List QL),
      (lazyRun mt dL (fixRight ct dR (stopAt i τ sR) sR) sL).2.1
        <+: (lazyRun mt dL (fixRight ct dR τ sR) sL).2.1 := by
  intro l r τ
  induction τ with
  | done a =>
      intro sR sL
      exact List.prefix_refl _
  | queryLeft q next ih =>
      intro sR sL
      simp only [stopAt, fixRight]
      rw [lazyRun_query, lazyRun_query]
      exact ih _ _ _
  | queryRight q next ih =>
      intro sR sL
      by_cases hstop : q ∉ sR ∧ sR.length = i
      · simp only [stopAt, if_pos hstop, fixRight, lazyRun_done]
        exact lazyRun_seen_prefix mt dL _ sL
      · simp only [stopAt, if_neg hstop, fixRight]
        exact ih _ _ _

/-- **The truncated program reads challenge slots below `i` only.**  Before it stops, it has fewer
than `i` distinct challenge queries, so every challenge answer it reads sits at a slot `< i`. -/
theorem fixRight_stopAt_congr {TR : ℕ} (ct ct' : Fin TR → DR) (dR : DR) (i : ℕ)
    (hag : ∀ j : Fin TR, j.val < i → ct j = ct' j) :
    ∀ {l r : ℕ} (τ : TwoOracleTree QL DL QR DR A l r) (sR : List QR), sR.length ≤ i →
      fixRight ct dR (stopAt i τ sR) sR = fixRight ct' dR (stopAt i τ sR) sR := by
  intro l r τ
  induction τ with
  | done a => intro sR _; rfl
  | queryLeft q next ih =>
      intro sR h
      simp only [stopAt, fixRight]
      congr 1
      funext y
      exact ih y sR h
  | queryRight q next ih =>
      intro sR h
      by_cases hstop : q ∉ sR ∧ sR.length = i
      · simp only [stopAt, if_pos hstop, fixRight]
      · simp only [stopAt, if_neg hstop, fixRight]
        set sR' := if q ∈ sR then sR else sR ++ [q] with hsR'
        have hlen : sR'.length ≤ i := by
          by_cases hq : q ∈ sR
          · rw [hsR', if_pos hq]; exact h
          · rw [hsR', if_neg hq, List.length_append, List.length_singleton]
            have : sR.length ≠ i := fun he => hstop ⟨hq, he⟩
            omega
        have hmem : q ∈ sR' := by
          by_cases hq : q ∈ sR
          · rw [hsR', if_pos hq]; exact hq
          · rw [hsR', if_neg hq]; simp
        have hidx : sR'.idxOf q < i :=
          lt_of_lt_of_le (List.idxOf_lt_length_of_mem hmem) hlen
        have hy : tapeAt ct dR (sR'.idxOf q) = tapeAt ct' dR (sR'.idxOf q) := by
          unfold tapeAt
          by_cases hT : sR'.idxOf q < TR
          · rw [dif_pos hT, dif_pos hT]
            exact hag ⟨_, hT⟩ hidx
          · rw [dif_neg hT, dif_neg hT]
        rw [hy]
        exact ih _ sR' hlen

end Stop

/-! ## 2. The joint execution and the cut -/

/--
**A re-committing Fiat–Shamir prover, with the verifier's reading of its proof.**

`body` is the prover: one adaptive program with at most `tA` Merkle-oracle and `N` challenge-oracle
queries.  `hashInput` is the verifier's round-`k` hash input, `key` what a point names, and `hkey`
says every verifier point names the proof's key.  Nothing constrains `body`.
-/
structure Setup (Enc D Pt C Out Key : Type) (tA N L : ℕ) where
  /-- The prover's program. -/
  body : TwoOracleTree Enc D Pt C Out tA N
  /-- Round `k`'s hash input, from the proof and the raw answers of the earlier rounds. -/
  hashInput : Out → (k : ℕ) → (Fin k → C) → Pt
  /-- The challenge answer an out-of-range slot would give; never read once the tape fits. -/
  dflt : C
  /-- The commitment a point names. -/
  key : Pt → Key
  /-- The commitment a proof names. -/
  keyOut : Out → Key
  /-- The verifier's points name the proof's commitment. -/
  hkey : ∀ (out : Out) (k : ℕ) (cp : Fin k → C), key (hashInput out k cp) = keyOut out

namespace Setup

variable {Enc D Pt C Out Key : Type} [DecidableEq Enc] [Inhabited D] [DecidableEq Pt]
  {tA N L TM TC : ℕ}
variable (S : Setup Enc D Pt C Out Key tA N L)

/-- **The joint execution**: the prover, then the verifier's recomputation of the `L` rounds. -/
def joint : TwoOracleTree Enc D Pt C (Out × (ℕ → C)) tA (L + N) :=
  S.body.bindRight fun out =>
    (Recompute.rounds (S.hashInput out) L 0 fun _ => S.dflt).map fun acc => (out, acc)

/-- The prover's search at a fixed Merkle tape: a challenge-oracle tree. -/
def search (mt : Fin TM → D) : Tree Pt C Out N := fixLeft mt default S.body []

omit [DecidableEq Pt] in
/-- At a fixed Merkle tape the joint execution is `Bcs.execution` of the search. -/
theorem fixLeft_joint (mt : Fin TM → D) :
    fixLeft mt default S.joint [] = execution (S.search mt) S.hashInput S.dflt L := by
  unfold joint execution search
  exact fixLeft_bindRight mt default S.body _ []

/-- The Fiat–Shamir execution at a fixed Merkle tape. -/
def fsExec (mt : Fin TM → D) : Tree Pt C (Out × (ℕ → C)) (L + N) :=
  execution (S.search mt) S.hashInput S.dflt L

/-- The proof and the recomputed answers. -/
def output (mt : Fin TM → D) (ct : Fin TC → C) : Out × (ℕ → C) :=
  (lazyRun ct S.dflt (S.fsExec mt) []).1

/-- The proof. -/
def proof (mt : Fin TM → D) (ct : Fin TC → C) : Out := (S.output mt ct).1

/-- The recomputed challenge answers, one per round. -/
def challenges (mt : Fin TM → D) (ct : Fin TC → C) : Fin L → C := fun i => (S.output mt ct).2 i.val

/-- The distinct challenge queries, in order. -/
def fsSeen (mt : Fin TM → D) (ct : Fin TC → C) : List Pt :=
  (lazyRun ct S.dflt (S.fsExec mt) []).2.1

/-- **The cut of a key**: the index, among the distinct challenge queries, of the first one naming
it. -/
def cutIdx [DecidableEq Key] (mt : Fin TM → D) (ct : Fin TC → C) (k : Key) : ℕ :=
  (S.fsSeen mt ct).findIdx fun q => decide (S.key q = k)

/-- The Merkle-oracle program up to the `i`-th distinct challenge query, at a fixed challenge tape. -/
def cutRun (ct : Fin TC → C) (i : ℕ) : Tree Enc D (Option Pt) tA :=
  fixRight ct S.dflt (stopAt i S.joint []) []

/-- **The cut trace of a key**: the Merkle queries made before the first challenge query naming
it. -/
def cutTrace [DecidableEq Key] (mt : Fin TM → D) (ct : Fin TC → C) (k : Key) : List (Enc × D) :=
  (lazyRun mt default (S.cutRun ct (S.cutIdx mt ct k)) []).2.2

/-- **The commitment context of a key**: the key and its cut trace. -/
def ctxAt [DecidableEq Key] (mt : Fin TM → D) (ct : Fin TC → C) (k : Key) : Key × List (Enc × D) :=
  (k, S.cutTrace mt ct k)

/-- **The commitment context of the proof**: its key and the cut trace of that key.  This is what
the extractor reads. -/
def context [DecidableEq Key] (mt : Fin TM → D) (ct : Fin TC → C) : Key × List (Enc × D) :=
  S.ctxAt mt ct (S.keyOut (S.proof mt ct))

/-- The search with nothing doomed, for its trace facts. -/
def plain [Fintype C] (mt : Fin TM → D) : TranscriptGrinding C Pt Out N L (fun _ _ => False) False where
  adversary := S.search mt
  dflt := S.dflt
  hashInput := S.hashInput
  doomed _ _ _ := False
  doomed_start h := h.elim
  accepts_undoomed _ _ h := h.elim
  DoomedQuery _ := False
  Escapes _ _ := False
  beta _ := 0
  escape_bound _ h := h.elim
  link _ _ _ _ _ h := h.elim

/-- **Every verifier point is a distinct challenge query of the run.** -/
theorem hashInput_mem_fsSeen [Fintype C] (mt : Fin TM → D) (ct : Fin TC → C) (k : ℕ) (hk : k < L) :
    S.hashInput (S.output mt ct).1 k (fun j : Fin k => (S.output mt ct).2 j.val)
      ∈ S.fsSeen mt ct := by
  have hmem := (S.plain mt).verifier_entry_mem ct k hk
  exact (lazyRun_trace_slot ct S.dflt (S.fsExec mt) [] _ hmem).1

/-- The cut of the proof's key is a real index: the verifier's round-`0` point names it. -/
theorem cutIdx_lt [DecidableEq Key] [Fintype C] (mt : Fin TM → D) (ct : Fin TC → C) (hL : 0 < L) :
    S.cutIdx mt ct (S.keyOut (S.output mt ct).1) < (S.fsSeen mt ct).length := by
  refine List.findIdx_lt_length_of_exists ⟨_, S.hashInput_mem_fsSeen mt ct 0 hL, ?_⟩
  simp [S.hkey]

/-- …and at most `L + N`. -/
theorem fsSeen_length_le (mt : Fin TM → D) (ct : Fin TC → C) :
    (S.fsSeen mt ct).length ≤ L + N := by
  have h := lazyRun_seen_length_le ct S.dflt (S.fsExec mt) []
  simp only [List.length_nil, Nat.zero_add] at h
  exact h

/-- **The cut's Merkle run returns the cut query**: the first challenge query naming the key. -/
theorem cutRun_output (mt : Fin TM → D) (ct : Fin TC → C) (i : ℕ) :
    (lazyRun mt default (S.cutRun ct i) []).1 = (S.fsSeen mt ct)[i]? := by
  unfold cutRun fsSeen fsExec
  rw [← fixLeft_fixRight_output mt ct default S.dflt (stopAt i S.joint []) [] [],
    (lazyRun_fixLeft_stopAt mt default ct S.dflt i S.joint [] [] (Nat.zero_le _)).2,
    S.fixLeft_joint]

/-- The cut's Merkle queries are a prefix of the whole run's. -/
theorem cutRun_seen_prefix (mt : Fin TM → D) (ct : Fin TC → C) (i : ℕ) :
    (lazyRun mt default (S.cutRun ct i) []).2.1
      <+: (lazyRun mt default (fixRight ct S.dflt S.joint []) []).2.1 :=
  lazyRun_fixRight_stopAt_prefix mt default ct S.dflt i S.joint [] []

/-- The first `j + 1` distinct challenge queries read challenge slots `< j` only. -/
theorem fsSeen_take_congr (mt : Fin TM → D) (ct ct' : Fin TC → C) (j : ℕ)
    (hag : ∀ i : Fin TC, i.val < j → ct i = ct' i) :
    (S.fsSeen mt ct).take (j + 1) = (S.fsSeen mt ct').take (j + 1) :=
  lazyRun_seen_take_congr ct ct' S.dflt j hag (S.fsExec mt) []

/--
**The context is fixed in time.**  If the point at challenge slot `j` names key `k`, then the cut of
`k` is at or before `j` and its trace reads challenge slots `< j` only: on any tape agreeing below
`j`, the context of `k` is the same.
-/
theorem ctxAt_congr [DecidableEq Key] (mt : Fin TM → D) (ct ct' : Fin TC → C) (j : Fin TC) (q : Pt)
    (hq : (S.fsSeen mt ct)[j.val]? = some q)
    (hag : ∀ i : Fin TC, i.val < j.val → ct i = ct' i) :
    S.ctxAt mt ct' (S.key q) = S.ctxAt mt ct (S.key q) := by
  set p : Pt → Bool := fun x => decide (S.key x = S.key q) with hp
  set P := (S.fsSeen mt ct).take (j.val + 1) with hP
  have hjlt : j.val < (S.fsSeen mt ct).length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hq
    cases hq
  have hPlen : P.length = j.val + 1 := by
    rw [hP, List.length_take]; omega
  have hPj : P[j.val]? = some q := by
    rw [hP, List.getElem?_take_of_lt (by omega)]; exact hq
  have hfind : P.findIdx p < P.length := by
    refine List.findIdx_lt_length_of_exists ⟨q, List.mem_of_getElem? hPj, ?_⟩
    simp [hp]
  have hcut : S.cutIdx mt ct (S.key q) = P.findIdx p :=
    (List.take_prefix _ _).findIdx_eq_of_findIdx_lt_length hfind
  have hcut' : S.cutIdx mt ct' (S.key q) = P.findIdx p := by
    have hP' : P = (S.fsSeen mt ct').take (j.val + 1) := by
      rw [hP]; exact S.fsSeen_take_congr mt ct ct' j.val hag
    have hpre : P <+: S.fsSeen mt ct' := by rw [hP']; exact List.take_prefix _ _
    exact hpre.findIdx_eq_of_findIdx_lt_length hfind
  have hle : P.findIdx p ≤ j.val := by omega
  unfold ctxAt cutTrace
  rw [hcut, hcut']
  unfold cutRun
  rw [fixRight_stopAt_congr ct ct' S.dflt (P.findIdx p)
    (fun i hi => hag i (lt_of_lt_of_le hi hle)) S.joint [] (Nat.zero_le _)]

end Setup

/-! ## 3. The Merkle count -/

/-- **The adaptive Merkle numerator**: `merkleExtractionNumerator`'s two terms at a check of `fc`
queries and an adversary of `tA` Merkle queries, plus one root target per distinct challenge query
per eligible slot. -/
def adaptiveNumerator (fc tA Lfs : ℕ) : ℕ :=
  tA * (tA - 1) / 2 + (fc + tA) * (2 * tA + 1) + (fc + tA) * Lfs

/-- A non-root candidate label reads only the seen-list entry it decodes. -/
theorem candidateLabel_of_ne_zero {Enc D Salt M Out' : Type} [Inhabited D]
    (codec : Codec Salt M D Enc) (dec : RoleDecoders codec) (rootOf : Out' → D)
    (run : Out' × List Enc × List (Enc × D)) {m : ℕ} (hm : m ≠ 0) :
    candidateLabel codec dec rootOf run m
      = ((run.2.1[(m - 1) / 2]?).bind dec.nodeDec).elim default fun lr =>
          if (m - 1) % 2 = 0 then lr.1 else lr.2 := by
  rw [candidateLabel, if_neg hm]

namespace Setup

section Merkle

variable {Enc D Pt C Out Key Salt M : Type} [DecidableEq Enc] [Inhabited D] [DecidableEq Pt]
  {tA N L TM TC fc : ℕ}
variable (S : Setup Enc D Pt C Out Key tA N L)

/-- **The Merkle-oracle run at a fixed challenge tape**: the prover and the recomputation, then the
verifier's Merkle check `check` on the proof. -/
def merkleRun (check : Out → Tree Enc D Unit fc) (ct : Fin TC → C) :
    Tree Enc D (Out × (ℕ → C)) (fc + tA) :=
  (fixRight ct S.dflt S.joint []).bind fun oc => (check oc.1).map fun _ => oc

/-- The verifier's Merkle oracle: lazy sampling over the whole Merkle run. -/
def merkleOracle (check : Out → Tree Enc D Unit fc) (mt : Fin TM → D) (ct : Fin TC → C) :
    Enc → D :=
  runOracle TM (S.merkleRun check ct) mt

/-- The prover-and-recomputation part of the Merkle run, evaluated against the verifier's oracle, is
its lazy run. -/
theorem joint_run_eq (check : Out → Tree Enc D Unit fc) (mt : Fin TM → D) (ct : Fin TC → C) :
    (fixRight ct S.dflt S.joint []).run (S.merkleOracle check mt ct)
      = ((lazyRun mt default (fixRight ct S.dflt S.joint []) []).1,
          (lazyRun mt default (fixRight ct S.dflt S.joint []) []).2.2) :=
  lazyRun_run_eq_of_prefix mt default _ [] _ _ (fun _ => rfl)
    (lazyRun_seen_prefix_bind mt default _ _ [])

/-- **Coherence**: the Merkle side's proof is the Fiat–Shamir side's. -/
theorem joint_output (mt : Fin TM → D) (ct : Fin TC → C) :
    (lazyRun mt default (fixRight ct S.dflt S.joint []) []).1 = S.output mt ct := by
  rw [← fixLeft_fixRight_output mt ct default S.dflt S.joint [] [], S.fixLeft_joint]
  rfl

/-- A pair the Merkle check queries is a pair of the Merkle run. -/
theorem mem_merkleRun_trace (check : Out → Tree Enc D Unit fc) (mt : Fin TM → D)
    (ct : Fin TC → C) (qa : Enc × D)
    (h : qa ∈ ((check (S.output mt ct).1).run (S.merkleOracle check mt ct)).2) :
    qa ∈ ((S.merkleRun check ct).run (S.merkleOracle check mt ct)).2 := by
  have hj := S.joint_run_eq check mt ct
  have hout := S.joint_output mt ct
  unfold merkleRun
  rw [Tree.run_bind, Tree.run_map]
  refine List.mem_append.mpr (Or.inr ?_)
  rw [show ((fixRight ct S.dflt S.joint []).run (S.merkleOracle check mt ct)).1
      = S.output mt ct by rw [hj]; exact hout]
  exact h

variable [DecidableEq Key] [DecidableEq D] [Inhabited Salt] [Inhabited M] {n : ℕ}

/-- The verifier's Merkle check accepts the proof's opening at the root its key names. -/
def MerkleAccepts (codec : Codec Salt M D Enc) (check : Out → Tree Enc D Unit fc)
    (rootOf : Key → D) (claimOf : Out → OpeningClaim n Salt M D)
    (mt : Fin TM → D) (ct : Fin TC → C) : Prop :=
  MH.Accepts (codec.withOracle (S.merkleOracle check mt ct)) n
    (rootOf (S.keyOut (S.output mt ct).1)) (claimOf (S.output mt ct).1).I
    (claimOf (S.output mt ct).1).a (claimOf (S.output mt ct).1).pf

/-- **The cut-trace extraction explains the opening**: from the Merkle queries made before the first
challenge query naming the proof's key, the extractor recovers the claimed leaves and literally the
opening proof. -/
def Explains {codec : Codec Salt M D Enc} (dec : RoleDecoders codec) (rootOf : Key → D)
    (claimOf : Out → OpeningClaim n Salt M D) (mt : Fin TM → D) (ct : Fin TC → C) : Prop :=
  ∃ e : Extracted n Salt M D,
    extract dec n (rootOf (S.keyOut (S.output mt ct).1))
        (S.cutTrace mt ct (S.keyOut (S.output mt ct).1)) = some e ∧
      (∀ i ∈ (claimOf (S.output mt ct).1).I, e.message i = (claimOf (S.output mt ct).1).a i) ∧
      openFromTrapdoor e.trapdoor (claimOf (S.output mt ct).1).I = (claimOf (S.output mt ct).1).pf

/-- The fixed hit family: a child label of the adversary run (or the default) per eligible slot and
label index, and the root of every cut per eligible slot. -/
def hits (fc tA Lfs : ℕ) : Finset ((Fin (fc + tA) × ℕ) ⊕ (Fin (fc + tA) × ℕ)) :=
  (extractionHits (fc + tA) tA).disjSum (univ ×ˢ range Lfs)

theorem hits_card (fc tA Lfs : ℕ) :
    (hits fc tA Lfs).card = (fc + tA) * (2 * tA + 1) + (fc + tA) * Lfs := by
  rw [hits, card_disjSum, extractionHits_card, card_product, card_univ, Fintype.card_fin,
    card_range]

/-- A family slot, as a tape slot. -/
def hitSlot (hF : fc + tA ≤ TM) : (Fin (fc + tA) × ℕ) ⊕ (Fin (fc + tA) × ℕ) → Fin TM :=
  Sum.elim (fun p => ⟨p.1.val, lt_of_lt_of_le p.1.isLt hF⟩)
    (fun p => ⟨p.1.val, lt_of_lt_of_le p.1.isLt hF⟩)

/-- A family target, read off the tape with its own slot neutralized. -/
def hitTarget (codec : Codec Salt M D Enc) (dec : RoleDecoders codec) (rootOf : Key → D)
    (ct : Fin TC → C) (hF : fc + tA ≤ TM) :
    (Fin (fc + tA) × ℕ) ⊕ (Fin (fc + tA) × ℕ) → (Fin TM → D) → D :=
  Sum.elim
    (fun p answers => candidateLabel codec dec (fun _ => default)
      (lazyRun (Function.update answers ⟨p.1.val, lt_of_lt_of_le p.1.isLt hF⟩ default) default
        (fixRight ct S.dflt S.joint []) []) p.2)
    (fun p answers =>
      (lazyRun (Function.update answers ⟨p.1.val, lt_of_lt_of_le p.1.isLt hF⟩ default) default
        (S.cutRun ct p.2) []).1.elim default (rootOf ∘ S.key))

omit [DecidableEq Key] [DecidableEq D] [Inhabited Salt] [Inhabited M] in
theorem hitTarget_isHitTarget (codec : Codec Salt M D Enc) (dec : RoleDecoders codec)
    (rootOf : Key → D) (ct : Fin TC → C) (hF : fc + tA ≤ TM)
    (p : (Fin (fc + tA) × ℕ) ⊕ (Fin (fc + tA) × ℕ)) :
    HitTarget (hitSlot hF p) (S.hitTarget codec dec rootOf ct hF p) := by
  rcases p with p | p
  · exact hitTarget_of_neutralize _ default fun tape =>
      candidateLabel codec dec (fun _ => default)
        (lazyRun tape default (fixRight ct S.dflt S.joint []) []) p.2
  · exact hitTarget_of_neutralize _ default fun tape =>
      (lazyRun tape default (S.cutRun ct p.2) []).1.elim default (rootOf ∘ S.key)

/--
**The cover.**  If the Merkle check accepts the proof's opening but the cut-trace extraction does
not explain it, then two of the adversary's Merkle answers collide, or some eligible slot carries a
fixed-family target.

The cut is a commitment stage: it is a prefix of the Merkle run (`cutRun_seen_prefix`) and returns
the first challenge query naming the proof's key (`cutRun_output`), whose root is the proof's root.
So `Merkle.MH.cover_of_failure_generic_eligible` applies to it.  Its collision event lives in a prefix
of the adversary trace, hence in the first `tA` slots; its root target is the family's root target
at this cut; its child targets are children of the adversary run, or the default.
-/
theorem cover [Fintype C] (codec : Codec Salt M D Enc) (dec : RoleDecoders codec)
    (check : Out → Tree Enc D Unit fc) (rootOf : Key → D)
    (claimOf : Out → OpeningClaim n Salt M D)
    (hcheck : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec n (claimOf out).I (claimOf out).a (claimOf out).pf (2 * n)
          fun _ => default).run H).2, qa ∈ ((check out).run H).2)
    (hL : 0 < L) (ht : tA ≤ TM) (hF : fc + tA ≤ TM) (mt : Fin TM → D) (ct : Fin TC → C)
    (hacc : S.MerkleAccepts codec check rootOf claimOf mt ct)
    (hfail : ¬ S.Explains dec rootOf claimOf mt ct) :
    PairCollision TM (slotPairs TM tA) mt ∨
      HitFamily TM (hits fc tA (L + N)) (hitSlot hF) (S.hitTarget codec dec rootOf ct hF) mt := by
  classical
  set out := (S.output mt ct).1 with hout
  set i := S.cutIdx mt ct (S.keyOut out) with hi_def
  have hi : i < (S.fsSeen mt ct).length := S.cutIdx_lt mt ct hL
  set commit := S.cutRun ct i with hcommit
  set R := S.merkleRun check ct with hR
  let rootOf' : Option Pt → D := fun o => o.elim default (rootOf ∘ S.key)
  have hpref : (lazyRun mt default commit []).2.1 <+: runSlots TM R mt :=
    (S.cutRun_seen_prefix mt ct i).trans (lazyRun_seen_prefix_bind mt default _ _ [])
  have hkeyi : S.key ((S.fsSeen mt ct)[i]'hi) = S.keyOut out := by
    have h := List.findIdx_getElem (xs := S.fsSeen mt ct)
      (p := fun q => decide (S.key q = S.keyOut out)) (w := hi)
    exact of_decide_eq_true h
  have hrt : rootOf (S.keyOut out) = rootOf' (lazyRun mt default commit []).1 := by
    rw [hcommit, S.cutRun_output, List.getElem?_eq_getElem hi]
    simp only [rootOf', Option.elim, Function.comp, hkeyi]
  have hcheck' : ∀ qa ∈ ((checkPass codec n (claimOf out).I (claimOf out).a (claimOf out).pf
      (2 * n) fun _ => default).run (runOracle TM R mt)).2, qa ∈ (R.run (runOracle TM R mt)).2 :=
    fun qa hqa => S.mem_merkleRun_trace check mt ct qa (hcheck _ out qa hqa)
  have hfail' : ¬ ∃ e : Extracted n Salt M D,
      extract dec n (rootOf (S.keyOut out)) (commit.run (runOracle TM R mt)).2 = some e ∧
        (∀ j ∈ (claimOf out).I, e.message j = (claimOf out).a j) ∧
        openFromTrapdoor e.trapdoor (claimOf out).I = (claimOf out).pf := by
    rw [commitTrace_eq_generic (commit := commit) (R := R) (answers := mt) (hpref := hpref)]
    exact hfail
  rcases cover_of_failure_generic_eligible codec n tA TM commit R mt dec rootOf'
      (rootOf (S.keyOut out)) (claimOf out) hF hpref hrt hcheck' hacc hfail' with hcol | hhit
  · exact Or.inl (pairCollision_of_not_collisionFree_generic (t₁ := tA) (T := TM)
      (commit := commit) (R := R) (answers := mt) ht hpref hcol)
  · right
    obtain ⟨⟨j, m⟩, hp, heq⟩ := hhit
    have hm : m < 2 * tA + 1 := Finset.mem_range.mp (Finset.mem_product.mp hp).2
    set jj : Fin TM := ⟨j.val, lt_of_lt_of_le j.isLt hF⟩ with hjj
    set nt := Function.update mt jj default with hnt
    have hval : mt jj = candidateLabel codec dec rootOf' (lazyRun nt default commit []) m := heq
    by_cases hm0 : m = 0
    · -- the cut's root
      refine ⟨Sum.inr (j, i), inr_mem_disjSum.mpr (Finset.mem_product.mpr ⟨Finset.mem_univ _,
        Finset.mem_range.mpr (lt_of_lt_of_le hi (S.fsSeen_length_le mt ct))⟩), ?_⟩
      rw [hm0, candidateLabel_zero] at hval
      exact hval
    · -- a child label of the cut, which is a child label of the adversary run or the default
      have hpre := S.cutRun_seen_prefix nt ct i
      rw [candidateLabel_of_ne_zero codec dec rootOf' _ hm0] at hval
      by_cases hlt : (m - 1) / 2 < (lazyRun nt default commit []).2.1.length
      · refine ⟨Sum.inl (j, m), inl_mem_disjSum.mpr hp, ?_⟩
        show mt jj = candidateLabel codec dec (fun _ => default)
          (lazyRun nt default (fixRight ct S.dflt S.joint []) []) m
        rw [candidateLabel_of_ne_zero codec dec _ _ hm0, hval]
        congr 2
        rw [List.prefix_iff_eq_take.mp hpre, List.getElem?_take_of_lt hlt]
      · refine ⟨Sum.inl (j, 0), inl_mem_disjSum.mpr (Finset.mem_product.mpr ⟨Finset.mem_univ _,
          Finset.mem_range.mpr (by omega)⟩), ?_⟩
        show mt jj = candidateLabel codec dec (fun _ => default)
          (lazyRun nt default (fixRight ct S.dflt S.joint []) []) 0
        rw [candidateLabel_zero, hval, List.getElem?_eq_none (by omega)]
        rfl

open scoped Classical in
/--
**The Merkle count at a fixed challenge tape.**

```text
#{ Merkle tapes : the Merkle check accepts ∧ the cut-trace extraction does not explain }
    ≤ adaptiveNumerator fc tA (L + N) · |D|^(T−1)
```

against a prover that may re-commit any number of times within its `tA` Merkle queries.
-/
theorem merkle_card_le [Fintype C] [Fintype D] (codec : Codec Salt M D Enc) (dec : RoleDecoders codec)
    (check : Out → Tree Enc D Unit fc) (rootOf : Key → D)
    (claimOf : Out → OpeningClaim n Salt M D)
    (hcheck : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec n (claimOf out).I (claimOf out).a (claimOf out).pf (2 * n)
          fun _ => default).run H).2, qa ∈ ((check out).run H).2)
    (hL : 0 < L) (ht : tA ≤ TM) (hF : fc + tA ≤ TM) (ct : Fin TC → C) :
    (univ.filter fun mt : Fin TM → D =>
        S.MerkleAccepts codec check rootOf claimOf mt ct ∧
          ¬ S.Explains dec rootOf claimOf mt ct).card
      ≤ adaptiveNumerator fc tA (L + N) * Fintype.card D ^ (TM - 1) := by
  calc (univ.filter fun mt : Fin TM → D =>
        S.MerkleAccepts codec check rootOf claimOf mt ct ∧
          ¬ S.Explains dec rootOf claimOf mt ct).card
      ≤ ((univ.filter (PairCollision (D := D) TM (slotPairs TM tA))) ∪
          (univ.filter (HitFamily (D := D) TM (hits fc tA (L + N)) (hitSlot hF)
            (S.hitTarget codec dec rootOf ct hF)))).card := by
        apply Finset.card_le_card
        intro mt hmt
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmt
        rcases S.cover codec dec check rootOf claimOf hcheck hL ht hF mt ct hmt.1 hmt.2 with h | h
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    _ ≤ (univ.filter (PairCollision (D := D) TM (slotPairs TM tA))).card +
        (univ.filter (HitFamily (D := D) TM (hits fc tA (L + N)) (hitSlot hF)
          (S.hitTarget codec dec rootOf ct hF))).card := Finset.card_union_le _ _
    _ ≤ tA * (tA - 1) / 2 * Fintype.card D ^ (TM - 1) +
        ((fc + tA) * (2 * tA + 1) + (fc + tA) * (L + N)) * Fintype.card D ^ (TM - 1) := by
        refine Nat.add_le_add ?_ ?_
        · exact le_trans (answerTape_pairCollision_card_le TM (slotPairs TM tA) slotPairs_distinct)
            (Nat.mul_le_mul_right _ (slotPairs_card_le TM tA))
        · have h := answerTape_hitFamily_card_le (D := D) TM (hits fc tA (L + N)) (hitSlot hF)
            (S.hitTarget codec dec rootOf ct hF)
            (fun p _ => S.hitTarget_isHitTarget codec dec rootOf ct hF p)
          rwa [hits_card] at h
    _ = adaptiveNumerator fc tA (L + N) * Fintype.card D ^ (TM - 1) := by
        unfold adaptiveNumerator; ring

end Merkle

end Setup

/-! ## 4. The composed count -/

namespace Setup

section Composed

variable {Enc D Pt C Out Key Salt M : Type} [DecidableEq Enc] [Inhabited D] [DecidableEq Pt]
  [DecidableEq Key] {tA N L TM TC fc : ℕ}
variable (S : Setup Enc D Pt C Out Key tA N L)

open scoped Classical in
/-- **The Fiat–Shamir side at a fixed Merkle tape**, as a `Bcs.CtxGrinding` whose context is the
cut-trace context. -/
def grinding [Fintype C] (mt : Fin TM → D) (Bad : Key × List (Enc × D) → Pt → C → Prop)
    (beta : Pt → ℕ) (hbad : ∀ κ q, (univ.filter fun c : C => Bad κ q c).card ≤ beta q) :
    CtxGrinding C Pt Out Key (Key × List (Enc × D)) N L TC where
  adversary := S.search mt
  dflt := S.dflt
  hashInput := S.hashInput
  key := S.key
  ctxAt := S.ctxAt mt
  ctxAt_congr tape tape' j q hq hag := S.ctxAt_congr mt tape tape' j q hq hag
  Bad := Bad
  beta := beta
  bad_bound := hbad

open scoped Classical in
theorem grinding_output [Fintype C] (mt : Fin TM → D) (Bad : Key × List (Enc × D) → Pt → C → Prop)
    (beta : Pt → ℕ) (hbad : ∀ κ q, (univ.filter fun c : C => Bad κ q c).card ≤ beta q)
    (ct : Fin TC → C) : (S.grinding mt Bad beta hbad).output ct = S.output mt ct := rfl

variable [DecidableEq D] [Inhabited Salt] [Inhabited M] {n : ℕ}

open scoped Classical in
/--
**A re-committing Fiat–Shamir prover, counted.**  Over the Merkle tape and a challenge tape of
`TC ≥ L + N` slots, for any acceptance event `Acc` that includes the Merkle check, and any failure
predicate `Fails` on the commitment context:

```text
Pr[ Acc  ∧  Fails(context of the proof's key) ]
    ≤  (N · βmax + ∑ k, slotBeta k) / |C|  +  adaptiveNumerator fc tA (L + N) / |D|
```

provided `hchain`: an accepted proof whose opening the cut-trace extraction explains, in a failing
context, has a round-level bad event.  The first term is `Bcs.CtxGrinding.card_mul_le` at each
Merkle tape, the second `merkle_card_le` at each challenge tape.
-/
theorem ratio_le [Fintype C] [DecidableEq C] [Nonempty C] [Fintype D]
    (codec : Codec Salt M D Enc) (dec : RoleDecoders codec)
    (check : Out → Tree Enc D Unit fc) (rootOf : Key → D)
    (claimOf : Out → OpeningClaim n Salt M D)
    (hcheck : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec n (claimOf out).I (claimOf out).a (claimOf out).pf (2 * n)
          fun _ => default).run H).2, qa ∈ ((check out).run H).2)
    (Bad : Key × List (Enc × D) → Pt → C → Prop) (beta : Pt → ℕ)
    (hbad : ∀ κ q, (univ.filter fun c : C => Bad κ q c).card ≤ beta q)
    (betaMax : ℕ) (hmax : ∀ q : Pt, beta q ≤ betaMax) (slotBeta : Fin L → ℕ)
    (hslot : ∀ (out : Out) (i : Fin L) (cp : Fin i.val → C),
      beta (S.hashInput out i.val cp) ≤ slotBeta i)
    (hL : 0 < L) (ht : tA ≤ TM) (hF : fc + tA ≤ TM) (hTM : 1 ≤ TM) (hfuel : L + N ≤ TC)
    (Acc : (Fin TM → D) → (Fin TC → C) → Prop) (Fails : Key × List (Enc × D) → Prop)
    (hacc : ∀ mt ct, Acc mt ct → S.MerkleAccepts codec check rootOf claimOf mt ct)
    (hchain : ∀ mt ct, Acc mt ct → S.Explains dec rootOf claimOf mt ct →
      Fails (S.context mt ct) → (S.grinding mt Bad beta hbad).RoundBad ct) :
    ((univ.filter fun ω : (Fin TM → D) × (Fin TC → C) =>
        Acc ω.1 ω.2 ∧ Fails (S.context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ TC)
      ≤ ((N * betaMax + ∑ i, slotBeta i : ℕ) : ℚ) / (Fintype.card C : ℚ)
        + (adaptiveNumerator fc tA (L + N) : ℚ) / (Fintype.card D : ℚ) := by
  classical
  set B := N * betaMax + ∑ i, slotBeta i with hB
  set A := adaptiveNumerator fc tA (L + N) with hA
  have hCpos : 0 < Fintype.card C := Fintype.card_pos
  have hDpos : 0 < Fintype.card D := Fintype.card_pos
  -- split on whether the cut-trace extraction explains the opening
  have hsplit : (univ.filter fun ω : (Fin TM → D) × (Fin TC → C) =>
        Acc ω.1 ω.2 ∧ Fails (S.context ω.1 ω.2)).card
      ≤ (univ.filter fun ω : (Fin TM → D) × (Fin TC → C) =>
          Acc ω.1 ω.2 ∧ S.Explains dec rootOf claimOf ω.1 ω.2 ∧
            Fails (S.context ω.1 ω.2)).card
        + (univ.filter fun ω : (Fin TM → D) × (Fin TC → C) =>
          S.MerkleAccepts codec check rootOf claimOf ω.1 ω.2 ∧
            ¬ S.Explains dec rootOf claimOf ω.1 ω.2).card := by
    refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
    by_cases hex : S.Explains dec rootOf claimOf ω.1 ω.2
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hω.1, hex, hω.2⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hacc _ _ hω.1, hex⟩)
  -- the Fiat–Shamir side, at each Merkle tape
  have hfs : (univ.filter fun ω : (Fin TM → D) × (Fin TC → C) =>
        Acc ω.1 ω.2 ∧ S.Explains dec rootOf claimOf ω.1 ω.2 ∧
          Fails (S.context ω.1 ω.2)).card * Fintype.card C
      ≤ Fintype.card D ^ TM * (B * Fintype.card C ^ TC) := by
    rw [card_filter_prod_fst, Finset.sum_mul]
    calc ∑ mt : Fin TM → D, (univ.filter fun ct : Fin TC → C =>
            Acc mt ct ∧ S.Explains dec rootOf claimOf mt ct ∧
              Fails (S.context mt ct)).card * Fintype.card C
        ≤ ∑ _mt : Fin TM → D, B * Fintype.card C ^ TC := by
          refine Finset.sum_le_sum fun mt _ => ?_
          exact (S.grinding mt Bad beta hbad).card_mul_le betaMax hmax slotBeta hslot hfuel _
            fun ct hct => hchain mt ct hct.1 hct.2.1 hct.2.2
      _ = Fintype.card D ^ TM * (B * Fintype.card C ^ TC) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
            smul_eq_mul]
  -- the Merkle side, at each challenge tape
  have hmk : (univ.filter fun ω : (Fin TM → D) × (Fin TC → C) =>
        S.MerkleAccepts codec check rootOf claimOf ω.1 ω.2 ∧
          ¬ S.Explains dec rootOf claimOf ω.1 ω.2).card
      ≤ Fintype.card C ^ TC * (A * Fintype.card D ^ (TM - 1)) := by
    rw [card_filter_prod_snd]
    calc ∑ ct : Fin TC → C, (univ.filter fun mt : Fin TM → D =>
            S.MerkleAccepts codec check rootOf claimOf mt ct ∧
              ¬ S.Explains dec rootOf claimOf mt ct).card
        ≤ ∑ _ct : Fin TC → C, A * Fintype.card D ^ (TM - 1) :=
          Finset.sum_le_sum fun ct _ =>
            S.merkle_card_le codec dec check rootOf claimOf hcheck hL ht hF ct
      _ = Fintype.card C ^ TC * (A * Fintype.card D ^ (TM - 1)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
            smul_eq_mul]
  -- assemble
  have hc : (0 : ℚ) < (Fintype.card C : ℚ) := by exact_mod_cast hCpos
  have hd : (0 : ℚ) < (Fintype.card D : ℚ) := by exact_mod_cast hDpos
  have hpowD : (Fintype.card D : ℚ) ^ TM = (Fintype.card D : ℚ) ^ (TM - 1) * (Fintype.card D : ℚ) := by
    rw [← pow_succ]; congr 1; omega
  have hsplitq := (Nat.cast_le (α := ℚ)).mpr hsplit
  have hfsq := (Nat.cast_le (α := ℚ)).mpr hfs
  have hmkq := (Nat.cast_le (α := ℚ)).mpr hmk
  push_cast at hsplitq hfsq hmkq
  rw [div_le_iff₀ (mul_pos (pow_pos hd TM) (pow_pos hc TC))]
  have e1 : ((B : ℕ) : ℚ) / (Fintype.card C : ℚ)
      * ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ TC)
      = (Fintype.card D : ℚ) ^ TM * ((B : ℚ) * (Fintype.card C : ℚ) ^ TC)
        / (Fintype.card C : ℚ) := by ring
  have e2 : ((A : ℕ) : ℚ) / (Fintype.card D : ℚ)
      * ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ TC)
      = (Fintype.card C : ℚ) ^ TC * ((A : ℚ) * (Fintype.card D : ℚ) ^ (TM - 1)) := by
    rw [hpowD]; field_simp
  rw [add_mul, e1, e2]
  have hfs' : ((univ.filter fun ω : (Fin TM → D) × (Fin TC → C) =>
        Acc ω.1 ω.2 ∧ S.Explains dec rootOf claimOf ω.1 ω.2 ∧
          Fails (S.context ω.1 ω.2)).card : ℚ)
      ≤ (Fintype.card D : ℚ) ^ TM * ((B : ℚ) * (Fintype.card C : ℚ) ^ TC)
        / (Fintype.card C : ℚ) := by
    rw [le_div_iff₀ hc]; exact hfsq
  linarith

end Composed

end Setup

/-! ## 5. Two commitments under one key: the product counts, and the two-root composition -/

namespace Setup

section Two

variable {Enc D Pt C Out Key : Type} [DecidableEq Enc] [Inhabited D] [DecidableEq Pt]
  [DecidableEq Key] {tA N L TM TC fc : ℕ}
variable (S : Setup Enc D Pt C Out Key tA N L)

open scoped Classical in
/-- **The Fiat–Shamir count over both tapes**: every event forcing a round-level bad event, summed
over Merkle tapes. -/
theorem fs_prod_card_le [Fintype C] [DecidableEq C] [Fintype D]
    (Bad : Key × List (Enc × D) → Pt → C → Prop) (beta : Pt → ℕ)
    (hbad : ∀ κ q, (univ.filter fun c : C => Bad κ q c).card ≤ beta q)
    (betaMax : ℕ) (hmax : ∀ q : Pt, beta q ≤ betaMax) (slotBeta : Fin L → ℕ)
    (hslot : ∀ (out : Out) (i : Fin L) (cp : Fin i.val → C),
      beta (S.hashInput out i.val cp) ≤ slotBeta i)
    (hfuel : L + N ≤ TC) (E : (Fin TM → D) → (Fin TC → C) → Prop)
    (hE : ∀ mt ct, E mt ct → (S.grinding mt Bad beta hbad).RoundBad ct) :
    (univ.filter fun ω : (Fin TM → D) × (Fin TC → C) => E ω.1 ω.2).card * Fintype.card C
      ≤ Fintype.card D ^ TM * ((N * betaMax + ∑ i, slotBeta i) * Fintype.card C ^ TC) := by
  classical
  rw [card_filter_prod_fst, Finset.sum_mul]
  calc ∑ mt : Fin TM → D, (univ.filter fun ct : Fin TC → C => E mt ct).card * Fintype.card C
      ≤ ∑ _mt : Fin TM → D, (N * betaMax + ∑ i, slotBeta i) * Fintype.card C ^ TC :=
        Finset.sum_le_sum fun mt _ =>
          (S.grinding mt Bad beta hbad).card_mul_le betaMax hmax slotBeta hslot hfuel _
            fun ct hct => hE mt ct hct
    _ = Fintype.card D ^ TM * ((N * betaMax + ∑ i, slotBeta i) * Fintype.card C ^ TC) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, smul_eq_mul]

variable [DecidableEq D]

open scoped Classical in
/-- **The Merkle count over both tapes**, for one root reader and one opening claim. -/
theorem merkle_prod_card_le [Fintype C] [Fintype D] {Salt M : Type} [Inhabited Salt]
    [Inhabited M] {n : ℕ} (codec : Codec Salt M D Enc) (dec : RoleDecoders codec)
    (check : Out → Tree Enc D Unit fc) (rootOf : Key → D)
    (claimOf : Out → OpeningClaim n Salt M D)
    (hcheck : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec n (claimOf out).I (claimOf out).a (claimOf out).pf (2 * n)
          fun _ => default).run H).2, qa ∈ ((check out).run H).2)
    (hL : 0 < L) (ht : tA ≤ TM) (hF : fc + tA ≤ TM) :
    (univ.filter fun ω : (Fin TM → D) × (Fin TC → C) =>
        S.MerkleAccepts codec check rootOf claimOf ω.1 ω.2 ∧
          ¬ S.Explains dec rootOf claimOf ω.1 ω.2).card
      ≤ Fintype.card C ^ TC * (adaptiveNumerator fc tA (L + N) * Fintype.card D ^ (TM - 1)) := by
  classical
  rw [card_filter_prod_snd]
  calc ∑ ct : Fin TC → C, (univ.filter fun mt : Fin TM → D =>
          S.MerkleAccepts codec check rootOf claimOf mt ct ∧
            ¬ S.Explains dec rootOf claimOf mt ct).card
      ≤ ∑ _ct : Fin TC → C, adaptiveNumerator fc tA (L + N) * Fintype.card D ^ (TM - 1) :=
        Finset.sum_le_sum fun ct _ =>
          S.merkle_card_le codec dec check rootOf claimOf hcheck hL ht hF ct
    _ = Fintype.card C ^ TC * (adaptiveNumerator fc tA (L + N) * Fintype.card D ^ (TM - 1)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, smul_eq_mul]

open scoped Classical in
/--
**Two Merkle commitments under one key, counted.**  `ratio_le` with two root readers and two
opening claims checked against one Merkle oracle (the two codecs share the hash): a proof both of
whose openings verify, and whose failure predicate holds in the joint context, costs

```text
(N · βmax + ∑ k, slotBeta k) / |C|  +  2 · adaptiveNumerator fc tA (L + N) / |D|.
```

The two Merkle terms are one cut-trace extraction per root, both at the cut of the joint key.
-/
theorem ratio_le_two [Fintype C] [DecidableEq C] [Nonempty C] [Fintype D]
    {Salt₁ M₁ Salt₂ M₂ : Type} [Inhabited Salt₁] [Inhabited M₁] [Inhabited Salt₂] [Inhabited M₂]
    {n₁ n₂ : ℕ}
    (codec₁ : Codec Salt₁ M₁ D Enc) (dec₁ : RoleDecoders codec₁)
    (codec₂ : Codec Salt₂ M₂ D Enc) (dec₂ : RoleDecoders codec₂)
    (check : Out → Tree Enc D Unit fc) (rootOf₁ rootOf₂ : Key → D)
    (claimOf₁ : Out → OpeningClaim n₁ Salt₁ M₁ D) (claimOf₂ : Out → OpeningClaim n₂ Salt₂ M₂ D)
    (hcheck₁ : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec₁ n₁ (claimOf₁ out).I (claimOf₁ out).a (claimOf₁ out).pf (2 * n₁)
          fun _ => default).run H).2, qa ∈ ((check out).run H).2)
    (hcheck₂ : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec₂ n₂ (claimOf₂ out).I (claimOf₂ out).a (claimOf₂ out).pf (2 * n₂)
          fun _ => default).run H).2, qa ∈ ((check out).run H).2)
    (Bad : Key × List (Enc × D) → Pt → C → Prop) (beta : Pt → ℕ)
    (hbad : ∀ κ q, (univ.filter fun c : C => Bad κ q c).card ≤ beta q)
    (betaMax : ℕ) (hmax : ∀ q : Pt, beta q ≤ betaMax) (slotBeta : Fin L → ℕ)
    (hslot : ∀ (out : Out) (i : Fin L) (cp : Fin i.val → C),
      beta (S.hashInput out i.val cp) ≤ slotBeta i)
    (hL : 0 < L) (ht : tA ≤ TM) (hF : fc + tA ≤ TM) (hTM : 1 ≤ TM) (hfuel : L + N ≤ TC)
    (Acc : (Fin TM → D) → (Fin TC → C) → Prop) (Fails : (Fin TM → D) → (Fin TC → C) → Prop)
    (hacc₁ : ∀ mt ct, Acc mt ct → S.MerkleAccepts codec₁ check rootOf₁ claimOf₁ mt ct)
    (hacc₂ : ∀ mt ct, Acc mt ct → S.MerkleAccepts codec₂ check rootOf₂ claimOf₂ mt ct)
    (hchain : ∀ mt ct, Acc mt ct → S.Explains dec₁ rootOf₁ claimOf₁ mt ct →
      S.Explains dec₂ rootOf₂ claimOf₂ mt ct → Fails mt ct →
      (S.grinding mt Bad beta hbad).RoundBad ct) :
    ((univ.filter fun ω : (Fin TM → D) × (Fin TC → C) => Acc ω.1 ω.2 ∧ Fails ω.1 ω.2).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ TC)
      ≤ ((N * betaMax + ∑ i, slotBeta i : ℕ) : ℚ) / (Fintype.card C : ℚ)
        + 2 * ((adaptiveNumerator fc tA (L + N) : ℚ) / (Fintype.card D : ℚ)) := by
  classical
  set B := N * betaMax + ∑ i, slotBeta i with hB
  set A := adaptiveNumerator fc tA (L + N) with hA
  have hsplit : (univ.filter fun ω : (Fin TM → D) × (Fin TC → C) =>
        Acc ω.1 ω.2 ∧ Fails ω.1 ω.2).card
      ≤ (univ.filter fun ω : (Fin TM → D) × (Fin TC → C) =>
          Acc ω.1 ω.2 ∧ S.Explains dec₁ rootOf₁ claimOf₁ ω.1 ω.2 ∧
            S.Explains dec₂ rootOf₂ claimOf₂ ω.1 ω.2 ∧ Fails ω.1 ω.2).card
        + (univ.filter fun ω : (Fin TM → D) × (Fin TC → C) =>
          S.MerkleAccepts codec₁ check rootOf₁ claimOf₁ ω.1 ω.2 ∧
            ¬ S.Explains dec₁ rootOf₁ claimOf₁ ω.1 ω.2).card
        + (univ.filter fun ω : (Fin TM → D) × (Fin TC → C) =>
          S.MerkleAccepts codec₂ check rootOf₂ claimOf₂ ω.1 ω.2 ∧
            ¬ S.Explains dec₂ rootOf₂ claimOf₂ ω.1 ω.2).card := by
    refine le_trans (Finset.card_le_card ?_)
      (le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right (Finset.card_union_le _ _) _))
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
    by_cases hex₁ : S.Explains dec₁ rootOf₁ claimOf₁ ω.1 ω.2
    · by_cases hex₂ : S.Explains dec₂ rootOf₂ claimOf₂ ω.1 ω.2
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hω.1, hex₁, hex₂, hω.2⟩))
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hacc₂ _ _ hω.1, hex₂⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hacc₁ _ _ hω.1, hex₁⟩))
  have hfs : (univ.filter fun ω : (Fin TM → D) × (Fin TC → C) =>
        Acc ω.1 ω.2 ∧ S.Explains dec₁ rootOf₁ claimOf₁ ω.1 ω.2 ∧
          S.Explains dec₂ rootOf₂ claimOf₂ ω.1 ω.2 ∧ Fails ω.1 ω.2).card * Fintype.card C
      ≤ Fintype.card D ^ TM * (B * Fintype.card C ^ TC) :=
    le_trans (Nat.mul_le_mul_right _ (Finset.card_le_card fun ω hω => by
        simp only [Finset.mem_filter] at hω ⊢; exact hω))
      (S.fs_prod_card_le Bad beta hbad betaMax hmax slotBeta hslot hfuel
        (fun mt ct => Acc mt ct ∧ S.Explains dec₁ rootOf₁ claimOf₁ mt ct ∧
          S.Explains dec₂ rootOf₂ claimOf₂ mt ct ∧ Fails mt ct)
        (fun mt ct h => hchain mt ct h.1 h.2.1 h.2.2.1 h.2.2.2))
  have hm₁ := S.merkle_prod_card_le (TC := TC) codec₁ dec₁ check rootOf₁ claimOf₁ hcheck₁ hL ht hF
  have hm₂ := S.merkle_prod_card_le (TC := TC) codec₂ dec₂ check rootOf₂ claimOf₂ hcheck₂ hL ht hF
  have hc : (0 : ℚ) < (Fintype.card C : ℚ) := by exact_mod_cast Fintype.card_pos
  have hd : (0 : ℚ) < (Fintype.card D : ℚ) := by exact_mod_cast Fintype.card_pos
  have hpowD : (Fintype.card D : ℚ) ^ TM
      = (Fintype.card D : ℚ) ^ (TM - 1) * (Fintype.card D : ℚ) := by
    rw [← pow_succ]; congr 1; omega
  have hsplitq := (Nat.cast_le (α := ℚ)).mpr hsplit
  have hfsq := (Nat.cast_le (α := ℚ)).mpr hfs
  have hm₁q := (Nat.cast_le (α := ℚ)).mpr hm₁
  have hm₂q := (Nat.cast_le (α := ℚ)).mpr hm₂
  push_cast at hsplitq hfsq hm₁q hm₂q
  rw [div_le_iff₀ (mul_pos (pow_pos hd TM) (pow_pos hc TC))]
  have e1 : ((B : ℕ) : ℚ) / (Fintype.card C : ℚ)
      * ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ TC)
      = (Fintype.card D : ℚ) ^ TM * ((B : ℚ) * (Fintype.card C : ℚ) ^ TC)
        / (Fintype.card C : ℚ) := by ring
  have e2 : 2 * (((A : ℕ) : ℚ) / (Fintype.card D : ℚ))
      * ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ TC)
      = 2 * ((Fintype.card C : ℚ) ^ TC * ((A : ℚ) * (Fintype.card D : ℚ) ^ (TM - 1))) := by
    rw [hpowD]; field_simp
  rw [add_mul, e1, e2]
  have hfs' : ((univ.filter fun ω : (Fin TM → D) × (Fin TC → C) =>
        Acc ω.1 ω.2 ∧ S.Explains dec₁ rootOf₁ claimOf₁ ω.1 ω.2 ∧
          S.Explains dec₂ rootOf₂ claimOf₂ ω.1 ω.2 ∧ Fails ω.1 ω.2).card : ℚ)
      ≤ (Fintype.card D : ℚ) ^ TM * ((B : ℚ) * (Fintype.card C : ℚ) ^ TC)
        / (Fintype.card C : ℚ) := by
    rw [le_div_iff₀ hc]; exact hfsq
  linarith

end Two

end Setup

end Bcs.AdaptiveCommit
