import Lfzk.RbrZkSplit
import Bcs.WeightedTerminal
import Bcs.PotentialChain

/-!
# A terminal-pair doom state for the zero-query Fiat–Shamir case

The ordinary round-by-round state may escape at Ligero's combination
challenge.  For a fresh challenge followed by a fresh query, the useful
state instead remains doomed through the combination challenge whenever the
built system has no satisfying decoded candidate.  It then charges the
accepted query answers *on average over that challenge*.

The verifier transitions are unchanged: only the proof's wrong-state marker
and its accounting differ.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.RbrZkFlat

open Finset Lfzk.RbrZkLongfellow Lfzk.RbrZkSplit
open scoped Classical

variable {C F X Q Msg Gpt Lift : Type} [Fintype C] [Field F] [Fintype F] [DecidableEq F]
  [SumcheckInterp F]
variable {M ninp logw logc nl : ℕ} {w : ℕ → ℕ}
variable [Fintype Gpt] [DecidableEq Gpt] [DecidableEq X] [Fintype Q] [DecidableEq Q]
variable {V : ZkCode C F X Q Msg Gpt M ninp logw logc}
variable {asg : Lift → LigeroAssignment ninp M F}

/-- Keep the built system doomed through the Ligero challenge.  A terminal
query is the only Ligero transition that can then shed doom. -/
noncomputable def flatData (LD : ZkLigeroData C X Q Msg V asg) :
    ZkLigeroData C X Q Msg V asg where
  LigDoomed sys _ := Fits V sys ∧ NoSat asg sys
  accepting := LD.accepting
  escaping _ := ∅
  hesc := by
    intro sys hf hn _ h
    exact (h ⟨hf, hn⟩).elim
  bq := Fintype.card Q
  hbq := by
    intro _ _ _ _ _ _
    exact Finset.card_le_card (Finset.subset_univ _)

omit [Fintype C] [Fintype F] [DecidableEq F] [Fintype Gpt]
  [DecidableEq Gpt] [DecidableEq X] [DecidableEq Q] in
theorem steps_flatData (LD : ZkLigeroData C X Q Msg V asg) (ms : ℕ → Msg) :
    steps (nl := nl) (w := w) V (flatData LD) ms =
      steps (nl := nl) (w := w) V LD ms := rfl

omit [Fintype C] [Fintype F] [DecidableEq F] [SumcheckInterp F]
  [Fintype Gpt] [DecidableEq Gpt] [DecidableEq X] [DecidableEq Q] in
/-- In the terminal-pair doom state, the Ligero combination challenge never
escapes doom.  At a built system, doom for the phantom gives `Fits`, and
doom for every real lift gives `NoSat`; the challenge transition preserves
both facts for every decoded challenge. -/
theorem flat_challenge_preserves_doom
    (LD : ZkLigeroData C X Q Msg V asg)
    (H : ZkHonest F Lift logw logc) (Sat : Lift → Prop)
    (s : ZkState M ninp logw logc F X) (c : C)
    (hdoom : ∀ cand : Option Lift,
      ZkWrong V H asg Sat (flatData LD).LigDoomed cand s) :
    ∀ cand : Option Lift,
      ZkWrong V H asg Sat (flatData LD).LigDoomed cand
        (zkLigChallenge V c s) := by
  cases s with
  | built sys =>
      have hf : Fits V sys := hdoom none
      have hn : NoSat asg sys := by
        intro ℓ
        exact (hdoom (some ℓ)).2
      intro cand
      simpa only [zkLigChallenge, ZkWrong, flatData] using
        (show Fits V sys ∧ NoSat asg sys from ⟨hf, hn⟩)
  | start => intro cand; simp [zkLigChallenge, ZkWrong]
  | running zs => intro cand; simp [zkLigChallenge, ZkWrong]
  | challenged sys x => intro cand; simp [zkLigChallenge, ZkWrong]
  | accepted => intro cand; simp [zkLigChallenge, ZkWrong]
  | failed => intro cand; simp [zkLigChallenge, ZkWrong]

omit [Fintype C] [Fintype F] [DecidableEq F] [Fintype Gpt]
  [DecidableEq Gpt] [DecidableEq X] [DecidableEq Q] in
/-- The preceding fact at the exact penultimate role of the Longfellow
claim chain.  This is the premise used by the global potential telescope. -/
theorem flat_chain_challenge_preserves_doom
    (LD : ZkLigeroData C X Q Msg V asg)
    (H : ZkHonest F Lift logw logc) (Sat : Lift → Prop)
    (ms : ℕ → Msg)
    (pref : Fin (Rounds.Role.layerBase w nl + 1) → C) (c : C) :
    (chain (nl := nl) (w := w) V H asg Sat (flatData LD) ms).doomed
      (Rounds.Role.layerBase w nl + 1) pref →
    (chain (nl := nl) (w := w) V H asg Sat (flatData LD) ms).doomed
      (Rounds.Role.layerBase w nl + 2) (Bcs.extend pref c) := by
  let u := Rounds.Role.layerBase w nl + 1
  have hu : u < Rounds.Role.length nl w := by
    dsimp [u, Rounds.Role.length]
    omega
  let idx : Fin (Rounds.Role.length nl w) := ⟨u, hu⟩
  have hrole : Rounds.Role.indexEquiv.symm idx = .ligeroChallenge := by
    have heq : idx = Rounds.Role.indexEquiv (.ligeroChallenge : Rounds.Role nl w) := by
      apply Fin.ext
      rfl
    rw [heq]
    exact Rounds.Role.indexEquiv.symm_apply_apply _
  intro hdoom cand
  let ch := chain (nl := nl) (w := w) V H asg Sat (flatData LD) ms
  change ch.Wrong cand (ch.state (idx.val + 1) (Bcs.extend pref c))
  rw [ch.state_extend idx pref c]
  simp only [ch, chain, RbrLayerStepS.layerStepChainS, RbrLayerStepS.stepAtS,
    hrole, steps, zkSteps]
  exact flat_challenge_preserves_doom LD H Sat (ch.state idx.val pref) c hdoom cand

/-- Doom along a concrete verifier tape, with an arbitrary value beyond the
protocol's final prefix. -/
def prefixDoom {T : ℕ} {S Cand : Type} (ch : Bcs.ClaimChain C T S Cand)
    (tape : Fin T → C) (j : ℕ) : Prop :=
  if hj : j ≤ T then ch.doomed j (Bcs.trunc tape j hj) else False

omit [Fintype C] [Fintype F] [DecidableEq F] [Fintype Gpt]
  [DecidableEq Gpt] [DecidableEq X] [DecidableEq Q] in
/-- The end-to-end deterministic potential telescope for the actual
Longfellow role order.  Earlier field roles pay unit escape charge; the
combination challenge and query split the terminal unit by any `ψ ≤ 1`.
The start/end doom premises are those already supplied by the extraction
chain, so this lemma changes no verifier transition. -/
theorem flat_chain_telescope
    (LD : ZkLigeroData C X Q Msg V asg)
    (H : ZkHonest F Lift logw logc) (Sat : Lift → Prop)
    (ms : ℕ → Msg)
    (tape : Fin (Rounds.Role.length nl w) → C)
    (ψ : ℚ) (hψ : ψ ≤ 1)
    (hstart : (chain (nl := nl) (w := w) V H asg Sat (flatData LD) ms).doomed
      0 (Bcs.trunc tape 0 (Nat.zero_le _)))
    (hend : ¬ (chain (nl := nl) (w := w) V H asg Sat (flatData LD) ms).doomed
      (Rounds.Role.length nl w) (Bcs.trunc tape (Rounds.Role.length nl w) le_rfl)) :
    let ch := chain (nl := nl) (w := w) V H asg Sat (flatData LD) ms
    let doom := prefixDoom ch tape
    let u := Rounds.Role.layerBase w nl + 1
    1 ≤ (∑ i ∈ range u,
      if doom i ∧ ¬ doom (i + 1) then (1 : ℚ) else 0) +
      (if doom u then ψ else 0) +
      (if doom (u + 1) ∧ ¬ doom (u + 2) then 1 - ψ else 0) := by
  let ch := chain (nl := nl) (w := w) V H asg Sat (flatData LD) ms
  let doom := prefixDoom ch tape
  let u := Rounds.Role.layerBase w nl + 1
  have hu : u < Rounds.Role.length nl w := by
    dsimp [u, Rounds.Role.length]
    omega
  let idx : Fin (Rounds.Role.length nl w) := ⟨u, hu⟩
  have hlength : u + 2 = Rounds.Role.length nl w := by
    dsimp [u, Rounds.Role.length]
  have hd0 : doom 0 := by
    simpa only [doom, prefixDoom, dif_pos (Nat.zero_le _)] using hstart
  have hdend : ¬ doom (u + 2) := by
    simpa only [doom, prefixDoom, hlength, dif_pos le_rfl] using hend
  have hdchal : doom u → doom (u + 1) := by
    intro hd
    have hd' : ch.doomed u (Sumcheck.extract_prefix tape idx) := by
      simpa only [doom, prefixDoom, dif_pos (le_of_lt hu),
        ← Bcs.trunc_eq_extract_prefix tape idx] using hd
    have hpres := flat_chain_challenge_preserves_doom LD H Sat ms
      (Sumcheck.extract_prefix tape idx) (tape idx) hd'
    have hpref : Bcs.trunc tape (u + 1) hu =
        Bcs.extend (Sumcheck.extract_prefix tape idx) (tape idx) := by
      exact Bcs.trunc_succ tape idx
    dsimp only [doom, prefixDoom]
    rw [dif_pos (le_of_lt (by omega : u + 1 < Rounds.Role.length nl w)), hpref]
    exact hpres
  exact Bcs.PotentialChain.field_challenge_query_telescope
    u doom ψ hψ hd0 hdchal hdend

omit [Fintype C] [Fintype F] [DecidableEq F] [Fintype Gpt]
  [DecidableEq Gpt] [DecidableEq X] [DecidableEq Q] in
/-- The same actual Longfellow path partition without a potential split.
The last branch is one joint challenge/query event, so an interactive
certificate may bound it with its flat pair probability. -/
theorem flat_chain_field_or_terminal
    (LD : ZkLigeroData C X Q Msg V asg)
    (H : ZkHonest F Lift logw logc) (Sat : Lift → Prop)
    (ms : ℕ → Msg)
    (tape : Fin (Rounds.Role.length nl w) → C)
    (hstart : (chain (nl := nl) (w := w) V H asg Sat (flatData LD) ms).doomed
      0 (Bcs.trunc tape 0 (Nat.zero_le _)))
    (hend : ¬ (chain (nl := nl) (w := w) V H asg Sat (flatData LD) ms).doomed
      (Rounds.Role.length nl w) (Bcs.trunc tape (Rounds.Role.length nl w) le_rfl)) :
    let ch := chain (nl := nl) (w := w) V H asg Sat (flatData LD) ms
    let doom := prefixDoom ch tape
    let u := Rounds.Role.layerBase w nl + 1
    (∃ i < u, doom i ∧ ¬ doom (i + 1)) ∨
      (doom (u + 1) ∧ ¬ doom (u + 2)) := by
  let ch := chain (nl := nl) (w := w) V H asg Sat (flatData LD) ms
  let doom := prefixDoom ch tape
  let u := Rounds.Role.layerBase w nl + 1
  have hu : u < Rounds.Role.length nl w := by
    dsimp [u, Rounds.Role.length]
    omega
  let idx : Fin (Rounds.Role.length nl w) := ⟨u, hu⟩
  have hlength : u + 2 = Rounds.Role.length nl w := by
    dsimp [u, Rounds.Role.length]
  have hd0 : doom 0 := by
    simpa only [doom, prefixDoom, dif_pos (Nat.zero_le _)] using hstart
  have hdend : ¬ doom (u + 2) := by
    simpa only [doom, prefixDoom, hlength, dif_pos le_rfl] using hend
  have hdchal : doom u → doom (u + 1) := by
    intro hd
    have hd' : ch.doomed u (Sumcheck.extract_prefix tape idx) := by
      simpa only [doom, prefixDoom, dif_pos (le_of_lt hu),
        ← Bcs.trunc_eq_extract_prefix tape idx] using hd
    have hpres := flat_chain_challenge_preserves_doom LD H Sat ms
      (Sumcheck.extract_prefix tape idx) (tape idx) hd'
    have hpref : Bcs.trunc tape (u + 1) hu =
        Bcs.extend (Sumcheck.extract_prefix tape idx) (tape idx) := by
      exact Bcs.trunc_succ tape idx
    dsimp only [doom, prefixDoom]
    rw [dif_pos (le_of_lt (by omega : u + 1 < Rounds.Role.length nl w)), hpref]
    exact hpres
  exact Bcs.PotentialChain.field_or_terminal_query u doom hd0 hdchal hdend

omit [Fintype C] [Fintype F] [DecidableEq F] [Fintype Gpt]
  [DecidableEq Gpt] [DecidableEq X] [DecidableEq Q] in
/-- An accepted full Longfellow transcript with no satisfying lift pays the
potential telescope.  Extraction failure is represented by the same
committed lift list as the existing sumcheck proof; verifier transitions are
those of `LD`. -/
theorem accepted_noSat_pays_potential
    (LD : ZkLigeroData C X Q Msg V asg)
    (H : ZkHonest F Lift logw logc) (Sat : Lift → Prop)
    (ms : ℕ → Msg)
    {Acc : (Fin (Rounds.Role.length nl w) → C) → Prop}
    (hright : ZkRight (nl := nl) (w := w) LD ms Acc)
    (hfalse : ∀ ℓ : Lift, ¬ Sat ℓ)
    (tape : Fin (Rounds.Role.length nl w) → C) (hacc : Acc tape)
    (ψ : ℚ) (hψ : ψ ≤ 1) :
    let ch := chain (nl := nl) (w := w) V H asg Sat (flatData LD) ms
    let doom := prefixDoom ch tape
    let u := Rounds.Role.layerBase w nl + 1
    1 ≤ (∑ i ∈ range u,
      if doom i ∧ ¬ doom (i + 1) then (1 : ℚ) else 0) +
      (if doom u then ψ else 0) +
      (if doom (u + 1) ∧ ¬ doom (u + 2) then 1 - ψ else 0) := by
  let ch := chain (nl := nl) (w := w) V H asg Sat (flatData LD) ms
  have hstart : ch.doomed 0 (Bcs.trunc tape 0 (Nat.zero_le _)) := by
    intro cand
    cases cand with
    | none => trivial
    | some ℓ => exact hfalse ℓ
  have hend : ¬ ch.doomed (Rounds.Role.length nl w)
      (Bcs.trunc tape (Rounds.Role.length nl w) le_rfl) := by
    have hrightFlat : ZkRight (nl := nl) (w := w) (flatData LD) ms Acc := by
      simpa only [ZkRight, steps_flatData] using hright
    obtain ⟨cand, hcand⟩ := right_of_zkAccepts
      (V := V) (H := H) (asg := asg) (Sat := Sat)
      (flatData LD) ms hrightFlat tape hacc
    exact fun hall => hcand (hall cand)
  exact flat_chain_telescope LD H Sat ms tape ψ hψ hstart hend

omit [Fintype C] [Fintype F] [DecidableEq F] [Fintype Gpt]
  [DecidableEq Gpt] [DecidableEq X] [DecidableEq Q] in
/-- Acceptance and failure of the committed-lift extractor imply either a
field escape or one bad final challenge/query pair.  This is the event
inclusion required before charging the flat Ligero IOP envelope. -/
theorem accepted_noSat_field_or_terminal
    (LD : ZkLigeroData C X Q Msg V asg)
    (H : ZkHonest F Lift logw logc) (Sat : Lift → Prop)
    (ms : ℕ → Msg)
    {Acc : (Fin (Rounds.Role.length nl w) → C) → Prop}
    (hright : ZkRight (nl := nl) (w := w) LD ms Acc)
    (hfalse : ∀ ℓ : Lift, ¬ Sat ℓ)
    (tape : Fin (Rounds.Role.length nl w) → C) (hacc : Acc tape) :
    let ch := chain (nl := nl) (w := w) V H asg Sat (flatData LD) ms
    let doom := prefixDoom ch tape
    let u := Rounds.Role.layerBase w nl + 1
    (∃ i < u, doom i ∧ ¬ doom (i + 1)) ∨
      (doom (u + 1) ∧ ¬ doom (u + 2)) := by
  let ch := chain (nl := nl) (w := w) V H asg Sat (flatData LD) ms
  have hstart : ch.doomed 0 (Bcs.trunc tape 0 (Nat.zero_le _)) := by
    intro cand
    cases cand with
    | none => trivial
    | some ℓ => exact hfalse ℓ
  have hend : ¬ ch.doomed (Rounds.Role.length nl w)
      (Bcs.trunc tape (Rounds.Role.length nl w) le_rfl) := by
    have hrightFlat : ZkRight (nl := nl) (w := w) (flatData LD) ms Acc := by
      simpa only [ZkRight, steps_flatData] using hright
    obtain ⟨cand, hcand⟩ := right_of_zkAccepts
      (V := V) (H := H) (asg := asg) (Sat := Sat)
      (flatData LD) ms hrightFlat tape hacc
    exact fun hall => hcand (hall cand)
  exact flat_chain_field_or_terminal LD H Sat ms tape hstart hend

omit [Fintype C] [Fintype F] [DecidableEq F] [Fintype Gpt]
  [DecidableEq Gpt] [DecidableEq X] [DecidableEq Q] in
theorem right_flatData (LD : ZkLigeroData C X Q Msg V asg) (ms : ℕ → Msg)
    {Acc : (Fin (Rounds.Role.length nl w) → C) → Prop}
    (h : ZkRight (nl := nl) (w := w) LD ms Acc) :
    ZkRight (nl := nl) (w := w) (flatData LD) ms Acc := by
  simpa only [ZkRight, steps_flatData] using h

/-- The field-round budgets of an existing proof also apply to the terminal
state.  The combination challenge costs zero; the query slot gets the
trivial budget here, to be sharpened by expected-budget counting. -/
def flatBudgets {H : ZkHonest F Lift logw logc} {Sat : Lift → Prop}
    {FD : ZkFieldData C F X Q Msg Gpt Lift M ninp logw logc nl w V H asg Sat}
    (LD : ZkLigeroData C X Q Msg V asg)
    {bpair bround bin blig bquery : ℕ}
    (hB : ZkBudgets FD LD bpair bround bin blig bquery) :
    ZkBudgets FD (flatData LD) bpair bround bin 0 (FD.kq * Fintype.card Q) where
  hbp0 := hB.hbp0
  hbp1 := hB.hbp1
  hbround := hB.hbround
  hbin := hB.hbin
  hblig := by
    intro _ _ _
    simp [flatData]
  hbquery := by
    simp [flatData]

end Lfzk.RbrZkFlat
