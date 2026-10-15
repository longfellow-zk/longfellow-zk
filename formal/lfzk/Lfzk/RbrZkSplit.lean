import Lfzk.RbrZkLongfellow

/-!
# The zero-knowledge LayerStep, assembled: field half, Ligero half, budgets, round by round

`Lfzk.RbrZkLongfellow` has the zero-knowledge verifier's transitions and each slot's escape count.
This file bundles their inputs the way `Lfzk.RbrSplit` bundles the clear verifier's, and assembles
the round-by-round object.

* `ZkFieldData` — the analysis data of the field half at one commitment context: the boundary facts
  (`ZkBoundary`), the layer-0 count `hinit`, and the four decoders' balances.  The verifier's code `V`,
  the honest values `H`, the candidates' assignments `asg` and the satisfaction predicate `Sat` are
  parameters, as in `RbrSplit.FieldData`;
* `ZkLigeroData` — the Ligero half, **indexed by the built system**: a doom predicate on
  `(sys, x)`, an escaping set per system that contains every undoomed challenge of every system no
  candidate satisfies (`hesc`), and a query bound at doomed challenges (`hbq`).  The query test may
  read the query slot's message (the Ligero response);
* `ZkBudgets` — the six inequalities, the Ligero one uniform over the systems no candidate
  satisfies;
* `rbr` — the round-by-round object (`RbrZkLongfellow.layerStepRbrW`): the field slots pay the list
  factor `|Lift|` (the phantom candidate pays nothing), the two Ligero slots pay `blig` and `bquery`;
* `ratio_le` — **the zero-knowledge LayerStep's ratio (Checkpoint B)**:

```text
Pr[ ZK LayerStep accepts  ∧  no candidate satisfies the circuit ]
    ≤  ( |Lift| · (nl·bpair + (∑ w)·bround + bin)  +  blig  +  bquery ) / |C|
```

## Where `hfalse` went

The clear verifier's theorem needs `hfalse`: the Ligero statement fixed by the commitment is false
when extraction fails.  Here the statement is the one the transcript builds, and its doom is the
state function's: `built sys` is doomed exactly when no candidate's assignment satisfies `sys`
(`RbrZkLongfellow.doomed_built_iff`), which the field slots' budgets *derive* from "no candidate
satisfies the circuit".  So the Ligero half is asked for its classifier only at systems no candidate
satisfies (`hesc`, `hblig`), and `Lfzk.ZkLigeroV1` builds it there from
`LigeroV1Rows.Row.rbr_soundness` at `NoDecodedSolution` — no falsity premise is left.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.RbrZkSplit

open Finset Sumcheck RbrLongfellow Lfzk.RbrLayerStepS Lfzk.RbrZkLongfellow
open scoped Classical

variable {C F X Q Msg Gpt Lift : Type} [Fintype C] [Field F] [Fintype F] [DecidableEq F]
  [SumcheckInterp F]
variable {M ninp logw logc nl : ℕ} {w : ℕ → ℕ}

/-! ## 1. The two halves and the budgets -/

/-- **The field half of the zero-knowledge LayerStep at one context.** -/
structure ZkFieldData (C F X Q Msg Gpt Lift : Type) [Fintype C] [Field F] [Fintype F]
    [DecidableEq F] [Fintype Gpt] [DecidableEq Gpt] [DecidableEq X] [Fintype Q] [DecidableEq Q]
    (M ninp logw logc nl : ℕ) (w : ℕ → ℕ) (V : ZkCode C F X Q Msg Gpt M ninp logw logc)
    (H : ZkHonest F Lift logw logc) (asg : Lift → LigeroAssignment ninp M F) (Sat : Lift → Prop) where
  /-- The boundary facts. -/
  B : ZkBoundary V H asg nl w
  /-- The layer-0 count: triples `(G, β, α)` at which the honest claim of an unsatisfied candidate
  with no pending assertion below the output vanishes (`hinit_of_output` supplies it). -/
  binit : ℕ
  hinit : ∀ ℓ : Lift, ¬ Sat ℓ → (∀ j, ¬ H.Pend ℓ j []) →
    (univ.filter fun p : Gpt × F × F =>
      H.sum ℓ 0 (V.st0 p.1) p.2.1 p.2.2 [] = 0).card ≤ binit
  /-- The decoders' balances. -/
  kinit : ℕ
  kpair : ℕ
  k : ℕ
  kchal : ℕ
  kq : ℕ
  hbalInit : ∀ y : Gpt × F × F, (univ.filter fun c : C => V.decodeInit c = y).card ≤ kinit
  hbalPair : ∀ y : F × F, (univ.filter fun c : C => V.decodePair c = y).card ≤ kpair
  hbalF : ∀ y : F, (univ.filter fun c : C => V.decodeF c = y).card ≤ k
  hbalChal : ∀ y : X, (univ.filter fun c : C => V.decodeChal c = y).card ≤ kchal
  hbalQuery : ∀ y : Q, (univ.filter fun c : C => V.decodeQuery c = y).card ≤ kq

/-- **The Ligero half of the zero-knowledge LayerStep at one context**, indexed by the built
system.  The query test reads the prefix and the query slot's message. -/
structure ZkLigeroData (C X Q Msg : Type) {F Gpt : Type} [Field F] {M ninp logw logc : ℕ}
    {Lift : Type} (V : ZkCode C F X Q Msg Gpt M ninp logw logc)
    (asg : Lift → LigeroAssignment ninp M F) where
  /-- The Ligero classifier's doom, per system. -/
  LigDoomed : LigeroSystem ninp M F → X → Prop
  /-- The queries the opened columns pass, per prefix, message, system and challenge. -/
  accepting : ∀ m : ℕ, (Fin m → C) → Msg → LigeroSystem ninp M F → X → Finset Q
  /-- The escaping challenges, per system. -/
  escaping : LigeroSystem ninp M F → Finset X
  hesc : ∀ sys, Fits V sys → NoSat asg sys → ∀ x, ¬ LigDoomed sys x → x ∈ escaping sys
  /-- A bound on a doomed challenge's accepting-query count, at every message. -/
  bq : ℕ
  hbq : ∀ (m : ℕ) (pref : Fin m → C) (msg : Msg) (sys : LigeroSystem ninp M F) (x : X),
    LigDoomed sys x → (accepting m pref msg sys x).card ≤ bq

variable [Fintype Gpt] [DecidableEq Gpt] [DecidableEq X] [Fintype Q] [DecidableEq Q]
variable {V : ZkCode C F X Q Msg Gpt M ninp logw logc} {H : ZkHonest F Lift logw logc}
  {asg : Lift → LigeroAssignment ninp M F} {Sat : Lift → Prop}

/-- The six budget inequalities. -/
structure ZkBudgets (FD : ZkFieldData C F X Q Msg Gpt Lift M ninp logw logc nl w V H asg Sat)
    (LD : ZkLigeroData C X Q Msg V asg) (bpair bround bin blig bquery : ℕ) : Prop where
  /-- Layer 0's pair slot. -/
  hbp0 : FD.kinit * FD.binit ≤ bpair
  /-- A later pair slot. -/
  hbp1 : FD.kpair * (2 * Fintype.card F) ≤ bpair
  hbround : FD.k * 2 ≤ bround
  hbin : FD.k * 1 ≤ bin
  /-- The Ligero challenge slot, at every system no candidate satisfies. -/
  hblig : ∀ sys, Fits V sys → NoSat asg sys → FD.kchal * (LD.escaping sys).card ≤ blig
  hbquery : FD.kq * LD.bq ≤ bquery

/-! ## 2. The transitions and the chain at a proof's messages -/

/-- The zero-knowledge transitions at a proof's messages: the query test reads the query slot's
message. -/
noncomputable def steps (V : ZkCode C F X Q Msg Gpt M ninp logw logc)
    (LD : ZkLigeroData C X Q Msg V asg) (ms : ℕ → Msg) :
    StepsS C (ZkState M ninp logw logc F X) nl w :=
  zkSteps nl w V ms fun m pref => LD.accepting m pref (ms m)

/-- **The zero-knowledge LayerStep at a proof's messages**, as a claim chain over `Option Lift`. -/
noncomputable def chain (V : ZkCode C F X Q Msg Gpt M ninp logw logc)
    (H : ZkHonest F Lift logw logc) (asg : Lift → LigeroAssignment ninp M F) (Sat : Lift → Prop)
    (LD : ZkLigeroData C X Q Msg V asg) (ms : ℕ → Msg) :
    Bcs.ClaimChain C (Rounds.Role.length nl w) (ZkState M ninp logw logc F X) (Option Lift) :=
  layerStepChainS (steps (nl := nl) (w := w) V LD ms) (ZkWrong V H asg Sat LD.LigDoomed) .start

/-- **The zero-knowledge LayerStep reaches `.accepted`**, stated with no doom predicate and no
candidate type. -/
noncomputable def ZkLayerStepAccepts {S : Type} (accd : S) (init : S)
    (steps : StepsS C S nl w) (tape : Fin (Rounds.Role.length nl w) → C) : Prop :=
  (layerStepChainS (Cand := PUnit) steps (fun _ _ => False) init).state
    (Rounds.Role.length nl w) (Bcs.trunc tape (Rounds.Role.length nl w) le_rfl) = accd

/-- **The acceptance obligation**: every tape of the event makes the zero-knowledge LayerStep at the
proof's messages reach `.accepted`. -/
def ZkRight (LD : ZkLigeroData C X Q Msg V asg) (ms : ℕ → Msg)
    (Acc : (Fin (Rounds.Role.length nl w) → C) → Prop) : Prop :=
  ∀ tape, Acc tape → ZkLayerStepAccepts .accepted .start (steps (nl := nl) (w := w) V LD ms) tape

omit [Fintype C] in
/-- Two claim chains with the same start and transitions visit the same states. -/
theorem state_eq_of {T : ℕ} {S Cand₁ Cand₂ : Type} (ch₁ : Bcs.ClaimChain C T S Cand₁)
    (ch₂ : Bcs.ClaimChain C T S Cand₂) (hi : ch₁.init = ch₂.init) (hs : ch₁.step = ch₂.step) :
    ∀ (j : ℕ) (p : Fin j → C), ch₁.state j p = ch₂.state j p
  | 0, _ => hi
  | j + 1, p => by
      rw [Bcs.ClaimChain.state, Bcs.ClaimChain.state, hs, state_eq_of ch₁ ch₂ hi hs j]

omit [Fintype C] [Fintype F] [DecidableEq F] [Fintype Gpt] [DecidableEq Gpt] [DecidableEq X]
  [Fintype Q] [DecidableEq Q] in
/-- **`right_of_accepts`**: an accepting run ends at `.accepted`, where the phantom is undoomed. -/
theorem right_of_zkAccepts (LD : ZkLigeroData C X Q Msg V asg) (ms : ℕ → Msg)
    {Acc : (Fin (Rounds.Role.length nl w) → C) → Prop}
    (hle : ZkRight (nl := nl) (w := w) LD ms Acc) :
    ∀ tape : Fin (Rounds.Role.length nl w) → C, Acc tape →
      ∃ cand : Option Lift, ¬ (chain (nl := nl) (w := w) V H asg Sat LD ms).Wrong cand
        ((chain (nl := nl) (w := w) V H asg Sat LD ms).state (Rounds.Role.length nl w)
          (Bcs.trunc tape (Rounds.Role.length nl w) le_rfl)) := by
  intro tape hacc
  refine ⟨none, ?_⟩
  have h := hle tape hacc
  unfold ZkLayerStepAccepts at h
  rw [← state_eq_of (chain (nl := nl) (w := w) V H asg Sat LD ms)
    (layerStepChainS (Cand := PUnit) (steps (nl := nl) (w := w) V LD ms) (fun _ _ => False)
      .start) rfl rfl] at h
  show ¬ ZkWrong V H asg Sat LD.LigDoomed none _
  rw [h]
  exact not_false

/-! ## 3. The per-slot budgets at the bundled data -/

namespace ZkFieldData

variable (FD : ZkFieldData C F X Q Msg Gpt Lift M ninp logw logc nl w V H asg Sat)
variable (LD : ZkLigeroData C X Q Msg V asg)
variable {bpair bround bin blig bquery : ℕ}

theorem budget_pair (hB : ZkBudgets FD LD bpair bround bin blig bquery) (ms : ℕ → Msg) :
    ∀ (ly : Fin nl) (m : ℕ) (pref : Fin m → C) (cand : Option Lift)
      (s : ZkState M ninp logw logc F X), ZkWrong V H asg Sat LD.LigDoomed cand s →
      (univ.filter fun c : C => ¬ ZkWrong V H asg Sat LD.LigDoomed cand
        ((steps (nl := nl) (w := w) V LD ms).pair ly m pref c s)).card ≤ wt cand * bpair := by
  intro ly m pref cand s hw
  by_cases hly : ly.val = 0
  · simp only [steps, zkSteps, if_pos hly]
    exact le_trans (zkInit_budget V H asg Sat LD.LigDoomed FD.kinit FD.binit FD.hbalInit
      FD.hinit cand s hw) (Nat.mul_le_mul_left _ hB.hbp0)
  · simp only [steps, zkSteps, if_neg hly]
    exact le_trans (zkCombine_budget Sat LD.LigDoomed FD.B (V.closeOf (ms m)) FD.kpair
      FD.hbalPair cand s hw) (Nat.mul_le_mul_left _ hB.hbp1)

theorem budget_round (hB : ZkBudgets FD LD bpair bround bin blig bquery) (ms : ℕ → Msg) :
    ∀ (ly : Fin nl) (j : Fin (w ly.val)) (m : ℕ) (pref : Fin m → C) (cand : Option Lift)
      (s : ZkState M ninp logw logc F X), ZkWrong V H asg Sat LD.LigDoomed cand s →
      (univ.filter fun c : C => ¬ ZkWrong V H asg Sat LD.LigDoomed cand
        ((steps (nl := nl) (w := w) V LD ms).round ly j m pref c s)).card
        ≤ wt cand * bround := by
  intro ly j m pref cand s hw
  exact le_trans (zkRound_budget Sat LD.LigDoomed FD.B (V.roundOf (ms m)) FD.k FD.hbalF
    cand s hw) (Nat.mul_le_mul_left _ hB.hbround)

theorem budget_in (hB : ZkBudgets FD LD bpair bround bin blig bquery) (ms : ℕ → Msg) :
    ∀ (m : ℕ) (pref : Fin m → C) (cand : Option Lift) (s : ZkState M ninp logw logc F X),
      ZkWrong V H asg Sat LD.LigDoomed cand s →
      (univ.filter fun c : C => ¬ ZkWrong V H asg Sat LD.LigDoomed cand
        ((steps (nl := nl) (w := w) V LD ms).inputBind m pref c s)).card ≤ wt cand * bin := by
  intro m pref cand s hw
  exact le_trans (zkInputBind_budget Sat LD.LigDoomed FD.B (V.closeOf (ms m)) FD.k FD.hbalF
    cand s hw) (Nat.mul_le_mul_left _ hB.hbin)

theorem budget_lig [Fintype Lift] (hB : ZkBudgets FD LD bpair bround bin blig bquery)
    (ms : ℕ → Msg) :
    ∀ (m : ℕ) (pref : Fin m → C) (s : ZkState M ninp logw logc F X),
      (∀ cand : Option Lift, ZkWrong V H asg Sat LD.LigDoomed cand s) →
      (univ.filter fun c : C => ¬ ∀ cand : Option Lift, ZkWrong V H asg Sat LD.LigDoomed cand
        ((steps (nl := nl) (w := w) V LD ms).ligeroChallenge m pref c s)).card ≤ blig :=
  fun _ _ s hw => zkLigChallenge_budget V H asg Sat LD.LigDoomed LD.escaping LD.hesc FD.kchal blig
    FD.hbalChal hB.hblig s hw

theorem budget_query [Fintype Lift] (hB : ZkBudgets FD LD bpair bround bin blig bquery)
    (ms : ℕ → Msg) :
    ∀ (m : ℕ) (pref : Fin m → C) (s : ZkState M ninp logw logc F X),
      (∀ cand : Option Lift, ZkWrong V H asg Sat LD.LigDoomed cand s) →
      (univ.filter fun c : C => ¬ ∀ cand : Option Lift, ZkWrong V H asg Sat LD.LigDoomed cand
        ((steps (nl := nl) (w := w) V LD ms).ligeroQuery m pref c s)).card ≤ bquery :=
  fun m pref s hw => le_trans (zkLigQuery_budget V H asg Sat LD.LigDoomed
    (LD.accepting m pref (ms m)) FD.kq LD.bq FD.hbalQuery (LD.hbq m pref (ms m)) s hw) hB.hbquery

/-! ## 4. Round by round -/

/--
**The zero-knowledge LayerStep at a proof's messages, as a round-by-round argument.**  The field
slots pay `|Lift| · b`, the Ligero slots `blig` and `bquery`; `wrong_init` is `hfail`.
-/
noncomputable def rbr [Fintype Lift] (hB : ZkBudgets FD LD bpair bround bin blig bquery)
    (ms : ℕ → Msg) {Acc : (Fin (Rounds.Role.length nl w) → C) → Prop} {Fails : Prop}
    (hfail : Fails → ∀ ℓ : Lift, ¬ Sat ℓ)
    (hright : ZkRight (nl := nl) (w := w) LD ms Acc) :
    Bcs.Rbr C (Rounds.Role.length nl w) Acc Fails :=
  layerStepRbrW (steps (nl := nl) (w := w) V LD ms) (ZkWrong V H asg Sat LD.LigDoomed) .start wt
    bpair bround bin blig bquery
    (fun hf cand => by
      cases cand with
      | none => exact trivial
      | some ℓ => exact hfail hf ℓ)
    (FD.budget_pair LD hB ms) (FD.budget_round LD hB ms) (FD.budget_in LD hB ms)
    (FD.budget_lig LD hB ms) (FD.budget_query LD hB ms)
    (right_of_zkAccepts (H := H) (Sat := Sat) LD ms hright)

/-- `rbr`'s doom is the chain's. -/
theorem rbr_doomed [Fintype Lift] (hB : ZkBudgets FD LD bpair bround bin blig bquery)
    (ms : ℕ → Msg) {Acc : (Fin (Rounds.Role.length nl w) → C) → Prop} {Fails : Prop}
    (hfail : Fails → ∀ ℓ : Lift, ¬ Sat ℓ)
    (hright : ZkRight (nl := nl) (w := w) LD ms Acc) :
    (FD.rbr LD hB ms hfail hright).doomed = (chain (nl := nl) (w := w) V H asg Sat LD ms).doomed :=
  rfl

/-- `rbr`'s per-slot budget is the mixed budget at the list factor `|Lift|`. -/
theorem rbr_beta [Fintype Lift] (hB : ZkBudgets FD LD bpair bround bin blig bquery)
    (ms : ℕ → Msg) {Acc : (Fin (Rounds.Role.length nl w) → C) → Prop} {Fails : Prop}
    (hfail : Fails → ∀ ℓ : Lift, ¬ Sat ℓ)
    (hright : ZkRight (nl := nl) (w := w) LD ms Acc)
    (i : Fin (Rounds.Role.length nl w)) :
    (FD.rbr LD hB ms hfail hright).beta i
      = mixedBudget (nl := nl) (w := w) (Fintype.card Lift) bpair bround bin blig bquery
          (Rounds.Role.indexEquiv.symm i) := by
  show mixedBudget (nl := nl) (w := w) (∑ cand : Option Lift, wt cand) bpair bround bin blig
    bquery (Rounds.Role.indexEquiv.symm i) = _
  rw [sum_wt]

/--
**Checkpoint B: the zero-knowledge LayerStep, round by round.**

```text
Pr[ ZK LayerStep accepts  ∧  no candidate satisfies the circuit ]
    ≤  ( |Lift| · (nl·bpair + (∑ w)·bround + bin)  +  blig  +  bquery ) / |C|
```

at one commitment context and one message sequence.
-/
theorem ratio_le [DecidableEq C] [Nonempty C] [Fintype Lift]
    (hB : ZkBudgets FD LD bpair bround bin blig bquery) (ms : ℕ → Msg)
    {Acc : (Fin (Rounds.Role.length nl w) → C) → Prop} {Fails : Prop}
    (hfail : Fails → ∀ ℓ : Lift, ¬ Sat ℓ)
    (hright : ZkRight (nl := nl) (w := w) LD ms Acc)
    (hT : 1 ≤ Rounds.Role.length nl w) :
    ((univ.filter fun tape : Fin (Rounds.Role.length nl w) → C =>
        Acc tape ∧ Fails).card : ℚ)
        / (Fintype.card C : ℚ) ^ Rounds.Role.length nl w
      ≤ ((Fintype.card Lift * (nl * bpair + (∑ i ∈ Finset.range nl, w i) * bround + bin)
            + blig + bquery : ℕ) : ℚ)
          / (Fintype.card C : ℚ) := by
  have h := (FD.rbr LD hB ms hfail hright).toCore.rbr_ratio_le hT
  have hsum : ∑ i, (FD.rbr LD hB ms hfail hright).toCore.beta i
      = Fintype.card Lift * (nl * bpair + (∑ i ∈ Finset.range nl, w i) * bround + bin)
          + blig + bquery := by
    show ∑ i, (FD.rbr LD hB ms hfail hright).beta i = _
    simp only [FD.rbr_beta LD hB ms hfail hright]
    exact mixed_budget_sum (nl := nl) (w := w) _ _ _ _ _ _
  rwa [hsum] at h

/-- **Doom preservation of the zero-knowledge chain at a message sequence**, slot by slot, at the
mixed budget with list factor `|Lift|`.  The round-by-round object's `doom_preserved`, stated on the
chain itself. -/
theorem doom_preserved_chain [Fintype Lift] (hB : ZkBudgets FD LD bpair bround bin blig bquery)
    (ms : ℕ → Msg) (i : Fin (Rounds.Role.length nl w)) (pref : Fin i.val → C)
    (hd : (chain (nl := nl) (w := w) V H asg Sat LD ms).doomed i.val pref) :
    (univ.filter fun c : C =>
        ¬ (chain (nl := nl) (w := w) V H asg Sat LD ms).doomed (i.val + 1) (Bcs.extend pref c)).card
      ≤ mixedBudget (nl := nl) (w := w) (Fintype.card Lift) bpair bround bin blig bquery
          (Rounds.Role.indexEquiv.symm i) := by
  have h := (FD.rbr LD hB ms (Acc := fun _ => False) (Fails := False) False.elim
    (fun _ h => h.elim)).doom_preserved i pref hd
  rw [FD.rbr_beta LD hB ms False.elim (fun _ h => h.elim) i] at h
  exact h

/-- **An accepting run escapes doom at some slot**, when no candidate satisfies the circuit. -/
theorem exists_escape_chain [Fintype Lift] (hB : ZkBudgets FD LD bpair bround bin blig bquery)
    (ms : ℕ → Msg) (tape : Fin (Rounds.Role.length nl w) → C) (hfail : ∀ ℓ : Lift, ¬ Sat ℓ)
    (hacc : ZkLayerStepAccepts .accepted .start (steps (nl := nl) (w := w) V LD ms) tape) :
    ∃ k : Fin (Rounds.Role.length nl w),
      (chain (nl := nl) (w := w) V H asg Sat LD ms).doomed k.val
          (Sumcheck.extract_prefix tape k) ∧
        ¬ (chain (nl := nl) (w := w) V H asg Sat LD ms).doomed (k.val + 1)
          (Bcs.extend (Sumcheck.extract_prefix tape k) (tape k)) := by
  have key : ∀ R0 : Bcs.Rbr C (Rounds.Role.length nl w)
      (fun t => ZkLayerStepAccepts .accepted .start (steps (nl := nl) (w := w) V LD ms) t)
      (∀ ℓ : Lift, ¬ Sat ℓ),
      R0.doomed = (chain (nl := nl) (w := w) V H asg Sat LD ms).doomed →
      ∃ k : Fin (Rounds.Role.length nl w),
        (chain (nl := nl) (w := w) V H asg Sat LD ms).doomed k.val
            (Sumcheck.extract_prefix tape k) ∧
          ¬ (chain (nl := nl) (w := w) V H asg Sat LD ms).doomed (k.val + 1)
            (Bcs.extend (Sumcheck.extract_prefix tape k) (tape k)) := by
    intro R0 hR0
    obtain ⟨k, h1, h2⟩ := R0.exists_escape tape (R0.doomed_start hfail _)
      (R0.accepts_undoomed tape hacc)
    rw [hR0] at h1 h2
    exact ⟨k, h1, h2⟩
  exact key _ (FD.rbr_doomed LD hB ms (fun hf => hf) (fun _ h => h))

end ZkFieldData

/-! ## 5. Layer 0's count from the output layer -/

section Output

open Lfzk.ZkMultilinear

variable {C F X Q Msg Lift : Type} [Field F] [Fintype F] [DecidableEq F]
variable {M ninp logw logc logv : ℕ}

/--
**`hinit` from the output layer.**  If layer 0's honest starting claim at the output point `G` (both
points `G`, claims zero: `begin_circuit`) is `out ℓ b G + α · out ℓ b G` for an output extension
`out` that is multilinear in `G` and affine in `beta₀ = b`, and an unsatisfied candidate **whose
intermediate assertions all hold** (`∀ j, ¬ H.Pend ℓ j []`) has `out` not identically zero, then the
layer-0 count is `(logv + 2) · |F|^(logv + 1)`.

`harith` is satisfiable at the honest `Sat := Satisfied`: with every assertion vector below layer 0
zero, `Satisfied` is `TopSat` (`Lfzk.Arith.QuadCircuit.satisfied_iff_top`, under `Isolated`), and an
unsatisfied `TopSat` has a non-zero output or layer-0 assertion wire, which is `out 0` or the slope
`out 1 − out 0` at a cube point (`top_harith`, under `DeadEnd`).  It is the *intermediate*
assertions that `out` cannot see; the chain's branches (b) and (c) carry those.
-/
theorem hinit_of_output {H : ZkHonest F Lift logw logc} {Sat : Lift → Prop}
    {V : ZkCode C F X Q Msg (Fin logv → F) M ninp logw logc}
    (out : Lift → F → (Fin logv → F) → F)
    (hclaim0 : ∀ (ℓ : Lift) (G : Fin logv → F) (b a : F),
      H.sum ℓ 0 (V.st0 G) b a [] = out ℓ b G + a * out ℓ b G)
    (hml : ∀ (ℓ : Lift) (b : F), MLin (out ℓ b))
    (haff : ∀ (ℓ : Lift) (b : F) (G : Fin logv → F),
      out ℓ b G = out ℓ 0 G + b * (out ℓ 1 G - out ℓ 0 G))
    (harith : ∀ ℓ : Lift, ¬ Sat ℓ → (∀ j, ¬ H.Pend ℓ j []) →
      ∃ (b : F) (G : Fin logv → F), out ℓ b G ≠ 0) :
    ∀ ℓ : Lift, ¬ Sat ℓ → (∀ j, ¬ H.Pend ℓ j []) →
      (univ.filter fun p : (Fin logv → F) × F × F =>
        H.sum ℓ 0 (V.st0 p.1) p.2.1 p.2.2 [] = 0).card
        ≤ (logv + 2) * Fintype.card F ^ (logv + 1) := by
  intro ℓ hℓ hnp
  classical
  refine le_trans (le_of_eq ?_) (init_bad_card (out ℓ) (hml ℓ) (haff ℓ) (harith ℓ hℓ hnp))
  congr 1
  refine Finset.filter_congr fun p _ => ?_
  simp only [hclaim0]

end Output

end Lfzk.RbrZkSplit
