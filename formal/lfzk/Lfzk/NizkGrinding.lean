import Lfzk.CertifiedV1
import Bcs.RecomputedRbr
import Bcs.CoinSpaceAux

/-!
# The composed Longfellow bound against a grinding Fiat–Shamir adversary

`Lfzk.Nizk`, `Lfzk.NizkMerkle` and `Lfzk.CertifiedV1` bound the composed LayerStep in the **sequential**
round-by-round model: the coin tape has one slot per challenge round, in order, and the adversary is
handed one challenge per round.  The number of hash queries never enters.  This file replaces that
with the Fiat–Shamir game.

## The adversary and the verifier

* The **Merkle adversary** `A : Bcs.Adversary` is unchanged: it commits on the hash tape, answers the
  Ligero challenge, and opens the queried columns.
* The **Fiat–Shamir adversary** is a query tree `adv aux : Tree (Point Ctx Msg C nl w) C Out N`
  against the challenge oracle, run after the commitment with the commit stage's private state
  `aux` in hand.  It makes at most `N` queries at points of its choosing and outputs a proof `out`,
  whose messages are `msgOf out : ℕ → Msg`.
* A **query point** `Point` is a transcript prefix, typed by the `Rounds.Role` it is drawn for: the
  commitment context, the role, the prover's messages through this round, and the **raw** oracle
  answers of the earlier rounds.
* The **verifier recomputes** every challenge: round `k`'s challenge is the oracle's answer at
  `hashPoint (ctxOf aux) msgOf out k (answers of rounds < k)`.  `Bcs.execution` runs the search and
  the recomputation on one lazy-sampling tape of length `L + N`, `L = Rounds.Role.length nl w`.

## How `N` enters

LayerStep's state function, at the proof's messages, is round-by-round sound with the per-role budgets
of `Lfzk.RbrSplit`.  At a query point it is determined by the point (`layerStep_state_congr`), so the bad
event at a tape slot is "the point queried there is doomed and its answer escapes", with the budget of
the point's role (`DoomedAt`, `EscapesAt`, `escapesAt_card`, `link_at`).  That is a
`Bcs.TranscriptGrinding` (`fsGrinding`), hence a `Bcs.RbrCore` over the `L + N` slots (`fsCore`, at
the worst role's budget).  The sharper per-role count, `Bcs.TranscriptGrinding.card_mul_le_weighted`,
gives per commitment

```text
Pr[ accept ∧ extraction fails ]  ≤  |Cand| · ( N · max_role β  +  ∑ role, β role ) / |C|
```

— the adversary's `N` own queries pay the worst role, the verifier's `L` recomputations pay their own.
`fs_card_le` is that count; `CertifiedV1.Row.fs_ratio_le_bound` composes it with the Merkle term
through `Bcs.drop_explains_ratio_le_aux` at a certified V1 row:

```text
Pr ≤ R.bound + N · R.fsCoefficient,          R.fsCoefficient = cardCand · maxDensity
   ≤ (L + N) · R.fsCoefficient + merkleTerm    (CertifiedV1.Row.bound_add_le_uniform)
```

`R.bound` is the sequential row's certified bound, so at `N = 0` nothing is lost; `fsChallenges_done`
checks that with no search the recomputed challenges are the tape itself.

At `CertifiedV1.v8Hash` (`v8Hash_fs_ratio_le`, `v8Hash_fs_ratio_le_uniform`):

```text
Pr ≤ 2^-114 + N · 2^-115          and          Pr ≤ (633 + N) · 2^-115 + merkleTerm
```

with the work-normalized coefficient `κ ≤ 2^-115` certified, and sharp, by evaluation
(`v8Hash_fsCoefficient`, `v8Hash_fsCoefficient_sharp`).  The worst slot there is the Ligero
challenge slot, `maxDensity = fail + arith` (`v8Hash_maxDensity_eq`).
`Lfzk.NizkGrindingTwoField` carries this to the two-field row.

## What is still a hypothesis

Everything `CertifiedV1.Row.nizk_ratio_le_family_bound` assumed, with `hright` restated for the
Fiat–Shamir verifier: if the compiled verifier accepts at the recomputed Ligero challenge and query,
with extraction explaining it, then LayerStep on the proof's messages accepts at the recomputed
challenges.  It is README gap 1's transliteration debt, now also carrying that `challengeOf`/`queryOf`
are the decoded recomputed Ligero rounds and that `lig pre`'s prover answers as `A` does.  The list is
in `Row.fs_ratio_le_bound`'s docstring.  `MsgData`, the one new datum, exists whenever the sequential
LayerStep data does (`MsgData.ofFieldData`).

## Modelling restrictions, stated rather than hidden

* **One commitment.**  The Fiat–Shamir search runs after the commit stage and sees its private state,
  but cannot re-commit: there is no interleaving driver, as in `Lfzk.CertifiedV1`.  Grinding over
  commitments is not covered.
* **No Merkle queries during the search.**  The search is a tree over the challenge oracle alone; the
  Merkle adversary's own stages make every hash-tape query after the commitment.  What the search may
  read of the hash tape is the commit stage's private state, which is what keeps
  `Bcs.drop_explains_ratio_le_aux`'s extraction argument sound.
* **The Ligero statement is fixed per commitment**, as in `Lfzk.CertifiedV1`.
* **Hash inputs carry the raw earlier answers.**  A point is `(ctx, role, msgs, chals)` with `chals`
  the raw oracle answers of the earlier rounds, the convention of `Bcs.RecomputedGrinding` (whose
  second hash input carries the first raw digest).  That is what makes doom a function of the point.
* LayerStep data's `B` and `prover` fields are **replaced** by `MsgData` read at the proof's messages
  (`withMsgs`); everything else in `FieldData` is the protocol's, as before.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.NizkGrinding

open Finset Bcs Merkle Merkle.MH Merkle.RandomOracle RbrLongfellow
open scoped Classical

/-! ## 1. The prover's messages, in LayerStep -/

section Messages

variable {C F X Q Cand Witness Msg : Type} [Fintype C] [Field F] [Fintype F] [DecidableEq F]
  [SumcheckInterp F] [DecidableEq X] [Fintype Q] [DecidableEq Q]
variable {nc nv logw logc nl : ℕ} {w : ℕ → ℕ}
variable {H : Honest F Cand logw logc} {Sat : Cand → Prop} {LigDoomed : X → Prop}

/-- **How round `m`'s message fixes the prover data LayerStep reads at round `m`**: the layer
boundary (the closing `wc0, wc1`) and the round polynomial.  Both may also read the earlier raw
answers. -/
structure MsgData (C Msg : Type) (H : Honest F Cand logw logc) where
  /-- The layer boundary at round `m`, from its message. -/
  bnd : ∀ m : ℕ, (Fin m → C) → Msg → Boundary H
  /-- The round polynomial at round `m`, from its message. -/
  poly : ∀ m : ℕ, (Fin m → C) → Msg →
    ℕ → LayerState logw logc F → F → F → List F → Sumcheck.RoundPoly F 2

/-- **LayerStep's data at a proof.**  `FieldData` with its two prover fields read from the messages:
round `m` reads message `m` and nothing later. -/
def withMsgs (FD : RbrSplit.FieldData C F X Q Cand Witness nc nv logw logc H Sat)
    (MD : MsgData C Msg H) (ms : ℕ → Msg) :
    RbrSplit.FieldData C F X Q Cand Witness nc nv logw logc H Sat :=
  { FD with
    B := fun m pref => MD.bnd m pref (ms m)
    prover := fun m pref => MD.poly m pref (ms m) }

/-- `withMsgs` changes nothing the budgets read. -/
theorem budgets_withMsgs {FD : RbrSplit.FieldData C F X Q Cand Witness nc nv logw logc H Sat}
    {LD : RbrSplit.LigeroData C X Q LigDoomed} {bpair bround bin blig bquery : ℕ}
    (hB : RbrSplit.Budgets FD LD bpair bround bin blig bquery) (MD : MsgData C Msg H)
    (ms : ℕ → Msg) :
    RbrSplit.Budgets (withMsgs FD MD ms) LD bpair bround bin blig bquery :=
  ⟨hB.hbp0, hB.hbp1, hB.hbround, hB.hbin, hB.hblig, hB.hbquery⟩

/-- **The sequential LayerStep's prover data, as message data that ignores the message.**  So `MsgData`
exists whenever the sequential `FieldData` does: the Fiat–Shamir theorem's premises are satisfiable
exactly when the sequential theorem's are. -/
def MsgData.ofFieldData (FD : RbrSplit.FieldData C F X Q Cand Witness nc nv logw logc H Sat) :
    MsgData C Msg H where
  bnd m pref _ := FD.B m pref
  poly m pref _ := FD.prover m pref

/-- Reading `MsgData.ofFieldData` at any messages gives back the sequential LayerStep data. -/
theorem withMsgs_ofFieldData (FD : RbrSplit.FieldData C F X Q Cand Witness nc nv logw logc H Sat)
    (ms : ℕ → Msg) : withMsgs FD (MsgData.ofFieldData FD) ms = FD := rfl

/--
**The Ligero half, reading the round's message.**  `RbrSplit.LigeroData` with a query test that
also reads the message of the round it is drawn at: under Fiat–Shamir the prover's Ligero response is
that message, and the opened columns are tested against *it*.  The escaping set and the doomed
challenges' query bound are uniform in the message — the doom predicate is fixed before the response
is sent, and `hbq` holds for every response a doomed challenge could get.
-/
structure MsgLigeroData (C X Q Msg : Type) (LigDoomed : X → Prop) where
  /-- The queries the opened columns pass, as a function of the prefix, the round's message and the
  challenge. -/
  accepting : ∀ m : ℕ, (Fin m → C) → Msg → X → Finset Q
  /-- The Ligero challenges that do not doom the run. -/
  escaping : Finset X
  hesc : ∀ x : X, ¬ LigDoomed x → x ∈ escaping
  /-- A bound on a doomed challenge's accepting-query count, at every message. -/
  bq : ℕ
  hbq : ∀ (m : ℕ) (pref : Fin m → C) (msg : Msg) (x : X), LigDoomed x →
    (accepting m pref msg x).card ≤ bq

/-- **The Ligero half at a proof's messages**: round `m`'s query test reads message `m`. -/
def withMsgsL (ML : MsgLigeroData C X Q Msg LigDoomed) (ms : ℕ → Msg) :
    RbrSplit.LigeroData C X Q LigDoomed where
  accepting m pref := ML.accepting m pref (ms m)
  escaping := ML.escaping
  hesc := ML.hesc
  bq := ML.bq
  hbq m pref x hx := ML.hbq m pref (ms m) x hx

/-- A message-blind Ligero half, as message data that ignores the message. -/
def MsgLigeroData.ofLigeroData (LD : RbrSplit.LigeroData C X Q LigDoomed) :
    MsgLigeroData C X Q Msg LigDoomed where
  accepting m pref _ := LD.accepting m pref
  escaping := LD.escaping
  hesc := LD.hesc
  bq := LD.bq
  hbq m pref _ x hx := LD.hbq m pref x hx

omit [Fintype C] [DecidableEq X] [Fintype Q] [DecidableEq Q] in
/-- Reading a message-blind half at any messages gives back the sequential half. -/
theorem withMsgsL_ofLigeroData (LD : RbrSplit.LigeroData C X Q LigDoomed) (ms : ℕ → Msg) :
    withMsgsL (MsgLigeroData.ofLigeroData LD) ms = LD := rfl

/-- `RbrSplit.Budgets` against a message-reading Ligero half: the six inequalities read nothing
the message changes. -/
structure MsgBudgets (FD : RbrSplit.FieldData C F X Q Cand Witness nc nv logw logc H Sat)
    (ML : MsgLigeroData C X Q Msg LigDoomed) (bpair bround bin blig bquery : ℕ) : Prop where
  hbp0 : FD.kpair * (2 * Fintype.card F) ≤ bpair
  hbp1 : FD.k * 1 ≤ bpair
  hbround : FD.k * 2 ≤ bround
  hbin : FD.k * 1 ≤ bin
  hblig : FD.kchal * ML.escaping.card ≤ blig
  hbquery : FD.kq * ML.bq ≤ bquery

/-- The budgets hold at every message sequence. -/
theorem MsgBudgets.withMsgs {FD : RbrSplit.FieldData C F X Q Cand Witness nc nv logw logc H Sat}
    {ML : MsgLigeroData C X Q Msg LigDoomed} {bpair bround bin blig bquery : ℕ}
    (hB : MsgBudgets FD ML bpair bround bin blig bquery) (MD : MsgData C Msg H) (ms : ℕ → Msg) :
    RbrSplit.Budgets (withMsgs FD MD ms) (withMsgsL ML ms) bpair bround bin blig bquery :=
  ⟨hB.hbp0, hB.hbp1, hB.hbround, hB.hbin, hB.hblig, hB.hbquery⟩

/-- A message-blind half's budgets are the sequential ones. -/
theorem MsgBudgets.ofLigeroData {FD : RbrSplit.FieldData C F X Q Cand Witness nc nv logw logc H Sat}
    {LD : RbrSplit.LigeroData C X Q LigDoomed} {bpair bround bin blig bquery : ℕ}
    (hB : RbrSplit.Budgets FD LD bpair bround bin blig bquery) :
    MsgBudgets FD (MsgLigeroData.ofLigeroData (Msg := Msg) LD) bpair bround bin blig bquery :=
  ⟨hB.hbp0, hB.hbp1, hB.hbround, hB.hbin, hB.hblig, hB.hbquery⟩

/-- LayerStep at the proof's messages, as a claim chain: the field half and the Ligero half both
read round `m`'s message at round `m`. -/
noncomputable def layerStep (FD : RbrSplit.FieldData C F X Q Cand Witness nc nv logw logc H Sat)
    (MD : MsgData C Msg H) (ML : MsgLigeroData C X Q Msg LigDoomed) (ms : ℕ → Msg) :
    Bcs.ClaimChain C (Rounds.Role.length nl w) (RbrLayerStep.WState logw logc F X) Cand :=
  RbrLayerStep.layerStepChain
    (RbrSplit.steps (nl := nl) (w := w) (withMsgs FD MD ms) (withMsgsL ML ms))
    (Wrong H Sat LigDoomed) .start

/-- **Round `i` reads message `i` only.** -/
theorem layerStep_step_congr (FD : RbrSplit.FieldData C F X Q Cand Witness nc nv logw logc H Sat)
    (MD : MsgData C Msg H) (ML : MsgLigeroData C X Q Msg LigDoomed) {ms ms' : ℕ → Msg}
    (i : Fin (Rounds.Role.length nl w)) (h : ms i.val = ms' i.val) :
    (layerStep (nl := nl) (w := w) FD MD ML ms).step i
      = (layerStep (nl := nl) (w := w) FD MD ML ms').step i := by
  funext pref c s
  simp only [layerStep, RbrLayerStep.layerStepChain, RbrLayerStep.stepAt, RbrSplit.steps, RbrSplit.stepsOf, lfSteps,
    withMsgs, withMsgsL]
  rw [h]

omit [Fintype C] in
/-- Two claim chains with the same start and the same transitions below `k` agree on every prefix of
length at most `k`. -/
theorem state_congr_below {T : ℕ} {S Cand' : Type} (ch₁ ch₂ : Bcs.ClaimChain C T S Cand')
    (hi : ch₁.init = ch₂.init) (k : ℕ) (hs : ∀ i : Fin T, i.val < k → ch₁.step i = ch₂.step i) :
    ∀ j : ℕ, j ≤ k → ∀ p : Fin j → C, ch₁.state j p = ch₂.state j p
  | 0, _, _ => hi
  | j + 1, hj, p => by
      rw [Bcs.ClaimChain.state, Bcs.ClaimChain.state]
      split_ifs with hjT
      · rw [hs ⟨j, hjT⟩ (by simp only; omega), state_congr_below ch₁ ch₂ hi k hs j (by omega)]
      · rw [state_congr_below ch₁ ch₂ hi k hs j (by omega)]

/-- **LayerStep's state at a prefix of length `j` reads only the first `j` messages.** -/
theorem layerStep_state_congr (FD : RbrSplit.FieldData C F X Q Cand Witness nc nv logw logc H Sat)
    (MD : MsgData C Msg H) (ML : MsgLigeroData C X Q Msg LigDoomed) {ms ms' : ℕ → Msg} (j : ℕ)
    (h : ∀ i, i < j → ms i = ms' i) (p : Fin j → C) :
    (layerStep (nl := nl) (w := w) FD MD ML ms).state j p
      = (layerStep (nl := nl) (w := w) FD MD ML ms').state j p :=
  state_congr_below (layerStep (nl := nl) (w := w) FD MD ML ms) (layerStep FD MD ML ms') rfl j
    (fun i hi => layerStep_step_congr (ms := ms) (ms' := ms') FD MD ML i (h i.val hi)) j le_rfl p

end Messages

/-! ## 2. Query points: transcript prefixes, one per role -/

section Points

variable {Ctx Msg C : Type} {nl : ℕ} {w : ℕ → ℕ}

/-- **A Fiat–Shamir hash input of the Longfellow LayerStep.**  The commitment context, the role it is
drawn for, the prover's messages through this round, and the raw oracle answers of the earlier
rounds. -/
structure Point (Ctx Msg C : Type) (nl : ℕ) (w : ℕ → ℕ) where
  ctx : Ctx
  role : Rounds.Role nl w
  msgs : List Msg
  chals : List C
  deriving DecidableEq

/-- The role at a slot of the schedule; the default past the end is never read. -/
noncomputable def roleAt (k : ℕ) : Rounds.Role nl w :=
  if h : k < Rounds.Role.length nl w then Rounds.Role.indexEquiv.symm ⟨k, h⟩ else .inputBind

theorem index_indexEquiv_symm (i : Fin (Rounds.Role.length nl w)) :
    (Rounds.Role.indexEquiv.symm i).index = i := by
  have h : Rounds.Role.indexEquiv (Rounds.Role.indexEquiv.symm i) = i :=
    Rounds.Role.indexEquiv.apply_symm_apply i
  exact h

theorem indexEquiv_symm_index (rl : Rounds.Role nl w) :
    Rounds.Role.indexEquiv.symm rl.index = rl :=
  Rounds.Role.indexEquiv.symm_apply_apply rl

theorem slot_roleAt {k : ℕ} (hk : k < Rounds.Role.length nl w) :
    (roleAt (nl := nl) (w := w) k).slot = k := by
  rw [roleAt, dif_pos hk]
  exact congrArg Fin.val (index_indexEquiv_symm ⟨k, hk⟩)

/-- **Round `k`'s hash input**: the context, round `k`'s role, messages `0, …, k`, and the raw
answers of rounds `< k`. -/
noncomputable def hashPoint {Out : Type} (ctx : Ctx) (msgOf : Out → ℕ → Msg) (out : Out) (k : ℕ)
    (cp : Fin k → C) : Point Ctx Msg C nl w :=
  ⟨ctx, roleAt k, List.ofFn fun i : Fin (k + 1) => msgOf out i.val, List.ofFn cp⟩

/-- A point's messages, as a function of the round. -/
def listMsgs [Inhabited Msg] (l : List Msg) : ℕ → Msg := fun i => l.getD i default

/-- A point's raw answers, as a prefix of length `j`. -/
def listPrefix (dflt : C) (l : List C) (j : ℕ) : Fin j → C := fun i => l.getD i.val dflt

theorem listPrefix_ofFn (dflt : C) {k : ℕ} (cp : Fin k → C) :
    listPrefix dflt (List.ofFn cp) k = cp := by
  funext i
  rw [listPrefix, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos i.isLt]
  rfl

theorem listMsgs_ofFn [Inhabited Msg] {k : ℕ} (f : ℕ → Msg) {i : ℕ} (hi : i < k + 1) :
    listMsgs (List.ofFn fun j : Fin (k + 1) => f j.val) i = f i := by
  rw [listMsgs, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hi]
  rfl

theorem roleAt_val (i : Fin (Rounds.Role.length nl w)) :
    roleAt (nl := nl) (w := w) i.val = Rounds.Role.indexEquiv.symm i := by
  rw [roleAt, dif_pos i.isLt]

end Points

/-! ## 3. One commitment: the grinding adversary is a `Bcs.TranscriptGrinding`

At a commitment where extraction fails, the Ligero half `ML` exists, and LayerStep is round-by-round
sound at **every** message sequence with the same budgets (`MsgBudgets.withMsgs`).  Doom at a point is the
LayerStep's doom at the point's messages and raw answers (`DoomedAt`); `escapesAt_card` is the role's
budget, from the sequential LayerStep at those messages; `link_at` says that at a verifier hash input the
sequential escape is the point's bad event, because LayerStep's state there reads only the messages and
answers the point carries (`layerStep_state_congr`).
-/

section OneCommitment

variable {C F X Q Cand Witness Msg Ctx Out : Type} [Fintype C] [DecidableEq C] [Nonempty C]
  [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F] [DecidableEq X] [Fintype Q]
  [DecidableEq Q] [Fintype Cand] [Nonempty Cand] [Inhabited Msg] [DecidableEq Msg] [DecidableEq Ctx]
variable {nc nv logw logc nl : ℕ} {w : ℕ → ℕ} {N : ℕ}
variable {H : Honest F Cand logw logc} {Sat : Cand → Prop} {LigDoomed : X → Prop}
variable (FD : RbrSplit.FieldData C F X Q Cand Witness nc nv logw logc H Sat)
  (MD : MsgData C Msg H) (ML : MsgLigeroData C X Q Msg LigDoomed)
variable {bpair bround bin blig bquery : ℕ}

/-- **Doom at a point**: LayerStep at the point's messages is doomed at the point's raw answers. -/
def DoomedAt (dflt : C) (p : Point Ctx Msg C nl w) : Prop :=
  (layerStep (nl := nl) (w := w) FD MD ML (listMsgs p.msgs)).doomed p.role.slot
    (listPrefix dflt p.chals p.role.slot)

/-- **Escape at a point**: the answer `c` takes LayerStep at the point's messages out of doom. -/
def EscapesAt (dflt : C) (p : Point Ctx Msg C nl w) (c : C) : Prop :=
  ¬ (layerStep (nl := nl) (w := w) FD MD ML (listMsgs p.msgs)).doomed (p.role.slot + 1)
    (Bcs.extend (listPrefix dflt p.chals p.role.slot) c)

/-- LayerStep at a message sequence, as a `Bcs.Rbr`, with `RbrSplit`'s per-role budgets. -/
noncomputable def layerStepRbr (hB : MsgBudgets FD ML bpair bround bin blig bquery)
    {Fails : Prop} (hfail : Fails → ∀ cand : Cand, ¬ Sat cand) (ms : ℕ → Msg) :
    Bcs.Rbr C (Rounds.Role.length nl w)
      (RbrSplit.LayerStepAccepts
        (RbrSplit.steps (nl := nl) (w := w) (withMsgs FD MD ms) (withMsgsL ML ms))) Fails :=
  (withMsgs FD MD ms).rbr (withMsgsL ML ms) (hB.withMsgs MD ms) hfail
    (RbrSplit.rightOfAccepts_of_layerStepAccepts _ fun _ h => h)

omit [DecidableEq Msg] [DecidableEq Ctx] in
/-- **A point's escape budget is its role's**: `|Cand| · classBudget role`.  It is the sequential
LayerStep's doom preservation at the point's messages, read at the point's slot. -/
theorem escapesAt_card (hB : MsgBudgets FD ML bpair bround bin blig bquery) (dflt : C)
    (p : Point Ctx Msg C nl w) (hp : DoomedAt FD MD ML dflt p) :
    (univ.filter fun c : C => EscapesAt FD MD ML dflt p c).card
      ≤ Fintype.card Cand *
          RbrLayerStep.classBudget (nl := nl) (w := w) bpair bround bin blig bquery p.role := by
  have h := (layerStepRbr FD MD ML hB (Fails := False) False.elim (listMsgs p.msgs)).doom_preserved
    p.role.index (listPrefix dflt p.chals p.role.slot) hp
  rw [show (layerStepRbr FD MD ML hB (Fails := False) False.elim (listMsgs p.msgs)).beta p.role.index
      = Fintype.card Cand * RbrLayerStep.classBudget (nl := nl) (w := w) bpair bround bin blig bquery
          (Rounds.Role.indexEquiv.symm p.role.index) from rfl,
    indexEquiv_symm_index] at h
  refine le_trans (Finset.card_le_card ?_) h
  intro c hc
  simp only [mem_filter, mem_univ, true_and] at hc ⊢
  exact hc

omit [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand] [DecidableEq Msg]
  [DecidableEq Ctx] in
/-- **The link**: at round `k`'s hash input, the sequential escape at the proof's messages is the
point's bad event. -/
theorem link_at (dflt : C) (ctx : Ctx) (msgOf : Out → ℕ → Msg) (out : Out) (k : ℕ) (cp : Fin k → C)
    (c : C) (hk : k < Rounds.Role.length nl w)
    (hd : (layerStep (nl := nl) (w := w) FD MD ML (msgOf out)).doomed k cp)
    (he : ¬ (layerStep (nl := nl) (w := w) FD MD ML (msgOf out)).doomed (k + 1) (Bcs.extend cp c)) :
    DoomedAt FD MD ML dflt (hashPoint (nl := nl) (w := w) ctx msgOf out k cp) ∧
      EscapesAt FD MD ML dflt (hashPoint (nl := nl) (w := w) ctx msgOf out k cp) c := by
  have hdoom : ∀ j, j ≤ k + 1 → ∀ q : Fin j → C,
      (layerStep (nl := nl) (w := w) FD MD ML
          (listMsgs (List.ofFn fun i : Fin (k + 1) => msgOf out i.val))).doomed j q ↔
        (layerStep (nl := nl) (w := w) FD MD ML (msgOf out)).doomed j q := by
    intro j hj q
    unfold Bcs.ClaimChain.doomed
    rw [layerStep_state_congr FD MD ML j (fun i hi => listMsgs_ofFn (msgOf out) (by omega)) q]
    rfl
  simp only [DoomedAt, EscapesAt, hashPoint]
  rw [slot_roleAt hk, listPrefix_ofFn]
  exact ⟨(hdoom k (by omega) cp).mpr hd, fun h => he ((hdoom (k + 1) le_rfl _).mp h)⟩

/-- The worst role's budget. -/
def maxBudget (bpair bround bin blig bquery : ℕ) : ℕ :=
  max (max (max (max bpair bround) bin) blig) bquery

theorem classBudget_le_max (rl : Rounds.Role nl w) :
    RbrLayerStep.classBudget (nl := nl) (w := w) bpair bround bin blig bquery rl
      ≤ maxBudget bpair bround bin blig bquery := by
  unfold maxBudget
  cases rl <;> simp [RbrLayerStep.classBudget]

/--
**One failing commitment's grinding adversary, as a `Bcs.TranscriptGrinding`.**

The adversary is `adv`, the hash inputs are `hashPoint ctx msgOf`, the state function at a proof is
LayerStep at its messages, and the bad event at a point is `DoomedAt`/`EscapesAt` with the role's
budget.  Every field is a theorem above.
-/
noncomputable def fsGrinding (hB : MsgBudgets FD ML bpair bround bin blig bquery)
    {Fails : Prop} (hfail : Fails → ∀ cand : Cand, ¬ Sat cand)
    (adv : Tree (Point Ctx Msg C nl w) C Out N) (dflt : C) (ctx : Ctx) (msgOf : Out → ℕ → Msg) :
    Bcs.TranscriptGrinding C (Point Ctx Msg C nl w) Out N (Rounds.Role.length nl w)
      (fun out ch => RbrSplit.LayerStepAccepts
        (RbrSplit.steps (nl := nl) (w := w) (withMsgs FD MD (msgOf out))
          (withMsgsL ML (msgOf out))) ch) Fails where
  adversary := adv
  dflt := dflt
  hashInput := hashPoint ctx msgOf
  doomed out := (layerStep (nl := nl) (w := w) FD MD ML (msgOf out)).doomed
  doomed_start hf out pt := (layerStepRbr FD MD ML hB hfail (msgOf out)).doomed_start hf pt
  accepts_undoomed out ch hacc := (layerStepRbr FD MD ML hB hfail (msgOf out)).accepts_undoomed ch hacc
  DoomedQuery := DoomedAt FD MD ML dflt
  Escapes := EscapesAt FD MD ML dflt
  beta p := Fintype.card Cand *
    RbrLayerStep.classBudget (nl := nl) (w := w) bpair bround bin blig bquery p.role
  escape_bound p hp := escapesAt_card FD MD ML hB dflt p hp
  link out k cp c hk hd he := link_at FD MD ML dflt ctx msgOf out k cp c hk hd he

/--
**The reduction to `Bcs.RbrCore`.**  The bad event at tape slot `i` is "the point queried at slot `i`
is doomed and the tape's answer there escapes", with the worst role's budget at every slot
(`Bcs.Grinding.toRbrCore`).  The tape has `L + N` slots.  `fs_card_le` uses the sharper per-role
count instead; this is the `RbrCore` form.
-/
noncomputable def fsCore (hB : MsgBudgets FD ML bpair bround bin blig bquery)
    {Fails : Prop} (hfail : Fails → ∀ cand : Cand, ¬ Sat cand)
    (adv : Tree (Point Ctx Msg C nl w) C Out N) (dflt : C) (ctx : Ctx) (msgOf : Out → ℕ → Msg) :
    Bcs.RbrCore C (Rounds.Role.length nl w + N)
      ((fsGrinding FD MD ML hB hfail adv dflt ctx msgOf).Accepts) Fails :=
  ((fsGrinding FD MD ML hB hfail adv dflt ctx msgOf).toGrinding
    (Fintype.card Cand * maxBudget bpair bround bin blig bquery)
    (fun p => Nat.mul_le_mul_left _ (classBudget_le_max p.role)) le_rfl).toRbrCore

/-- The Fiat–Shamir run's output on a challenge tape: the proof and the recomputed answers. -/
noncomputable def fsOutput (adv : Tree (Point Ctx Msg C nl w) C Out N) (dflt : C) (ctx : Ctx)
    (msgOf : Out → ℕ → Msg) {T : ℕ} (ct : Fin T → C) : Out × (ℕ → C) :=
  (lazyRun ct dflt (Bcs.execution adv (hashPoint ctx msgOf) dflt (Rounds.Role.length nl w)) []).1

/-- The adversary's proof. -/
noncomputable def fsProof (adv : Tree (Point Ctx Msg C nl w) C Out N) (dflt : C) (ctx : Ctx)
    (msgOf : Out → ℕ → Msg) {T : ℕ} (ct : Fin T → C) : Out :=
  (fsOutput adv dflt ctx msgOf ct).1

/-- The verifier's recomputed challenge answers, one per round. -/
noncomputable def fsChallenges (adv : Tree (Point Ctx Msg C nl w) C Out N) (dflt : C) (ctx : Ctx)
    (msgOf : Out → ℕ → Msg) {T : ℕ} (ct : Fin T → C) : Fin (Rounds.Role.length nl w) → C :=
  fun i => (fsOutput adv dflt ctx msgOf ct).2 i.val

/--
**One failing commitment, counted.**  Every event `E` on the challenge tape that implies LayerStep
accepts the adversary's proof at the recomputed challenges satisfies

```text
#E · |C|  ≤  |Cand| · ( N · max_role β  +  (nl·bpair + (∑ w)·bround + bin + blig + bquery) )
               · |C|^(L+N)
```

`Bcs.TranscriptGrinding.card_mul_le_weighted` at `fsGrinding`: each slot pays the budget of the role of
the point queried there.
-/
theorem fs_card_le (hB : MsgBudgets FD ML bpair bround bin blig bquery)
    {Fails : Prop} (hfail : Fails → ∀ cand : Cand, ¬ Sat cand) (hF : Fails)
    (adv : Tree (Point Ctx Msg C nl w) C Out N) (dflt : C) (ctx : Ctx) (msgOf : Out → ℕ → Msg)
    (E : (Fin (Rounds.Role.length nl w + N) → C) → Prop) [DecidablePred E]
    (hE : ∀ ct, E ct → RbrSplit.LayerStepAccepts
      (RbrSplit.steps (nl := nl) (w := w)
        (withMsgs FD MD (msgOf (fsProof adv dflt ctx msgOf ct)))
        (withMsgsL ML (msgOf (fsProof adv dflt ctx msgOf ct))))
      (fsChallenges adv dflt ctx msgOf ct)) :
    (univ.filter E).card * Fintype.card C
      ≤ Fintype.card Cand * (N * maxBudget bpair bround bin blig bquery
          + (nl * bpair + (∑ i ∈ Finset.range nl, w i) * bround + bin + blig + bquery))
        * Fintype.card C ^ (Rounds.Role.length nl w + N) := by
  have h := (fsGrinding FD MD ML hB hfail adv dflt ctx msgOf).card_mul_le_weighted
    (Fintype.card Cand * maxBudget bpair bround bin blig bquery)
    (fun p => Nat.mul_le_mul_left _ (classBudget_le_max p.role))
    (fun i => Fintype.card Cand *
      RbrLayerStep.classBudget (nl := nl) (w := w) bpair bround bin blig bquery
        (Rounds.Role.indexEquiv.symm i))
    (fun out i cp => by
      show Fintype.card Cand * RbrLayerStep.classBudget (nl := nl) (w := w) bpair bround bin blig bquery
          (roleAt i.val) ≤ _
      rw [roleAt_val])
    le_rfl E hE hF
  have hsum : ∑ i : Fin (Rounds.Role.length nl w), Fintype.card Cand *
        RbrLayerStep.classBudget (nl := nl) (w := w) bpair bround bin blig bquery
          (Rounds.Role.indexEquiv.symm i)
      = Fintype.card Cand *
          (nl * bpair + (∑ i ∈ Finset.range nl, w i) * bround + bin + blig + bquery) := by
    rw [← Finset.mul_sum, RbrLayerStep.layerStep_budget_sum]
  rw [hsum] at h
  refine le_trans h (le_of_eq ?_)
  ring

/-! ### With no search, the recomputed challenges are the tape

A check on the model rather than a step of the bound: when the adversary makes no query
(`adv = .done out`), the verifier's `L` hash inputs are pairwise distinct — they carry different
roles — so they take slots `0, …, L - 1` in order and round `i`'s challenge is tape slot `i`.  The
Fiat–Shamir LayerStep at `N = 0` is then the sequential LayerStep on the tape, which is the reading under which
`Row.fs_ratio_le_bound`'s `R.bound + 0 · κ` is the sequential row's bound.
-/

omit [Fintype C] [Nonempty C] [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
  [DecidableEq X] [Fintype Q] [DecidableEq Q] [Fintype Cand] [Nonempty Cand] [Inhabited Msg] in
theorem roleAt_injOn {i j : ℕ} (hi : i < Rounds.Role.length nl w) (hj : j < Rounds.Role.length nl w)
    (h : roleAt (nl := nl) (w := w) i = roleAt j) : i = j := by
  rw [roleAt, dif_pos hi, roleAt, dif_pos hj] at h
  exact congrArg Fin.val (Rounds.Role.indexEquiv.symm.injective h)

omit [Fintype C] [Nonempty C] [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
  [DecidableEq X] [Fintype Q] [DecidableEq Q] [Fintype Cand] [Nonempty Cand] [Inhabited Msg] in
/-- **No search, no grinding**: round `i`'s recomputed challenge is tape slot `i`. -/
theorem fsChallenges_done (out : Out) (dflt : C) (ctx : Ctx) (msgOf : Out → ℕ → Msg) {T : ℕ}
    (hT : Rounds.Role.length nl w ≤ T) (ct : Fin T → C) (i : Fin (Rounds.Role.length nl w)) :
    fsChallenges (Tree.done out : Tree (Point Ctx Msg C nl w) C Out 0) dflt ctx msgOf ct i
      = ct ⟨i.val, lt_of_lt_of_le i.isLt hT⟩ := by
  classical
  set E := Bcs.execution (Tree.done out : Tree (Point Ctx Msg C nl w) C Out 0)
    (hashPoint ctx msgOf) dflt (Rounds.Role.length nl w)
  set v := lazyRun ct dflt (Bcs.Recompute.rounds (hashPoint (nl := nl) (w := w) ctx msgOf out)
    (Rounds.Role.length nl w) 0 fun _ => dflt) []
  have hrun : lazyRun ct dflt E [] = ((out, v.1), v.2.1, v.2.2) := by
    have h := Bcs.lazyRun_execution (L := Rounds.Role.length nl w) ct dflt
      (Tree.done out : Tree (Point Ctx Msg C nl w) C Out 0) (hashPoint ctx msgOf)
    simpa using h
  obtain ⟨-, htr⟩ := Bcs.Recompute.lazyRun_rounds ct dflt
    (hashPoint (nl := nl) (w := w) ctx msgOf out) (Rounds.Role.length nl w) 0 (fun _ => dflt) []
  -- the trace's queries are the `L` hash inputs, pairwise distinct
  have hqs : (lazyRun ct dflt E []).2.2.map Prod.fst
      = (List.range' 0 (Rounds.Role.length nl w)).map fun k =>
          hashPoint (nl := nl) (w := w) ctx msgOf out k fun j : Fin k => v.1 j.val := by
    rw [hrun]
    show v.2.2.map Prod.fst = _
    rw [htr, List.map_map]
    rfl
  have hnodup : ((lazyRun ct dflt E []).2.2.map Prod.fst).Nodup := by
    rw [hqs]
    refine List.Nodup.map_on ?_ List.nodup_range'
    intro a ha b hb hab
    have ha' := (List.mem_range'.mp ha)
    have hb' := (List.mem_range'.mp hb)
    exact roleAt_injOn (nl := nl) (w := w) (by omega) (by omega)
      (congrArg Point.role hab)
  have hlen : i.val < ((lazyRun ct dflt E []).2.2.map Prod.fst).length := by
    rw [hqs]
    simp
  have hidx := lazyRun_slot_eq_of_nodup ct dflt E hnodup i.val hlen
  have hget : ((lazyRun ct dflt E []).2.2.map Prod.fst)[i.val]
      = hashPoint (nl := nl) (w := w) ctx msgOf out i.val fun j : Fin i.val => v.1 j.val := by
    simp only [hqs, List.getElem_map]
    have hr : ∀ h : i.val < (List.range' 0 (Rounds.Role.length nl w)).length,
        (List.range' 0 (Rounds.Role.length nl w))[i.val]'h = i.val := fun _ => by simp
    rw [hr]
  rw [hget] at hidx
  -- round `i`'s entry, and its slot
  have hmem : (hashPoint (nl := nl) (w := w) ctx msgOf out i.val (fun j : Fin i.val => v.1 j.val),
      v.1 i.val) ∈ (lazyRun ct dflt E []).2.2 := by
    rw [hrun]
    show _ ∈ v.2.2
    rw [htr]
    exact List.mem_map.mpr ⟨i.val, List.mem_range'.mpr ⟨i.val, by omega, by omega⟩, rfl⟩
  obtain ⟨-, hval⟩ := lazyRun_trace_slot ct dflt E [] _ hmem
  have hout : fsChallenges (Tree.done out : Tree (Point Ctx Msg C nl w) C Out 0) dflt ctx msgOf ct i
      = v.1 i.val := by
    show (lazyRun ct dflt E []).1.2 i.val = v.1 i.val
    rw [hrun]
  rw [hout]
  have hval' : v.1 i.val = tapeAt ct dflt ((lazyRun ct dflt E []).2.1.idxOf
      (hashPoint (nl := nl) (w := w) ctx msgOf out i.val fun j : Fin i.val => v.1 j.val)) := hval
  rw [hval', hidx, tapeAt, dif_pos (lt_of_lt_of_le i.isLt hT)]

end OneCommitment

/-! ## 4. Summing over commitments -/

/-- **Slicing on the commitment.**  A per-commitment count `#slice · |C| ≤ B · |Coins|` is the
probability bound `B / |C|` over the product. -/
theorem ratio_of_slices {Pre Coins : Type} [Fintype Pre] [Fintype Coins] [Nonempty Pre]
    [Nonempty Coins] (P : Pre × Coins → Prop) [DecidablePred P] (cardC : ℕ) (hC : 0 < cardC)
    (B : ℕ) (h : ∀ pre : Pre, (univ.filter fun c : Coins => P (pre, c)).card * cardC
      ≤ B * Fintype.card Coins) :
    ((univ.filter P).card : ℚ) / ((Fintype.card Pre : ℚ) * Fintype.card Coins)
      ≤ (B : ℚ) / cardC := by
  have hsum : (univ.filter P).card * cardC ≤ Fintype.card Pre * (B * Fintype.card Coins) := by
    rw [Bcs.card_filter_prod_fst, Finset.sum_mul]
    calc ∑ pre : Pre, (univ.filter fun c : Coins => P (pre, c)).card * cardC
        ≤ ∑ _pre : Pre, B * Fintype.card Coins := Finset.sum_le_sum fun pre _ => h pre
      _ = Fintype.card Pre * (B * Fintype.card Coins) := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hq : ((univ.filter P).card : ℚ) * cardC
      ≤ (Fintype.card Pre : ℚ) * ((B : ℚ) * Fintype.card Coins) := by exact_mod_cast hsum
  have hPpos : (0 : ℚ) < Fintype.card Pre := by exact_mod_cast Fintype.card_pos
  have hCpos : (0 : ℚ) < Fintype.card Coins := by exact_mod_cast Fintype.card_pos
  have hcpos : (0 : ℚ) < cardC := by exact_mod_cast hC
  rw [div_le_div_iff₀ (mul_pos hPpos hCpos) hcpos]
  linarith

end Lfzk.NizkGrinding

/-! ## 5. At a certified V1 row -/

namespace Lfzk.CertifiedV1

open Finset Bcs Merkle Merkle.MH Merkle.RandomOracle RbrLongfellow Lfzk.NizkGrinding
open scoped Classical

/-- A row's challenge-tape length against an `N`-query search: `L` recomputed rounds, then `N`. -/
abbrev Row.fsLen (R : Row) (N : ℕ) : ℕ := Rounds.Role.length R.params.nl R.params.rounds + N

/-- **The worst slot's density at a row**: a field slot's `2/|F|` (the input binding's `1/|F|` is
below it), the Ligero challenge slot's `fail + arith`, the query slot's `cover`. -/
def Row.maxDensity (R : Row) : ℚ :=
  max (max (2 / (R.params.row.fieldSize : ℚ)) (R.params.row.fail + R.params.row.arith))
    R.params.row.cover

/-- **The work-normalized coefficient**: the soundness error one hash query can buy,
`cardCand · maxDensity`. -/
def Row.fsCoefficient (R : Row) : ℚ := (R.cardCand : ℚ) * R.maxDensity

/-- Every slot's budget is at most `|C|` times the worst density. -/
theorem maxBudget_le_density (R : Row) {cardC : ℕ} (hC : 0 < cardC)
    (hF : 0 < R.params.row.fieldSize) :
    (maxBudget (pairBudget cardC R.params.row.fieldSize) (pairBudget cardC R.params.row.fieldSize)
        (inBudget cardC R.params.row.fieldSize) (ligBudget R.params.row cardC)
        (queryBudget R.params.row cardC) : ℚ)
      ≤ (cardC : ℚ) * R.maxDensity := by
  have hc : (0 : ℚ) < (cardC : ℚ) := by exact_mod_cast hC
  have hf : (0 : ℚ) < (R.params.row.fieldSize : ℚ) := by exact_mod_cast hF
  set f : ℚ := (R.params.row.fieldSize : ℚ)
  set c : ℚ := (cardC : ℚ)
  have hfa := add_nonneg (LigeroV1LayerStep.fail_nonneg R.params.row)
    (LigeroV1LayerStep.arith_nonneg R.params.row)
  have hcv := LigeroV1LayerStep.cover_nonneg R.params.row
  have hbp : (pairBudget cardC R.params.row.fieldSize : ℚ) ≤ c * (2 / f) := by
    unfold pairBudget
    refine le_trans (Nat.cast_div_le) (le_of_eq ?_)
    push_cast
    ring
  have hbi : (inBudget cardC R.params.row.fieldSize : ℚ) ≤ c * (2 / f) := by
    unfold inBudget
    refine le_trans (Nat.cast_div_le) ?_
    rw [show c * (2 / f) = 2 * (c / f) by ring]
    have : 0 ≤ c / f := by positivity
    linarith
  have hbl : (ligBudget R.params.row cardC : ℚ) ≤ c * (R.params.row.fail + R.params.row.arith) := by
    unfold ligBudget
    refine le_trans (Nat.floor_le (mul_nonneg hfa (Nat.cast_nonneg _))) (le_of_eq ?_)
    ring
  have hbq : (queryBudget R.params.row cardC : ℚ) ≤ c * R.params.row.cover := by
    unfold queryBudget
    refine le_trans (Nat.floor_le (mul_nonneg hcv (Nat.cast_nonneg _))) (le_of_eq ?_)
    ring
  have h1 : c * (2 / f) ≤ c * R.maxDensity :=
    mul_le_mul_of_nonneg_left (le_trans (le_max_left _ _) (le_max_left _ _)) hc.le
  have h2 : c * (R.params.row.fail + R.params.row.arith) ≤ c * R.maxDensity :=
    mul_le_mul_of_nonneg_left (le_trans (le_max_right _ _) (le_max_left _ _)) hc.le
  have h3 : c * R.params.row.cover ≤ c * R.maxDensity :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) hc.le
  unfold maxBudget
  push_cast
  refine max_le (max_le (max_le (max_le ?_ ?_) ?_) ?_) ?_ <;> linarith

/-- The schedule's length at a row: `nl` layer pairs, the sumcheck rounds, three tail slots. -/
theorem length_eq (P : Lfzk.CostV1.Params) :
    Rounds.Role.length P.nl P.rounds = P.nl + P.totalRounds + 3 := by
  unfold Rounds.Role.length Rounds.Role.layerBase Lfzk.CostV1.Params.totalRounds
  rw [Finset.sum_add_distrib]
  simp

/--
**A certified V1 row, against a grinding Fiat–Shamir adversary.**

Over the hash tape and a challenge tape of `L + N` slots, against a Merkle adversary `A` and a
Fiat–Shamir search `adv` making at most `N` challenge-oracle queries after the commitment:

```text
Pr[ the compiled verifier accepts at the recomputed Ligero challenge and query  ∧  Fails ]
    ≤  R.bound  +  N · R.fsCoefficient
```

`R.bound` is the sequential row's bound (so `N = 0` loses nothing) and `R.fsCoefficient =
cardCand · maxDensity` is what each extra hash query can buy.

**Every premise**, and nothing else:

* the protocol instance — `|F| = row.fieldSize` (`hF`), a Reed–Solomon domain `dom`, one Ligero V1
  instance per commitment `lig`, the field half of LayerStep `Ffam` with exactly balanced decoders
  (`hexact`) and `RbrLongfellow`'s field premises inside it, the message reading `MD`, `|Cand|`,
  `|D|`, and the Merkle fuels `ht₁`, `hT`, `hT1`;
* `hfalse` — at a commitment where extraction fails, the Ligero statement is false (Ligero's
  extractor; what the V1 theorem needs);
* `hfail` — extraction failure means no candidate satisfies the circuit;
* `hright` — **the Fiat–Shamir transliteration**: if the compiled verifier accepts at
  `challengeOf`/`queryOf` with extraction explaining it, then LayerStep on the adversary's proof's
  messages accepts at the verifier's recomputed challenges, with the V1 query test.  It carries that
  `challengeOf`/`queryOf` are the decoded recomputed Ligero rounds and that `lig pre`'s prover
  answers as `A` does (README gap 1).

`Ffam`'s `B` and `prover` fields are not read: `withMsgs` replaces them by `MD` at the proof's
messages.
-/
theorem Row.fs_ratio_le_bound {R : Row} (h : R.Valid)
    {C Cand : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
    {F Equations Witness : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype Equations] [DecidableEq Equations]
    {logw logc nc nv : ℕ}
    {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
    {Enc D Salt M Aux Aux' : Type} {n respondFuel revealFuel : ℕ}
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    {Ctx Msg Out : Type} [DecidableEq Ctx] [DecidableEq Msg] [Inhabited Msg] {N : ℕ}
    {codec : Codec Salt M D Enc} (dec : RoleDecoders codec)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (A : Adversary Enc D Salt M Challenge Response Query Aux Aux'
      n R.commitFuel respondFuel revealFuel)
    -- the Fiat–Shamir search, run after the commitment, and how its proof is read
    (adv : Aux → Tree (Point Ctx Msg C R.params.nl R.params.rounds) C Out N)
    (dflt : C) (ctxOf : Aux → Ctx) (msgOf : Out → ℕ → Msg)
    -- the compiled verifier's Ligero challenge and query, read after the commitment
    (challengeOf : Aux → (Fin (R.fsLen N) → C) →
      Challenge)
    (queryOf : Aux → (Fin (R.fsLen N) → C) → Query)
    (statement : (Fin R.tape → D) ×
      (Fin (R.fsLen N) → C) → Statement)
    {Fails : (Fin R.tape → D) → Prop}
    -- the Ligero V1 step: the field, the code's domain, and one instance per commitment
    (hF : Fintype.card F = R.params.row.fieldSize)
    (dom : LigeroFamily.ReedSolomon.Domain F R.params.row.openings R.params.q R.params.row.n)
    (lig : ∀ _pre : Fin R.tape → D,
      LigeroV1LayerStep.Instance R.params.row F Equations R.params.nw R.params.nq R.params.q)
    (hfalse : ∀ pre : Fin R.tape → D, Fails pre → ¬ (lig pre).statement.Language)
    -- the field half of LayerStep, one per commitment, with exactly balanced decoders
    (H : ∀ _pre : Fin R.tape → D, RbrLongfellow.Honest F Cand logw logc)
    (Sat : (Fin R.tape → D) → Cand → Prop)
    (Ffam : ∀ pre : Fin R.tape → D,
      RbrSplit.FieldData C F (LigeroV1LayerStep.Chal F Equations R.params.nw R.params.nq)
        (LigeroV1LayerStep.Qry R.params.row) Cand Witness nc nv logw logc (H pre) (Sat pre))
    (hexact : ∀ pre : Fin R.tape → D, (Ffam pre).Exact)
    (MD : ∀ pre : Fin R.tape → D, MsgData C Msg (H pre))
    -- extraction, and acceptance
    (hfail : ∀ pre : Fin R.tape → D, Fails pre → ∀ cand : Cand, ¬ Sat pre cand)
    (hright : ∀ pre : Fin R.tape → D, Fails pre →
      ∀ ct : Fin (R.fsLen N) → C,
        (CompiledAccepts K A codec (statement (pre, ct))
            (challengeOf (A.auxOf pre) ct) (queryOf (A.auxOf pre) ct) pre ∧
          ExtractionExplains codec dec n R.commitFuel (revealFuel + respondFuel) R.tape A.commit
            (A.openingStage (challengeOf (A.auxOf pre) ct) (queryOf (A.auxOf pre) ct)) pre) →
        RbrSplit.LayerStepAccepts
          (RbrSplit.stepsOf (nl := R.params.nl) (w := R.params.rounds)
            (withMsgs (Ffam pre) (MD pre)
              (msgOf (fsProof (adv (A.auxOf pre)) dflt (ctxOf (A.auxOf pre)) msgOf ct)))
            (fun _ _ => LigeroV1LayerStep.accepting (Row.rowValid h) dom (Row.hkrow h) (lig pre)))
          (fsChallenges (adv (A.auxOf pre)) dflt (ctxOf (A.auxOf pre)) msgOf ct))
    -- the Merkle extractor's fuels
    (ht₁ : R.commitFuel ≤ R.tape)
    (hT : 2 * n + (revealFuel + respondFuel) + R.commitFuel ≤ R.tape) (hT1 : 1 ≤ R.tape)
    (hcand : Fintype.card Cand = R.cardCand)
    (hD : Fintype.card D = 2 ^ R.params.digestBits) :
    ((univ.filter fun omega : (Fin R.tape → D) ×
          (Fin (R.fsLen N) → C) =>
        CompiledAccepts K A codec (statement omega)
            (challengeOf (A.auxOf omega.1) omega.2) (queryOf (A.auxOf omega.1) omega.2) omega.1 ∧
          Fails omega.1).card : ℚ)
        / (Fintype.card (Fin R.tape → D) *
            (Fintype.card C : ℚ) ^ (R.fsLen N))
      ≤ R.bound + N * R.fsCoefficient := by
  classical
  -- the Ligero half, at each commitment where extraction fails
  have hex := fun (pre : Fin R.tape → D) (hFp : Fails pre) =>
    LigeroV1LayerStep.exists_ligeroData C (Row.rowValid h) (Row.coreRows h) hF dom (Row.hkrow h)
      (lig pre) (hfalse pre hFp)
  choose LigD LD hacc hesc hbq using hex
  have hFpos : 0 < R.params.row.fieldSize := by rw [← hF]; exact Fintype.card_pos
  have hCpos : 0 < Fintype.card C := Fintype.card_pos
  have ep : 2 * Fintype.card C / Fintype.card F
      = pairBudget (Fintype.card C) R.params.row.fieldSize := by rw [hF]; rfl
  have ei : Fintype.card C / Fintype.card F
      = inBudget (Fintype.card C) R.params.row.fieldSize := by rw [hF]; rfl
  have hB : ∀ (pre : Fin R.tape → D) (hFp : Fails pre),
      MsgBudgets (Ffam pre) (MsgLigeroData.ofLigeroData (Msg := Msg) (LD pre hFp))
        (pairBudget (Fintype.card C) R.params.row.fieldSize)
        (pairBudget (Fintype.card C) R.params.row.fieldSize)
        (inBudget (Fintype.card C) R.params.row.fieldSize)
        (ligBudget R.params.row (Fintype.card C)) (queryBudget R.params.row (Fintype.card C)) := by
    intro pre hFp
    obtain ⟨hp0, hp1, hr, hi⟩ := (hexact pre).field_budgets
    obtain ⟨-, -, hchal, hq⟩ := hexact pre
    exact MsgBudgets.ofLigeroData ⟨hp0.trans_eq ep, hp1.trans_eq ep, hr.trans_eq ep, hi.trans_eq ei,
      LigeroV1LayerStep.ligBudget_le (hesc pre hFp) hchal,
      (hbq pre hFp) ▸ LigeroV1LayerStep.queryBudget_le hq⟩
  -- the per-commitment grinding count
  set βmax := maxBudget (pairBudget (Fintype.card C) R.params.row.fieldSize)
    (pairBudget (Fintype.card C) R.params.row.fieldSize)
    (inBudget (Fintype.card C) R.params.row.fieldSize) (ligBudget R.params.row (Fintype.card C))
    (queryBudget R.params.row (Fintype.card C))
  set sumβ := R.params.nl * pairBudget (Fintype.card C) R.params.row.fieldSize
    + (∑ i ∈ Finset.range R.params.nl, R.params.rounds i)
      * pairBudget (Fintype.card C) R.params.row.fieldSize
    + inBudget (Fintype.card C) R.params.row.fieldSize + ligBudget R.params.row (Fintype.card C)
    + queryBudget R.params.row (Fintype.card C)
  let Acc : (Fin R.tape → D) × (Fin (R.fsLen N) → C) → Prop := fun omega =>
    CompiledAccepts K A codec (statement omega)
        (challengeOf (A.auxOf omega.1) omega.2) (queryOf (A.auxOf omega.1) omega.2) omega.1 ∧
      ExtractionExplains codec dec n R.commitFuel (revealFuel + respondFuel) R.tape A.commit
        (A.openingStage (challengeOf (A.auxOf omega.1) omega.2)
          (queryOf (A.auxOf omega.1) omega.2)) omega.1
  have hslice : ∀ pre : Fin R.tape → D,
      (univ.filter fun ct : Fin (R.fsLen N) → C => Acc (pre, ct) ∧ Fails pre).card * Fintype.card C
        ≤ (Fintype.card Cand * (N * βmax + sumβ)) * Fintype.card (Fin (R.fsLen N) → C) := by
    intro pre
    rw [Fintype.card_fun, Fintype.card_fin]
    by_cases hFp : Fails pre
    · refine fs_card_le (Ffam pre) (MD pre) (MsgLigeroData.ofLigeroData (LD pre hFp)) (hB pre hFp)
        (hfail pre) hFp (adv (A.auxOf pre)) dflt (ctxOf (A.auxOf pre)) msgOf _ fun ct hct => ?_
      show RbrSplit.LayerStepAccepts (RbrSplit.stepsOf _ (LD pre hFp).accepting) _
      rw [hacc pre hFp]
      exact hright pre hFp ct hct.1
    · refine le_trans (le_of_eq ?_) (Nat.zero_le _)
      rw [Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun ct _ hct => hFp hct.2),
        zero_mul]
  have hcount := ratio_of_slices (fun omega : (Fin R.tape → D) × (Fin (R.fsLen N) → C) =>
      Acc omega ∧ Fails omega.1) (Fintype.card C) hCpos _ hslice
  -- the Merkle step
  have hmerkle := drop_explains_ratio_le_aux dec K A challengeOf queryOf statement
    (fun omega => Fails omega.1) ht₁ hT hT1
  have hden : (Fintype.card (Fin R.tape → D) : ℚ) * (Fintype.card C : ℚ) ^ (R.fsLen N)
      = (Fintype.card D : ℚ) ^ R.tape * Fintype.card (Fin (R.fsLen N) → C) := by
    rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    push_cast
    ring
  have hden' : (Fintype.card (Fin R.tape → D) : ℚ) * Fintype.card (Fin (R.fsLen N) → C)
      = (Fintype.card D : ℚ) ^ R.tape * Fintype.card (Fin (R.fsLen N) → C) := by
    rw [Fintype.card_fun, Fintype.card_fin]
    push_cast
    ring
  rw [hden]
  rw [hden'] at hcount
  have hstep : ((univ.filter fun omega : (Fin R.tape → D) × (Fin (R.fsLen N) → C) =>
        CompiledAccepts K A codec (statement omega)
            (challengeOf (A.auxOf omega.1) omega.2) (queryOf (A.auxOf omega.1) omega.2) omega.1 ∧
          Fails omega.1).card : ℚ)
        / ((Fintype.card D : ℚ) ^ R.tape * Fintype.card (Fin (R.fsLen N) → C))
      ≤ ((Fintype.card Cand * (N * βmax + sumβ) : ℕ) : ℚ) / (Fintype.card C : ℚ)
        + (merkleNumerator R.commitFuel R.tape : ℚ) / (Fintype.card D : ℚ) := by
    refine le_trans (by convert hmerkle using 3) (add_le_add_left ?_ _)
    convert hcount using 3
  refine le_trans hstep ?_
  -- the densities
  have hc : (0 : ℚ) < (Fintype.card C : ℚ) := by exact_mod_cast hCpos
  have hseq := budgets_le_bound R hCpos hFpos (cardCand := Fintype.card Cand) hD
  have hmax := maxBudget_le_density R hCpos hFpos
  have hsplit : ((Fintype.card Cand * (N * βmax + sumβ) : ℕ) : ℚ) / (Fintype.card C : ℚ)
      = ((Fintype.card Cand * sumβ : ℕ) : ℚ) / (Fintype.card C : ℚ)
        + (Fintype.card Cand : ℚ) * N * ((βmax : ℚ) / (Fintype.card C : ℚ)) := by
    push_cast
    field_simp
    ring
  have hβ : (βmax : ℚ) / (Fintype.card C : ℚ) ≤ R.maxDensity := by
    rw [div_le_iff₀ hc]
    linarith
  rw [hsplit]
  have hbound : R.bound = R.params.nizkBound R.cardCand R.commitFuel R.tape := rfl
  rw [hbound, ← hcand]
  unfold Row.fsCoefficient
  rw [← hcand]
  have hNcand : (0 : ℚ) ≤ (Fintype.card Cand : ℚ) * N := by positivity
  have := mul_le_mul_of_nonneg_left hβ hNcand
  linarith

/-- A row's field size is positive: a prime order or a power of two. -/
theorem fieldSize_pos (row : Lfzk.LigeroV1Rows.Row) : 0 < row.fieldSize := by
  unfold Lfzk.LigeroV1Rows.Row.fieldSize Ligero.Examples.Grid.Certificate.fieldSize
  split_ifs with h
  · positivity
  · omega

/-- The sequential densities are at most `L` slots at the worst density. -/
theorem densities_le_length (R : Row) :
    R.params.fieldDensity + R.params.ligeroDensity
      ≤ (Rounds.Role.length R.params.nl R.params.rounds : ℚ) * R.maxDensity := by
  have hf : (0 : ℚ) < (R.params.row.fieldSize : ℚ) := by exact_mod_cast fieldSize_pos R.params.row
  have h2 : 2 / (R.params.row.fieldSize : ℚ) ≤ R.maxDensity :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have h1 : 1 / (R.params.row.fieldSize : ℚ) ≤ R.maxDensity := by
    refine le_trans ?_ h2
    exact div_le_div_of_nonneg_right (by norm_num) hf.le
  have hfa : R.params.row.fail + R.params.row.arith ≤ R.maxDensity :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hcv : R.params.row.cover ≤ R.maxDensity := le_max_right _ _
  have hfield : R.params.fieldDensity
      = ((R.params.nl : ℚ) + R.params.totalRounds) * (2 / (R.params.row.fieldSize : ℚ))
        + 1 / (R.params.row.fieldSize : ℚ) := by
    unfold Lfzk.CostV1.Params.fieldDensity
    push_cast
    field_simp
  have hlen : (Rounds.Role.length R.params.nl R.params.rounds : ℚ)
      = (R.params.nl : ℚ) + R.params.totalRounds + 3 := by
    rw [length_eq]
    push_cast
    ring
  rw [hfield, hlen]
  unfold Lfzk.CostV1.Params.ligeroDensity
  have hS : (0 : ℚ) ≤ (R.params.nl : ℚ) + R.params.totalRounds := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h2 hS]

/-- **The uniform form**: `R.bound + N · κ ≤ (L + N) · κ + merkleTerm`.  `κ = R.fsCoefficient` is the
factor multiplying the adversary's total work `N + L`. -/
theorem Row.bound_add_le_uniform (R : Row) (N : ℕ) :
    R.bound + N * R.fsCoefficient
      ≤ ((Rounds.Role.length R.params.nl R.params.rounds + N : ℕ) : ℚ) * R.fsCoefficient
        + R.params.merkleTerm R.commitFuel R.tape := by
  have h := densities_le_length R
  have hc : (0 : ℚ) ≤ (R.cardCand : ℚ) := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left h hc
  rw [Nat.cast_add]
  unfold Row.bound Lfzk.CostV1.Params.nizkBound Row.fsCoefficient
  linarith

/-! ## 6. The v8 hash row -/

/-- **The row's work-normalized coefficient is at most `2^-115`.**  Checked by evaluation, as
`v8Hash_valid` is. -/
theorem v8Hash_fsCoefficient : v8Hash.fsCoefficient ≤ (1 : ℚ) / 2 ^ 115 := by
  native_decide

/-- **…and `117` is its exact integer bit level.** -/
theorem v8Hash_fsCoefficient_sharp : ¬ v8Hash.fsCoefficient ≤ (1 : ℚ) / 2 ^ 116 := by
  native_decide

/-- **The worst slot at the row is the Ligero challenge slot.** -/
theorem v8Hash_maxDensity_eq :
    v8Hash.maxDensity = v8Hash.params.row.fail + v8Hash.params.row.arith := by
  native_decide

/-- The schedule length at the row: `20 + 610 + 3`. -/
theorem v8Hash_length :
    Rounds.Role.length v8Hash.params.nl v8Hash.params.rounds = 633 := by
  native_decide

/--
**The v8 hash row against a grinding Fiat–Shamir adversary.**

`Row.fs_ratio_le_bound` at `v8Hash` (the deployed hash profile (20 layers, 610 sumcheck slots) over
`GF(2^128)`, Ligero V1 at the deployed geometry `n = 4088`, `k = 584` with 132 opened columns):

```text
Pr[ accept ∧ Fails ]  ≤  2^-114  +  N · 2^-115
```

over the hash tape and a challenge tape of `633 + N` slots, against an `N`-query search.  `2^-114`
is the sequential row's certified bound (`v8Hash_valid`) and `2^-115` the certified
work-normalized coefficient (`v8Hash_fsCoefficient`).  The premises are `Row.fs_ratio_le_bound`'s.
-/
theorem v8Hash_fs_ratio_le
    {C Cand : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
    {F Equations Witness : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype Equations] [DecidableEq Equations]
    {logw logc nc nv : ℕ}
    {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
    {Enc D Salt M Aux Aux' : Type} {n respondFuel revealFuel : ℕ}
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    {Ctx Msg Out : Type} [DecidableEq Ctx] [DecidableEq Msg] [Inhabited Msg] {N : ℕ}
    {codec : Codec Salt M D Enc} (dec : RoleDecoders codec)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (A : Adversary Enc D Salt M Challenge Response Query Aux Aux'
      n v8Hash.commitFuel respondFuel revealFuel)
    -- the Fiat–Shamir search, run after the commitment, and how its proof is read
    (adv : Aux → Tree (Point Ctx Msg C v8Hash.params.nl v8Hash.params.rounds) C Out N)
    (dflt : C) (ctxOf : Aux → Ctx) (msgOf : Out → ℕ → Msg)
    -- the compiled verifier's Ligero challenge and query, read after the commitment
    (challengeOf : Aux → (Fin (v8Hash.fsLen N) → C) →
      Challenge)
    (queryOf : Aux → (Fin (v8Hash.fsLen N) → C) → Query)
    (statement : (Fin v8Hash.tape → D) ×
      (Fin (v8Hash.fsLen N) → C) → Statement)
    {Fails : (Fin v8Hash.tape → D) → Prop}
    -- the Ligero V1 step: the field, the code's domain, and one instance per commitment
    (hF : Fintype.card F = v8Hash.params.row.fieldSize)
    (dom : LigeroFamily.ReedSolomon.Domain F v8Hash.params.row.openings v8Hash.params.q
      v8Hash.params.row.n)
    (lig : ∀ _pre : Fin v8Hash.tape → D,
      LigeroV1LayerStep.Instance v8Hash.params.row F Equations v8Hash.params.nw
        v8Hash.params.nq v8Hash.params.q)
    (hfalse : ∀ pre : Fin v8Hash.tape → D, Fails pre → ¬ (lig pre).statement.Language)
    -- the field half of LayerStep, one per commitment, with exactly balanced decoders
    (H : ∀ _pre : Fin v8Hash.tape → D, RbrLongfellow.Honest F Cand logw logc)
    (Sat : (Fin v8Hash.tape → D) → Cand → Prop)
    (Ffam : ∀ pre : Fin v8Hash.tape → D,
      RbrSplit.FieldData C F
        (LigeroV1LayerStep.Chal F Equations v8Hash.params.nw v8Hash.params.nq)
        (LigeroV1LayerStep.Qry v8Hash.params.row) Cand Witness nc nv logw logc (H pre) (Sat pre))
    (hexact : ∀ pre : Fin v8Hash.tape → D, (Ffam pre).Exact)
    (MD : ∀ pre : Fin v8Hash.tape → D, MsgData C Msg (H pre))
    -- extraction, and acceptance
    (hfail : ∀ pre : Fin v8Hash.tape → D, Fails pre → ∀ cand : Cand, ¬ Sat pre cand)
    (hright : ∀ pre : Fin v8Hash.tape → D, Fails pre →
      ∀ ct : Fin (v8Hash.fsLen N) → C,
        (CompiledAccepts K A codec (statement (pre, ct))
            (challengeOf (A.auxOf pre) ct) (queryOf (A.auxOf pre) ct) pre ∧
          ExtractionExplains codec dec n v8Hash.commitFuel (revealFuel + respondFuel)
            v8Hash.tape A.commit
            (A.openingStage (challengeOf (A.auxOf pre) ct) (queryOf (A.auxOf pre) ct)) pre) →
        RbrSplit.LayerStepAccepts
          (RbrSplit.stepsOf (nl := v8Hash.params.nl) (w := v8Hash.params.rounds)
            (withMsgs (Ffam pre) (MD pre)
              (msgOf (fsProof (adv (A.auxOf pre)) dflt (ctxOf (A.auxOf pre)) msgOf ct)))
            (fun _ _ => LigeroV1LayerStep.accepting (Row.rowValid v8Hash_valid) dom
              (Row.hkrow v8Hash_valid) (lig pre)))
          (fsChallenges (adv (A.auxOf pre)) dflt (ctxOf (A.auxOf pre)) msgOf ct))
    -- the Merkle extractor's fuels
    (ht₁ : v8Hash.commitFuel ≤ v8Hash.tape)
    (hT : 2 * n + (revealFuel + respondFuel) + v8Hash.commitFuel ≤ v8Hash.tape)
    (hT1 : 1 ≤ v8Hash.tape)
    (hcand : Fintype.card Cand = v8Hash.cardCand)
    (hD : Fintype.card D = 2 ^ v8Hash.params.digestBits) :
    ((univ.filter fun omega : (Fin v8Hash.tape → D) ×
          (Fin (v8Hash.fsLen N) → C) =>
        CompiledAccepts K A codec (statement omega)
            (challengeOf (A.auxOf omega.1) omega.2) (queryOf (A.auxOf omega.1) omega.2) omega.1 ∧
          Fails omega.1).card : ℚ)
        / (Fintype.card (Fin v8Hash.tape → D) *
            (Fintype.card C : ℚ) ^ (v8Hash.fsLen N))
      ≤ (1 : ℚ) / 2 ^ 114 + N * ((1 : ℚ) / 2 ^ 115) :=
  le_trans
    (Row.fs_ratio_le_bound v8Hash_valid dec K A adv dflt ctxOf msgOf challengeOf queryOf
      statement hF dom lig hfalse H Sat Ffam hexact MD hfail hright ht₁ hT hT1 hcand hD)
    (add_le_add (Row.target v8Hash_valid)
      (mul_le_mul_of_nonneg_left v8Hash_fsCoefficient (Nat.cast_nonneg N)))

/--
**The same row in the uniform, work-normalized form**:

```text
Pr[ accept ∧ Fails ]  ≤  (633 + N) · 2^-115  +  merkleTerm
```

The factor multiplying the adversary's total work `L + N` (`L = 633` recomputed rounds, `N` own
queries) is the certified coefficient `2^-115`; the Merkle term is the row's, unchanged from the
sequential theorem.  This form is weaker than `v8Hash_fs_ratio_le` at every `N` — it charges the
verifier's `633` recomputations at the worst slot's density too — and is stated because it is the
normalization the plan quotes.
-/
theorem v8Hash_fs_ratio_le_uniform
    {C Cand : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
    {F Equations Witness : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype Equations] [DecidableEq Equations]
    {logw logc nc nv : ℕ}
    {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
    {Enc D Salt M Aux Aux' : Type} {n respondFuel revealFuel : ℕ}
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    {Ctx Msg Out : Type} [DecidableEq Ctx] [DecidableEq Msg] [Inhabited Msg] {N : ℕ}
    {codec : Codec Salt M D Enc} (dec : RoleDecoders codec)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (A : Adversary Enc D Salt M Challenge Response Query Aux Aux'
      n v8Hash.commitFuel respondFuel revealFuel)
    -- the Fiat–Shamir search, run after the commitment, and how its proof is read
    (adv : Aux → Tree (Point Ctx Msg C v8Hash.params.nl v8Hash.params.rounds) C Out N)
    (dflt : C) (ctxOf : Aux → Ctx) (msgOf : Out → ℕ → Msg)
    -- the compiled verifier's Ligero challenge and query, read after the commitment
    (challengeOf : Aux → (Fin (v8Hash.fsLen N) → C) →
      Challenge)
    (queryOf : Aux → (Fin (v8Hash.fsLen N) → C) → Query)
    (statement : (Fin v8Hash.tape → D) ×
      (Fin (v8Hash.fsLen N) → C) → Statement)
    {Fails : (Fin v8Hash.tape → D) → Prop}
    -- the Ligero V1 step: the field, the code's domain, and one instance per commitment
    (hF : Fintype.card F = v8Hash.params.row.fieldSize)
    (dom : LigeroFamily.ReedSolomon.Domain F v8Hash.params.row.openings v8Hash.params.q
      v8Hash.params.row.n)
    (lig : ∀ _pre : Fin v8Hash.tape → D,
      LigeroV1LayerStep.Instance v8Hash.params.row F Equations v8Hash.params.nw
        v8Hash.params.nq v8Hash.params.q)
    (hfalse : ∀ pre : Fin v8Hash.tape → D, Fails pre → ¬ (lig pre).statement.Language)
    -- the field half of LayerStep, one per commitment, with exactly balanced decoders
    (H : ∀ _pre : Fin v8Hash.tape → D, RbrLongfellow.Honest F Cand logw logc)
    (Sat : (Fin v8Hash.tape → D) → Cand → Prop)
    (Ffam : ∀ pre : Fin v8Hash.tape → D,
      RbrSplit.FieldData C F
        (LigeroV1LayerStep.Chal F Equations v8Hash.params.nw v8Hash.params.nq)
        (LigeroV1LayerStep.Qry v8Hash.params.row) Cand Witness nc nv logw logc (H pre) (Sat pre))
    (hexact : ∀ pre : Fin v8Hash.tape → D, (Ffam pre).Exact)
    (MD : ∀ pre : Fin v8Hash.tape → D, MsgData C Msg (H pre))
    -- extraction, and acceptance
    (hfail : ∀ pre : Fin v8Hash.tape → D, Fails pre → ∀ cand : Cand, ¬ Sat pre cand)
    (hright : ∀ pre : Fin v8Hash.tape → D, Fails pre →
      ∀ ct : Fin (v8Hash.fsLen N) → C,
        (CompiledAccepts K A codec (statement (pre, ct))
            (challengeOf (A.auxOf pre) ct) (queryOf (A.auxOf pre) ct) pre ∧
          ExtractionExplains codec dec n v8Hash.commitFuel (revealFuel + respondFuel)
            v8Hash.tape A.commit
            (A.openingStage (challengeOf (A.auxOf pre) ct) (queryOf (A.auxOf pre) ct)) pre) →
        RbrSplit.LayerStepAccepts
          (RbrSplit.stepsOf (nl := v8Hash.params.nl) (w := v8Hash.params.rounds)
            (withMsgs (Ffam pre) (MD pre)
              (msgOf (fsProof (adv (A.auxOf pre)) dflt (ctxOf (A.auxOf pre)) msgOf ct)))
            (fun _ _ => LigeroV1LayerStep.accepting (Row.rowValid v8Hash_valid) dom
              (Row.hkrow v8Hash_valid) (lig pre)))
          (fsChallenges (adv (A.auxOf pre)) dflt (ctxOf (A.auxOf pre)) msgOf ct))
    -- the Merkle extractor's fuels
    (ht₁ : v8Hash.commitFuel ≤ v8Hash.tape)
    (hT : 2 * n + (revealFuel + respondFuel) + v8Hash.commitFuel ≤ v8Hash.tape)
    (hT1 : 1 ≤ v8Hash.tape)
    (hcand : Fintype.card Cand = v8Hash.cardCand)
    (hD : Fintype.card D = 2 ^ v8Hash.params.digestBits) :
    ((univ.filter fun omega : (Fin v8Hash.tape → D) ×
          (Fin (v8Hash.fsLen N) → C) =>
        CompiledAccepts K A codec (statement omega)
            (challengeOf (A.auxOf omega.1) omega.2) (queryOf (A.auxOf omega.1) omega.2) omega.1 ∧
          Fails omega.1).card : ℚ)
        / (Fintype.card (Fin v8Hash.tape → D) *
            (Fintype.card C : ℚ) ^ (v8Hash.fsLen N))
      ≤ ((633 + N : ℕ) : ℚ) * ((1 : ℚ) / 2 ^ 115)
        + v8Hash.params.merkleTerm v8Hash.commitFuel v8Hash.tape := by
  refine le_trans
    (Row.fs_ratio_le_bound v8Hash_valid dec K A adv dflt ctxOf msgOf challengeOf queryOf
      statement hF dom lig hfalse H Sat Ffam hexact MD hfail hright ht₁ hT hT1 hcand hD)
    (le_trans (v8Hash.bound_add_le_uniform N) ?_)
  rw [v8Hash_length]
  exact add_le_add_left (mul_le_mul_of_nonneg_left v8Hash_fsCoefficient (Nat.cast_nonneg _)) _

end Lfzk.CertifiedV1
