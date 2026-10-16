import Lfzk.NizkGrinding
import Bcs.TotalOracle

/-!
# The Longfellow bound with Fiat–Shamir hash inputs as deployed: message prefixes only

`Lfzk.NizkGrinding` charges a grinding adversary per hash query at points `NizkGrinding.Point` that
carry the **raw answers of the earlier rounds** (README R4).  The deployed transcript does not hash
earlier challenges: one SHA-256 running state absorbs the prover's messages, and round `k`'s challenge
is a PRF expansion of the digest after message `k`, never re-absorbed.  So round `k`'s challenge is
a function of the message prefix alone, and a deployed adversary that asks one prefix asks *one*
point — translated into the raw-answer model it would have to ask every earlier round first, a factor
`L` (`L = 633` at the v8 hash row) on `N`.  This file states the composed Longfellow bound with `N`
counting **deployed** hash queries.

## The idealisation, exactly

The SHA-256 running state plus the PRF expansion is modelled as **one random oracle on message
prefixes**: a uniformly random function `ro : MPoint Ctx Msg nl w → C` (`Bcs.TotalOracle`), where
`MPoint` is the commitment context (the root), the role the challenge is drawn for, and the prover's
messages through that round.  Stated rather than proved:

* **domain separation** — distinct `(context, round, message prefix)` triples are distinct oracle
  inputs; in the deployed transcript this is the injectivity of the absorbed byte encoding
  (length-prefixed field elements, round labels), plus SHA-256 behaving as a random oracle on it;
* **the PRF expansion** of a digest into a challenge is part of the oracle (its output is uniform
  on `C`);
* **the challenge decoders** `C → F`, `C → X`, `C → Q` are the ones `RbrSplit.FieldData` already
  carries, with `Exact` balance as before (`hexact`): no new decoder assumption;
* `Msg` and `Ctx` are finite types (deployed messages are bounded byte strings), so the oracle is a
  finite sample space.

Transliteration debt that remains (unchanged from `Lfzk.NizkGrinding`): that the deployed byte
encoding of a prefix is what `msgPoint` abstracts (R4 is reduced to this), that the verifier's
challenge for round `k` is read at round `k`'s prefix (`msgPoint ctx msgOf out k`), and `hright`.

## What is proved

* `MPoint`, `msgPoint`, `mpoints` — the deployed hash inputs, round `k`'s point, and their ancestor
  structure: round `j < k`'s point of the same prefix is the ancestor, and no point is its own
  (`Bcs.TotalOracle.PrefixPoints`).
* `prefixGrinding`, `shed_at_msgPoint_of` — **for any chain on the Longfellow schedule** (any family
  of `Bcs.Rbr`s indexed by the message sequence whose state at length `j` reads only messages `< j`):
  the prefix-only grinding count and the chain step of the re-committing form.  This is the
  interface a second chain (the deployed ZK verifier's LayerStep) instantiates.
* `fsGrinding` — one failing commitment's prefix-only adversary as a `Bcs.TotalOracle.Grinding`,
  from LayerStep's round-by-round analysis at every message sequence (`Bcs.TotalOracle.Grinding.ofRbr`
  at `NizkGrinding.layerStepRbr`).  `fs_card_le` is its count:
  `#E · |C| ≤ |Cand| · (N · max_role β + ∑ role, β role) · |C|^|MPoint|` — the same right-hand side as
  `NizkGrinding.fs_card_le`, with `N` now the number of **prefix-only** queries.
* `row_fs_ratio_le_bound` — at any certified V1 row, against a Merkle adversary and an `N`-query
  prefix-only search: `Pr[accept ∧ Fails] ≤ R.bound + N · R.fsCoefficient` (the numerals of
  `CertifiedV1.Row.fs_ratio_le_bound`, unchanged); `row_fs_ratio_le_bits` the same at any certified
  bit levels, and `v8Hash_fs_ratio_le`: `≤ 2^-114 + N · 2^-115`.

The re-committing (adaptive) and compiled forms are in `Lfzk.NizkDeployedHashAdaptive`, the
two-field composition in `Lfzk.NizkDeployedHashTwoField`, and the v7 restatements in
`Lfzk.NizkDeployedHashV7`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.NizkDeployedHash

open Finset Bcs Merkle Merkle.MH Merkle.RandomOracle RbrLongfellow Lfzk.NizkGrinding
open scoped Classical

/-! ## 1. Deployed hash inputs -/

section Points

variable {Ctx Msg : Type} {nl : ℕ} {w : ℕ → ℕ}

/-- **A deployed Fiat–Shamir hash input**: the commitment context, the role the challenge is drawn
for, and the prover's messages through that round (`msgs i` for `i ≤ role.slot`; the entries past it
are padding, `default` at the verifier's points).  No challenge. -/
structure MPoint (Ctx Msg : Type) (nl : ℕ) (w : ℕ → ℕ) where
  /-- The commitment context (the root). -/
  ctx : Ctx
  /-- The round the challenge is drawn for. -/
  role : Rounds.Role nl w
  /-- The prover's messages, through `role.slot`. -/
  msgs : Fin (Rounds.Role.length nl w) → Msg

/-- `MPoint` is a triple. -/
def MPoint.equiv : MPoint Ctx Msg nl w ≃
    Ctx × Rounds.Role nl w × (Fin (Rounds.Role.length nl w) → Msg) where
  toFun p := (p.ctx, p.role, p.msgs)
  invFun t := ⟨t.1, t.2.1, t.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance [DecidableEq Ctx] [DecidableEq Msg] : DecidableEq (MPoint Ctx Msg nl w) :=
  MPoint.equiv.decidableEq

noncomputable instance [Fintype Ctx] [Fintype Msg] : Fintype (MPoint Ctx Msg nl w) :=
  Fintype.ofEquiv _ MPoint.equiv.symm

variable [Inhabited Msg]

/-- The messages `0, …, k` of `f`, padded with `default`. -/
def padMsgs (f : ℕ → Msg) (k : ℕ) : Fin (Rounds.Role.length nl w) → Msg :=
  fun i => if i.val ≤ k then f i.val else default

/-- **Round `k`'s deployed hash input**: the context, round `k`'s role and the proof's messages
`0, …, k`. -/
noncomputable def msgPoint {Out : Type} (ctx : Ctx) (msgOf : Out → ℕ → Msg) (out : Out) (k : ℕ) :
    MPoint Ctx Msg nl w :=
  ⟨ctx, roleAt k, padMsgs (msgOf out) k⟩

/-- The messages a point carries, as a function of the round. -/
def MPoint.msgFn (p : MPoint Ctx Msg nl w) : ℕ → Msg :=
  fun i => if h : i < Rounds.Role.length nl w then p.msgs ⟨i, h⟩ else default

/-- **The ancestor structure**: a point's round is its role's slot, and its round-`j` ancestor is
the point of round `j` with the same context and messages `0, …, j`.  Distinct roles, so no point is
its own ancestor. -/
noncomputable def mpoints : TotalOracle.PrefixPoints (MPoint Ctx Msg nl w) where
  slot p := p.role.slot
  anc p j := ⟨p.ctx, roleAt j, padMsgs p.msgFn j⟩
  anc_ne p j hj h := by
    have hr := congrArg (fun q : MPoint Ctx Msg nl w => q.role.slot) h
    simp only at hr
    rw [slot_roleAt (lt_trans hj p.role.slot_lt)] at hr
    omega

theorem msgFn_msgPoint {Out : Type} (ctx : Ctx) (msgOf : Out → ℕ → Msg) (out : Out) {k i : ℕ}
    (hk : k < Rounds.Role.length nl w) (hi : i ≤ k) :
    (msgPoint (nl := nl) (w := w) ctx msgOf out k).msgFn i = msgOf out i := by
  simp only [MPoint.msgFn, msgPoint, dif_pos (lt_of_le_of_lt hi hk), padMsgs, if_pos hi]

theorem slot_msgPoint {Out : Type} (ctx : Ctx) (msgOf : Out → ℕ → Msg) (out : Out) {k : ℕ}
    (hk : k < Rounds.Role.length nl w) :
    (mpoints (Ctx := Ctx) (Msg := Msg) (nl := nl) (w := w)).slot (msgPoint ctx msgOf out k) = k :=
  slot_roleAt hk

/-- Round `k`'s point's round-`j` ancestor is round `j`'s point. -/
theorem anc_msgPoint {Out : Type} (ctx : Ctx) (msgOf : Out → ℕ → Msg) (out : Out) {k j : ℕ}
    (hjk : j < k) (hk : k < Rounds.Role.length nl w) :
    (mpoints (Ctx := Ctx) (Msg := Msg) (nl := nl) (w := w)).anc (msgPoint ctx msgOf out k) j
      = msgPoint ctx msgOf out j := by
  show (⟨ctx, roleAt j, padMsgs (msgPoint (nl := nl) (w := w) ctx msgOf out k).msgFn j⟩ :
      MPoint Ctx Msg nl w) = ⟨ctx, roleAt j, padMsgs (msgOf out) j⟩
  congr 1
  funext i
  simp only [padMsgs]
  split_ifs with hi
  · exact msgFn_msgPoint ctx msgOf out hk (by omega)
  · rfl

/-- At a deployed verifier point, the ancestor answers are exactly the
preceding verifier answers on the same proof's message schedule. -/
theorem chal_msgPoint_eq_prefix {C Out : Type} (ctx : Ctx)
    (msgOf : Out → ℕ → Msg) (out : Out)
    (ro : MPoint Ctx Msg nl w → C)
    (k : Fin (Rounds.Role.length nl w)) :
    (fun j : Fin k.val =>
      mpoints.chal ro (msgPoint ctx msgOf out k.val)
        ⟨j.val, by rw [slot_msgPoint ctx msgOf out k.isLt]; exact j.isLt⟩) =
      Sumcheck.extract_prefix
        (fun i : Fin (Rounds.Role.length nl w) =>
          ro (msgPoint ctx msgOf out i.val)) k := by
  funext j
  change ro (mpoints.anc (msgPoint ctx msgOf out k.val) j.val) =
    ro (msgPoint ctx msgOf out j.val)
  rw [anc_msgPoint ctx msgOf out j.isLt k.isLt]

end Points

/-! ## 2. Any chain on the Longfellow schedule

What a round-by-round analysis must provide to be counted over the oracle on message prefixes, for
any family of state functions indexed by the prover's message sequence — the LayerStep chain below,
or another chain on the same `Rounds.Role` schedule (the deployed ZK verifier's): the state at a
prefix of length `j` reads only messages `< j` (`hcongr`).  Then round `k`'s point carries all the
state reads through length `k + 1`, `prefixGrinding` is the `Bcs.TotalOracle.Grinding`, and
`shed_at_msgPoint_of` is the chain step for the re-committing form.
-/

section AnyChain

variable {C Msg Ctx Out : Type} [Fintype C] [Inhabited Msg] {nl : ℕ} {w : ℕ → ℕ}

omit [Fintype C] in
/-- **The chain step at a verifier point, for any state family that reads messages causally.**  If
the proof's state function, at the verifier's challenges `ro (msgPoint … i)`, sheds doom at round
`k`, then at round `k`'s point — judged at its ancestors' answers — the point's state function is
doomed and the point's own answer escapes. -/
theorem shed_at_msgPoint_of (doomedF : (ℕ → Msg) → (j : ℕ) → (Fin j → C) → Prop)
    (hcongr : ∀ (ms ms' : ℕ → Msg) (j : ℕ), (∀ i, i < j → ms i = ms' i) →
      ∀ p : Fin j → C, doomedF ms j p ↔ doomedF ms' j p)
    (ctx : Ctx) (msgOf : Out → ℕ → Msg) (out : Out)
    (ro : MPoint Ctx Msg nl w → C) (k : Fin (Rounds.Role.length nl w))
    (hd : doomedF (msgOf out) k.val
      (Sumcheck.extract_prefix
        (fun i : Fin (Rounds.Role.length nl w) => ro (msgPoint ctx msgOf out i.val)) k))
    (he : ¬ doomedF (msgOf out) (k.val + 1)
      (Bcs.extend (Sumcheck.extract_prefix
        (fun i : Fin (Rounds.Role.length nl w) => ro (msgPoint ctx msgOf out i.val)) k)
        (ro (msgPoint ctx msgOf out k.val)))) :
    doomedF (msgPoint (nl := nl) (w := w) ctx msgOf out k.val).msgFn
        (mpoints.slot (msgPoint (nl := nl) (w := w) ctx msgOf out k.val))
        (mpoints.chal ro (msgPoint (nl := nl) (w := w) ctx msgOf out k.val)) ∧
      ¬ doomedF (msgPoint (nl := nl) (w := w) ctx msgOf out k.val).msgFn
        (mpoints.slot (msgPoint (nl := nl) (w := w) ctx msgOf out k.val) + 1)
        (Bcs.extend (mpoints.chal ro (msgPoint (nl := nl) (w := w) ctx msgOf out k.val))
          (ro (msgPoint (nl := nl) (w := w) ctx msgOf out k.val))) := by
  set p := msgPoint (nl := nl) (w := w) ctx msgOf out k.val with hp
  have hs : (mpoints (Ctx := Ctx) (Msg := Msg) (nl := nl) (w := w)).slot p = k.val :=
    slot_msgPoint ctx msgOf out k.isLt
  have hpre : (fun j : Fin k.val => ro (mpoints.anc p j.val))
      = Sumcheck.extract_prefix
          (fun i : Fin (Rounds.Role.length nl w) => ro (msgPoint ctx msgOf out i.val)) k := by
    funext j
    show ro (mpoints.anc p j.val) = ro (msgPoint ctx msgOf out j.val)
    rw [hp, anc_msgPoint ctx msgOf out j.isLt k.isLt]
  have hmsg : ∀ j, j ≤ k.val + 1 → ∀ i, i < j → p.msgFn i = msgOf out i :=
    fun j hj i hi => msgFn_msgPoint ctx msgOf out k.isLt (by omega)
  show doomedF p.msgFn (mpoints.slot p) (fun j => ro (mpoints.anc p j.val)) ∧
    ¬ doomedF p.msgFn (mpoints.slot p + 1) (Bcs.extend (fun j => ro (mpoints.anc p j.val)) (ro p))
  rw [TotalOracle.prefix_cast (doomedF p.msgFn) (fun j => ro (mpoints.anc p j)) hs,
    TotalOracle.prefix_cast_extend (doomedF p.msgFn) (fun j => ro (mpoints.anc p j)) (ro p) hs,
    hpre, hcongr _ _ k.val (hmsg k.val (Nat.le_succ _)),
    hcongr _ _ (k.val + 1) (hmsg (k.val + 1) le_rfl)]
  exact ⟨hd, he⟩

variable {N : ℕ} [DecidableEq Msg] [DecidableEq Ctx]

/-- **Any causal family of `Bcs.Rbr`s on the Longfellow schedule, as a prefix-only grinding count.**
`R ms` is the round-by-round analysis at the message sequence `ms` (from a `Bcs.ClaimChain` by
`ClaimChain.toRbr`); `hcongr` says its state at length `j` reads only messages `< j`. -/
noncomputable def prefixGrinding {Acc : (ℕ → Msg) → (Fin (Rounds.Role.length nl w) → C) → Prop}
    {Fails : Prop} (R : ∀ ms : ℕ → Msg, Bcs.Rbr C (Rounds.Role.length nl w) (Acc ms) Fails)
    (hcongr : ∀ (ms ms' : ℕ → Msg) (j : ℕ), (∀ i, i < j → ms i = ms' i) →
      ∀ p : Fin j → C, (R ms).doomed j p ↔ (R ms').doomed j p)
    (adv : Tree (MPoint Ctx Msg nl w) C Out N) (ctx : Ctx) (msgOf : Out → ℕ → Msg) :
    TotalOracle.Grinding C (MPoint Ctx Msg nl w) Out N (Rounds.Role.length nl w)
      (fun out => Acc (msgOf out)) Fails :=
  TotalOracle.Grinding.ofRbr R adv (msgPoint ctx msgOf) mpoints msgOf MPoint.msgFn
    (fun q => q.role.slot_lt)
    (fun out _ hk => slot_msgPoint ctx msgOf out hk)
    (fun out _ _ hjk hk => anc_msgPoint ctx msgOf out hjk hk)
    (fun out k hk j hj p => hcongr _ _ j
      (fun i hi => msgFn_msgPoint ctx msgOf out hk (by omega)) p)

end AnyChain

/-! ## 3. One commitment: the prefix-only adversary is a `Bcs.TotalOracle.Grinding` -/

section OneCommitment

variable {C F X Q Cand Witness Msg Ctx Out : Type} [Fintype C] [DecidableEq C] [Nonempty C]
  [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F] [DecidableEq X] [Fintype Q]
  [DecidableEq Q] [Fintype Cand] [Nonempty Cand] [Inhabited Msg] [DecidableEq Msg] [DecidableEq Ctx]
variable {nc nv logw logc nl : ℕ} {w : ℕ → ℕ} {N : ℕ}
variable {H : Honest F Cand logw logc} {Sat : Cand → Prop} {LigDoomed : X → Prop}
variable (FD : RbrSplit.FieldData C F X Q Cand Witness nc nv logw logc H Sat)
  (MD : MsgData C Msg H) (ML : MsgLigeroData C X Q Msg LigDoomed)
variable {bpair bround bin blig bquery : ℕ}

/-- The adversary's proof against the oracle `ro`. -/
def dProof (adv : Tree (MPoint Ctx Msg nl w) C Out N) (ro : MPoint Ctx Msg nl w → C) : Out :=
  (adv.run ro).1

/-- **The verifier's challenges**: round `i`'s is the oracle at round `i`'s message prefix. -/
noncomputable def dChallenges (adv : Tree (MPoint Ctx Msg nl w) C Out N) (ctx : Ctx)
    (msgOf : Out → ℕ → Msg) (ro : MPoint Ctx Msg nl w → C) : Fin (Rounds.Role.length nl w) → C :=
  fun i => ro (msgPoint ctx msgOf (dProof adv ro) i.val)

omit [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand] [DecidableEq Msg]
  [DecidableEq Ctx] in
/-- **The link**: round `k`'s point carries the proof's messages through round `k`, which is all
LayerStep's state reads through length `k + 1`. -/
theorem doomed_msgPoint (ctx : Ctx) (msgOf : Out → ℕ → Msg) (out : Out) (k : ℕ)
    (hk : k < Rounds.Role.length nl w) (j : ℕ) (hj : j ≤ k + 1) (p : Fin j → C) :
    (layerStep (nl := nl) (w := w) FD MD ML
        (msgPoint (nl := nl) (w := w) ctx msgOf out k).msgFn).doomed j p ↔
      (layerStep (nl := nl) (w := w) FD MD ML (msgOf out)).doomed j p := by
  unfold Bcs.ClaimChain.doomed
  rw [layerStep_state_congr FD MD ML j (fun i hi => msgFn_msgPoint ctx msgOf out hk (by omega)) p]
  rfl

omit [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand] [DecidableEq Msg]
  [DecidableEq Ctx] in
/--
**The chain at a verifier point.**  If LayerStep at the proof's messages, read at the verifier's
challenges (round `i`'s is `ro` at round `i`'s message prefix), sheds doom at round `k`, then at round
`k`'s point — judged at its ancestors' answers, each read at its own coordinate — LayerStep at the
point's messages is doomed, and the point's own answer escapes.
-/
theorem shed_at_msgPoint (ctx : Ctx) (msgOf : Out → ℕ → Msg) (out : Out)
    (ro : MPoint Ctx Msg nl w → C) (k : Fin (Rounds.Role.length nl w))
    (hd : (layerStep (nl := nl) (w := w) FD MD ML (msgOf out)).doomed k.val
      (Sumcheck.extract_prefix
        (fun i : Fin (Rounds.Role.length nl w) => ro (msgPoint ctx msgOf out i.val)) k))
    (he : ¬ (layerStep (nl := nl) (w := w) FD MD ML (msgOf out)).doomed (k.val + 1)
      (Bcs.extend (Sumcheck.extract_prefix
        (fun i : Fin (Rounds.Role.length nl w) => ro (msgPoint ctx msgOf out i.val)) k)
        (ro (msgPoint ctx msgOf out k.val)))) :
    (layerStep (nl := nl) (w := w) FD MD ML
        (msgPoint (nl := nl) (w := w) ctx msgOf out k.val).msgFn).doomed
        (mpoints.slot (msgPoint (nl := nl) (w := w) ctx msgOf out k.val))
        (mpoints.chal ro (msgPoint (nl := nl) (w := w) ctx msgOf out k.val)) ∧
      ¬ (layerStep (nl := nl) (w := w) FD MD ML
        (msgPoint (nl := nl) (w := w) ctx msgOf out k.val).msgFn).doomed
        (mpoints.slot (msgPoint (nl := nl) (w := w) ctx msgOf out k.val) + 1)
        (Bcs.extend (mpoints.chal ro (msgPoint (nl := nl) (w := w) ctx msgOf out k.val))
          (ro (msgPoint (nl := nl) (w := w) ctx msgOf out k.val))) := by
  set p := msgPoint (nl := nl) (w := w) ctx msgOf out k.val with hp
  have hs : (mpoints (Ctx := Ctx) (Msg := Msg) (nl := nl) (w := w)).slot p = k.val :=
    slot_msgPoint ctx msgOf out k.isLt
  have hpre : (fun j : Fin k.val => ro (mpoints.anc p j.val))
      = Sumcheck.extract_prefix
          (fun i : Fin (Rounds.Role.length nl w) => ro (msgPoint ctx msgOf out i.val)) k := by
    funext j
    show ro (mpoints.anc p j.val) = ro (msgPoint ctx msgOf out j.val)
    rw [hp, anc_msgPoint ctx msgOf out j.isLt k.isLt]
  show (layerStep (nl := nl) (w := w) FD MD ML p.msgFn).doomed (mpoints.slot p)
      (fun j => ro (mpoints.anc p j.val)) ∧
    ¬ (layerStep (nl := nl) (w := w) FD MD ML p.msgFn).doomed (mpoints.slot p + 1)
      (Bcs.extend (fun j => ro (mpoints.anc p j.val)) (ro p))
  rw [TotalOracle.prefix_cast (layerStep (nl := nl) (w := w) FD MD ML p.msgFn).doomed
      (fun j => ro (mpoints.anc p j)) hs,
    TotalOracle.prefix_cast_extend (layerStep (nl := nl) (w := w) FD MD ML p.msgFn).doomed
      (fun j => ro (mpoints.anc p j)) (ro p) hs, hpre,
    doomed_msgPoint FD MD ML ctx msgOf out k.val k.isLt k.val (Nat.le_succ _),
    doomed_msgPoint FD MD ML ctx msgOf out k.val k.isLt (k.val + 1) le_rfl]
  exact ⟨hd, he⟩

/--
**One failing commitment's prefix-only adversary, as a `Bcs.TotalOracle.Grinding`.**

The state function at a proof is LayerStep at its messages, the state function at a point is
LayerStep at the point's messages, the hash inputs are `msgPoint ctx msgOf` (no challenge
argument), and every field is `Bcs.TotalOracle.Grinding.ofRbr` at `NizkGrinding.layerStepRbr`.
-/
noncomputable def fsGrinding (hB : MsgBudgets FD ML bpair bround bin blig bquery)
    {Fails : Prop} (hfail : Fails → ∀ cand : Cand, ¬ Sat cand)
    (adv : Tree (MPoint Ctx Msg nl w) C Out N) (ctx : Ctx) (msgOf : Out → ℕ → Msg) :
    TotalOracle.Grinding C (MPoint Ctx Msg nl w) Out N (Rounds.Role.length nl w)
      (fun out => RbrSplit.LayerStepAccepts
        (RbrSplit.steps (nl := nl) (w := w) (withMsgs FD MD (msgOf out))
          (withMsgsL ML (msgOf out)))) Fails :=
  TotalOracle.Grinding.ofRbr (fun ms => layerStepRbr (nl := nl) (w := w) FD MD ML hB hfail ms) adv
    (msgPoint ctx msgOf) mpoints msgOf MPoint.msgFn (fun q => q.role.slot_lt)
    (fun out _ hk => slot_msgPoint ctx msgOf out hk)
    (fun out _ _ hjk hk => anc_msgPoint ctx msgOf out hjk hk)
    (fun out k hk j hj p => doomed_msgPoint FD MD ML ctx msgOf out k hk j hj p)

/-- A point's budget is its role's, times the list factor. -/
theorem fsGrinding_beta (hB : MsgBudgets FD ML bpair bround bin blig bquery)
    {Fails : Prop} (hfail : Fails → ∀ cand : Cand, ¬ Sat cand)
    (adv : Tree (MPoint Ctx Msg nl w) C Out N) (ctx : Ctx) (msgOf : Out → ℕ → Msg)
    (p : MPoint Ctx Msg nl w) :
    (fsGrinding FD MD ML hB hfail adv ctx msgOf).beta p
      = Fintype.card Cand *
          RbrLayerStep.classBudget (nl := nl) (w := w) bpair bround bin blig bquery p.role := by
  show Fintype.card Cand * RbrLayerStep.classBudget (nl := nl) (w := w) bpair bround bin blig bquery
      (Rounds.Role.indexEquiv.symm p.role.index) = _
  rw [indexEquiv_symm_index]

/--
**One failing commitment, counted**, over the total oracle on message prefixes.  Every event `E`
that implies LayerStep accepts the adversary's proof at the verifier's challenges satisfies

```text
#E · |C|  ≤  |Cand| · ( N · max_role β  +  (nl·bpair + (∑ w)·bround + bin + blig + bquery) )
               · |C|^|MPoint|
```

`NizkGrinding.fs_card_le`'s right-hand side, with `N` the number of prefix-only queries.
-/
theorem fs_card_le [Fintype Ctx] [Fintype Msg] (hB : MsgBudgets FD ML bpair bround bin blig bquery)
    {Fails : Prop} (hfail : Fails → ∀ cand : Cand, ¬ Sat cand) (hF : Fails)
    (adv : Tree (MPoint Ctx Msg nl w) C Out N) (ctx : Ctx) (msgOf : Out → ℕ → Msg)
    (E : (MPoint Ctx Msg nl w → C) → Prop) [DecidablePred E]
    (hE : ∀ ro, E ro → RbrSplit.LayerStepAccepts
      (RbrSplit.steps (nl := nl) (w := w)
        (withMsgs FD MD (msgOf (dProof adv ro))) (withMsgsL ML (msgOf (dProof adv ro))))
      (dChallenges adv ctx msgOf ro)) :
    (univ.filter E).card * Fintype.card C
      ≤ Fintype.card Cand * (N * maxBudget bpair bround bin blig bquery
          + (nl * bpair + (∑ i ∈ Finset.range nl, w i) * bround + bin + blig + bquery))
        * Fintype.card C ^ Fintype.card (MPoint Ctx Msg nl w) := by
  set G := fsGrinding FD MD ML hB hfail adv ctx msgOf with hG
  have h := G.card_mul_le (Fintype.card Cand * maxBudget bpair bround bin blig bquery)
    (fun p => by
      rw [hG, fsGrinding_beta]
      exact Nat.mul_le_mul_left _ (classBudget_le_max p.role))
    (fun i => Fintype.card Cand *
      RbrLayerStep.classBudget (nl := nl) (w := w) bpair bround bin blig bquery
        (Rounds.Role.indexEquiv.symm i))
    (fun out i => by
      rw [hG, fsGrinding_beta]
      show Fintype.card Cand * RbrLayerStep.classBudget (nl := nl) (w := w) bpair bround bin blig
          bquery (roleAt i.val) ≤ _
      rw [roleAt_val])
    E (fun ro hro => hE ro hro) hF
  have hsum : ∑ i : Fin (Rounds.Role.length nl w), Fintype.card Cand *
        RbrLayerStep.classBudget (nl := nl) (w := w) bpair bround bin blig bquery
          (Rounds.Role.indexEquiv.symm i)
      = Fintype.card Cand *
          (nl * bpair + (∑ i ∈ Finset.range nl, w i) * bround + bin + blig + bquery) := by
    rw [← Finset.mul_sum, RbrLayerStep.layerStep_budget_sum]
  rw [hsum] at h
  refine le_trans h (le_of_eq ?_)
  ring

end OneCommitment

/-! ## 4. At a certified V1 row -/

section Row

open Lfzk.CertifiedV1

/--
**A certified V1 row against a prefix-only grinding Fiat–Shamir adversary.**

Over the hash tape and the random oracle on message prefixes, against a Merkle adversary `A` and a
search `adv` making at most `N` queries at message prefixes after the commitment:

```text
Pr[ the compiled verifier accepts at the Ligero challenge and query  ∧  Fails ]
    ≤  R.bound  +  N · R.fsCoefficient
```

`CertifiedV1.Row.fs_ratio_le_bound`'s numerals, with `N` the number of **deployed** hash queries.
Premises are that theorem's, with `hright` restated at the oracle: if the compiled verifier accepts at
`challengeOf`/`queryOf` with extraction explaining it, LayerStep on the proof's messages accepts at
the verifier's challenges `dChallenges` (round `k`'s is the oracle at round `k`'s message prefix).
-/
theorem row_fs_ratio_le_bound {R : Row} (h : R.Valid)
    {C Cand : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
    {F Equations Witness : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype Equations] [DecidableEq Equations]
    {logw logc nc nv : ℕ}
    {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
    {Enc D Salt M Aux Aux' : Type} {n respondFuel revealFuel : ℕ}
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    {Ctx Msg Out : Type} [Fintype Ctx] [DecidableEq Ctx] [Fintype Msg] [DecidableEq Msg]
    [Inhabited Msg] {N : ℕ}
    {codec : Codec Salt M D Enc} (dec : RoleDecoders codec)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (A : Adversary Enc D Salt M Challenge Response Query Aux Aux'
      n R.commitFuel respondFuel revealFuel)
    -- the prefix-only search, run after the commitment, and how its proof is read
    (adv : Aux → Tree (MPoint Ctx Msg R.params.nl R.params.rounds) C Out N)
    (ctxOf : Aux → Ctx) (msgOf : Out → ℕ → Msg)
    -- the compiled verifier's Ligero challenge and query, read after the commitment
    (challengeOf : Aux → (MPoint Ctx Msg R.params.nl R.params.rounds → C) → Challenge)
    (queryOf : Aux → (MPoint Ctx Msg R.params.nl R.params.rounds → C) → Query)
    (statement : (Fin R.tape → D) × (MPoint Ctx Msg R.params.nl R.params.rounds → C) → Statement)
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
      ∀ ro : MPoint Ctx Msg R.params.nl R.params.rounds → C,
        (CompiledAccepts K A codec (statement (pre, ro))
            (challengeOf (A.auxOf pre) ro) (queryOf (A.auxOf pre) ro) pre ∧
          ExtractionExplains codec dec n R.commitFuel (revealFuel + respondFuel) R.tape A.commit
            (A.openingStage (challengeOf (A.auxOf pre) ro) (queryOf (A.auxOf pre) ro)) pre) →
        RbrSplit.LayerStepAccepts
          (RbrSplit.stepsOf (nl := R.params.nl) (w := R.params.rounds)
            (withMsgs (Ffam pre) (MD pre) (msgOf (dProof (adv (A.auxOf pre)) ro)))
            (fun _ _ => LigeroV1LayerStep.accepting (Row.rowValid h) dom (Row.hkrow h) (lig pre)))
          (dChallenges (adv (A.auxOf pre)) (ctxOf (A.auxOf pre)) msgOf ro))
    -- the Merkle extractor's fuels
    (ht₁ : R.commitFuel ≤ R.tape)
    (hT : 2 * n + (revealFuel + respondFuel) + R.commitFuel ≤ R.tape) (hT1 : 1 ≤ R.tape)
    (hcand : Fintype.card Cand = R.cardCand)
    (hD : Fintype.card D = 2 ^ R.params.digestBits) :
    ((univ.filter fun omega : (Fin R.tape → D) × (MPoint Ctx Msg R.params.nl R.params.rounds → C) =>
        CompiledAccepts K A codec (statement omega)
            (challengeOf (A.auxOf omega.1) omega.2) (queryOf (A.auxOf omega.1) omega.2) omega.1 ∧
          Fails omega.1).card : ℚ)
        / ((Fintype.card D : ℚ) ^ R.tape *
            Fintype.card (MPoint Ctx Msg R.params.nl R.params.rounds → C))
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
  -- the per-commitment count, over the oracle on message prefixes
  set βmax := maxBudget (pairBudget (Fintype.card C) R.params.row.fieldSize)
    (pairBudget (Fintype.card C) R.params.row.fieldSize)
    (inBudget (Fintype.card C) R.params.row.fieldSize) (ligBudget R.params.row (Fintype.card C))
    (queryBudget R.params.row (Fintype.card C))
  set sumβ := R.params.nl * pairBudget (Fintype.card C) R.params.row.fieldSize
    + (∑ i ∈ Finset.range R.params.nl, R.params.rounds i)
      * pairBudget (Fintype.card C) R.params.row.fieldSize
    + inBudget (Fintype.card C) R.params.row.fieldSize + ligBudget R.params.row (Fintype.card C)
    + queryBudget R.params.row (Fintype.card C)
  let Acc : (Fin R.tape → D) × (MPoint Ctx Msg R.params.nl R.params.rounds → C) → Prop :=
    fun omega =>
      CompiledAccepts K A codec (statement omega)
          (challengeOf (A.auxOf omega.1) omega.2) (queryOf (A.auxOf omega.1) omega.2) omega.1 ∧
        ExtractionExplains codec dec n R.commitFuel (revealFuel + respondFuel) R.tape A.commit
          (A.openingStage (challengeOf (A.auxOf omega.1) omega.2)
            (queryOf (A.auxOf omega.1) omega.2)) omega.1
  have hslice : ∀ pre : Fin R.tape → D,
      (univ.filter fun ro : MPoint Ctx Msg R.params.nl R.params.rounds → C =>
          Acc (pre, ro) ∧ Fails pre).card * Fintype.card C
        ≤ (Fintype.card Cand * (N * βmax + sumβ))
          * Fintype.card (MPoint Ctx Msg R.params.nl R.params.rounds → C) := by
    intro pre
    rw [Fintype.card_fun]
    by_cases hFp : Fails pre
    · refine fs_card_le (Ffam pre) (MD pre) (MsgLigeroData.ofLigeroData (LD pre hFp)) (hB pre hFp)
        (hfail pre) hFp (adv (A.auxOf pre)) (ctxOf (A.auxOf pre)) msgOf _ fun ro hro => ?_
      show RbrSplit.LayerStepAccepts (RbrSplit.stepsOf _ (LD pre hFp).accepting) _
      rw [hacc pre hFp]
      exact hright pre hFp ro hro.1
    · refine le_trans (le_of_eq ?_) (Nat.zero_le _)
      rw [Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun ro _ hro => hFp hro.2),
        zero_mul]
  have hcount := ratio_of_slices
    (fun omega : (Fin R.tape → D) × (MPoint Ctx Msg R.params.nl R.params.rounds → C) =>
      Acc omega ∧ Fails omega.1) (Fintype.card C) hCpos _ hslice
  -- the Merkle step
  have hmerkle := drop_explains_ratio_le_aux dec K A challengeOf queryOf statement
    (fun omega => Fails omega.1) ht₁ hT hT1
  have hden : (Fintype.card (Fin R.tape → D) : ℚ) = (Fintype.card D : ℚ) ^ R.tape := by
    rw [Fintype.card_fun, Fintype.card_fin]
    push_cast
    ring
  rw [hden] at hcount
  have hstep : ((univ.filter fun omega :
          (Fin R.tape → D) × (MPoint Ctx Msg R.params.nl R.params.rounds → C) =>
        CompiledAccepts K A codec (statement omega)
            (challengeOf (A.auxOf omega.1) omega.2) (queryOf (A.auxOf omega.1) omega.2) omega.1 ∧
          Fails omega.1).card : ℚ)
        / ((Fintype.card D : ℚ) ^ R.tape
            * Fintype.card (MPoint Ctx Msg R.params.nl R.params.rounds → C))
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

/-- **At certified bit levels**: if a row's sequential bound is at most `2^-a` and its
work-normalized coefficient at most `2^-b`, then `R.bound + N · κ ≤ 2^-a + N · 2^-b`.  With
`row_fs_ratio_le_bound` this instantiates a new row in one line. -/
theorem bound_add_le_bits (R : Row) {a b : ℕ} (ha : R.bound ≤ (1 : ℚ) / 2 ^ a)
    (hb : R.fsCoefficient ≤ (1 : ℚ) / 2 ^ b) (N : ℕ) :
    R.bound + N * R.fsCoefficient ≤ (1 : ℚ) / 2 ^ a + N * ((1 : ℚ) / 2 ^ b) :=
  add_le_add ha (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg N))

/--
**The v8 hash row against a prefix-only grinding Fiat–Shamir adversary.**

`row_fs_ratio_le_bound` at `CertifiedV1.v8Hash` (the deployed hash profile, 20 layers and 610
sumcheck slots, over `GF(2^128)`; Ligero V1 at `n = 4088`, `k = 584`, 132 opened columns):

```text
Pr[ accept ∧ Fails ]  ≤  2^-114  +  N · 2^-115
```

with `N` the number of **deployed** (message-prefix) hash queries.  The same numerals as
`CertifiedV1.v8Hash_fs_ratio_le`, where `N` counted raw-answer points.
-/
theorem v8Hash_fs_ratio_le
    {C Cand : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
    {F Equations Witness : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype Equations] [DecidableEq Equations]
    {logw logc nc nv : ℕ}
    {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
    {Enc D Salt M Aux Aux' : Type} {n respondFuel revealFuel : ℕ}
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    {Ctx Msg Out : Type} [Fintype Ctx] [DecidableEq Ctx] [Fintype Msg] [DecidableEq Msg]
    [Inhabited Msg] {N : ℕ}
    {codec : Codec Salt M D Enc} (dec : RoleDecoders codec)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (A : Adversary Enc D Salt M Challenge Response Query Aux Aux'
      n v8Hash.commitFuel respondFuel revealFuel)
    (adv : Aux → Tree (MPoint Ctx Msg v8Hash.params.nl v8Hash.params.rounds) C Out N)
    (ctxOf : Aux → Ctx) (msgOf : Out → ℕ → Msg)
    (challengeOf : Aux → (MPoint Ctx Msg v8Hash.params.nl v8Hash.params.rounds → C) → Challenge)
    (queryOf : Aux → (MPoint Ctx Msg v8Hash.params.nl v8Hash.params.rounds → C) → Query)
    (statement : (Fin v8Hash.tape → D) × (MPoint Ctx Msg v8Hash.params.nl v8Hash.params.rounds → C)
      → Statement)
    {Fails : (Fin v8Hash.tape → D) → Prop}
    (hF : Fintype.card F = v8Hash.params.row.fieldSize)
    (dom : LigeroFamily.ReedSolomon.Domain F v8Hash.params.row.openings v8Hash.params.q
      v8Hash.params.row.n)
    (lig : ∀ _pre : Fin v8Hash.tape → D,
      LigeroV1LayerStep.Instance v8Hash.params.row F Equations v8Hash.params.nw
        v8Hash.params.nq v8Hash.params.q)
    (hfalse : ∀ pre : Fin v8Hash.tape → D, Fails pre → ¬ (lig pre).statement.Language)
    (H : ∀ _pre : Fin v8Hash.tape → D, RbrLongfellow.Honest F Cand logw logc)
    (Sat : (Fin v8Hash.tape → D) → Cand → Prop)
    (Ffam : ∀ pre : Fin v8Hash.tape → D,
      RbrSplit.FieldData C F
        (LigeroV1LayerStep.Chal F Equations v8Hash.params.nw v8Hash.params.nq)
        (LigeroV1LayerStep.Qry v8Hash.params.row) Cand Witness nc nv logw logc (H pre) (Sat pre))
    (hexact : ∀ pre : Fin v8Hash.tape → D, (Ffam pre).Exact)
    (MD : ∀ pre : Fin v8Hash.tape → D, MsgData C Msg (H pre))
    (hfail : ∀ pre : Fin v8Hash.tape → D, Fails pre → ∀ cand : Cand, ¬ Sat pre cand)
    (hright : ∀ pre : Fin v8Hash.tape → D, Fails pre →
      ∀ ro : MPoint Ctx Msg v8Hash.params.nl v8Hash.params.rounds → C,
        (CompiledAccepts K A codec (statement (pre, ro))
            (challengeOf (A.auxOf pre) ro) (queryOf (A.auxOf pre) ro) pre ∧
          ExtractionExplains codec dec n v8Hash.commitFuel (revealFuel + respondFuel)
            v8Hash.tape A.commit
            (A.openingStage (challengeOf (A.auxOf pre) ro) (queryOf (A.auxOf pre) ro)) pre) →
        RbrSplit.LayerStepAccepts
          (RbrSplit.stepsOf (nl := v8Hash.params.nl) (w := v8Hash.params.rounds)
            (withMsgs (Ffam pre) (MD pre) (msgOf (dProof (adv (A.auxOf pre)) ro)))
            (fun _ _ => LigeroV1LayerStep.accepting (Row.rowValid v8Hash_valid) dom
              (Row.hkrow v8Hash_valid) (lig pre)))
          (dChallenges (adv (A.auxOf pre)) (ctxOf (A.auxOf pre)) msgOf ro))
    (ht₁ : v8Hash.commitFuel ≤ v8Hash.tape)
    (hT : 2 * n + (revealFuel + respondFuel) + v8Hash.commitFuel ≤ v8Hash.tape)
    (hT1 : 1 ≤ v8Hash.tape)
    (hcand : Fintype.card Cand = v8Hash.cardCand)
    (hD : Fintype.card D = 2 ^ v8Hash.params.digestBits) :
    ((univ.filter fun omega :
          (Fin v8Hash.tape → D) × (MPoint Ctx Msg v8Hash.params.nl v8Hash.params.rounds → C) =>
        CompiledAccepts K A codec (statement omega)
            (challengeOf (A.auxOf omega.1) omega.2) (queryOf (A.auxOf omega.1) omega.2) omega.1 ∧
          Fails omega.1).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v8Hash.tape *
            Fintype.card (MPoint Ctx Msg v8Hash.params.nl v8Hash.params.rounds → C))
      ≤ (1 : ℚ) / 2 ^ 114 + N * ((1 : ℚ) / 2 ^ 115) :=
  le_trans
    (row_fs_ratio_le_bound v8Hash_valid dec K A adv ctxOf msgOf challengeOf queryOf statement hF dom
      lig hfalse H Sat Ffam hexact MD hfail hright ht₁ hT hT1 hcand hD)
    (bound_add_le_bits v8Hash (Row.target v8Hash_valid) v8Hash_fsCoefficient N)

end Row

end Lfzk.NizkDeployedHash
