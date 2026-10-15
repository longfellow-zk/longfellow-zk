import Lfzk.NizkZk
import Lfzk.CertifiedV7

/-!
# The deployed zero-knowledge verifier, against a re-committing Fiat–Shamir prover

`Lfzk.CompiledLongfellowAdaptive` proves its headline about `AcceptsAt`: a verifier that checks
the sumcheck rounds in the clear (`FieldPass`) and runs Ligero V1 on a statement **fixed by the
root**, with `hfalse` (that statement is false where extraction fails) among the premises.  This
file states the bound about the **deployed** verifier (`zk_common.h:L46-L135`,
`ZkVerifier::verify`), with no such premise.

## The verifier (`AcceptsZk`)

On a joint execution (`Bcs.AdaptiveCommit.Setup`, `NizkAdaptive.lfSetup`) with proof `out` and
recomputed answers `chals`:

1. **the transcript builds a system** (`zkBuilt`): the zero-knowledge transitions of
   `Lfzk.RbrZkLongfellow` — `begin_circuit` and `begin_layer` draws, `ConstraintBuilder::first`,
   `next` with `p(1) := claim − p(0)`, each layer's `finalize` row and triple, the input row at
   `alpha_in` — run on `out`'s messages at `chals` reach `built sys` after the input binding.  No
   sumcheck check is performed; the only rejections are the shape guards (`Fits`, the round count,
   the layer count);
2. **the Merkle opening and Ligero V1's policy** (`Bcs.Compiler.Accepts` at `v1K`, the V1 compiler
   at the row's Reed–Solomon code, under the run's Merkle oracle) **on the statement the transcript
   built**, `Encode.encodeLig pl nlin sys`, at the decoded recomputed Ligero challenge and query,
   with the proof's response read from its query-round message.

## `hright`, and where `hfalse` went

`hright_zk`: where the cut-trace extraction explains the opening, the compiled V1 check at
`(encodeLig sys, x, ρ, q)` puts `q` in V1's test at the extracted matrix
(`CompiledLongfellowAdaptive.mem_acceptingR_of_accepts`), which is the query test of the
zero-knowledge LayerStep's Ligero half built by `ZkLigeroV1.exists_zkLigeroData`; with the
decomposition `zkAccepts_iff` that is the zero-knowledge LayerStep's acceptance.  The Ligero half
needs no falsity premise (`ZkLigeroV1.noDecoded_of_noSat`), so the headline's premises are the
field analysis data, the decoders' exactness, and the protocol's numbers.

## Headlines

`row_zk_compiled_ratio_le` at an abstract certified V1 row and output dimension `logv`:

```text
Pr[ AcceptsZk  ∧  no lift-list member's witness satisfies the circuit ]
    ≤  R.zkBound logv  +  N · R.zkCoefficient logv  +  R.tape · (L + N) / 2^digestBits
```

instantiated (`native_decide` numerals, re-commitment terms absorbed) at

| row | `logv` | bound |
|---|---|---|
| `v7Hash1` (deployed v7, 1 attribute) | 3 | `2^-115 + N · 2^-117` |
| `v7Hash2`, `v7Hash3` | 4 | `2^-115 + N · 2^-117` |
| `v7Hash4` | 5 | `2^-115 + N · 2^-117` |
| `v7Sig` | 8 | `2^-123 + N · 2^-123` |
| `v8Hash` | 5 | `2^-115 + N · 2^-116` |
| `v8Sig` | 3 | `2^-122 + N · 2^-122` |

## What is still a hypothesis

* **The field analysis data** per context (`ZkFieldData`): the honest values at each layer's own
  `beta` with the next layer read at `beta = 0`, and the pending-assertion predicate `Pend`
  (`ZkHonest`); the boundary facts `rel`, `final`, `W_affine`, `pend_round`, `pend_close`,
  `pend_last`, `hin` (`ZkBoundary`); and the layer-0 count
  (`RbrZkSplit.hinit_of_output`: an unsatisfied candidate whose intermediate assertions all hold has
  a non-zero output-or-layer-0-assertion wire — satisfiable at the honest `Satisfied` under
  `Isolated` and `DeadEnd`, `satisfied_iff_top` and `top_harith`).  Intermediate assertions are
  caught by the chain's branches (b) and (c) at their own layer's pair slot, not by `hinit`.
  **All of it is constructed** for `Lfzk.Arith`'s compiled-circuit model under `DeadEnd` and
  `Isolated` (`ZkArithInit.zkFieldDataOf`, in `Lfzk.ZkArithBoundary`), given the decoders' balances
  and a code that agrees with the construction (`CodeAgrees`, `AsgAgrees`);
* exactly balanced decoders (`ZkFieldData.ExactAt`), `|F| = row.fieldSize`, `|D| = 2^digestBits`,
  the Merkle budget, a placement `pl` of the system into the tableau with `V.nlin = nlin`,
  `V.nt = nt`;
* **transliteration** (README gap 1): R1 (Merkle leaf = column), R2 (the deployed Ligero check is
  V1's policy), R4 (hash inputs carry raw earlier answers; Phase 5), R6 (context = root), and that
  `V`'s data (`eqqOf`, `inCoeffs`, `pubBinding`, `stNext`, the message readers) are the deployed
  verifier's.  R3 (the field rounds) and R5 (the statement is the transcript's) are discharged by
  construction: the transitions are `ConstraintBuilder`'s and the statement is the built one.

The candidates are the extracted oracle's lift list (`ZkLigeroV1.Lift`), at most `listBound` of
them; the extractor is "the first lift-list member whose decoded witness satisfies the circuit".
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.CompiledZk

open Finset Bcs Bcs.AdaptiveCommit Merkle Merkle.MH Merkle.RandomOracle
  Merkle.RandomOracle.TwoOracleTree RbrLongfellow Lfzk.NizkGrinding Lfzk.NizkAdaptive
  Lfzk.RbrLayerStepS Lfzk.RbrZkLongfellow Lfzk.RbrZkSplit Lfzk.NizkZk Lfzk.ZkLigeroV1
  Lfzk.CompiledLongfellow Lfzk.CompiledLongfellowAdaptive
open scoped Classical

/-! ## 1. Where the zero-knowledge LayerStep can fail -/

section Decompose

variable {C F X Q Msg Gpt : Type} [Field F] [SumcheckInterp F] [DecidableEq Q]
variable {M ninp logw logc nl : ℕ} {w : ℕ → ℕ}

/-- The zero-knowledge verifier's run, as a claim chain with no candidates. -/
noncomputable abbrev zkRun (V : ZkCode C F X Q Msg Gpt M ninp logw logc) (ms : ℕ → Msg)
    (acc : ∀ m : ℕ, (Fin m → C) → LigeroSystem ninp M F → X → Finset Q) :
    Bcs.ClaimChain C (Rounds.Role.length nl w) (ZkState M ninp logw logc F X) PUnit :=
  layerStepChainS (Cand := PUnit) (zkSteps nl w V ms acc) (fun _ _ => False) .start

/-- The state after the input binding, read off a state. -/
def builtOf : ZkState M ninp logw logc F X → Option (LigeroSystem ninp M F)
  | .built sys => some sys
  | _ => none

omit [SumcheckInterp F] in
theorem builtOf_eq_some {s : ZkState M ninp logw logc F X} {sys : LigeroSystem ninp M F} :
    builtOf s = some sys ↔ s = .built sys := by
  cases s <;> simp [builtOf]

/-- **The system the verifier builds** from a proof's messages and a tape: the state after the input
binding, if it is `built`. -/
noncomputable def zkBuilt (V : ZkCode C F X Q Msg Gpt M ninp logw logc) (ms : ℕ → Msg)
    (tape : Fin (Rounds.Role.length nl w) → C) : Option (LigeroSystem ninp M F) :=
  builtOf ((zkRun (nl := nl) (w := w) V ms fun _ _ _ _ => ∅).state
    (Rounds.Role.layerBase w nl + 1) (Bcs.trunc tape _ fieldLen_le))

omit [DecidableEq Q] in
/-- The chain's step at a role's slot is that role's transition. -/
theorem chainS_step_index {S Cand : Type} (steps : StepsS C S nl w) (Wrong : Cand → S → Prop)
    (init : S) (rl : Rounds.Role nl w) (pref : Fin rl.index.val → C) (c : C) (s : S) :
    (layerStepChainS steps Wrong init).step rl.index pref c s
      = stepAtS steps rl rl.index.val pref c s := by
  show stepAtS steps (Rounds.Role.indexEquiv.symm rl.index) rl.index.val pref c s = _
  rw [indexEquiv_symm_index]

omit [DecidableEq Q] in
/-- **Before the query slot, the run does not read the query test.** -/
theorem zk_state_acc_congr (V : ZkCode C F X Q Msg Gpt M ninp logw logc) (ms : ℕ → Msg)
    (acc acc' : ∀ m : ℕ, (Fin m → C) → LigeroSystem ninp M F → X → Finset Q) (j : ℕ)
    (hj : j ≤ Rounds.Role.layerBase w nl + 2) (p : Fin j → C) :
    (zkRun (nl := nl) (w := w) V ms acc).state j p
      = (zkRun (nl := nl) (w := w) V ms acc').state j p := by
  refine state_congr_below (zkRun (nl := nl) (w := w) V ms acc)
    (zkRun (nl := nl) (w := w) V ms acc') rfl (Rounds.Role.layerBase w nl + 2)
    (fun i hi => ?_) j hj p
  funext pref c s
  show stepAtS (zkSteps nl w V ms acc) (Rounds.Role.indexEquiv.symm i) i.val pref c s
    = stepAtS (zkSteps nl w V ms acc') (Rounds.Role.indexEquiv.symm i) i.val pref c s
  cases hrole : Rounds.Role.indexEquiv.symm i with
  | ligeroQuery =>
      have hi' := index_indexEquiv_symm (nl := nl) (w := w) i
      rw [hrole] at hi'
      have hv : i.val = Rounds.Role.layerBase w nl + 2 := by rw [← hi']; rfl
      omega
  | layerPair _ => rfl
  | sumcheck _ _ => rfl
  | inputBind => rfl
  | ligeroChallenge => rfl

omit [SumcheckInterp F] in
/-- The two Ligero transitions accept exactly from a built state, at a query in the test. -/
theorem zk_ligero_accepted_iff (V : ZkCode C F X Q Msg Gpt M ninp logw logc)
    (A : LigeroSystem ninp M F → X → Finset Q) (cq cx : C) (s : ZkState M ninp logw logc F X) :
    zkLigQuery V A cq (zkLigChallenge V cx s) = .accepted ↔
      ∃ sys, s = .built sys ∧ V.decodeQuery cq ∈ A sys (V.decodeChal cx) := by
  cases s with
  | built sys =>
      simp only [zkLigChallenge, zkLigQuery]
      split_ifs with h <;> simp [h]
  | start => simp [zkLigChallenge, zkLigQuery]
  | running _ => simp [zkLigChallenge, zkLigQuery]
  | challenged _ _ => simp [zkLigChallenge, zkLigQuery]
  | accepted => simp [zkLigChallenge, zkLigQuery]
  | failed => simp [zkLigChallenge, zkLigQuery]

/--
**The zero-knowledge LayerStep accepts iff the transcript builds a system and the drawn query
passes the test at it.**
-/
theorem zkAccepts_iff (V : ZkCode C F X Q Msg Gpt M ninp logw logc) (ms : ℕ → Msg)
    (acc : ∀ m : ℕ, (Fin m → C) → LigeroSystem ninp M F → X → Finset Q)
    (tape : Fin (Rounds.Role.length nl w) → C) :
    ZkLayerStepAccepts .accepted .start (zkSteps nl w V ms acc) tape ↔
      ∃ sys, zkBuilt (nl := nl) (w := w) V ms tape = some sys ∧
        V.decodeQuery (tape qryIdx) ∈ acc (Rounds.Role.layerBase w nl + 2)
          (Bcs.trunc tape _ queryLen_le) sys (V.decodeChal (tape ligIdx)) := by
  set ch := zkRun (nl := nl) (w := w) V ms acc
  have h3 : ch.state (Rounds.Role.length nl w) (Bcs.trunc tape _ le_rfl)
      = zkLigQuery V (acc (Rounds.Role.layerBase w nl + 2) (Bcs.trunc tape _ queryLen_le))
          (tape qryIdx)
          (ch.state (Rounds.Role.layerBase w nl + 2) (Bcs.trunc tape _ queryLen_le)) := by
    have h := state_trunc_succ ch tape qryIdx
    rw [chainS_step_index] at h
    exact h
  have h2 : ch.state (Rounds.Role.layerBase w nl + 2) (Bcs.trunc tape _ queryLen_le)
      = zkLigChallenge V (tape ligIdx)
          (ch.state (Rounds.Role.layerBase w nl + 1) (Bcs.trunc tape _ fieldLen_le)) := by
    have h := state_trunc_succ ch tape ligIdx
    rw [chainS_step_index] at h
    exact h
  have h1 : ch.state (Rounds.Role.layerBase w nl + 1) (Bcs.trunc tape _ fieldLen_le)
      = (zkRun (nl := nl) (w := w) V ms fun _ _ _ _ => ∅).state
          (Rounds.Role.layerBase w nl + 1) (Bcs.trunc tape _ fieldLen_le) :=
    zk_state_acc_congr V ms acc _ _ (by omega) _
  show ch.state (Rounds.Role.length nl w) (Bcs.trunc tape _ le_rfl) = .accepted ↔ _
  rw [h3, h2, zk_ligero_accepted_iff, h1]
  unfold zkBuilt
  constructor
  · rintro ⟨sys, hs, hq⟩
    exact ⟨sys, by rw [hs]; rfl, hq⟩
  · rintro ⟨sys, hs, hq⟩
    exact ⟨sys, builtOf_eq_some.mp hs, hq⟩

end Decompose

/-! ## 2. The deployed verifier -/

section Verifier

variable {C F X Q Msg Gpt : Type} [Field F] [SumcheckInterp F] [DecidableEq Q]
variable {M ninp logw logc nl : ℕ} {w : ℕ → ℕ}
variable {Out Statement Resp : Type}
variable {Enc D Salt Pt Key : Type} [DecidableEq Enc] [Inhabited D] [DecidableEq Pt]
  {tA N TM TC fc : ℕ}
variable {Oracle Mc : Type} {Opening : Q → Type} {n : ℕ}

/--
**The deployed zero-knowledge verifier on a joint execution.**  With the proof `out` and the
recomputed answers `chals`: the transcript builds a system `sys` (`zkBuilt`), and `K`'s compiled
verifier accepts — the opened set is the query's, the Merkle opening reconstructs `out`'s root, and
`K`'s IPCP verifier accepts the opened leaves — on the statement `stmtOf sys`, at the decoded
recomputed Ligero challenge and query, with the response read from the query-round message.
-/
def AcceptsZk (K : Compiler Statement Oracle X Resp Q Opening Mc n)
    (V : ZkCode C F X Q Msg Gpt M ninp logw logc) (codec : Codec Salt Mc D Enc)
    (S : Setup Enc D Pt C Out Key tA N (Rounds.Role.length nl w))
    (check : Out → Tree Enc D Unit fc) (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim n Salt Mc D) (stmtOf : LigeroSystem ninp M F → Statement)
    (respOf : Msg → Resp) (mt : Fin TM → D) (ct : Fin TC → C) : Prop :=
  ∃ sys, zkBuilt (nl := nl) (w := w) V (msgOf (S.proof mt ct)) (S.challenges mt ct) = some sys ∧
    K.Accepts (codec.withOracle (S.merkleOracle check mt ct)) (stmtOf sys) (rootOf (S.proof mt ct))
      (V.decodeChal (S.challenges mt ct ligIdx))
      (respOf (msgOf (S.proof mt ct) (Rounds.Role.layerBase w nl + 2)))
      (V.decodeQuery (S.challenges mt ct qryIdx)) (claimOf (S.proof mt ct))

/-- The empty system, the statement's default when the transcript builds none. -/
def emptySys : LigeroSystem ninp M F := ⟨[], []⟩

/-- **The statement for `guarded K`**: the statement of the system the transcript builds, and
whether it built one. -/
noncomputable def zkStatementOf (V : ZkCode C F X Q Msg Gpt M ninp logw logc)
    (msgOf : Out → ℕ → Msg) (stmtOf : LigeroSystem ninp M F → Statement) (out : Out)
    (chals : Fin (Rounds.Role.length nl w) → C) : Statement × Bool :=
  (stmtOf ((zkBuilt (nl := nl) (w := w) V (msgOf out) chals).getD emptySys),
    (zkBuilt (nl := nl) (w := w) V (msgOf out) chals).isSome)

/-- The verifier's Ligero challenge. -/
def zkChallengeOf (V : ZkCode C F X Q Msg Gpt M ninp logw logc) (_out : Out)
    (chals : Fin (Rounds.Role.length nl w) → C) : X :=
  V.decodeChal (chals ligIdx)

/-- The verifier's Ligero query. -/
def zkQueryOf (V : ZkCode C F X Q Msg Gpt M ninp logw logc) (_out : Out)
    (chals : Fin (Rounds.Role.length nl w) → C) : Q :=
  V.decodeQuery (chals qryIdx)

omit [DecidableEq Q] in
/-- **`AcceptsZk` is `guarded K`'s joint acceptance** at the verifier's maps. -/
theorem acceptsZk_iff_joint (K : Compiler Statement Oracle X Resp Q Opening Mc n)
    (V : ZkCode C F X Q Msg Gpt M ninp logw logc) (codec : Codec Salt Mc D Enc)
    (S : Setup Enc D Pt C Out Key tA N (Rounds.Role.length nl w))
    (check : Out → Tree Enc D Unit fc) (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim n Salt Mc D) (stmtOf : LigeroSystem ninp M F → Statement)
    (respOf : Msg → Resp) (mt : Fin TM → D) (ct : Fin TC → C) :
    AcceptsZk (nl := nl) (w := w) K V codec S check rootOf msgOf claimOf stmtOf respOf mt ct ↔
      JointAccepts (guarded K) codec S check rootOf claimOf
        (zkStatementOf (nl := nl) (w := w) V msgOf stmtOf) (responseOfAt nl w respOf msgOf)
        (zkChallengeOf (nl := nl) (w := w) V) (zkQueryOf (nl := nl) (w := w) V) mt ct := by
  unfold JointAccepts AcceptsZk zkStatementOf
  rw [accepts_guarded]
  constructor
  · rintro ⟨sys, hs, hacc⟩
    rw [hs]
    exact ⟨rfl, hacc⟩
  · rintro ⟨hb, hacc⟩
    rcases hs : zkBuilt (nl := nl) (w := w) V (msgOf (S.proof mt ct)) (S.challenges mt ct)
      with _ | sys
    · rw [hs] at hb; exact absurd hb (by simp)
    · rw [hs] at hacc
      exact ⟨sys, rfl, hacc⟩

end Verifier

/-! ## 3. `hright`, at Ligero V1 -/

section V1

open Lfzk.LigeroV1Rows

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
variable {row : Row} {nw nq qw ninp M nt nlin : ℕ}
variable {C Msg Gpt : Type} [Fintype C] [DecidableEq C] [DecidableEq Msg] {logw logc nl : ℕ}
  {w : ℕ → ℕ}
variable {Enc D Salt Out : Type} [Inhabited D] [DecidableEq D] [DecidableEq Enc] [Inhabited Salt]
variable {tA N TM TC : ℕ}

/-- **The extracted matrix at a commitment context**: what Merkle extraction recovers from the
context's root and cut trace (defaulted where it fails). -/
noncomputable def extOracle (nlin nt : ℕ) (h : row.Valid)
    (dom : LigeroFamily.ReedSolomon.Domain F row.openings qw row.n)
    (hkrow : row.openings + qw = row.k) (hr : 0 < row.openings)
    {codec : Codec Salt (Col F nw nq) D Enc} (dec : RoleDecoders codec)
    (κ : D × List (Enc × D)) : Ligero.V1.Oracle F nw nq row.n 1 :=
  (v1K (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide)) (nw := nw) (nq := nq) h dom hkrow
    hr).oracleOfClaim (((extract dec row.n κ.1 κ.2).map Extracted.message).getD default)

omit [Fintype F] [Fintype C] in
/--
**`hright`, proved for the deployed zero-knowledge verifier.**

From the guarded joint acceptance: the transcript built `sys`, and the compiled V1 check accepted
at its encoded statement; where the cut-trace extraction explains the opening, the query is in V1's
test at the extracted matrix (`mem_acceptingR_of_accepts`), which is the Ligero half's query test
`accZ` at the context.  By `zkAccepts_iff` that is the zero-knowledge LayerStep's acceptance.
-/
theorem hright_zk (h : row.Valid) (dom : LigeroFamily.ReedSolomon.Domain F row.openings qw row.n)
    (hkrow : row.openings + qw = row.k) (hr : 0 < row.openings)
    {codec : Codec Salt (Col F nw nq) D Enc} (dec : RoleDecoders codec)
    (pl : Encode.Placement ninp M qw nw nq nt)
    (V : ZkCode C F (ZkLigeroV1.Chal F nw nq nlin nt) (LigeroV1LayerStep.Qry row) Msg Gpt M ninp
      logw logc)
    (body : TwoOracleTree Enc D (Point D Msg C nl w) C Out tA N) (dflt : C) (rootOf : Out → D)
    (msgOf : Out → ℕ → Msg) (claimOf : Out → OpeningClaim row.n Salt (Col F nw nq) D)
    (respOf : Msg → LigeroFamily.Response F row.openings qw row.n 1)
    (LD : ∀ κ : D × List (Enc × D), ZkLigeroData C (ZkLigeroV1.Chal F nw nq nlin nt)
      (LigeroV1LayerStep.Qry row) Msg V
      (asgOf pl (h := h) (D := dom) (hkrow := hkrow)
        (O := extOracle nlin nt h dom hkrow hr dec κ)))
    (hLD : ∀ κ, (LD κ).accepting = accZ h dom hkrow pl nlin
      (extOracle nlin nt h dom hkrow hr dec κ) respOf)
    (mt : Fin TM → D) (ct : Fin TC → C)
    (hacc : JointAccepts (guarded (v1K (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide))
        (nw := nw) (nq := nq) h dom hkrow hr))
      codec (lfSetup body dflt rootOf msgOf) (lfCheck codec claimOf) rootOf claimOf
      (zkStatementOf (nl := nl) (w := w) V msgOf (stmtOf pl nlin))
      (responseOfAt nl w respOf msgOf) (zkChallengeOf (nl := nl) (w := w) V)
      (zkQueryOf (nl := nl) (w := w) V) mt ct)
    (hexp : (lfSetup body dflt rootOf msgOf).Explains dec id claimOf mt ct) :
    ZkLayerStepAccepts .accepted .start
      (steps (nl := nl) (w := w) V (LD ((lfSetup body dflt rootOf msgOf).context mt ct))
        (msgOf ((lfSetup body dflt rootOf msgOf).proof mt ct)))
      ((lfSetup body dflt rootOf msgOf).challenges mt ct) := by
  rw [← acceptsZk_iff_joint] at hacc
  obtain ⟨sys, hsys, hv1⟩ := hacc
  obtain ⟨e, hext, hagree, -⟩ := hexp
  show ZkLayerStepAccepts .accepted .start (zkSteps nl w V _ _) _
  rw [zkAccepts_iff]
  refine ⟨sys, hsys, ?_⟩
  rw [hLD]
  exact mem_acceptingR_of_accepts h dom hkrow hr dec _ _ _ _ _ _ _ _ e hext hagree hv1

end V1

/-! ## 4. The certified V1 rows -/

section Row

open Lfzk.CertifiedV1

variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
variable {ninp M nt nlin logw logc : ℕ}
variable {Enc D Salt : Type} [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc]
  [Inhabited Salt]
variable {Msg Out : Type} [DecidableEq Msg] [Inhabited Msg] {tA N : ℕ}

/--
**A certified V1 row at the deployed zero-knowledge verifier, against a re-committing Fiat–Shamir
prover.**

```text
Pr[ AcceptsZk (v1K …) V codec (lfSetup body dflt rootOf msgOf) …  ∧  ZkFails Sat (context) ]
    ≤  R.zkBound logv  +  N · R.zkCoefficient logv  +  R.tape · (L + N) / 2^digestBits
```

The candidates at a context `κ` are the extracted matrix's lift list `Lift κ` (at most
`listBound = cardCand` members, `lift_card_le`), each with the assignment its decoded tableau
gives; `Sat κ ℓ` is "`ℓ`'s witness satisfies the circuit".  **Every premise**:

* the verifier: a certified row `h`, `hr`, a Reed–Solomon domain `dom`, the zero-knowledge code `V`
  with its tableau size equal to the placement's (`hnlin`, `hnt`), how a message carries the Ligero
  response (`respOf`);
* the analysis, per context: honest values and pending predicate `H κ`, the satisfaction predicate
  `Sat κ`, and the field data `FD κ` with exactly balanced decoders (`hexact`);
* `|F| = row.fieldSize`, `|D| = 2^digestBits`, the Merkle budget `tA ≤ commitFuel` and room
  `2n + tA ≤ tape`.

No `hfalse`, no `hright`, no `hlig`: all three are theorems.
-/
theorem row_zk_compiled_ratio_le {R : Row} (h : R.Valid) (hr : 0 < R.params.row.openings)
    (logv : ℕ) (pl : Encode.Placement ninp M R.params.q R.params.nw R.params.nq nt)
    {codec : Codec Salt (Col F R.params.nw R.params.nq) D Enc} (dec : RoleDecoders codec)
    (V : ZkCode C F (ZkLigeroV1.Chal F R.params.nw R.params.nq nlin nt)
      (LigeroV1LayerStep.Qry R.params.row) Msg (Fin logv → F) M ninp logw logc)
    (hnlin : V.nlin = nlin) (hnt : V.nt = nt)
    (dom : LigeroFamily.ReedSolomon.Domain F R.params.row.openings R.params.q R.params.row.n)
    (respOf : Msg → LigeroFamily.Response F R.params.row.openings R.params.q R.params.row.n 1)
    (body : TwoOracleTree Enc D (Point D Msg C R.params.nl R.params.rounds) C Out tA N)
    (dflt : C) (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim R.params.row.n Salt (Col F R.params.nw R.params.nq) D)
    (hF : Fintype.card F = R.params.row.fieldSize)
    (H : ∀ κ : D × List (Enc × D), ZkHonest F
      (ZkLigeroV1.Lift (Row.rowValid h) dom (Row.hkrow h)
        (extOracle nlin nt (Row.rowValid h) dom (Row.hkrow h) hr dec κ))
      logw logc)
    (Sat : ∀ κ : D × List (Enc × D),
      ZkLigeroV1.Lift (Row.rowValid h) dom (Row.hkrow h)
        (extOracle nlin nt (Row.rowValid h) dom (Row.hkrow h) hr dec κ) → Prop)
    (FD : ∀ κ : D × List (Enc × D), ZkFieldData C F (ZkLigeroV1.Chal F R.params.nw R.params.nq nlin nt)
      (LigeroV1LayerStep.Qry R.params.row) Msg (Fin logv → F)
      (ZkLigeroV1.Lift (Row.rowValid h) dom (Row.hkrow h)
        (extOracle nlin nt (Row.rowValid h) dom (Row.hkrow h) hr dec κ))
      M ninp logw logc R.params.nl R.params.rounds V (H κ) (asgOf pl) (Sat κ))
    (hexact : ∀ κ, (FD κ).ExactAt)
    (htA : tA ≤ R.commitFuel) (htape : 2 * R.params.row.n + tA ≤ R.tape)
    (hD : Fintype.card D = 2 ^ R.params.digestBits) :
    ((univ.filter fun ω : (Fin R.tape → D) × (Fin (R.fsLen N) → C) =>
        AcceptsZk (nl := R.params.nl) (w := R.params.rounds)
            (v1K (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide)) (Row.rowValid h) dom
              (Row.hkrow h) hr) V codec
            (lfSetup body dflt rootOf msgOf) (lfCheck codec claimOf) rootOf msgOf claimOf
            (stmtOf pl nlin) respOf ω.1 ω.2 ∧
          ZkFails Sat ((lfSetup body dflt rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ R.tape * (Fintype.card C : ℚ) ^ R.fsLen N)
      ≤ R.zkBound logv + N * R.zkCoefficient logv
        + ((R.tape * (Rounds.Role.length R.params.nl R.params.rounds + N) : ℕ) : ℚ)
          / 2 ^ R.params.digestBits := by
  have key : ∀ ω : (Fin R.tape → D) × (Fin (R.fsLen N) → C),
      AcceptsZk (nl := R.params.nl) (w := R.params.rounds)
            (v1K (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide)) (Row.rowValid h) dom
              (Row.hkrow h) hr) V codec
            (lfSetup body dflt rootOf msgOf) (lfCheck codec claimOf) rootOf msgOf claimOf
            (stmtOf pl nlin) respOf ω.1 ω.2 ↔
        JointAccepts (guarded (v1K (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide))
            (Row.rowValid h) dom (Row.hkrow h) hr))
          codec (lfSetup body dflt rootOf msgOf) (lfCheck codec claimOf) rootOf claimOf
          (zkStatementOf (nl := R.params.nl) (w := R.params.rounds) V msgOf (stmtOf pl nlin))
          (responseOfAt R.params.nl R.params.rounds respOf msgOf)
          (zkChallengeOf (nl := R.params.nl) (w := R.params.rounds) V)
          (zkQueryOf (nl := R.params.nl) (w := R.params.rounds) V) ω.1 ω.2 :=
    fun ω => acceptsZk_iff_joint _ _ _ _ _ _ _ _ _ _ _ _
  classical
  -- the Ligero half, at every context's extracted matrix
  have hex := fun κ : D × List (Enc × D) =>
    exists_zkLigeroData V hnlin hnt pl (Row.rowValid h) (Row.coreRows h) hF dom (Row.hkrow h)
      (extOracle nlin nt (Row.rowValid h) dom (Row.hkrow h) hr dec κ) respOf
  choose LD hLDacc hLDesc hLDbq using hex
  refine le_trans (le_of_eq ?_) (Row.zk_adaptive_ratio_le h logv dec
      (guarded (v1K (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide)) (Row.rowValid h) dom
        (Row.hkrow h) hr))
      body dflt rootOf msgOf claimOf
      (zkStatementOf (nl := R.params.nl) (w := R.params.rounds) V msgOf (stmtOf pl nlin))
      (responseOfAt R.params.nl R.params.rounds respOf msgOf)
      (zkChallengeOf (nl := R.params.nl) (w := R.params.rounds) V)
      (zkQueryOf (nl := R.params.nl) (w := R.params.rounds) V)
      hF V
      (fun κ => ZkLigeroV1.Lift (Row.rowValid h) dom (Row.hkrow h)
        (extOracle nlin nt (Row.rowValid h) dom (Row.hkrow h) hr dec κ))
      (fun κ => (lift_card_le (Row.rowValid h) dom (Row.hkrow h) _).trans_eq (Row.cand_eq h).symm)
      H (fun κ => asgOf pl) Sat FD hexact LD hLDesc (fun κ => (hLDbq κ).le)
      (by simp [LigeroV1LayerStep.Qry])
      (fun mt ct hacc hexp => hright_zk (Row.rowValid h) dom (Row.hkrow h) hr dec pl V body dflt
        rootOf msgOf claimOf respOf LD hLDacc mt ct hacc hexp)
      htA htape hD)
  exact congrArg (fun t : Finset ((Fin R.tape → D) × (Fin (R.fsLen N) → C)) =>
      ((t.card : ℕ) : ℚ) / ((Fintype.card D : ℚ) ^ R.tape * (Fintype.card C : ℚ) ^ R.fsLen N))
    (Finset.filter_congr fun ω _ => and_congr_left' (key ω))

end Row

end Lfzk.CompiledZk
