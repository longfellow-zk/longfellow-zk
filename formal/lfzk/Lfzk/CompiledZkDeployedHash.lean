import Lfzk.NizkZkDeployedHash
import Lfzk.CompiledZkTwoField

/-!
# The deployed zero-knowledge verifier, with Fiat–Shamir hash inputs as deployed

`Lfzk.CompiledZk.row_zk_compiled_ratio_le` and `Lfzk.CompiledZk.twofield_zk_compiled_ratio_le` bound
the **deployed** zero-knowledge verifier (`zk_common.h`, `ZkVerifier::verify`: the transcript builds a
system, and Ligero V1's verdict on it is the only check) against a re-committing prover, at hash
inputs that carry the raw earlier answers (README "R4").  This file states the same two headlines
over the total random oracle on the deployed hash inputs — context, role, and the prover's messages
through the round, no challenge — so that `N` counts **deployed** hash queries.  The right-hand
sides are those of `CompiledZk` verbatim, so `Lfzk.CompiledZkDeployedHashRows` instantiates the v7
rows with the numerals of `CompiledZkRows` / `CompiledZkTwoFieldRows`.

## The verifier at `(mt, ro)`

`AcceptsZkDH` is `CompiledZk.AcceptsZk` on a `Bcs.TotalOracleCommit.Setup`: with the proof
`out = S.proof mt ro` and the verifier's challenges `S.challenges mt ro` (round `k`'s is `ro` at
round `k`'s message prefix), the transcript builds a system `sys` (`CompiledZk.zkBuilt`) and the
Merkle-compiled V1 check accepts on `encodeLig sys` at the decoded challenge and query.  The
two-field side `CompiledZkSide.acceptsDH` reads the side's zero-knowledge code at the MAC-key share
`av` **the proof carries in its public inputs** (`CompiledZkSide.VofDH`), not at a raw oracle
answer; the composed event adds `ro(key point) = av`, as in `NizkDeployedHashTwoField`.

## The built statement is a function of the earlier messages

`zkBuilt_congr`: the system the transcript builds — the state after the input binding — reads only
the messages `0, …, layerBase` (`zkRun_msgLocal`: each transition reads its own message).  So the
statement Ligero V1 checks is determined by the message prefix hashed at the Ligero challenge's
point, which is what lets the Ligero slots' doom ("every candidate violates the built system") be
judged at a point (`zkStatementOf_congr`).  The chain-level congruence is
`NizkZkDeployedHash.zkChain_doomed_congr`.

## Headlines

* `row_zk_deployed_ratio_le` — at any certified V1 row and output dimension `logv`:

```text
Pr[ AcceptsZkDH  ∧  no lift-list member's witness satisfies the circuit ]
    ≤  R.zkBound logv  +  N · R.zkCoefficient logv  +  R.tape · (L + N) / 2^digestBits
```

* `twofield_zk_deployed_ratio_le` — two deployed sides, hash side first, `av` in the public inputs:

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧  no two good witnesses agree ]
    ≤  R₁.zkBound logv₁ + R₂.zkBound logv₂ + 1/|Fmac|
       +  N · max(R₁.zkCoefficient logv₁, R₂.zkCoefficient logv₂, 1/|Fmac|)
       +  2 · tape · (1 + L₁ + L₂ + N) / 2^digestBits
```

`hright` (`hright_zkDH`, `CompiledZkSide.hrightDH`) and the Ligero halves
(`ZkLigeroV1.exists_zkLigeroData`) are theorems, as in `CompiledZk`: no `hfalse`, no `hlig`.

## What is still a hypothesis

Those of `CompiledZk.row_zk_compiled_ratio_le` and `CompiledZk.twofield_zk_compiled_ratio_le` (the
field analysis data per context with exactly balanced decoders, the placement, `|F|`, `|D|`, the
Merkle budget; per side the `CompiledZkSide` data, the MAC data and the MAC rows `hrow₁`, `hrow₂`,
here at the `av` the proof carries), plus finiteness of the message types and the public data.  The
random-oracle idealisation of the SHA-256 transcript on (context, role, message prefix) and the
transliteration debt that the deployed byte encoding of a prefix is what `msgPoint` abstracts are
`Lfzk.NizkDeployedHash`'s; R1, R2, R6 and the verifier's data are `CompiledZk`'s.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.CompiledZkDeployedHash

open Finset Bcs Merkle Merkle.MH Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree
  RbrLongfellow Lfzk.NizkGrinding Lfzk.NizkDeployedHash Lfzk.NizkDeployedHashAdaptive
  Lfzk.RbrLayerStepS Lfzk.RbrZkLongfellow Lfzk.RbrZkSplit Lfzk.NizkZk Lfzk.ZkLigeroV1
  Lfzk.CompiledZk Lfzk.NizkZkDeployedHash
open Lfzk.CompiledLongfellow (Col guarded v1K ligIdx qryIdx)
open Lfzk.CompiledLongfellowAdaptive (accepts_guarded responseOfAt mem_acceptingR_of_accepts)
open scoped Classical

/-! ## 1. The built statement reads only the earlier messages -/

section Congr

variable {C F X Q Msg Gpt : Type} [Field F] [SumcheckInterp F] [DecidableEq Q]
variable {M ninp logw logc nl : ℕ} {w : ℕ → ℕ}

omit [DecidableEq Q] in
/-- **The verifier's run reads the messages round by round**: start and doom are message-blind,
and slot `i`'s transition reads message `i` only. -/
theorem zkRun_msgLocal (V : ZkCode C F X Q Msg Gpt M ninp logw logc)
    (acc : ∀ m : ℕ, (Fin m → C) → LigeroSystem ninp M F → X → Finset Q) :
    MsgLocal (nl := nl) (w := w) (fun ms => zkRun (nl := nl) (w := w) V ms acc) where
  init _ _ := rfl
  wrong _ _ := rfl
  step ms ms' i h := by
    funext pref c s
    simp only [zkRun, layerStepChainS, stepAtS, zkSteps]
    cases Rounds.Role.indexEquiv.symm i <;> simp only [h]

omit [DecidableEq Q] in
/-- **The system the transcript builds reads only the messages before the Ligero slots**: it is
the state after the input binding, slot `layerBase`. -/
theorem zkBuilt_congr (V : ZkCode C F X Q Msg Gpt M ninp logw logc) {ms ms' : ℕ → Msg}
    (h : ∀ i, i < Rounds.Role.layerBase w nl + 1 → ms i = ms' i)
    (tape : Fin (Rounds.Role.length nl w) → C) :
    zkBuilt (nl := nl) (w := w) V ms tape = zkBuilt (nl := nl) (w := w) V ms' tape :=
  congrArg builtOf (state_congrG (zkRun_msgLocal (nl := nl) (w := w) V fun _ _ _ _ => ∅) _ h _)

omit [DecidableEq Q] in
/-- **The statement the verifier checks is a function of the message prefix hashed at the Ligero
challenge's point.** -/
theorem zkStatementOf_congr {Out Statement : Type} (V : ZkCode C F X Q Msg Gpt M ninp logw logc)
    (msgOf : Out → ℕ → Msg) (stmtOf : LigeroSystem ninp M F → Statement) {out out' : Out}
    (h : ∀ i, i < Rounds.Role.layerBase w nl + 1 → msgOf out i = msgOf out' i)
    (chals : Fin (Rounds.Role.length nl w) → C) :
    zkStatementOf (nl := nl) (w := w) V msgOf stmtOf out chals
      = zkStatementOf (nl := nl) (w := w) V msgOf stmtOf out' chals := by
  unfold zkStatementOf
  rw [zkBuilt_congr V h chals]

end Congr

/-! ## 2. The deployed verifier on `(mt, ro)` -/

section Verifier

variable {C F X Q Msg Gpt : Type} [Field F] [SumcheckInterp F] [DecidableEq Q]
variable {M ninp logw logc nl : ℕ} {w : ℕ → ℕ}
variable {Out Statement Resp : Type}
variable {Enc D Salt Pt Key : Type} [DecidableEq Enc] [Inhabited D] [DecidableEq Pt]
  {tA N L TM fc : ℕ}
variable {Oracle Mc : Type} {Opening : Q → Type} {n : ℕ}

/--
**The deployed zero-knowledge verifier on `(mt, ro)`.**  With the proof `out = S.proof mt ro` and the
verifier's challenges `S.challenges mt ro` (round `k`'s is `ro` at round `k`'s hash input): the
transcript builds a system `sys`, and `K`'s compiled verifier accepts — the opened set is the
query's, the Merkle opening reconstructs `out`'s root under the run's Merkle oracle, and `K`'s IPCP
verifier accepts the opened leaves — on `stmtOf sys`, at the decoded Ligero challenge and query, with
the response read from the query-round message.
-/
def AcceptsZkDH (K : Compiler Statement Oracle X Resp Q Opening Mc n)
    (V : ZkCode C F X Q Msg Gpt M ninp logw logc) (codec : Codec Salt Mc D Enc)
    (S : TotalOracleCommit.Setup Enc D Pt C Out Key tA N (Rounds.Role.length nl w))
    (check : Out → Tree Enc D Unit fc) (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim n Salt Mc D) (stmtOf : LigeroSystem ninp M F → Statement)
    (respOf : Msg → Resp) (mt : Fin TM → D) (ro : Pt → C) : Prop :=
  ∃ sys, zkBuilt (nl := nl) (w := w) V (msgOf (S.proof mt ro)) (S.challenges mt ro) = some sys ∧
    K.Accepts (codec.withOracle (S.merkleOracle check mt ro)) (stmtOf sys) (rootOf (S.proof mt ro))
      (V.decodeChal (S.challenges mt ro ligIdx))
      (respOf (msgOf (S.proof mt ro) (Rounds.Role.layerBase w nl + 2)))
      (V.decodeQuery (S.challenges mt ro qryIdx)) (claimOf (S.proof mt ro))

omit [DecidableEq Q] in
/-- **`AcceptsZkDH` is `guarded K`'s joint acceptance** at the verifier's maps. -/
theorem acceptsZkDH_iff_joint (K : Compiler Statement Oracle X Resp Q Opening Mc n)
    (V : ZkCode C F X Q Msg Gpt M ninp logw logc) (codec : Codec Salt Mc D Enc)
    (S : TotalOracleCommit.Setup Enc D Pt C Out Key tA N (Rounds.Role.length nl w))
    (check : Out → Tree Enc D Unit fc) (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim n Salt Mc D) (stmtOf : LigeroSystem ninp M F → Statement)
    (respOf : Msg → Resp) (mt : Fin TM → D) (ro : Pt → C) :
    AcceptsZkDH (nl := nl) (w := w) K V codec S check rootOf msgOf claimOf stmtOf respOf mt ro ↔
      JointAccepts (guarded K) codec S check rootOf claimOf
        (zkStatementOf (nl := nl) (w := w) V msgOf stmtOf) (responseOfAt nl w respOf msgOf)
        (zkChallengeOf (nl := nl) (w := w) V) (zkQueryOf (nl := nl) (w := w) V) mt ro := by
  unfold JointAccepts AcceptsZkDH zkStatementOf
  rw [accepts_guarded]
  constructor
  · rintro ⟨sys, hs, hacc⟩
    rw [hs]
    exact ⟨rfl, hacc⟩
  · rintro ⟨hb, hacc⟩
    rcases hs : zkBuilt (nl := nl) (w := w) V (msgOf (S.proof mt ro)) (S.challenges mt ro)
      with _ | sys
    · rw [hs] at hb; exact absurd hb (by simp)
    · rw [hs] at hacc
      exact ⟨sys, rfl, hacc⟩

/-- **The deployed zero-knowledge verifier of one side, at its slice `sl` of the merged tape**, with
the code read from the proof (`Vof`). -/
def AcceptsZkAtDH (K : Compiler Statement Oracle X Resp Q Opening Mc n)
    (Vof : Out → (Fin L → C) → ZkCode C F X Q Msg Gpt M ninp logw logc)
    (codec : Codec Salt Mc D Enc) (S : TotalOracleCommit.Setup Enc D Pt C Out Key tA N L)
    (check : Out → Tree Enc D Unit fc) (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim n Salt Mc D) (stmtOf : LigeroSystem ninp M F → Statement)
    (respOf : Msg → Resp) (sl : (Fin L → C) → Fin (Rounds.Role.length nl w) → C)
    (mt : Fin TM → D) (ro : Pt → C) : Prop :=
  ∃ sys, zkBuilt (nl := nl) (w := w) (Vof (S.proof mt ro) (S.challenges mt ro))
      (msgOf (S.proof mt ro)) (sl (S.challenges mt ro)) = some sys ∧
    K.Accepts (codec.withOracle (S.merkleOracle check mt ro)) (stmtOf sys) (rootOf (S.proof mt ro))
      ((Vof (S.proof mt ro) (S.challenges mt ro)).decodeChal (sl (S.challenges mt ro) ligIdx))
      (respOf (msgOf (S.proof mt ro) (Rounds.Role.layerBase w nl + 2)))
      ((Vof (S.proof mt ro) (S.challenges mt ro)).decodeQuery (sl (S.challenges mt ro) qryIdx))
      (claimOf (S.proof mt ro))

omit [DecidableEq Q] in
/-- **`AcceptsZkAtDH` is `guarded K`'s joint acceptance** at the side's maps. -/
theorem acceptsZkAtDH_iff_joint (K : Compiler Statement Oracle X Resp Q Opening Mc n)
    (Vof : Out → (Fin L → C) → ZkCode C F X Q Msg Gpt M ninp logw logc)
    (codec : Codec Salt Mc D Enc) (S : TotalOracleCommit.Setup Enc D Pt C Out Key tA N L)
    (check : Out → Tree Enc D Unit fc) (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim n Salt Mc D) (stmtOf : LigeroSystem ninp M F → Statement)
    (respOf : Msg → Resp) (sl : (Fin L → C) → Fin (Rounds.Role.length nl w) → C)
    (mt : Fin TM → D) (ro : Pt → C) :
    AcceptsZkAtDH (nl := nl) (w := w) K Vof codec S check rootOf msgOf claimOf stmtOf respOf sl
        mt ro ↔
      JointAccepts (guarded K) codec S check rootOf claimOf
        (zkStatementOfAt (nl := nl) (w := w) Vof msgOf stmtOf sl) (responseOfAt nl w respOf msgOf)
        (zkChallengeOfAt (nl := nl) (w := w) Vof sl) (zkQueryOfAt (nl := nl) (w := w) Vof sl)
        mt ro := by
  unfold JointAccepts AcceptsZkAtDH zkStatementOfAt
  rw [accepts_guarded]
  constructor
  · rintro ⟨sys, hs, hacc⟩
    rw [hs]
    exact ⟨rfl, hacc⟩
  · rintro ⟨hb, hacc⟩
    rcases hs : zkBuilt (nl := nl) (w := w) (Vof (S.proof mt ro) (S.challenges mt ro))
      (msgOf (S.proof mt ro)) (sl (S.challenges mt ro)) with _ | sys
    · rw [hs] at hb; exact absurd hb (by simp)
    · rw [hs] at hacc
      exact ⟨sys, rfl, hacc⟩

end Verifier

/-! ## 3. `hright`, at Ligero V1 -/

section V1

open Lfzk.LigeroV1Rows

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
variable {row : Row} {nw nq qw ninp M nt nlin : ℕ}
variable {C Msg Gpt : Type} [Fintype C] [DecidableEq C] [Nonempty C] [DecidableEq Msg]
  [Inhabited Msg] {logw logc nl : ℕ} {w : ℕ → ℕ}
variable {Enc D Salt Out : Type} [Inhabited D] [DecidableEq D] [DecidableEq Enc] [Inhabited Salt]
variable {tA N TM : ℕ}

omit [Fintype F] [Fintype C] [DecidableEq C] in
/--
**`hright`, proved for the deployed zero-knowledge verifier against a prefix-only prover.**

The proof of `CompiledZk.hright_zk`, at the deployed reading `NizkDeployedHashAdaptive.lfSetup`:
the transcript built `sys` and the compiled V1 check accepted on its encoding; where the cut-trace
extraction explains the opening, the query is in V1's test at the extracted matrix, which is the
Ligero half's query test.  Nothing in it reads how challenges are hashed.
-/
theorem hright_zkDH (h : row.Valid) (dom : LigeroFamily.ReedSolomon.Domain F row.openings qw row.n)
    (hkrow : row.openings + qw = row.k) (hr : 0 < row.openings)
    {codec : Codec Salt (Col F nw nq) D Enc} (dec : RoleDecoders codec)
    (pl : Encode.Placement ninp M qw nw nq nt)
    (V : ZkCode C F (ZkLigeroV1.Chal F nw nq nlin nt) (LigeroV1LayerStep.Qry row) Msg Gpt M ninp
      logw logc)
    (body : TwoOracleTree Enc D (MPoint D Msg nl w) C Out tA N) (rootOf : Out → D)
    (msgOf : Out → ℕ → Msg) (claimOf : Out → OpeningClaim row.n Salt (Col F nw nq) D)
    (respOf : Msg → LigeroFamily.Response F row.openings qw row.n 1)
    (LD : ∀ κ : D × List (Enc × D), ZkLigeroData C (ZkLigeroV1.Chal F nw nq nlin nt)
      (LigeroV1LayerStep.Qry row) Msg V
      (asgOf pl (h := h) (D := dom) (hkrow := hkrow)
        (O := extOracle nlin nt h dom hkrow hr dec κ)))
    (hLD : ∀ κ, (LD κ).accepting = accZ h dom hkrow pl nlin
      (extOracle nlin nt h dom hkrow hr dec κ) respOf)
    (mt : Fin TM → D) (ro : MPoint D Msg nl w → C)
    (hacc : JointAccepts (guarded (v1K (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide))
        (nw := nw) (nq := nq) h dom hkrow hr))
      codec (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf claimOf
      (zkStatementOf (nl := nl) (w := w) V msgOf (stmtOf pl nlin))
      (responseOfAt nl w respOf msgOf) (zkChallengeOf (nl := nl) (w := w) V)
      (zkQueryOf (nl := nl) (w := w) V) mt ro)
    (hexp : (lfSetup body rootOf msgOf).Explains dec id claimOf mt ro) :
    ZkLayerStepAccepts .accepted .start
      (steps (nl := nl) (w := w) V (LD ((lfSetup body rootOf msgOf).context mt ro))
        (msgOf ((lfSetup body rootOf msgOf).proof mt ro)))
      ((lfSetup body rootOf msgOf).challenges mt ro) := by
  rw [← acceptsZkDH_iff_joint] at hacc
  obtain ⟨sys, hsys, hv1⟩ := hacc
  obtain ⟨e, hext, hagree, -⟩ := hexp
  show ZkLayerStepAccepts .accepted .start (zkSteps nl w V _ _) _
  rw [zkAccepts_iff]
  refine ⟨sys, hsys, ?_⟩
  rw [hLD]
  exact mem_acceptingR_of_accepts h dom hkrow hr dec _ _ _ _ _ _ _ _ e hext hagree hv1

end V1

/-! ## 4. One field, at a certified V1 row -/

section Row

open Lfzk.CertifiedV1

variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
variable {ninp M nt nlin logw logc : ℕ}
variable {Enc D Salt : Type} [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc]
  [Inhabited Salt]
variable {Msg Out : Type} [Fintype Msg] [DecidableEq Msg] [Inhabited Msg] {tA N : ℕ}

/--
**A certified V1 row at the deployed zero-knowledge verifier, against a re-committing prefix-only
Fiat–Shamir prover, with no bound on the prover's Merkle queries.**  `row_zk_deployed_ratio_le` over a
Merkle tape of any length `TM` with room for the run, the Merkle term the exact count:

```text
Pr[ AcceptsZkDH (v1K …) V codec (lfSetup body rootOf msgOf) …  ∧  ZkFails Sat (context) ]
    ≤  zkCore  +  N · R.zkCoefficient logv  +  adaptiveNumerator (2n) tA (L + N) / 2^digestBits
```
-/
theorem row_zk_deployed_ratio_leT {R : Row} (h : R.Valid) (hr : 0 < R.params.row.openings) {TM : ℕ}
    (logv : ℕ) (pl : Encode.Placement ninp M R.params.q R.params.nw R.params.nq nt)
    {codec : Codec Salt (Col F R.params.nw R.params.nq) D Enc} (dec : RoleDecoders codec)
    (V : ZkCode C F (ZkLigeroV1.Chal F R.params.nw R.params.nq nlin nt)
      (LigeroV1LayerStep.Qry R.params.row) Msg (Fin logv → F) M ninp logw logc)
    (hnlin : V.nlin = nlin) (hnt : V.nt = nt)
    (dom : LigeroFamily.ReedSolomon.Domain F R.params.row.openings R.params.q R.params.row.n)
    (respOf : Msg → LigeroFamily.Response F R.params.row.openings R.params.q R.params.row.n 1)
    (body : TwoOracleTree Enc D (MPoint D Msg R.params.nl R.params.rounds) C Out tA N)
    (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim R.params.row.n Salt (Col F R.params.nw R.params.nq) D)
    (hF : Fintype.card F = R.params.row.fieldSize)
    (H : ∀ κ : D × List (Enc × D), ZkHonest F
      (ZkLigeroV1.Lift (Row.rowValid h) dom (Row.hkrow h)
        (extOracle nlin nt (Row.rowValid h) dom (Row.hkrow h) hr dec κ))
      logw logc)
    (Sat : ∀ κ : D × List (Enc × D),
      ZkLigeroV1.Lift (Row.rowValid h) dom (Row.hkrow h)
        (extOracle nlin nt (Row.rowValid h) dom (Row.hkrow h) hr dec κ) → Prop)
    (FD : ∀ κ : D × List (Enc × D), ZkFieldData C F
      (ZkLigeroV1.Chal F R.params.nw R.params.nq nlin nt)
      (LigeroV1LayerStep.Qry R.params.row) Msg (Fin logv → F)
      (ZkLigeroV1.Lift (Row.rowValid h) dom (Row.hkrow h)
        (extOracle nlin nt (Row.rowValid h) dom (Row.hkrow h) hr dec κ))
      M ninp logw logc R.params.nl R.params.rounds V (H κ) (asgOf pl) (Sat κ))
    (hexact : ∀ κ, (FD κ).ExactAt)
    (htape : 2 * R.params.row.n + tA ≤ TM) (hTM : 0 < TM)
    (hD : Fintype.card D = 2 ^ R.params.digestBits) :
    ((univ.filter fun ω : (Fin TM → D) × (MPoint D Msg R.params.nl R.params.rounds → C) =>
        AcceptsZkDH (nl := R.params.nl) (w := R.params.rounds)
            (v1K (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide)) (Row.rowValid h) dom
              (Row.hkrow h) hr) V codec
            (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf msgOf claimOf
            (stmtOf pl nlin) respOf ω.1 ω.2 ∧
          ZkFails Sat ((lfSetup body rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM
            * (Fintype.card C : ℚ) ^ Fintype.card (MPoint D Msg R.params.nl R.params.rounds))
      ≤ zkCoreAt R logv R.cardCand + N * R.zkCoefficient logv
        + (AdaptiveCommit.adaptiveNumerator (2 * R.params.row.n) tA
            (Rounds.Role.length R.params.nl R.params.rounds + N) : ℚ)
          / 2 ^ R.params.digestBits := by
  have key : ∀ ω : (Fin TM → D) × (MPoint D Msg R.params.nl R.params.rounds → C),
      AcceptsZkDH (nl := R.params.nl) (w := R.params.rounds)
            (v1K (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide)) (Row.rowValid h) dom
              (Row.hkrow h) hr) V codec
            (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf msgOf claimOf
            (stmtOf pl nlin) respOf ω.1 ω.2 ↔
        JointAccepts (guarded (v1K (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide))
            (Row.rowValid h) dom (Row.hkrow h) hr))
          codec (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf claimOf
          (zkStatementOf (nl := R.params.nl) (w := R.params.rounds) V msgOf (stmtOf pl nlin))
          (responseOfAt R.params.nl R.params.rounds respOf msgOf)
          (zkChallengeOf (nl := R.params.nl) (w := R.params.rounds) V)
          (zkQueryOf (nl := R.params.nl) (w := R.params.rounds) V) ω.1 ω.2 :=
    fun ω => acceptsZkDH_iff_joint _ _ _ _ _ _ _ _ _ _ _ _
  classical
  -- the Ligero half, at every context's extracted matrix
  have hex := fun κ : D × List (Enc × D) =>
    exists_zkLigeroData V hnlin hnt pl (Row.rowValid h) (Row.coreRows h) hF dom (Row.hkrow h)
      (extOracle nlin nt (Row.rowValid h) dom (Row.hkrow h) hr dec κ) respOf
  choose LD hLDacc hLDesc hLDbq using hex
  refine le_trans (le_of_eq ?_) (row_zk_deployed_adaptive_ratio_leT h logv dec
      (guarded (v1K (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide)) (Row.rowValid h) dom
        (Row.hkrow h) hr))
      body rootOf msgOf claimOf
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
      (fun mt ro hacc hexp => hright_zkDH (Row.rowValid h) dom (Row.hkrow h) hr dec pl V body
        rootOf msgOf claimOf respOf LD hLDacc mt ro hacc hexp)
      htape hTM hD)
  exact congrArg (fun t : Finset ((Fin TM → D) × (MPoint D Msg R.params.nl R.params.rounds → C)) =>
      ((t.card : ℕ) : ℚ) / ((Fintype.card D : ℚ) ^ TM
        * (Fintype.card C : ℚ) ^ Fintype.card (MPoint D Msg R.params.nl R.params.rounds)))
    (Finset.filter_congr fun ω _ => and_congr_left' (key ω))

/--
**A certified V1 row at the deployed zero-knowledge verifier, against a re-committing prefix-only
Fiat–Shamir prover.**

```text
Pr[ AcceptsZkDH (v1K …) V codec (lfSetup body rootOf msgOf) …  ∧  ZkFails Sat (context) ]
    ≤  R.zkBound logv  +  N · R.zkCoefficient logv  +  R.tape · (L + N) / 2^digestBits
```

over the Merkle tape and the total random oracle on the deployed hash inputs
`MPoint D Msg nl w` (root, role, messages through the round), against one adaptive program making
at most `tA` Merkle-oracle and `N` **deployed** hash queries.  `CompiledZk.row_zk_compiled_ratio_le`
with the hash inputs as deployed; the right-hand side is unchanged.  The candidates at a context
`κ` are the extracted matrix's lift list.  **Every premise**: the verifier (`h`, `hr`, `dom`, `V`
with `hnlin`, `hnt`, the placement `pl`, `respOf`), the analysis per context (`H κ`, `Sat κ`,
`FD κ` with `hexact`), `|F|`, `|D|`, the Merkle budget, and `Fintype Msg`.  `hfalse`, `hright` and
`hlig` are theorems.
-/
theorem row_zk_deployed_ratio_le {R : Row} (h : R.Valid) (hr : 0 < R.params.row.openings)
    (logv : ℕ) (pl : Encode.Placement ninp M R.params.q R.params.nw R.params.nq nt)
    {codec : Codec Salt (Col F R.params.nw R.params.nq) D Enc} (dec : RoleDecoders codec)
    (V : ZkCode C F (ZkLigeroV1.Chal F R.params.nw R.params.nq nlin nt)
      (LigeroV1LayerStep.Qry R.params.row) Msg (Fin logv → F) M ninp logw logc)
    (hnlin : V.nlin = nlin) (hnt : V.nt = nt)
    (dom : LigeroFamily.ReedSolomon.Domain F R.params.row.openings R.params.q R.params.row.n)
    (respOf : Msg → LigeroFamily.Response F R.params.row.openings R.params.q R.params.row.n 1)
    (body : TwoOracleTree Enc D (MPoint D Msg R.params.nl R.params.rounds) C Out tA N)
    (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim R.params.row.n Salt (Col F R.params.nw R.params.nq) D)
    (hF : Fintype.card F = R.params.row.fieldSize)
    (H : ∀ κ : D × List (Enc × D), ZkHonest F
      (ZkLigeroV1.Lift (Row.rowValid h) dom (Row.hkrow h)
        (extOracle nlin nt (Row.rowValid h) dom (Row.hkrow h) hr dec κ))
      logw logc)
    (Sat : ∀ κ : D × List (Enc × D),
      ZkLigeroV1.Lift (Row.rowValid h) dom (Row.hkrow h)
        (extOracle nlin nt (Row.rowValid h) dom (Row.hkrow h) hr dec κ) → Prop)
    (FD : ∀ κ : D × List (Enc × D), ZkFieldData C F
      (ZkLigeroV1.Chal F R.params.nw R.params.nq nlin nt)
      (LigeroV1LayerStep.Qry R.params.row) Msg (Fin logv → F)
      (ZkLigeroV1.Lift (Row.rowValid h) dom (Row.hkrow h)
        (extOracle nlin nt (Row.rowValid h) dom (Row.hkrow h) hr dec κ))
      M ninp logw logc R.params.nl R.params.rounds V (H κ) (asgOf pl) (Sat κ))
    (hexact : ∀ κ, (FD κ).ExactAt)
    (htA : tA ≤ R.commitFuel) (htape : 2 * R.params.row.n + tA ≤ R.tape)
    (hD : Fintype.card D = 2 ^ R.params.digestBits) :
    ((univ.filter fun ω : (Fin R.tape → D) × (MPoint D Msg R.params.nl R.params.rounds → C) =>
        AcceptsZkDH (nl := R.params.nl) (w := R.params.rounds)
            (v1K (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide)) (Row.rowValid h) dom
              (Row.hkrow h) hr) V codec
            (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf msgOf claimOf
            (stmtOf pl nlin) respOf ω.1 ω.2 ∧
          ZkFails Sat ((lfSetup body rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ R.tape
            * (Fintype.card C : ℚ) ^ Fintype.card (MPoint D Msg R.params.nl R.params.rounds))
      ≤ R.zkBound logv + N * R.zkCoefficient logv
        + ((R.tape * (Rounds.Role.length R.params.nl R.params.rounds + N) : ℕ) : ℚ)
          / 2 ^ R.params.digestBits := by
  refine le_trans (row_zk_deployed_ratio_leT h hr logv pl dec V hnlin hnt dom respOf body rootOf
    msgOf claimOf hF H Sat FD hexact htape (by have := Row.fuel_room h; omega) hD) ?_
  exact row_cap h logv htA htape

end Row

end Lfzk.CompiledZkDeployedHash

/-! ## 5. A deployed zero-knowledge side, at `(mt, ro)` -/

namespace Lfzk.CompiledZk.CompiledZkSide

open Finset Bcs Merkle Merkle.MH Merkle.RandomOracle RbrLongfellow Lfzk.RbrZkLongfellow
  Lfzk.RbrZkSplit Lfzk.ZkLigeroV1 Lfzk.CompiledZkDeployedHash
open Lfzk.CompiledLongfellow (Col guarded v1K)
open Lfzk.CompiledLongfellowAdaptive (Sig accepts_guarded responseOfAt mem_acceptingR_of_accepts)
open Lfzk.NizkDeployedHashAdaptive (JointAccepts)
open Lfzk.NizkDeployedHashTwoField (sideCtx)
open scoped Classical

variable {R : Lfzk.CertifiedV1.Row} {hR : R.Valid} {hr : 0 < R.params.row.openings} {logv : ℕ}
variable {C : Type} [Fintype C] [DecidableEq C] {F Msg Witness : Type} [Field F] [Fintype F]
  [DecidableEq F] [SumcheckInterp F] [DecidableEq Msg] [Inhabited Msg]
variable {M ninp nt nlin logw logc : ℕ}
variable {Enc D Salt : Type} [Inhabited D] [DecidableEq D] [DecidableEq Enc] [Inhabited Salt]
variable {X : Type} {codec : Codec Salt (Col F R.params.nw R.params.nq) D Enc}
  {dec : RoleDecoders codec} {rootOfKey : D × D → D}
variable (L : CompiledZkSide R hR hr logv C F Msg Witness M ninp nt nlin logw logc X dec rootOfKey)
variable {Out : Type} {Pt : Type} [DecidableEq Pt] {tA N Lsch fc TM : ℕ}

/-- **The side's code on `(mt, ro)`**: at the MAC-key share `av` the proof carries in its public
inputs, and the public data — not at a raw oracle answer.  The composed event checks `av` against the
oracle's answer at the key point. -/
def VofDH (avOf : Out → C) (pubOf : Out → X) (out : Out) (_chals : Fin Lsch → C) :
    ZkCode C F (ZkLigeroV1.Chal F R.params.nw R.params.nq nlin nt)
      (LigeroV1LayerStep.Qry R.params.row) Msg (Fin logv → F) M ninp logw logc :=
  L.Vc (avOf out) (pubOf out)

/-- **The side's deployed verifier on `(mt, ro)`**, at its slice `sl` of the verifier's
challenges. -/
def acceptsDH (S : TotalOracleCommit.Setup Enc D Pt C Out (D × D) tA N Lsch)
    (check : Out → Tree Enc D Unit fc) (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim R.params.row.n Salt (Col F R.params.nw R.params.nq) D)
    (avOf : Out → C) (pubOf : Out → X)
    (sl : (Fin Lsch → C) → Fin (Rounds.Role.length R.params.nl R.params.rounds) → C)
    (mt : Fin TM → D) (ro : Pt → C) : Prop :=
  AcceptsZkAtDH (nl := R.params.nl) (w := R.params.rounds)
    (v1K (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide)) (CertifiedV1.Row.rowValid hR) L.dom
      (CertifiedV1.Row.hkrow hR) hr)
    (L.VofDH avOf pubOf) codec S check rootOf msgOf claimOf (stmtOf L.pl nlin) L.respOf sl mt ro

omit [DecidableEq C] [DecidableEq Msg] [Inhabited Msg] in
/--
**`hright`, proved for one deployed zero-knowledge side against a prefix-only prover**: from the
guarded joint acceptance at the side's maps and the cut-trace extraction at the side's root, the
side's zero-knowledge LayerStep, in the side context `(κ, av, pub)`, accepts at its slice of the
verifier's challenges.  `CompiledZkSide.hright` at a `Bcs.TotalOracleCommit.Setup`.
-/
theorem hrightDH (S : TotalOracleCommit.Setup Enc D Pt C Out (D × D) tA N Lsch)
    (check : Out → Tree Enc D Unit fc)
    (rootOf : Out → D) (hroot : ∀ out, rootOfKey (S.keyOut out) = rootOf out)
    (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim R.params.row.n Salt (Col F R.params.nw R.params.nq) D)
    (avOf : Out → C) (pubOf : Out → X)
    (sl : (Fin Lsch → C) → Fin (Rounds.Role.length R.params.nl R.params.rounds) → C)
    (mt : Fin TM → D) (ro : Pt → C)
    (hacc : JointAccepts (guarded (v1K (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide))
        (CertifiedV1.Row.rowValid hR) L.dom (CertifiedV1.Row.hkrow hR) hr)) codec S check
      rootOf claimOf
      (zkStatementOfAt (nl := R.params.nl) (w := R.params.rounds) (L.VofDH avOf pubOf) msgOf
        (stmtOf L.pl nlin) sl)
      (responseOfAt R.params.nl R.params.rounds L.respOf msgOf)
      (zkChallengeOfAt (nl := R.params.nl) (w := R.params.rounds) (L.VofDH avOf pubOf) sl)
      (zkQueryOfAt (nl := R.params.nl) (w := R.params.rounds) (L.VofDH avOf pubOf) sl) mt ro)
    (hexp : S.Explains dec rootOfKey claimOf mt ro) :
    ZkLayerStepAccepts .accepted .start
      (steps (nl := R.params.nl) (w := R.params.rounds)
        (L.toZkSide.V (sideCtx S avOf pubOf mt ro)) (L.toZkSide.LD (sideCtx S avOf pubOf mt ro))
        (msgOf (S.proof mt ro)))
      (sl (S.challenges mt ro)) := by
  rw [← acceptsZkAtDH_iff_joint] at hacc
  obtain ⟨sys, hsys, hv1⟩ := hacc
  obtain ⟨e, hext, hagree, -⟩ := hexp
  show ZkLayerStepAccepts .accepted .start (zkSteps _ _ _ _ _) _
  rw [zkAccepts_iff]
  refine ⟨sys, hsys, ?_⟩
  show _ ∈ (L.LD (sideCtx S avOf pubOf mt ro)).accepting _ _ _ _ _
  rw [L.LD_acc]
  rw [← hroot (S.proof mt ro)] at hv1
  exact mem_acceptingR_of_accepts (CertifiedV1.Row.rowValid hR) L.dom (CertifiedV1.Row.hkrow hR)
    hr dec _ _ _ _ _ _ _ _ e hext hagree hv1

end Lfzk.CompiledZk.CompiledZkSide

/-! ## 6. Two deployed zero-knowledge sides, hash side first -/

namespace Lfzk.CompiledZkDeployedHash

open Finset Bcs Merkle Merkle.MH Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree
  RbrLongfellow Lfzk.RbrZkLongfellow Lfzk.RbrZkSplit Lfzk.NizkZk Lfzk.ZkLigeroV1 Lfzk.CompiledZk
  Lfzk.NizkZkDeployedHash Lfzk.CertifiedV1 Lfzk.Mac
open Lfzk.CompiledLongfellow (Col guarded v1K)
open Lfzk.CompiledLongfellowAdaptive (slice1 slice2 responseOfAt)
open Lfzk.NizkDeployedHashAdaptive (JointAccepts)
open Lfzk.NizkAdaptiveTwoField (check2 len2)
open Lfzk.NizkDeployedHashTwoField (Pt2 setup2 sideCtx)
open scoped Classical

section Compose

variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {D : Type} [Fintype D] [DecidableEq D] [Inhabited D]
variable {Enc X Out : Type} [DecidableEq Enc] [Fintype X]
variable {Fmac : Type} [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {nblk : ℕ}
variable {F₁ Msg₁ Witness₁ : Type} [Field F₁] [Fintype F₁] [DecidableEq F₁] [SumcheckInterp F₁]
  [DecidableEq Msg₁] [Inhabited Msg₁] [Fintype Msg₁] {M₁ ninp₁ nt₁ nlin₁ logw₁ logc₁ : ℕ}
variable {F₂ Msg₂ Witness₂ : Type} [Field F₂] [Fintype F₂] [DecidableEq F₂] [SumcheckInterp F₂]
  [DecidableEq Msg₂] [Inhabited Msg₂] [Fintype Msg₂] {M₂ ninp₂ nt₂ nlin₂ logw₂ logc₂ : ℕ}
variable {Salt₁ Salt₂ : Type} [Inhabited Salt₁] [Inhabited Salt₂]

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**Two-field Longfellow at the deployed zero-knowledge verifiers, against one re-committing
prefix-only Fiat–Shamir prover, with no bound on the prover's Merkle queries.**
`twofield_zk_deployed_ratio_le` over one Merkle tape of any length `TM` with room for the run, both
Merkle terms the exact count:

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧  no two good witnesses agree ]
    ≤  zkCore₁ + zkCore₂ + 1/|Fmac|
       +  N · max(R₁.zkCoefficient logv₁, R₂.zkCoefficient logv₂, 1/|Fmac|)
       +  2 · adaptiveNumerator (2n₂ + 2n₁) tA (len2 + N) / 2^digestBits
```
-/
theorem twofield_zk_deployed_ratio_leT {R₁ R₂ : Row} (h₁ : R₁.Valid) (h₂ : R₂.Valid)
    (hr₁ : 0 < R₁.params.row.openings) (hr₂ : 0 < R₂.params.row.openings)
    {logv₁ logv₂ tA N TM : ℕ}
    {codec₁ : Codec Salt₁ (Col F₁ R₁.params.nw R₁.params.nq) D Enc} {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ R₂.params.nw R₂.params.nq) D Enc} {dec₂ : RoleDecoders codec₂}
    (L₁ : CompiledZkSide R₁ h₁ hr₁ logv₁ C F₁ Msg₁ Witness₁ M₁ ninp₁ nt₁ nlin₁ logw₁ logc₁ X dec₁
      Prod.fst)
    (L₂ : CompiledZkSide R₂ h₂ hr₂ logv₂ C F₂ Msg₂ Witness₂ M₂ ninp₂ nt₂ nlin₂ logw₂ logc₂ X dec₂
      Prod.snd)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds
      R₂.params.rounds) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim R₁.params.row.n Salt₁ (Col F₁ R₁.params.nw R₁.params.nq) D)
    (claimOf₂ : Out → OpeningClaim R₂.params.row.n Salt₂ (Col F₂ R₂.params.nw R₂.params.nq) D)
    (hD₁ : Fintype.card D = 2 ^ R₁.params.digestBits)
    (hD₂ : Fintype.card D = 2 ^ R₂.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : Witness₁ → Fin nblk → Fmac) (common₂ : Witness₂ → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C)
        (a : Witness₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      L₁.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
        (slice1 R₁ R₂) mt ro →
      L₁.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C)
        (a : Witness₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      L₂.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
        (slice2 R₁ R₂) mt ro →
      L₂.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₂ a) = tagOf (S.proof mt ro))
    (htape : 2 * R₂.params.row.n + 2 * R₁.params.row.n + tA ≤ TM) (hTM : 0 < TM) :
    ((univ.filter fun ω : (Fin TM → D) ×
          (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C) =>
        L₁.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 R₁ R₂) ω.1 ω.2 ∧
          L₂.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 R₁ R₂) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            L₁.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf pubOf
              ω.1 ω.2) a₁ ∧
            L₂.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf pubOf
              ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds))
      ≤ zkCoreAt R₁ logv₁ R₁.cardCand + zkCoreAt R₂ logv₂ R₂.cardCand
        + 1 / (Fintype.card Fmac : ℚ)
        + N * max (max (R₁.zkCoefficient logv₁) (R₂.zkCoefficient logv₂))
            (1 / (Fintype.card Fmac : ℚ))
        + 2 * ((AdaptiveCommit.adaptiveNumerator (2 * R₂.params.row.n + 2 * R₁.params.row.n) tA
            (len2 R₁ R₂ + N) : ℚ) / 2 ^ R₁.params.digestBits) := by
  have hroot₁ : ∀ out, Prod.fst ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).keyOut out)
      = rootOf₁ out := fun _ => rfl
  have hroot₂ : ∀ out, Prod.snd ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).keyOut out)
      = rootOf₂ out := fun _ => rfl
  have key₁ : ∀ ω : (Fin TM → D) ×
        (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C),
      L₁.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
          (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
          (slice1 R₁ R₂) ω.1 ω.2 ↔
        JointAccepts (guarded (v1K (Equations := Fin nlin₁ ⊕ (Fin nt₁ × Encode.QSide))
            (Row.rowValid h₁) L₁.dom (Row.hkrow h₁) hr₁)) codec₁
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
          (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ claimOf₁
          (zkStatementOfAt (nl := R₁.params.nl) (w := R₁.params.rounds)
            (L₁.VofDH avOf pubOf) msgOf₁ (stmtOf L₁.pl nlin₁) (slice1 R₁ R₂))
          (responseOfAt R₁.params.nl R₁.params.rounds L₁.respOf msgOf₁)
          (zkChallengeOfAt (nl := R₁.params.nl) (w := R₁.params.rounds)
            (L₁.VofDH avOf pubOf) (slice1 R₁ R₂))
          (zkQueryOfAt (nl := R₁.params.nl) (w := R₁.params.rounds)
            (L₁.VofDH avOf pubOf) (slice1 R₁ R₂)) ω.1 ω.2 :=
    fun ω => acceptsZkAtDH_iff_joint _ _ _ _ _ _ _ _ _ _ _ _ _
  have key₂ : ∀ ω : (Fin TM → D) ×
        (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C),
      L₂.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
          (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
          (slice2 R₁ R₂) ω.1 ω.2 ↔
        JointAccepts (guarded (v1K (Equations := Fin nlin₂ ⊕ (Fin nt₂ × Encode.QSide))
            (Row.rowValid h₂) L₂.dom (Row.hkrow h₂) hr₂)) codec₂
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
          (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂
          (zkStatementOfAt (nl := R₂.params.nl) (w := R₂.params.rounds)
            (L₂.VofDH avOf pubOf) msgOf₂ (stmtOf L₂.pl nlin₂) (slice2 R₁ R₂))
          (responseOfAt R₂.params.nl R₂.params.rounds L₂.respOf msgOf₂)
          (zkChallengeOfAt (nl := R₂.params.nl) (w := R₂.params.rounds)
            (L₂.VofDH avOf pubOf) (slice2 R₁ R₂))
          (zkQueryOfAt (nl := R₂.params.nl) (w := R₂.params.rounds)
            (L₂.VofDH avOf pubOf) (slice2 R₁ R₂)) ω.1 ω.2 :=
    fun ω => acceptsZkAtDH_iff_joint _ _ _ _ _ _ _ _ _ _ _ _ _
  refine le_trans (le_of_eq ?_)
    (twofield_zk_deployed_adaptive_ratio_leT h₁ dec₁ dec₂
      (guarded (v1K (Equations := Fin nlin₁ ⊕ (Fin nt₁ × Encode.QSide))
        (Row.rowValid h₁) L₁.dom (Row.hkrow h₁) hr₁))
      (guarded (v1K (Equations := Fin nlin₂ ⊕ (Fin nt₂ × Encode.QSide))
        (Row.rowValid h₂) L₂.dom (Row.hkrow h₂) hr₂))
      body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂
      (zkStatementOfAt (nl := R₁.params.nl) (w := R₁.params.rounds)
        (L₁.VofDH avOf pubOf) msgOf₁ (stmtOf L₁.pl nlin₁) (slice1 R₁ R₂))
      (responseOfAt R₁.params.nl R₁.params.rounds L₁.respOf msgOf₁)
      (zkChallengeOfAt (nl := R₁.params.nl) (w := R₁.params.rounds)
        (L₁.VofDH avOf pubOf) (slice1 R₁ R₂))
      (zkQueryOfAt (nl := R₁.params.nl) (w := R₁.params.rounds)
        (L₁.VofDH avOf pubOf) (slice1 R₁ R₂))
      (zkStatementOfAt (nl := R₂.params.nl) (w := R₂.params.rounds)
        (L₂.VofDH avOf pubOf) msgOf₂ (stmtOf L₂.pl nlin₂) (slice2 R₁ R₂))
      (responseOfAt R₂.params.nl R₂.params.rounds L₂.respOf msgOf₂)
      (zkChallengeOfAt (nl := R₂.params.nl) (w := R₂.params.rounds)
        (L₂.VofDH avOf pubOf) (slice2 R₁ R₂))
      (zkQueryOfAt (nl := R₂.params.nl) (w := R₂.params.rounds)
        (L₂.VofDH avOf pubOf) (slice2 R₁ R₂))
      L₁.toZkSide L₂.toZkSide L₁.hF L₂.hF hD₁ hD₂ aP decode kmac hbal hmac keyB tagOf
      common₁ common₂
      (fun mt ro hacc hexp => L₁.hrightDH _ _ rootOf₁ hroot₁ msgOf₁ claimOf₁ avOf pubOf
        (slice1 R₁ R₂) mt ro hacc hexp)
      (fun mt ro hacc hexp => L₂.hrightDH _ _ rootOf₂ hroot₂ msgOf₂ claimOf₂ avOf pubOf
        (slice2 R₁ R₂) mt ro hacc hexp)
      (fun mt ro a hacc hgood => hrow₁ mt ro a ((key₁ (mt, ro)).mpr hacc) hgood)
      (fun mt ro a hacc hgood => hrow₂ mt ro a ((key₂ (mt, ro)).mpr hacc) hgood)
      htape hTM)
  exact congrArg (fun t : Finset ((Fin TM → D) ×
        (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C)) =>
      ((t.card : ℕ) : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ Fintype.card
          (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds)))
    (Finset.filter_congr fun ω _ => and_congr (key₁ ω) (and_congr_left' (key₂ ω)))

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**Two-field Longfellow at the deployed zero-knowledge verifiers, against one re-committing
prefix-only Fiat–Shamir prover with a hashed MAC key, in the deployed transcript order.**

`NizkZkDeployedHash.twofield_zk_deployed_adaptive_ratio_le` at two `CompiledZkSide`s, `hright`
discharged by `CompiledZkSide.hrightDH` and the Ligero halves built from V1.  Side 1 is proved first
on the transcript (in the deployed mdoc pairing the `GF(2^128)` hash circuit), side 2 on the same
transcript after it; each side's acceptance is `CompiledZkSide.acceptsDH` — its transcript, at its
slice of the verifier's challenges and with its code at the proof's `av` and public data, builds a
system, and its Merkle-compiled V1 check accepts the proof's response on the encoded system — and the
event adds `ro(key point) = av`:

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧  no two good witnesses agree ]
    ≤  R₁.zkBound logv₁ + R₂.zkBound logv₂ + 1/|Fmac|
       +  N · max(R₁.zkCoefficient logv₁, R₂.zkCoefficient logv₂, 1/|Fmac|)
       +  2 · tape · (len2 + N) / 2^digestBits
```

`N` counts deployed hash queries over all three roles.  **Every premise:** per side a
`CompiledZkSide`, `|D|`, the MAC data `aP`, `decode`, `hbal`, `hmac`, the MAC rows `hrow₁`, `hrow₂`
(`assert_mac`, at the `av` the proof carries), and the instance's numbers.
-/
theorem twofield_zk_deployed_ratio_le {R₁ R₂ : Row} (h₁ : R₁.Valid) (h₂ : R₂.Valid)
    (hr₁ : 0 < R₁.params.row.openings) (hr₂ : 0 < R₂.params.row.openings)
    {logv₁ logv₂ tA N : ℕ}
    {codec₁ : Codec Salt₁ (Col F₁ R₁.params.nw R₁.params.nq) D Enc} {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ R₂.params.nw R₂.params.nq) D Enc} {dec₂ : RoleDecoders codec₂}
    (L₁ : CompiledZkSide R₁ h₁ hr₁ logv₁ C F₁ Msg₁ Witness₁ M₁ ninp₁ nt₁ nlin₁ logw₁ logc₁ X dec₁
      Prod.fst)
    (L₂ : CompiledZkSide R₂ h₂ hr₂ logv₂ C F₂ Msg₂ Witness₂ M₂ ninp₂ nt₂ nlin₂ logw₂ logc₂ X dec₂
      Prod.snd)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds
      R₂.params.rounds) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim R₁.params.row.n Salt₁ (Col F₁ R₁.params.nw R₁.params.nq) D)
    (claimOf₂ : Out → OpeningClaim R₂.params.row.n Salt₂ (Col F₂ R₂.params.nw R₂.params.nq) D)
    (hD₁ : Fintype.card D = 2 ^ R₁.params.digestBits)
    (hD₂ : Fintype.card D = 2 ^ R₂.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : Witness₁ → Fin nblk → Fmac) (common₂ : Witness₂ → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin R₁.tape → D)
        (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C)
        (a : Witness₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      L₁.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
        (slice1 R₁ R₂) mt ro →
      L₁.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin R₁.tape → D)
        (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C)
        (a : Witness₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      L₂.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
        (slice2 R₁ R₂) mt ro →
      L₂.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₂ a) = tagOf (S.proof mt ro))
    (htA₁ : tA ≤ R₁.commitFuel) (htA₂ : tA ≤ R₂.commitFuel)
    (htape : 2 * R₂.params.row.n + 2 * R₁.params.row.n + tA ≤ R₁.tape)
    (htape₂ : R₁.tape = R₂.tape) :
    ((univ.filter fun ω : (Fin R₁.tape → D) ×
          (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C) =>
        L₁.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 R₁ R₂) ω.1 ω.2 ∧
          L₂.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 R₁ R₂) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            L₁.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf pubOf
              ω.1 ω.2) a₁ ∧
            L₂.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf pubOf
              ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ R₁.tape * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds))
      ≤ R₁.zkBound logv₁ + R₂.zkBound logv₂ + 1 / (Fintype.card Fmac : ℚ)
        + N * max (max (R₁.zkCoefficient logv₁) (R₂.zkCoefficient logv₂))
            (1 / (Fintype.card Fmac : ℚ))
        + 2 * (((R₁.tape * (len2 R₁ R₂ + N) : ℕ) : ℚ) / 2 ^ R₁.params.digestBits) := by
  refine le_trans (twofield_zk_deployed_ratio_leT h₁ h₂ hr₁ hr₂ L₁ L₂ body rootOf₁ rootOf₂ avOf pubOf
    msgOf₁ msgOf₂ claimOf₁ claimOf₂ hD₁ hD₂ aP decode kmac hbal hmac keyB tagOf common₁ common₂
    hrow₁ hrow₂ htape (by have := Row.fuel_room h₁; omega)) ?_
  exact twofield_cap (logv₁ := logv₁) (logv₂ := logv₂) hD₁ hD₂ htA₁ htA₂ htape htape₂

end Compose

end Lfzk.CompiledZkDeployedHash
