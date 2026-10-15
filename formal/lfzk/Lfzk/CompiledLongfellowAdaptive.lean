import Lfzk.NizkAdaptiveTwoField
import Lfzk.CompiledLongfellow

/-!
# The compiled Longfellow verifier against a re-committing Fiat–Shamir prover

`Lfzk.CertifiedV1.Row.adaptive_ratio_le` and `NizkAdaptiveTwoField.twofield_adaptive_ratio_le`
bound `Pr[JointAccepts … ∧ Fails]` against one adaptive program that interleaves Merkle-oracle and
challenge-oracle queries, for an **abstract** compiled verifier `K` with abstract `statementOf`,
`challengeOf`, `queryOf`, `responseOf`, an abstract Ligero half `hlig`, and the bridge `hright`.
This file fixes the verifier to the compiled Longfellow verifier of `Lfzk.CompiledLongfellow` and
proves `hlig` and `hright` for it, so that both headline theorems are stated about `AcceptsAt` with
no acceptance bridge left among the premises.

## The verifier (`AcceptsAt`)

On a joint execution (`Bcs.AdaptiveCommit.Setup`) with proof `out` and recomputed answers `chals`:

1. **the field rounds** (`FieldPass V (msgOf out) (sl chals)`): the Longfellow LayerStep's transitions,
   read from the verifier's code `V`, are still `running` after the input binding on the proof's
   messages at the slice `sl chals` of the recomputed answers that is this LayerStep's tape;
2. **the Merkle opening and Ligero V1's policy on the opened columns** (`Bcs.Compiler.Accepts` at
   `v1K`, the V1 compiler at the row's Reed–Solomon code, under the run's lazily sampled Merkle
   oracle): the opened set is the drawn query's, the opening reconstructs the proof's root, and the
   V1 policy accepts the proof's response at the decoded recomputed challenge and query, on the
   Ligero statement the verifier reads from the proof and the recomputed answers.

The proof's Ligero response is **the message of the query round** (`responseOfAt`): the V1 response
is sent after the linear-combination challenge and before the query, so it is the last message the
query's hash input absorbs.

## `hlig`: Ligero V1 at the proof's own response

`NizkGrinding` and `NizkAdaptive` took a Ligero V1 *instance* per commitment, a prover with a fixed
response strategy, and `hright` carried that the proof answered as that prover does.  Here no
strategy is assumed.  The query test reads the proof's response (`acceptingR`), and the Ligero half
is built at the **maximizing** response strategy (`maxResponse`): the doom predicate and escaping
set are `Lfzk.LigeroV1Rows.Row.rbr_soundness`'s at the prover that answers every challenge with the
response that has the most accepting queries, so a doomed challenge has at most `queryCount`
accepting queries at *every* response (`exists_msgLigeroData`).  The Ligero statement is a function
of the commitment context's root (single-field) or of the root, the MAC-key answer and the public
data (two-field); the committed matrix is the one Merkle extraction recovers from the context's root
and cut trace (`extractedInstance`).

## `hright`

`mem_acceptingR_of_accepts`: where the cut-trace extraction explains the opening, the compiled V1
check at `(x, ρ, q)` puts `q` in `acceptingR` of the extracted instance at `ρ` and `x`
(`Bcs.Compiler.protocol_accepts_of_accepts`).  With `Matches` (LayerStep data's computational
fields are the code's), the field verdict and this are LayerStep's acceptance
(`CompiledLongfellow.stepsOf_withMsgs_eq`, `layerStepAccepts_iff`): `hright_v1`, `hright_side`.

`guarded` is the formal device of `Lfzk.CompiledLongfellow`: the field verdict rides in the
statement slot of the `Bcs.Compiler`, which `JointAccepts` now reads from the proof and the
recomputed answers, so that `JointAccepts (guarded K) …` *is* `AcceptsAt` (`acceptsAt_iff_joint`).

## What is still a hypothesis

`row_adaptive_ratio_le_v1`, `v8Hash_adaptive_compiled_ratio_le` and
`p256sha_adaptive_compiled_ratio_le` list them: the protocol instance (field, domain, fuels, `|D|`,
`|Cand|`), `Matches`, `hfalse` (at a context where extraction fails, the Ligero statement is false —
Ligero's extractor), `hfail`, and — two-field — the MAC rows `hrow`.  `hlig` and `hright` are
theorems.  Which verifier this is (the non-ZK-path sumcheck checks with a Ligero statement fixed by
the commitment and the MAC key, not the deployed zero-knowledge verifier), and the residual
refinement claim, are in `Lfzk.CompiledLongfellow`'s module docstring and apply here with R5 read as
"the deployed statement is a function of the root (and the MAC key)".
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.CompiledLongfellowAdaptive

open Finset Bcs Bcs.AdaptiveCommit Merkle Merkle.MH Merkle.RandomOracle
  Merkle.RandomOracle.TwoOracleTree RbrLongfellow Lfzk.NizkGrinding Lfzk.NizkAdaptive
  Lfzk.CompiledLongfellow
open scoped Classical

/-! ## 1. Ligero V1 at the proof's own response -/

section Response

open Lfzk.LigeroV1Rows LigeroFamily

variable {F Equations : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype Equations]
  [DecidableEq Equations]
variable {row : Row} {nw nq w : ℕ}

/-- A V1 instance without a response strategy: the Ligero statement and the committed matrix. -/
structure OracleInstance (row : Row) (F Equations : Type) (nw nq w : ℕ) where
  statement : ConstraintSystem F nw nq w Equations
  oracle : Ligero.V1.Oracle F nw nq row.n 1

/-- **The V1 verifier's accepting queries at a challenge and a response**: the queries on which
`SchemeVerifier.policy C Ligero.V1.scheme` accepts the response against the committed matrix's
opened columns. -/
noncomputable def acceptingR (h : row.Valid) (D : ReedSolomon.Domain F row.openings w row.n)
    (hkrow : row.openings + w = row.k) (I : OracleInstance row F Equations nw nq w)
    (ρ : Response F row.openings w row.n 1) (x : LigeroV1LayerStep.Chal F Equations nw nq) :
    Finset (LigeroV1LayerStep.Qry row) := by
  classical
  exact univ.filter fun query =>
    (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1)
      (LigeroV1LayerStep.code h D hkrow) Ligero.V1.scheme).accepts I.statement x ρ query
      (openSchemeOracle I.oracle query)

instance instInhabitedResponse {r w n repetitions : ℕ} : Inhabited (Response F r w n repetitions) :=
  ⟨⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0⟩⟩

/-- **The maximizing response** at a challenge: a response with the most accepting queries. -/
noncomputable def maxResponse (h : row.Valid) (D : ReedSolomon.Domain F row.openings w row.n)
    (hkrow : row.openings + w = row.k) (I : OracleInstance row F Equations nw nq w)
    (x : LigeroV1LayerStep.Chal F Equations nw nq) : Response F row.openings w row.n 1 :=
  Classical.choose (Finset.exists_max_image (univ : Finset (Response F row.openings w row.n 1))
    (fun ρ => (acceptingR h D hkrow I ρ x).card) univ_nonempty)

omit [DecidableEq Equations] in
theorem card_acceptingR_le_max (h : row.Valid) (D : ReedSolomon.Domain F row.openings w row.n)
    (hkrow : row.openings + w = row.k) (I : OracleInstance row F Equations nw nq w)
    (ρ : Response F row.openings w row.n 1) (x : LigeroV1LayerStep.Chal F Equations nw nq) :
    (acceptingR h D hkrow I ρ x).card
      ≤ (acceptingR h D hkrow I (maxResponse h D hkrow I x) x).card :=
  (Classical.choose_spec (Finset.exists_max_image (univ : Finset (Response F row.openings w row.n 1))
    (fun ρ => (acceptingR h D hkrow I ρ x).card) univ_nonempty)).2 ρ (mem_univ _)

/-- The IPCP prover that commits the matrix and answers every challenge with its maximizing
response. -/
noncomputable def maxProver (h : row.Valid) (D : ReedSolomon.Domain F row.openings w row.n)
    (hkrow : row.openings + w = row.k) (I : OracleInstance row F Equations nw nq w) :
    IPCPProver (ConstraintSystem F nw nq w Equations) (Ligero.V1.Oracle F nw nq row.n 1)
      (Ligero.V1.Challenge F nw nq 1 Equations) (Response F row.openings w row.n 1) where
  commit _ := I.oracle
  respond _ _ x := maxResponse h D hkrow I x

/--
**LayerStep's Ligero half at the proof's own response.**

At a valid row and a false Ligero statement there is a doom predicate on V1 challenges and a
message-reading `MsgLigeroData` over it whose query test is `acceptingR` at the response the message
carries (`respOf`), whose escaping set has density at most `fail + arith`, and whose query bound is
`queryCount`, **whatever the response**.

Proof: `Row.rbr_soundness` at the maximizing prover; the doom predicate is the classifier's
`ProfiledDoomedAfter` at the row's thresholds and `escaping` its `profiledEscaping`, as in
`LigeroV1LayerStep.exists_ligeroData`; at a doomed challenge the response the message carries has at
most as many accepting queries as the maximizing one, which has at most `queryCount`.
-/
theorem exists_msgLigeroData (C Msg : Type) (h : row.Valid) (hrows : CoreRowsNonempty nw nq)
    (hfield : Fintype.card F = row.fieldSize) (D : ReedSolomon.Domain F row.openings w row.n)
    (hkrow : row.openings + w = row.k) (I : OracleInstance row F Equations nw nq w)
    (hfalse : ¬ I.statement.Language) (respOf : Msg → Response F row.openings w row.n 1) :
    ∃ (LigDoomed : LigeroV1LayerStep.Chal F Equations nw nq → Prop)
      (ML : MsgLigeroData C (LigeroV1LayerStep.Chal F Equations nw nq)
        (LigeroV1LayerStep.Qry row) Msg LigDoomed),
      ML.accepting = (fun _ _ msg x => acceptingR h D hkrow I (respOf msg) x) ∧
      (ML.escaping.card : ℚ)
        ≤ (row.fail + row.arith) * Fintype.card (LigeroV1LayerStep.Chal F Equations nw nq) ∧
      ML.bq = LigeroV1LayerStep.queryCount row := by
  classical
  obtain ⟨cl, hq, hesc, hcov⟩ := Row.rbr_soundness h hrows hfield D hkrow I.statement
    (maxProver h D hkrow I) hfalse
  have hchoose : (0 : ℚ) < (row.n.choose row.openings : ℚ) := by
    exact_mod_cast Nat.choose_pos (Row.openings_le h)
  have hcard : ((cl.profiledEscaping row.failureThreshold row.arithmeticThreshold).card : ℚ)
      ≤ (row.fail + row.arith) * Fintype.card (Ligero.V1.Challenge F nw nq 1 Equations) := by
    rcases Nat.eq_zero_or_pos (Fintype.card (Ligero.V1.Challenge F nw nq 1 Equations))
      with hX | hX
    · haveI : IsEmpty (Ligero.V1.Challenge F nw nq 1 Equations) :=
        Fintype.card_eq_zero_iff.mp hX
      rw [Finset.eq_empty_of_isEmpty
        (cl.profiledEscaping row.failureThreshold row.arithmeticThreshold),
        Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg (add_nonneg (LigeroV1LayerStep.fail_nonneg row)
        (LigeroV1LayerStep.arith_nonneg row)) (Nat.cast_nonneg _)
    · have hXpos : (0 : ℚ) <
          (Fintype.card (Ligero.V1.Challenge F nw nq 1 Equations) : ℚ) := by
        exact_mod_cast hX
      rw [div_le_iff₀ hXpos] at hesc
      exact hesc
  refine ⟨cl.ProfiledDoomedAfter row.failureThreshold row.arithmeticThreshold,
    { accepting := fun _ _ msg x => acceptingR h D hkrow I (respOf msg) x
      escaping := cl.profiledEscaping row.failureThreshold row.arithmeticThreshold
      hesc := hcov
      bq := LigeroV1LayerStep.queryCount row
      hbq := ?_ }, rfl, hcard, rfl⟩
  intro m pref msg x hx
  show (acceptingR h D hkrow I (respOf msg) x).card ≤ LigeroV1LayerStep.queryCount row
  have hdens := hq x hx
  have hacc : cl.acceptingQueries x = acceptingR h D hkrow I (maxResponse h D hkrow I x) x := rfl
  rw [hacc, div_le_iff₀ hchoose] at hdens
  exact le_trans (card_acceptingR_le_max h D hkrow I (respOf msg) x) (Nat.le_floor hdens)

variable {Enc D Salt : Type} [Inhabited D] [DecidableEq D] [DecidableEq Enc] [Inhabited Salt]

/-- **The extracted V1 instance at a commitment context**: the statement, and the matrix Merkle
extraction recovers from the context's root and cut trace (defaulted where it fails). -/
noncomputable def extractedInstance (h : row.Valid) (dom : ReedSolomon.Domain F row.openings w row.n)
    (hkrow : row.openings + w = row.k) (hr : 0 < row.openings)
    {codec : Codec Salt (Col F nw nq) D Enc} (dec : RoleDecoders codec)
    (stmt : ConstraintSystem F nw nq w Equations) (root : D) (tr : List (Enc × D)) :
    OracleInstance row F Equations nw nq w where
  statement := stmt
  oracle := (v1K (Equations := Equations) (nw := nw) (nq := nq) h dom hkrow hr).oracleOfClaim
    (((extract dec row.n root tr).map Extracted.message).getD default)

omit [Fintype F] [DecidableEq Equations] [DecidableEq Enc] in
/--
**The compiled Ligero check is V1's policy at the extracted columns, at the proof's response.**
Where an extraction from `(root, tr)` explains the opening, a compiled acceptance at `(x, ρ, q)` puts
`q` in the response-reading test of the extracted instance at `ρ` and `x`
(`Bcs.Compiler.protocol_accepts_of_accepts`; the V1 protocol's verifier is `decide` of the V1
policy).
-/
theorem mem_acceptingR_of_accepts (h : row.Valid) (dom : ReedSolomon.Domain F row.openings w row.n)
    (hkrow : row.openings + w = row.k) (hr : 0 < row.openings)
    {codec : Codec Salt (Col F nw nq) D Enc} (dec : RoleDecoders codec)
    (S : MH.Scheme Salt (Col F nw nq) D Enc) (stmt : ConstraintSystem F nw nq w Equations)
    (root : D) (tr : List (Enc × D)) (x : LigeroV1LayerStep.Chal F Equations nw nq)
    (ρ : Response F row.openings w row.n 1) (q : LigeroV1LayerStep.Qry row)
    (claim : OpeningClaim row.n Salt (Col F nw nq) D) (e : Extracted row.n Salt (Col F nw nq) D)
    (hext : extract dec row.n root tr = some e)
    (hagree : ∀ i ∈ claim.I, e.message i = claim.a i)
    (hacc : (v1K (Equations := Equations) (nw := nw) (nq := nq) h dom hkrow hr).Accepts S stmt root
      x ρ q claim) :
    q ∈ acceptingR h dom hkrow (extractedInstance h dom hkrow hr dec stmt root tr) ρ x := by
  have hprot := (v1K (Equations := Equations) (nw := nw) (nq := nq) h dom hkrow hr)
    |>.protocol_accepts_of_accepts S stmt root x q claim e.message (fun _ => ρ) hagree hacc
  have horacle : (extractedInstance h dom hkrow hr dec stmt root tr).oracle
      = (v1K (Equations := Equations) (nw := nw) (nq := nq) h dom hkrow hr).oracleOfClaim
          e.message := by
    show (v1K (Equations := Equations) (nw := nw) (nq := nq) h dom hkrow hr).oracleOfClaim
      (((extract dec row.n root tr).map Extracted.message).getD default) = _
    rw [hext]
    rfl
  unfold acceptingR
  rw [Finset.mem_filter, horacle]
  exact ⟨Finset.mem_univ _, @of_decide_eq_true _ _ hprot⟩

end Response

/-! ## 2. The compiled verifier on a joint execution -/

section Verifier

variable {C F X Q Msg : Type} [Fintype C] [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
  [DecidableEq X] [Fintype Q] [DecidableEq Q]
variable {logw logc nl : ℕ} {w : ℕ → ℕ}
variable {Out Statement Resp : Type} {L : ℕ}

/-- **The verifier's statement for `guarded K`**: its Ligero statement, read from the proof and the
recomputed answers, and the field rounds' verdict on the proof's messages at the slice `sl` of the
recomputed answers that is this LayerStep's tape. -/
noncomputable def statementOfAt (V : Code C F X Q Msg logw logc) (msgOf : Out → ℕ → Msg)
    (stmtOf : Out → (Fin L → C) → Statement)
    (sl : (Fin L → C) → Fin (Rounds.Role.length nl w) → C) (out : Out) (chals : Fin L → C) :
    Statement × Bool :=
  (stmtOf out chals, decide (FieldPass V (msgOf out) (sl chals)))

/-- **The verifier's Ligero challenge**: the challenge decoder at the recomputed answer of the
Ligero challenge slot. -/
def challengeOfAt (V : Code C F X Q Msg logw logc)
    (sl : (Fin L → C) → Fin (Rounds.Role.length nl w) → C) (_out : Out) (chals : Fin L → C) : X :=
  V.decodeChal (sl chals ligIdx)

/-- **The verifier's Ligero query**: the query decoder at the recomputed answer of the query slot. -/
def queryOfAt (V : Code C F X Q Msg logw logc)
    (sl : (Fin L → C) → Fin (Rounds.Role.length nl w) → C) (_out : Out) (chals : Fin L → C) : Q :=
  V.decodeQuery (sl chals qryIdx)

/-- **The verifier's reading of the proof's Ligero response**: the message of the query round. -/
def responseOfAt (nl : ℕ) (w : ℕ → ℕ) (respOf : Msg → Resp) (msgOf : Out → ℕ → Msg) (out : Out) :
    Resp :=
  respOf (msgOf out (Rounds.Role.layerBase w nl + 2))

variable {Enc D Salt Pt Key : Type} [DecidableEq Enc] [Inhabited D] [DecidableEq Pt]
  {tA N TM TC fc : ℕ}
variable {Oracle M : Type} {Opening : Q → Type} {n : ℕ}

/--
**The compiled Longfellow verifier on a joint execution.**  With the proof `out = S.proof mt ct` and
the recomputed answers `chals = S.challenges mt ct`:

* LayerStep's field rounds pass on `out`'s messages at the tape `sl chals` (`FieldPass`), and
* `K`'s compiled verifier accepts under the run's Merkle oracle — the opened set is the query's, the
  Merkle opening reconstructs `out`'s root, and `K`'s IPCP verifier accepts the opened leaves — on the
  statement `stmtOf out chals`, at the decoded recomputed Ligero challenge and query, with the proof's
  response read from its query-round message.
-/
def AcceptsAt (K : Compiler Statement Oracle X Resp Q Opening M n) (V : Code C F X Q Msg logw logc)
    (codec : Codec Salt M D Enc) (S : Setup Enc D Pt C Out Key tA N L)
    (check : Out → Tree Enc D Unit fc) (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim n Salt M D) (stmtOf : Out → (Fin L → C) → Statement)
    (respOf : Msg → Resp) (sl : (Fin L → C) → Fin (Rounds.Role.length nl w) → C)
    (mt : Fin TM → D) (ct : Fin TC → C) : Prop :=
  FieldPass V (msgOf (S.proof mt ct)) (sl (S.challenges mt ct)) ∧
    K.Accepts (codec.withOracle (S.merkleOracle check mt ct))
      (stmtOf (S.proof mt ct) (S.challenges mt ct)) (rootOf (S.proof mt ct))
      (V.decodeChal (sl (S.challenges mt ct) ligIdx))
      (respOf (msgOf (S.proof mt ct) (Rounds.Role.layerBase w nl + 2)))
      (V.decodeQuery (sl (S.challenges mt ct) qryIdx)) (claimOf (S.proof mt ct))

omit [DecidableEq X] [Fintype Q] [DecidableEq Q] [DecidableEq Enc] in
/-- The guarded compiler's verifier is the guard and `K`'s verifier. -/
theorem accepts_guarded (K : Compiler Statement Oracle X Resp Q Opening M n)
    (S' : MH.Scheme Salt M D Enc) (s : Statement) (b : Bool) (root : D) (x : X) (ρ : Resp)
    (q : Q) (claim : OpeningClaim n Salt M D) :
    (guarded K).Accepts S' (s, b) root x ρ q claim ↔ b = true ∧ K.Accepts S' s root x ρ q claim := by
  unfold Compiler.Accepts
  simp only [guarded, Compiler.oracleOfClaim, Bool.and_eq_true]
  tauto

omit [Fintype C] [Fintype F] [DecidableEq X] [Fintype Q] in
/-- **`AcceptsAt` is `guarded K`'s joint acceptance** at the verifier's statement, response,
challenge and query maps. -/
theorem acceptsAt_iff_joint (K : Compiler Statement Oracle X Resp Q Opening M n)
    (V : Code C F X Q Msg logw logc) (codec : Codec Salt M D Enc)
    (S : Setup Enc D Pt C Out Key tA N L) (check : Out → Tree Enc D Unit fc) (rootOf : Out → D)
    (msgOf : Out → ℕ → Msg) (claimOf : Out → OpeningClaim n Salt M D)
    (stmtOf : Out → (Fin L → C) → Statement) (respOf : Msg → Resp)
    (sl : (Fin L → C) → Fin (Rounds.Role.length nl w) → C) (mt : Fin TM → D) (ct : Fin TC → C) :
    AcceptsAt (nl := nl) (w := w) K V codec S check rootOf msgOf claimOf stmtOf respOf sl mt ct ↔
      JointAccepts (guarded K) codec S check rootOf claimOf (statementOfAt V msgOf stmtOf sl)
        (responseOfAt nl w respOf msgOf) (challengeOfAt V sl) (queryOfAt V sl) mt ct := by
  unfold JointAccepts AcceptsAt statementOfAt
  rw [accepts_guarded, decide_eq_true_iff]
  rfl

end Verifier

/-! ## 3. `hright`, single field -/

section V1

open Lfzk.LigeroV1Rows

variable {C F Equations Msg : Type} [Fintype C] [DecidableEq C] [Field F] [Fintype F]
  [DecidableEq F] [SumcheckInterp F] [Fintype Equations] [DecidableEq Equations]
variable {logw logc nl : ℕ} {w : ℕ → ℕ} {row : Row} {nw nq qw : ℕ}
variable {Enc D Salt Out Cand Witness : Type} [Inhabited D] [DecidableEq D] [DecidableEq Enc]
  [Inhabited Salt] [DecidableEq Msg] [Inhabited Msg]
variable {nc nv tA N TM TC : ℕ}

/-- The single-field statement map: the Ligero statement at the proof's root. -/
def rootStatement {Statement : Type} (rootOf : Out → D) (stmt : D → Statement) (out : Out)
    (_chals : Fin (Rounds.Role.length nl w) → C) : Statement :=
  stmt (rootOf out)

/-- **The response-reading V1 query test at a commitment context**: the extracted instance at the
context's root and cut trace, with the statement at the root. -/
noncomputable def accR (h : row.Valid) (dom : LigeroFamily.ReedSolomon.Domain F row.openings qw row.n)
    (hkrow : row.openings + qw = row.k) (hr : 0 < row.openings)
    {codec : Codec Salt (Col F nw nq) D Enc} (dec : RoleDecoders codec)
    (stmt : D → LigeroFamily.ConstraintSystem F nw nq qw Equations)
    (respOf : Msg → LigeroFamily.Response F row.openings qw row.n 1) (κ : D × List (Enc × D))
    (_m : ℕ) (_pref : Fin _m → C) (msg : Msg) (x : LigeroV1LayerStep.Chal F Equations nw nq) :
    Finset (LigeroV1LayerStep.Qry row) :=
  acceptingR h dom hkrow (extractedInstance h dom hkrow hr dec (stmt κ.1) κ.1 κ.2) (respOf msg) x

omit [Inhabited Msg] in
/--
**`hright`, proved for the compiled Longfellow verifier against a re-committing prover.**

`Row.adaptive_ratio_le`'s acceptance hypothesis at `K := guarded (v1K …)`, the verifier's maps, and
the response-reading test `accR`: from the guarded joint acceptance, the guard is `FieldPass` and
the V1 part puts the drawn query in the extracted instance's test at the proof's response
(`mem_acceptingR_of_accepts`); with LayerStep data matching the verifier these are LayerStep's
acceptance.
-/
theorem hright_v1 (h : row.Valid) (dom : LigeroFamily.ReedSolomon.Domain F row.openings qw row.n)
    (hkrow : row.openings + qw = row.k) (hr : 0 < row.openings)
    {codec : Codec Salt (Col F nw nq) D Enc} (dec : RoleDecoders codec)
    (V : Code C F (LigeroV1LayerStep.Chal F Equations nw nq) (LigeroV1LayerStep.Qry row) Msg logw logc)
    (body : TwoOracleTree Enc D (Point D Msg C nl w) C Out tA N) (dflt : C) (rootOf : Out → D)
    (msgOf : Out → ℕ → Msg) (claimOf : Out → OpeningClaim row.n Salt (Col F nw nq) D)
    (stmt : D → LigeroFamily.ConstraintSystem F nw nq qw Equations)
    (respOf : Msg → LigeroFamily.Response F row.openings qw row.n 1)
    {H : Honest F Cand logw logc} {Sat : Cand → Prop}
    (FD : RbrSplit.FieldData C F (LigeroV1LayerStep.Chal F Equations nw nq)
      (LigeroV1LayerStep.Qry row) Cand Witness nc nv logw logc H Sat)
    (MD : MsgData C Msg H) (hm : Matches V FD MD) (mt : Fin TM → D) (ct : Fin TC → C)
    (hacc : JointAccepts (guarded (v1K (Equations := Equations) (nw := nw) (nq := nq) h dom hkrow hr))
      codec (lfSetup body dflt rootOf msgOf) (lfCheck codec claimOf) rootOf claimOf
      (statementOfAt V msgOf (rootStatement rootOf stmt) id) (responseOfAt nl w respOf msgOf)
      (challengeOfAt V id) (queryOfAt V id) mt ct)
    (hexp : (lfSetup body dflt rootOf msgOf).Explains dec id claimOf mt ct) :
    RbrSplit.LayerStepAccepts
      (RbrSplit.stepsOf (nl := nl) (w := w)
        (withMsgs FD MD (msgOf ((lfSetup body dflt rootOf msgOf).proof mt ct)))
        (fun m pref => accR h dom hkrow hr dec stmt respOf
          ((lfSetup body dflt rootOf msgOf).context mt ct) m pref
          (msgOf ((lfSetup body dflt rootOf msgOf).proof mt ct) m)))
      ((lfSetup body dflt rootOf msgOf).challenges mt ct) := by
  unfold JointAccepts statementOfAt at hacc
  rw [accepts_guarded, decide_eq_true_iff] at hacc
  obtain ⟨hfield, hv1⟩ := hacc
  obtain ⟨e, hext, hagree, -⟩ := hexp
  rw [stepsOf_withMsgs_eq hm, layerStepAccepts_iff]
  exact ⟨hfield, mem_acceptingR_of_accepts h dom hkrow hr dec _ _ _ _ _ _ _ _ e hext hagree hv1⟩

end V1

/-! ## 4. The certified V1 rows, single field -/

section Row

open Lfzk.CertifiedV1

variable {C Cand : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
variable {F Equations Witness : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
  [Fintype Equations] [DecidableEq Equations]
variable {logw logc nc nv : ℕ}
variable {Enc D Salt : Type} [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc]
  [Inhabited Salt]
variable {Msg Out : Type} [DecidableEq Msg] [Inhabited Msg] {tA N : ℕ}

/--
**A certified V1 row at the compiled Longfellow verifier, against a re-committing Fiat–Shamir
prover.**

```text
Pr[ AcceptsAt (v1K …) V codec (lfSetup body dflt rootOf msgOf) …  ∧  Fails(context) ]
    ≤  R.bound  +  N · R.fsCoefficient  +  R.tape · (L + N) / 2^digestBits
```

`CertifiedV1.Row.adaptive_ratio_le` with `hlig` discharged by `exists_msgLigeroData` at the extracted
instance and the proof's own response, and `hright` by `hright_v1`.

**Every premise**, and nothing else:

* the protocol instance — `hr`, `|F| = row.fieldSize` (`hF`), the domain `dom`, the verifier's field
  code `V`, the Ligero statement per root `stmt`, how a message carries the response `respOf`, the
  field half of LayerStep per context `Ffam` with exactly balanced decoders (`hexact`) and
  `RbrLongfellow`'s field premises inside it, the message data `MD`, `|Cand|`, `|D|`, the prover's
  Merkle budget `tA ≤ commitFuel` and the Merkle tape's room `2n + tA ≤ tape`;
* `hmatch` — LayerStep data's computational fields are `V`'s (`Matches`);
* `hfalse` — in a failing context the Ligero statement at the context's root is false (Ligero's
  extractor);
* `hfail` — in a failing context no candidate satisfies the circuit.
-/
theorem row_adaptive_ratio_le_v1 {R : Row} (h : R.Valid) (hr : 0 < R.params.row.openings)
    {codec : Codec Salt (Col F R.params.nw R.params.nq) D Enc} (dec : RoleDecoders codec)
    (V : Code C F (LigeroV1LayerStep.Chal F Equations R.params.nw R.params.nq)
      (LigeroV1LayerStep.Qry R.params.row) Msg logw logc)
    (dom : LigeroFamily.ReedSolomon.Domain F R.params.row.openings R.params.q R.params.row.n)
    (stmt : D → LigeroFamily.ConstraintSystem F R.params.nw R.params.nq R.params.q Equations)
    (respOf : Msg → LigeroFamily.Response F R.params.row.openings R.params.q R.params.row.n 1)
    (body : TwoOracleTree Enc D (Point D Msg C R.params.nl R.params.rounds) C Out tA N)
    (dflt : C) (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim R.params.row.n Salt (Col F R.params.nw R.params.nq) D)
    {Fails : D × List (Enc × D) → Prop}
    (hF : Fintype.card F = R.params.row.fieldSize)
    (hfalse : ∀ κ, Fails κ → ¬ (stmt κ.1).Language)
    (H : ∀ _κ : D × List (Enc × D), RbrLongfellow.Honest F Cand logw logc)
    (Sat : D × List (Enc × D) → Cand → Prop)
    (Ffam : ∀ κ, RbrSplit.FieldData C F (LigeroV1LayerStep.Chal F Equations R.params.nw R.params.nq)
        (LigeroV1LayerStep.Qry R.params.row) Cand Witness nc nv logw logc (H κ) (Sat κ))
    (hexact : ∀ κ, (Ffam κ).Exact)
    (MD : ∀ κ, MsgData C Msg (H κ))
    (hmatch : ∀ κ, Matches V (Ffam κ) (MD κ))
    (hfail : ∀ κ, Fails κ → ∀ cand : Cand, ¬ Sat κ cand)
    (htA : tA ≤ R.commitFuel) (htape : 2 * R.params.row.n + tA ≤ R.tape)
    (hcand : Fintype.card Cand = R.cardCand)
    (hD : Fintype.card D = 2 ^ R.params.digestBits) :
    ((univ.filter fun ω : (Fin R.tape → D) × (Fin (R.fsLen N) → C) =>
        AcceptsAt (v1K (Row.rowValid h) dom (Row.hkrow h) hr) V codec
            (lfSetup body dflt rootOf msgOf) (lfCheck codec claimOf) rootOf msgOf claimOf
            (rootStatement rootOf stmt) respOf id ω.1 ω.2 ∧
          Fails ((lfSetup body dflt rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ R.tape * (Fintype.card C : ℚ) ^ R.fsLen N)
      ≤ R.bound + N * R.fsCoefficient
        + ((R.tape * (Rounds.Role.length R.params.nl R.params.rounds + N) : ℕ) : ℚ)
          / 2 ^ R.params.digestBits := by
  refine le_trans (le_of_eq ?_)
    (Row.adaptive_ratio_le h dec (guarded (v1K (Row.rowValid h) dom (Row.hkrow h) hr)) body dflt
      rootOf msgOf claimOf (statementOfAt V msgOf (rootStatement rootOf stmt) id)
      (responseOfAt R.params.nl R.params.rounds respOf msgOf) (challengeOfAt V id) (queryOfAt V id)
      hF (accR (Row.rowValid h) dom (Row.hkrow h) hr dec stmt respOf)
      (fun κ hκ => exists_msgLigeroData C Msg (Row.rowValid h) (Row.coreRows h) hF dom (Row.hkrow h)
        (extractedInstance (Row.rowValid h) dom (Row.hkrow h) hr dec (stmt κ.1) κ.1 κ.2)
        (hfalse κ hκ) respOf)
      H Sat Ffam hexact MD hfail
      (fun mt ct _ hacc hexp => hright_v1 (Row.rowValid h) dom (Row.hkrow h) hr dec V body dflt
        rootOf msgOf claimOf stmt respOf (Ffam _) (MD _) (hmatch _) mt ct hacc hexp)
      htA htape hcand hD)
  congr 3
  refine Finset.filter_congr fun ω _ => ?_
  rw [acceptsAt_iff_joint]

/-- `CertifiedV1.v8Hash_adaptive_ratio_le`'s numerals: the row's bound, coefficient and
re-commitment term are within `2^-114 + N · 2^-115`. -/
theorem v8Hash_adaptive_rhs_le (N : ℕ) :
    v8Hash.bound + N * v8Hash.fsCoefficient
        + ((v8Hash.tape * (Rounds.Role.length v8Hash.params.nl v8Hash.params.rounds + N) : ℕ) : ℚ)
          / 2 ^ v8Hash.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 114 + N * ((1 : ℚ) / 2 ^ 115) := by
  have hsb := v8Hash_adaptive_slack_bound
  have hsc := v8Hash_adaptive_slack_coeff
  have hsplit : ((v8Hash.tape
        * (Rounds.Role.length v8Hash.params.nl v8Hash.params.rounds + N) : ℕ) : ℚ)
        / 2 ^ v8Hash.params.digestBits
      = ((v8Hash.tape * Rounds.Role.length v8Hash.params.nl v8Hash.params.rounds
          : ℕ) : ℚ) / 2 ^ v8Hash.params.digestBits
        + N * ((v8Hash.tape : ℚ) / 2 ^ v8Hash.params.digestBits) := by
    push_cast
    ring
  rw [hsplit]
  have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg N
  have := mul_le_mul_of_nonneg_left hsc hN
  nlinarith

/--
**The v8 hash row at the compiled Longfellow verifier, against a re-committing Fiat–Shamir
prover.**

`row_adaptive_ratio_le_v1` at `CertifiedV1.v8Hash` (the deployed hash profile, 20 layers and 610
sumcheck slots, over `GF(2^128)`, Ligero V1 at `n = 4088`, `k = 584` with 132 opened columns), with
the numerals of `CertifiedV1.v8Hash_adaptive_ratio_le`: against one adaptive program making at most
`tA ≤ 2^60` Merkle-oracle and `N` challenge-oracle queries, interleaved as it likes,

```text
Pr[ AcceptsAt (v1K …) …  ∧  Fails(context of the proof's root) ]  ≤  2^-114  +  N · 2^-115
```

over the Merkle tape (`2^62` slots) and a challenge tape of `633 + N` slots.  The premises are
`row_adaptive_ratio_le_v1`'s; `hr` is discharged.
-/
theorem v8Hash_adaptive_compiled_ratio_le
    {codec : Codec Salt (Col F v8Hash.params.nw v8Hash.params.nq) D Enc} (dec : RoleDecoders codec)
    (V : Code C F (LigeroV1LayerStep.Chal F Equations v8Hash.params.nw v8Hash.params.nq)
      (LigeroV1LayerStep.Qry v8Hash.params.row) Msg logw logc)
    (dom : LigeroFamily.ReedSolomon.Domain F v8Hash.params.row.openings v8Hash.params.q
      v8Hash.params.row.n)
    (stmt : D → LigeroFamily.ConstraintSystem F v8Hash.params.nw v8Hash.params.nq v8Hash.params.q
      Equations)
    (respOf : Msg → LigeroFamily.Response F v8Hash.params.row.openings v8Hash.params.q
      v8Hash.params.row.n 1)
    (body : TwoOracleTree Enc D (Point D Msg C v8Hash.params.nl v8Hash.params.rounds) C Out tA N)
    (dflt : C) (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim v8Hash.params.row.n Salt (Col F v8Hash.params.nw v8Hash.params.nq) D)
    {Fails : D × List (Enc × D) → Prop}
    (hF : Fintype.card F = v8Hash.params.row.fieldSize)
    (hfalse : ∀ κ, Fails κ → ¬ (stmt κ.1).Language)
    (H : ∀ _κ : D × List (Enc × D), RbrLongfellow.Honest F Cand logw logc)
    (Sat : D × List (Enc × D) → Cand → Prop)
    (Ffam : ∀ κ, RbrSplit.FieldData C F
        (LigeroV1LayerStep.Chal F Equations v8Hash.params.nw v8Hash.params.nq)
        (LigeroV1LayerStep.Qry v8Hash.params.row) Cand Witness nc nv logw logc (H κ) (Sat κ))
    (hexact : ∀ κ, (Ffam κ).Exact)
    (MD : ∀ κ, MsgData C Msg (H κ))
    (hmatch : ∀ κ, Matches V (Ffam κ) (MD κ))
    (hfail : ∀ κ, Fails κ → ∀ cand : Cand, ¬ Sat κ cand)
    (htA : tA ≤ v8Hash.commitFuel) (htape : 2 * v8Hash.params.row.n + tA ≤ v8Hash.tape)
    (hcand : Fintype.card Cand = v8Hash.cardCand)
    (hD : Fintype.card D = 2 ^ v8Hash.params.digestBits) :
    ((univ.filter fun ω : (Fin v8Hash.tape → D) × (Fin (v8Hash.fsLen N) → C) =>
        AcceptsAt (v1K (Row.rowValid v8Hash_valid) dom (Row.hkrow v8Hash_valid) v8Hash_openings_pos)
            V codec (lfSetup body dflt rootOf msgOf) (lfCheck codec claimOf) rootOf msgOf claimOf
            (rootStatement rootOf stmt) respOf id ω.1 ω.2 ∧
          Fails ((lfSetup body dflt rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v8Hash.tape * (Fintype.card C : ℚ) ^ v8Hash.fsLen N)
      ≤ (1 : ℚ) / 2 ^ 114 + N * ((1 : ℚ) / 2 ^ 115) :=
  le_trans
    (row_adaptive_ratio_le_v1 v8Hash_valid v8Hash_openings_pos dec V dom stmt respOf body dflt
      rootOf msgOf claimOf hF hfalse H Sat Ffam hexact MD hmatch hfail htA htape hcand hD)
    (v8Hash_adaptive_rhs_le N)

end Row

/-! ## 5. Two fields: one re-committing prover, one hashed MAC key -/

section TwoField

open Lfzk.CertifiedV1 Lfzk.NizkAdaptiveTwoField Lfzk.TwoFieldV1Rows Lfzk.Mac

variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {D : Type} [Fintype D] [DecidableEq D] [Inhabited D]
variable {Enc X Out : Type} [DecidableEq Enc]

/-- A side's context: the pair of roots and the cut trace, the raw MAC-key answer, and the public
data sent with the key. -/
abbrev Sig (D C X Enc : Type) := ((D × D) × List (Enc × D)) × C × X

/-- The side context a joint execution determines: the commitment context, the raw key answer (slot
`0` of the merged tape) and the public data. -/
def sideCtx {Pt : Type} [DecidableEq Pt] {tA N Lsch TM TC : ℕ}
    (S : Setup Enc D Pt C Out (D × D) tA N Lsch) (pubOf : Out → X) (hL : 0 < Lsch)
    (mt : Fin TM → D) (ct : Fin TC → C) : Sig D C X Enc :=
  (S.context mt ct, S.challenges mt ct ⟨0, hL⟩, pubOf (S.proof mt ct))

/--
**One side at the compiled Longfellow verifier**, against a re-committing prover: the verifier's data
(`dom`, `V`, `stmt`, `respOf`) and LayerStep's analysis data per side context
(`CertifiedV1.Row.adaptive_ratio_le`'s premises other than `hlig` and `hright`, which are theorems
here).  `rootOfKey` picks the side's root from the pair.
-/
structure CompiledSide (R : Row) (hR : R.Valid) (hr : 0 < R.params.row.openings)
    (C : Type) [Fintype C] (Cand F Equations Witness Msg : Type) [Fintype Cand] [Field F]
    [Fintype F] [DecidableEq F] [SumcheckInterp F] [Fintype Equations] [DecidableEq Equations]
    (nc nv logw logc : ℕ) {Enc D Salt : Type} [Inhabited D] [DecidableEq D] [DecidableEq Enc]
    [Inhabited Salt] (X : Type)
    {codec : Codec Salt (Col F R.params.nw R.params.nq) D Enc} (dec : RoleDecoders codec)
    (rootOfKey : D × D → D) where
  /-- The code's evaluation domain. -/
  dom : LigeroFamily.ReedSolomon.Domain F R.params.row.openings R.params.q R.params.row.n
  /-- The verifier's field code. -/
  V : Code C F (LigeroV1LayerStep.Chal F Equations R.params.nw R.params.nq)
    (LigeroV1LayerStep.Qry R.params.row) Msg logw logc
  /-- The side's Ligero statement: a function of its root, the raw MAC-key answer and the public
  data (the tag and blinds) sent with the key. -/
  stmt : D → C → X → LigeroFamily.ConstraintSystem F R.params.nw R.params.nq R.params.q Equations
  /-- How a message carries the side's Ligero response. -/
  respOf : Msg → LigeroFamily.Response F R.params.row.openings R.params.q R.params.row.n 1
  /-- LayerStep's honest values, per side context. -/
  H : Sig D C X Enc → RbrLongfellow.Honest F Cand logw logc
  /-- Which candidates satisfy the side's circuit, per side context. -/
  Sat : Sig D C X Enc → Cand → Prop
  /-- The field half of LayerStep, per side context. -/
  field : ∀ σ, RbrSplit.FieldData C F (LigeroV1LayerStep.Chal F Equations R.params.nw R.params.nq)
    (LigeroV1LayerStep.Qry R.params.row) Cand Witness nc nv logw logc (H σ) (Sat σ)
  /-- Its decoders are exactly balanced. -/
  hexact : ∀ σ, (field σ).Exact
  /-- How a round's message fixes LayerStep's prover data at that round. -/
  MD : ∀ σ, MsgData C Msg (H σ)
  /-- **LayerStep data describes the verifier** (`CompiledLongfellow.Matches`). -/
  hmatch : ∀ σ, Matches V (field σ) (MD σ)
  /-- **Ligero's extractor**: no satisfying candidate means a false Ligero statement. -/
  hfalse : ∀ σ : Sig D C X Enc, (∀ cand : Cand, ¬ Sat σ cand) →
    ¬ (stmt (rootOfKey σ.1.1) σ.2.1 σ.2.2).Language
  hF : Fintype.card F = R.params.row.fieldSize

namespace CompiledSide

variable {R : Row} {hR : R.Valid} {hr : 0 < R.params.row.openings}
variable {Cand F Equations Witness Msg : Type} [Fintype Cand] [Field F] [Fintype F] [DecidableEq F]
  [SumcheckInterp F] [Fintype Equations] [DecidableEq Equations] {nc nv logw logc : ℕ}
variable {Salt : Type} [Inhabited Salt]
variable {codec : Codec Salt (Col F R.params.nw R.params.nq) D Enc} {dec : RoleDecoders codec}
  {rootOfKey : D × D → D}
variable (L : CompiledSide R hR hr C Cand F Equations Witness Msg nc nv logw logc X dec rootOfKey)

/-- The side's extracted V1 instance at a side context. -/
noncomputable def inst (σ : Sig D C X Enc) :
    OracleInstance R.params.row F Equations R.params.nw R.params.nq R.params.q :=
  extractedInstance (Row.rowValid hR) L.dom (Row.hkrow hR) hr dec
    (L.stmt (rootOfKey σ.1.1) σ.2.1 σ.2.2) (rootOfKey σ.1.1) σ.1.2

/-- A good witness of the side: the witness of a satisfying candidate. -/
def Good (σ : Sig D C X Enc) (a : Witness) : Prop :=
  ∃ cand : Cand, L.Sat σ cand ∧ (L.field σ).wOf cand = a

/-- **The `Side` the compiled side is**: the response-reading test of the extracted instance, with
`hlig` from `exists_msgLigeroData`. -/
noncomputable def toSide [DecidableEq Msg] [Inhabited Msg] :
    Side R (Sig D C X Enc) C Cand F Equations Witness Msg nc nv logw logc where
  accR σ _ _ msg x := acceptingR (Row.rowValid hR) L.dom (Row.hkrow hR) (L.inst σ)
    (L.respOf msg) x
  H := L.H
  Sat := L.Sat
  field := L.field
  hexact := L.hexact
  MD := L.MD
  hlig σ hσ := exists_msgLigeroData C Msg (Row.rowValid hR) (Row.coreRows hR) L.hF L.dom
    (Row.hkrow hR) (L.inst σ) (L.hfalse σ hσ) L.respOf

omit [DecidableEq C] [Nonempty C] [Fintype D] in
theorem toSide_good [DecidableEq Msg] [Inhabited Msg] (σ : Sig D C X Enc) (a : Witness) :
    L.toSide.Good σ a ↔ L.Good σ a := Iff.rfl

variable {Pt : Type} [DecidableEq Pt] {tA N Lsch fc TM TC : ℕ}

/-- The side's statement map on a joint execution: at the side's root, the raw key answer (slot
`0` of the merged tape) and the public data. -/
def stmtOf (rootOf : Out → D) (pubOf : Out → X) (hL : 0 < Lsch) (out : Out)
    (chals : Fin Lsch → C) :
    LigeroFamily.ConstraintSystem F R.params.nw R.params.nq R.params.q Equations :=
  L.stmt (rootOf out) (chals ⟨0, hL⟩) (pubOf out)

/-- **The side's compiled verifier on the joint execution**, at its slice `sl` of the merged tape. -/
def accepts (S : Setup Enc D Pt C Out (D × D) tA N Lsch) (check : Out → Tree Enc D Unit fc)
    (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim R.params.row.n Salt (Col F R.params.nw R.params.nq) D)
    (pubOf : Out → X) (hL : 0 < Lsch)
    (sl : (Fin Lsch → C) → Fin (Rounds.Role.length R.params.nl R.params.rounds) → C)
    (mt : Fin TM → D) (ct : Fin TC → C) : Prop :=
  AcceptsAt (v1K (Row.rowValid hR) L.dom (Row.hkrow hR) hr) L.V codec S check rootOf msgOf claimOf
    (L.stmtOf rootOf pubOf hL) L.respOf sl mt ct

omit [DecidableEq C] [Nonempty C] [Fintype D] in
/-- The side's compiled verifier is `guarded (v1K …)`'s joint acceptance at the side's maps. -/
theorem accepts_iff_joint [DecidableEq Msg] [Inhabited Msg]
    (S : Setup Enc D Pt C Out (D × D) tA N Lsch) (check : Out → Tree Enc D Unit fc)
    (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim R.params.row.n Salt (Col F R.params.nw R.params.nq) D)
    (pubOf : Out → X) (hL : 0 < Lsch)
    (sl : (Fin Lsch → C) → Fin (Rounds.Role.length R.params.nl R.params.rounds) → C)
    (mt : Fin TM → D) (ct : Fin TC → C) :
    L.accepts S check rootOf msgOf claimOf pubOf hL sl mt ct ↔
      JointAccepts (guarded (v1K (Row.rowValid hR) L.dom (Row.hkrow hR) hr)) codec S check
        rootOf claimOf (statementOfAt L.V msgOf (L.stmtOf rootOf pubOf hL) sl)
        (responseOfAt R.params.nl R.params.rounds L.respOf msgOf) (challengeOfAt L.V sl)
        (queryOfAt L.V sl) mt ct :=
  acceptsAt_iff_joint _ _ _ _ _ _ _ _ _ _ _ _ _

omit [DecidableEq C] [Nonempty C] [Fintype D] in
/--
**`hright`, proved for one side**: from the guarded joint acceptance at the side's maps and the
cut-trace extraction at the side's root, the side's LayerStep accepts at its slice of the recomputed
answers, with the response-reading test of the extracted instance.
-/
theorem hright [DecidableEq Msg] [Inhabited Msg]
    (S : Setup Enc D Pt C Out (D × D) tA N Lsch) (check : Out → Tree Enc D Unit fc)
    (rootOf : Out → D) (hroot : ∀ out, rootOfKey (S.keyOut out) = rootOf out)
    (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim R.params.row.n Salt (Col F R.params.nw R.params.nq) D)
    (pubOf : Out → X) (hL : 0 < Lsch)
    (sl : (Fin Lsch → C) → Fin (Rounds.Role.length R.params.nl R.params.rounds) → C)
    (mt : Fin TM → D) (ct : Fin TC → C)
    (hacc : JointAccepts (guarded (v1K (Row.rowValid hR) L.dom (Row.hkrow hR) hr)) codec S check
      rootOf claimOf (statementOfAt L.V msgOf (L.stmtOf rootOf pubOf hL) sl)
      (responseOfAt R.params.nl R.params.rounds L.respOf msgOf) (challengeOfAt L.V sl)
      (queryOfAt L.V sl) mt ct)
    (hexp : S.Explains dec rootOfKey claimOf mt ct) :
    RbrSplit.LayerStepAccepts
      (RbrSplit.stepsOf (nl := R.params.nl) (w := R.params.rounds)
        (withMsgs (L.field (sideCtx S pubOf hL mt ct)) (L.MD (sideCtx S pubOf hL mt ct))
          (msgOf (S.proof mt ct)))
        (fun m pref => L.toSide.accR (sideCtx S pubOf hL mt ct) m pref (msgOf (S.proof mt ct) m)))
      (sl (S.challenges mt ct)) := by
  unfold JointAccepts statementOfAt at hacc
  rw [accepts_guarded, decide_eq_true_iff] at hacc
  obtain ⟨hfield, hv1⟩ := hacc
  obtain ⟨e, hext, hagree, -⟩ := hexp
  rw [stepsOf_withMsgs_eq (L.hmatch _), layerStepAccepts_iff]
  refine ⟨hfield, ?_⟩
  unfold stmtOf at hv1
  rw [← hroot (S.proof mt ct)] at hv1
  exact mem_acceptingR_of_accepts (Row.rowValid hR) L.dom (Row.hkrow hR) hr dec _ _ _ _ _ _ _ _
    e hext hagree hv1

end CompiledSide

/-- Side 1's slice of the merged tape: slots `1, …, L₁`. -/
def slice1 (R₁ R₂ : Row) (chals : Fin (len2 R₁ R₂) → C) :
    Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) → C :=
  fun i => chals ⟨1 + i.val, by unfold len2; omega⟩

/-- Side 2's slice of the merged tape: slots `1 + L₁, …, L₁ + L₂`. -/
def slice2 (R₁ R₂ : Row) (chals : Fin (len2 R₁ R₂) → C) :
    Fin (Rounds.Role.length R₂.params.nl R₂.params.rounds) → C :=
  fun i => chals ⟨1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + i.val, by unfold len2; omega⟩

/-- The merged schedule has the key slot. -/
theorem len2_pos (R₁ R₂ : Row) : 0 < len2 R₁ R₂ := by unfold len2; omega

variable {Fmac : Type} [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {nblk : ℕ}
variable {Cand₁ F₁ Equations₁ Witness₁ Msg₁ : Type} [Fintype Cand₁] [Nonempty Cand₁] [Field F₁]
  [Fintype F₁] [DecidableEq F₁] [SumcheckInterp F₁] [Fintype Equations₁] [DecidableEq Equations₁]
  [DecidableEq Msg₁] [Inhabited Msg₁] {nc₁ nv₁ logw₁ logc₁ : ℕ}
variable {Cand₂ F₂ Equations₂ Witness₂ Msg₂ : Type} [Fintype Cand₂] [Nonempty Cand₂] [Field F₂]
  [Fintype F₂] [DecidableEq F₂] [SumcheckInterp F₂] [Fintype Equations₂] [DecidableEq Equations₂]
  [DecidableEq Msg₂] [Inhabited Msg₂] {nc₂ nv₂ logw₂ logc₂ : ℕ}
variable {Salt₁ Salt₂ : Type} [Inhabited Salt₁] [Inhabited Salt₂]

/--
**Two-field Longfellow at the compiled verifiers, against one re-committing Fiat–Shamir prover
with a hashed MAC key.**

`NizkAdaptiveTwoField.twofield_adaptive_ratio_le` at two compiled sides, `hlig` and `hright`
discharged.  Each side's acceptance is `CompiledSide.accepts`: its field rounds pass on its messages
at its slice of the recomputed answers, and its Merkle-compiled V1 check accepts the proof's
response on the statement at its root, the hashed MAC-key answer and the public data.

**Every premise:** per side a `CompiledSide` (the verifier's data, LayerStep's field data with
`hexact` and `RbrLongfellow`'s field premises inside it, `MD`, `hmatch`, Ligero's extractor
`hfalse`, `|F|`), `|Cand|`, `|D|`, the MAC data `aP`, `decode`, `hbal`, `hmac`, the MAC rows
`hrow₁`, `hrow₂` (the arithmetization assumption `assert_mac`: a good witness of an accepting side
satisfies the MAC at the hashed key and the proof's tag), and the instance's numbers.
-/
theorem twofield_adaptive_compiled_ratio_le {R₁ R₂ : Row} (h₁ : R₁.Valid) (h₂ : R₂.Valid)
    (hr₁ : 0 < R₁.params.row.openings) (hr₂ : 0 < R₂.params.row.openings) {tA N : ℕ}
    {codec₁ : Codec Salt₁ (Col F₁ R₁.params.nw R₁.params.nq) D Enc} {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ R₂.params.nw R₂.params.nq) D Enc} {dec₂ : RoleDecoders codec₂}
    (L₁ : CompiledSide R₁ h₁ hr₁ C Cand₁ F₁ Equations₁ Witness₁ Msg₁ nc₁ nv₁ logw₁ logc₁ X dec₁
      Prod.fst)
    (L₂ : CompiledSide R₂ h₂ hr₂ C Cand₂ F₂ Equations₂ Witness₂ Msg₂ nc₂ nv₂ logw₂ logc₂ X dec₂
      Prod.snd)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds
      R₂.params.rounds) C Out tA N)
    (dflt : C) (rootOf₁ rootOf₂ : Out → D) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim R₁.params.row.n Salt₁ (Col F₁ R₁.params.nw R₁.params.nq) D)
    (claimOf₂ : Out → OpeningClaim R₂.params.row.n Salt₂ (Col F₂ R₂.params.nw R₂.params.nq) D)
    (hcand₁ : Fintype.card Cand₁ = R₁.cardCand) (hcand₂ : Fintype.card Cand₂ = R₂.cardCand)
    (hD₁ : Fintype.card D = 2 ^ R₁.params.digestBits)
    (hD₂ : Fintype.card D = 2 ^ R₂.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : Witness₁ → Fin nblk → Fmac) (common₂ : Witness₂ → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin R₁.tape → D) (ct : Fin (len2 R₁ R₂ + N) → C) (a : Witness₁),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      L₁.accepts S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ pubOf
        (len2_pos R₁ R₂) (slice1 R₁ R₂) mt ct →
      L₁.Good (sideCtx S pubOf (len2_pos R₁ R₂) mt ct) a →
      macTag (aP (S.context mt ct) + decode (S.challenges mt ct ⟨0, len2_pos R₁ R₂⟩))
        (keyB (S.proof mt ct)) (common₁ a) = tagOf (S.proof mt ct))
    (hrow₂ : ∀ (mt : Fin R₁.tape → D) (ct : Fin (len2 R₁ R₂ + N) → C) (a : Witness₂),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      L₂.accepts S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ pubOf
        (len2_pos R₁ R₂) (slice2 R₁ R₂) mt ct →
      L₂.Good (sideCtx S pubOf (len2_pos R₁ R₂) mt ct) a →
      macTag (aP (S.context mt ct) + decode (S.challenges mt ct ⟨0, len2_pos R₁ R₂⟩))
        (keyB (S.proof mt ct)) (common₂ a) = tagOf (S.proof mt ct))
    (htA₁ : tA ≤ R₁.commitFuel) (htA₂ : tA ≤ R₂.commitFuel)
    (htape : 2 * R₂.params.row.n + 2 * R₁.params.row.n + tA ≤ R₁.tape)
    (htape₂ : R₁.tape = R₂.tape) :
    ((univ.filter fun ω : (Fin R₁.tape → D) × (Fin (len2 R₁ R₂ + N) → C) =>
        L₁.accepts (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ pubOf
            (len2_pos R₁ R₂) (slice1 R₁ R₂) ω.1 ω.2 ∧
          L₂.accepts (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ pubOf
            (len2_pos R₁ R₂) (slice2 R₁ R₂) ω.1 ω.2 ∧
          ¬ ∃ a₁ a₂,
            L₁.Good (sideCtx (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂) pubOf
              (len2_pos R₁ R₂) ω.1 ω.2) a₁ ∧
            L₂.Good (sideCtx (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂) pubOf
              (len2_pos R₁ R₂) ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ R₁.tape * (Fintype.card C : ℚ) ^ (len2 R₁ R₂ + N))
      ≤ R₁.bound + R₂.bound + 1 / (Fintype.card Fmac : ℚ)
        + N * max (max R₁.fsCoefficient R₂.fsCoefficient) (1 / (Fintype.card Fmac : ℚ))
        + 2 * (((R₁.tape * (len2 R₁ R₂ + N) : ℕ) : ℚ) / 2 ^ R₁.params.digestBits) := by
  have hroot₁ : ∀ out, Prod.fst ((setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).keyOut out)
      = rootOf₁ out := fun _ => rfl
  have hroot₂ : ∀ out, Prod.snd ((setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).keyOut out)
      = rootOf₂ out := fun _ => rfl
  refine le_trans (le_of_eq ?_)
    (twofield_adaptive_ratio_le h₁ dec₁ dec₂
      (guarded (v1K (Row.rowValid h₁) L₁.dom (Row.hkrow h₁) hr₁))
      (guarded (v1K (Row.rowValid h₂) L₂.dom (Row.hkrow h₂) hr₂))
      body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂
      (statementOfAt L₁.V msgOf₁ (L₁.stmtOf rootOf₁ pubOf (len2_pos R₁ R₂)) (slice1 R₁ R₂))
      (responseOfAt R₁.params.nl R₁.params.rounds L₁.respOf msgOf₁)
      (challengeOfAt L₁.V (slice1 R₁ R₂)) (queryOfAt L₁.V (slice1 R₁ R₂))
      (statementOfAt L₂.V msgOf₂ (L₂.stmtOf rootOf₂ pubOf (len2_pos R₁ R₂)) (slice2 R₁ R₂))
      (responseOfAt R₂.params.nl R₂.params.rounds L₂.respOf msgOf₂)
      (challengeOfAt L₂.V (slice2 R₁ R₂)) (queryOfAt L₂.V (slice2 R₁ R₂))
      L₁.toSide L₂.toSide L₁.hF L₂.hF hcand₁ hcand₂ hD₁ hD₂ aP decode kmac hbal hmac keyB tagOf
      common₁ common₂
      (fun mt ct _ hacc hexp => L₁.hright _ _ rootOf₁ hroot₁ msgOf₁ claimOf₁ pubOf (len2_pos R₁ R₂)
        (slice1 R₁ R₂) mt ct hacc hexp)
      (fun mt ct _ hacc hexp => L₂.hright _ _ rootOf₂ hroot₂ msgOf₂ claimOf₂ pubOf (len2_pos R₁ R₂)
        (slice2 R₁ R₂) mt ct hacc hexp)
      (fun mt ct a hacc hgood => hrow₁ mt ct a
        ((L₁.accepts_iff_joint _ _ rootOf₁ msgOf₁ claimOf₁ pubOf (len2_pos R₁ R₂) (slice1 R₁ R₂)
          mt ct).mpr hacc) hgood)
      (fun mt ct a hacc hgood => hrow₂ mt ct a
        ((L₂.accepts_iff_joint _ _ rootOf₂ msgOf₂ claimOf₂ pubOf (len2_pos R₁ R₂) (slice2 R₁ R₂)
          mt ct).mpr hacc) hgood)
      htA₁ htA₂ htape htape₂)
  congr 3
  refine Finset.filter_congr fun ω _ => ?_
  rw [L₁.accepts_iff_joint, L₂.accepts_iff_joint]
  exact Iff.rfl

/-- The `P-256` side opens `132` columns. -/
theorem p256sha_ecdsa_openings_pos : 0 < p256sha.ecdsa.params.row.openings := by decide

/-- The `GF(2^128)` side opens `132` columns. -/
theorem p256sha_sha_openings_pos : 0 < p256sha.sha.params.row.openings := by decide

omit [Field Fmac] [DecidableEq Fmac] in
/-- `NizkAdaptiveTwoField.p256sha_adaptive_ratio_le`'s numerals: the two rows' bounds, the MAC
term, the worst coefficient and the two re-commitment terms are within `2^-114 + N · 2^-115`. -/
theorem p256sha_adaptive_rhs_le (N : ℕ) (hFmac : Fintype.card Fmac = 2 ^ 128) :
    p256sha.ecdsa.bound + p256sha.sha.bound + 1 / (Fintype.card Fmac : ℚ)
        + N * max (max p256sha.ecdsa.fsCoefficient p256sha.sha.fsCoefficient)
            (1 / (Fintype.card Fmac : ℚ))
        + 2 * (((p256sha.ecdsa.tape * (len2 p256sha.ecdsa p256sha.sha + N) : ℕ) : ℚ)
          / 2 ^ p256sha.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 114 + N * ((1 : ℚ) / 2 ^ 115) := by
  have hsb := p256sha_adaptive_slack_bound
  have hsc := p256sha_adaptive_slack_coeff
  have hmf : (Fintype.card Fmac : ℚ) = (p256sha.macFieldSize : ℚ) := by
    rw [hFmac]; rfl
  rw [hmf]
  have hsplit : 2 * (((p256sha.ecdsa.tape * (len2 p256sha.ecdsa p256sha.sha + N) : ℕ) : ℚ)
        / 2 ^ p256sha.ecdsa.params.digestBits)
      = 2 * (((p256sha.ecdsa.tape * len2 p256sha.ecdsa p256sha.sha : ℕ) : ℚ)
          / 2 ^ p256sha.ecdsa.params.digestBits)
        + N * (2 * ((p256sha.ecdsa.tape : ℚ) / 2 ^ p256sha.ecdsa.params.digestBits)) := by
    push_cast
    ring
  rw [hsplit]
  have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg N
  have := mul_le_mul_of_nonneg_left hsc hN
  nlinarith

/--
**Two-field Longfellow at `p256sha`, at the compiled verifiers, against one re-committing
Fiat–Shamir prover with a hashed MAC key.**

`twofield_adaptive_compiled_ratio_le` at `TwoFieldV1Rows.p256sha` — ECDSA over `P-256`'s base
field and SHA-256 over `GF(2^128)`, each at its deployed v8 circuit profile proved with Ligero V1 at
132 openings, composed through the MAC over a field of `2^128` elements — with the numerals of
`NizkAdaptiveTwoField.p256sha_adaptive_ratio_le`: against one adaptive program making at most
`tA ≤ 2^60` Merkle-oracle and `N` challenge-oracle queries, over all roles, interleaved as it likes,

```text
Pr [ both compiled verifiers accept  ∧  no two good witnesses agree on the common value ]
    ≤  2^-114  +  N · 2^-115
```

over one Merkle tape of `2^62` slots and one challenge tape of `1178 + N` slots.  The premises are
`twofield_adaptive_compiled_ratio_le`'s; `hr₁`, `hr₂` are discharged.
-/
theorem p256sha_adaptive_compiled_ratio_le {tA N : ℕ} (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ p256sha.ecdsa.params.nw p256sha.ecdsa.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ p256sha.sha.params.nw p256sha.sha.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (L₁ : CompiledSide p256sha.ecdsa (TwoFieldRowV1.ecdsa_valid p256sha_valid)
      p256sha_ecdsa_openings_pos C Cand₁ F₁ Equations₁ Witness₁ Msg₁ nc₁ nv₁ logw₁ logc₁ X dec₁
      Prod.fst)
    (L₂ : CompiledSide p256sha.sha (TwoFieldRowV1.sha_valid p256sha_valid)
      p256sha_sha_openings_pos C Cand₂ F₂ Equations₂ Witness₂ Msg₂ nc₂ nv₂ logw₂ logc₂ X dec₂
      Prod.snd)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ p256sha.ecdsa.params.nl
      p256sha.sha.params.nl p256sha.ecdsa.params.rounds p256sha.sha.params.rounds) C Out tA N)
    (dflt : C) (rootOf₁ rootOf₂ : Out → D) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim p256sha.ecdsa.params.row.n Salt₁
      (Col F₁ p256sha.ecdsa.params.nw p256sha.ecdsa.params.nq) D)
    (claimOf₂ : Out → OpeningClaim p256sha.sha.params.row.n Salt₂
      (Col F₂ p256sha.sha.params.nw p256sha.sha.params.nq) D)
    (hcand₁ : Fintype.card Cand₁ = p256sha.ecdsa.cardCand)
    (hcand₂ : Fintype.card Cand₂ = p256sha.sha.cardCand)
    (hD : Fintype.card D = 2 ^ p256sha.ecdsa.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : Witness₁ → Fin nblk → Fmac) (common₂ : Witness₂ → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin p256sha.ecdsa.tape → D)
      (ct : Fin (len2 p256sha.ecdsa p256sha.sha + N) → C) (a : Witness₁),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      L₁.accepts S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ pubOf
        (len2_pos _ _) (slice1 p256sha.ecdsa p256sha.sha) mt ct →
      L₁.Good (sideCtx S pubOf (len2_pos _ _) mt ct) a →
      macTag (aP (S.context mt ct) + decode (S.challenges mt ct ⟨0, len2_pos _ _⟩))
        (keyB (S.proof mt ct)) (common₁ a) = tagOf (S.proof mt ct))
    (hrow₂ : ∀ (mt : Fin p256sha.ecdsa.tape → D)
      (ct : Fin (len2 p256sha.ecdsa p256sha.sha + N) → C) (a : Witness₂),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      L₂.accepts S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ pubOf
        (len2_pos _ _) (slice2 p256sha.ecdsa p256sha.sha) mt ct →
      L₂.Good (sideCtx S pubOf (len2_pos _ _) mt ct) a →
      macTag (aP (S.context mt ct) + decode (S.challenges mt ct ⟨0, len2_pos _ _⟩))
        (keyB (S.proof mt ct)) (common₂ a) = tagOf (S.proof mt ct))
    (htA : tA ≤ 2 ^ 60)
    (htape : 2 * p256sha.sha.params.row.n + 2 * p256sha.ecdsa.params.row.n + tA ≤ 2 ^ 62) :
    ((univ.filter fun ω : (Fin p256sha.ecdsa.tape → D) ×
          (Fin (len2 p256sha.ecdsa p256sha.sha + N) → C) =>
        L₁.accepts (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ pubOf (len2_pos _ _)
            (slice1 p256sha.ecdsa p256sha.sha) ω.1 ω.2 ∧
          L₂.accepts (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ pubOf (len2_pos _ _)
            (slice2 p256sha.ecdsa p256sha.sha) ω.1 ω.2 ∧
          ¬ ∃ a₁ a₂,
            L₁.Good (sideCtx (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂) pubOf
              (len2_pos _ _) ω.1 ω.2) a₁ ∧
            L₂.Good (sideCtx (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂) pubOf
              (len2_pos _ _) ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ p256sha.ecdsa.tape *
            (Fintype.card C : ℚ) ^ (len2 p256sha.ecdsa p256sha.sha + N))
      ≤ (1 : ℚ) / 2 ^ 114 + N * ((1 : ℚ) / 2 ^ 115) :=
  le_trans
    (twofield_adaptive_compiled_ratio_le (TwoFieldRowV1.ecdsa_valid p256sha_valid)
      (TwoFieldRowV1.sha_valid p256sha_valid) p256sha_ecdsa_openings_pos p256sha_sha_openings_pos
      L₁ L₂ body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂ hcand₁ hcand₂ hD hD
      aP decode kmac hbal hmac keyB tagOf common₁ common₂ hrow₁ hrow₂ htA htA htape rfl)
    (p256sha_adaptive_rhs_le N hFmac)

end TwoField

end Lfzk.CompiledLongfellowAdaptive
