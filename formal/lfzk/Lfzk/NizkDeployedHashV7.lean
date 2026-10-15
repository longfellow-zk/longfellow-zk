import Lfzk.NizkDeployedHashTwoField
import Lfzk.CertifiedV7
import Lfzk.TwoFieldV7Rows

/-!
# The deployed-hash headlines at the deployed v7 parameters

The headlines of `Lfzk.NizkDeployedHash`, `Lfzk.NizkDeployedHashAdaptive` and
`Lfzk.NizkDeployedHashTwoField` — Fiat–Shamir with hash inputs as deployed (message prefixes,
challenges not re-absorbed), `N` counting deployed hash queries — restated at the registered v7 rows
(`Lfzk.CertifiedV7`, `Lfzk.TwoFieldV7Rows`).  Each is the abstract-row theorem
(`row_fs_ratio_le_bound`, `row_adaptive_ratio_le`, `row_adaptive_ratio_le_v1`,
`twofield_adaptive_compiled_ratio_le`) at the row, followed by the row's certified right-hand-side
numeral (`_fs_rhs_le`, `_adaptive_rhs_le`); the statements are the v8 ones with the row and the
numerals replaced, so the premises are exactly the v8 headlines' (listed in those files'
docstrings).

| row | grinding (one commitment) | re-committing, abstract / compiled verifier |
|---|---|---|
| `v7Sig` | `2^-122 + N · 2^-122` | `2^-122 + N · 2^-122` |
| `v7Hash1` … `v7Hash4` | `2^-115 + N · 2^-116` | `2^-115 + N · 2^-116` |
| `v7P256Sha1` … `v7P256Sha4` (two-field, hash side first) | — | `2^-115 + N · 2^-116` |

The two-field rows are instantiated in the deployed transcript's order (the `GF(2^128)` hash side is
proved first, then the `P-256` signature side on the same transcript), with the ECDSA-first certified
numerals moved over by `NizkDeployedHashTwoField.twofield_rhs_swap`.

Restated from the v8 statements with the row and the numerals replaced; nothing here is a
hypothesis beyond those statements' premises.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.NizkDeployedHashV7

open Finset Bcs Bcs.TotalOracleCommit Merkle Merkle.MH Merkle.RandomOracle
  Merkle.RandomOracle.TwoOracleTree RbrLongfellow Lfzk.NizkGrinding Lfzk.NizkDeployedHash
  Lfzk.NizkDeployedHashAdaptive Lfzk.NizkDeployedHashTwoField Lfzk.CertifiedV1 Lfzk.Mac
open Lfzk.NizkAdaptiveTwoField (SideCtx Side check2 len2)
open scoped Classical

/-! ## 1. One commitment, prefix-only grinding -/

section Fs
/-- **v7Sig against a prefix-only grinding Fiat–Shamir adversary**: `row_fs_ratio_le_bound` at
`CertifiedV1.v7Sig` — the v7 signature component (21 layers, 542 sumcheck slots, over P-256's base field; Ligero V1 at `n = 3187`, `k = 455`, 132 openings) — with `CertifiedV1.v7Sig_fs_rhs_le`:
`Pr[accept ∧ Fails] ≤ 2^-122 + N · 2^-122`, `N` the number of deployed hash queries. -/
theorem v7Sig_fs_ratio_le
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
      n v7Sig.commitFuel respondFuel revealFuel)
    (adv : Aux → Tree (MPoint Ctx Msg v7Sig.params.nl v7Sig.params.rounds) C Out N)
    (ctxOf : Aux → Ctx) (msgOf : Out → ℕ → Msg)
    (challengeOf : Aux → (MPoint Ctx Msg v7Sig.params.nl v7Sig.params.rounds → C) → Challenge)
    (queryOf : Aux → (MPoint Ctx Msg v7Sig.params.nl v7Sig.params.rounds → C) → Query)
    (statement : (Fin v7Sig.tape → D) × (MPoint Ctx Msg v7Sig.params.nl v7Sig.params.rounds → C)
      → Statement)
    {Fails : (Fin v7Sig.tape → D) → Prop}
    (hF : Fintype.card F = v7Sig.params.row.fieldSize)
    (dom : LigeroFamily.ReedSolomon.Domain F v7Sig.params.row.openings v7Sig.params.q
      v7Sig.params.row.n)
    (lig : ∀ _pre : Fin v7Sig.tape → D,
      LigeroV1LayerStep.Instance v7Sig.params.row F Equations v7Sig.params.nw
        v7Sig.params.nq v7Sig.params.q)
    (hfalse : ∀ pre : Fin v7Sig.tape → D, Fails pre → ¬ (lig pre).statement.Language)
    (H : ∀ _pre : Fin v7Sig.tape → D, RbrLongfellow.Honest F Cand logw logc)
    (Sat : (Fin v7Sig.tape → D) → Cand → Prop)
    (Ffam : ∀ pre : Fin v7Sig.tape → D,
      RbrSplit.FieldData C F
        (LigeroV1LayerStep.Chal F Equations v7Sig.params.nw v7Sig.params.nq)
        (LigeroV1LayerStep.Qry v7Sig.params.row) Cand Witness nc nv logw logc (H pre) (Sat pre))
    (hexact : ∀ pre : Fin v7Sig.tape → D, (Ffam pre).Exact)
    (MD : ∀ pre : Fin v7Sig.tape → D, MsgData C Msg (H pre))
    (hfail : ∀ pre : Fin v7Sig.tape → D, Fails pre → ∀ cand : Cand, ¬ Sat pre cand)
    (hright : ∀ pre : Fin v7Sig.tape → D, Fails pre →
      ∀ ro : MPoint Ctx Msg v7Sig.params.nl v7Sig.params.rounds → C,
        (CompiledAccepts K A codec (statement (pre, ro))
            (challengeOf (A.auxOf pre) ro) (queryOf (A.auxOf pre) ro) pre ∧
          ExtractionExplains codec dec n v7Sig.commitFuel (revealFuel + respondFuel)
            v7Sig.tape A.commit
            (A.openingStage (challengeOf (A.auxOf pre) ro) (queryOf (A.auxOf pre) ro)) pre) →
        RbrSplit.LayerStepAccepts
          (RbrSplit.stepsOf (nl := v7Sig.params.nl) (w := v7Sig.params.rounds)
            (withMsgs (Ffam pre) (MD pre) (msgOf (dProof (adv (A.auxOf pre)) ro)))
            (fun _ _ => LigeroV1LayerStep.accepting (Row.rowValid v7Sig_valid) dom
              (Row.hkrow v7Sig_valid) (lig pre)))
          (dChallenges (adv (A.auxOf pre)) (ctxOf (A.auxOf pre)) msgOf ro))
    (ht₁ : v7Sig.commitFuel ≤ v7Sig.tape)
    (hT : 2 * n + (revealFuel + respondFuel) + v7Sig.commitFuel ≤ v7Sig.tape)
    (hT1 : 1 ≤ v7Sig.tape)
    (hcand : Fintype.card Cand = v7Sig.cardCand)
    (hD : Fintype.card D = 2 ^ v7Sig.params.digestBits) :
    ((univ.filter fun omega :
          (Fin v7Sig.tape → D) × (MPoint Ctx Msg v7Sig.params.nl v7Sig.params.rounds → C) =>
        CompiledAccepts K A codec (statement omega)
            (challengeOf (A.auxOf omega.1) omega.2) (queryOf (A.auxOf omega.1) omega.2) omega.1 ∧
          Fails omega.1).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7Sig.tape *
            Fintype.card (MPoint Ctx Msg v7Sig.params.nl v7Sig.params.rounds → C))
      ≤ (1 : ℚ) / 2 ^ 122 + N * ((1 : ℚ) / 2 ^ 122) :=
  le_trans
    (row_fs_ratio_le_bound v7Sig_valid dec K A adv ctxOf msgOf challengeOf queryOf statement hF dom
      lig hfalse H Sat Ffam hexact MD hfail hright ht₁ hT hT1 hcand hD)
    (v7Sig_fs_rhs_le N)

/-- **v7Hash1 against a prefix-only grinding Fiat–Shamir adversary**: `row_fs_ratio_le_bound` at
`CertifiedV1.v7Hash1` — the v7 1-attribute hash component (17 layers, 566 sumcheck slots, over `GF(2^128)`; Ligero V1 at `n = 3230`, `k = 461`, 132 openings) — with `CertifiedV1.v7Hash1_fs_rhs_le`:
`Pr[accept ∧ Fails] ≤ 2^-115 + N · 2^-116`, `N` the number of deployed hash queries. -/
theorem v7Hash1_fs_ratio_le
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
      n v7Hash1.commitFuel respondFuel revealFuel)
    (adv : Aux → Tree (MPoint Ctx Msg v7Hash1.params.nl v7Hash1.params.rounds) C Out N)
    (ctxOf : Aux → Ctx) (msgOf : Out → ℕ → Msg)
    (challengeOf : Aux → (MPoint Ctx Msg v7Hash1.params.nl v7Hash1.params.rounds → C) → Challenge)
    (queryOf : Aux → (MPoint Ctx Msg v7Hash1.params.nl v7Hash1.params.rounds → C) → Query)
    (statement : (Fin v7Hash1.tape → D) × (MPoint Ctx Msg v7Hash1.params.nl v7Hash1.params.rounds → C)
      → Statement)
    {Fails : (Fin v7Hash1.tape → D) → Prop}
    (hF : Fintype.card F = v7Hash1.params.row.fieldSize)
    (dom : LigeroFamily.ReedSolomon.Domain F v7Hash1.params.row.openings v7Hash1.params.q
      v7Hash1.params.row.n)
    (lig : ∀ _pre : Fin v7Hash1.tape → D,
      LigeroV1LayerStep.Instance v7Hash1.params.row F Equations v7Hash1.params.nw
        v7Hash1.params.nq v7Hash1.params.q)
    (hfalse : ∀ pre : Fin v7Hash1.tape → D, Fails pre → ¬ (lig pre).statement.Language)
    (H : ∀ _pre : Fin v7Hash1.tape → D, RbrLongfellow.Honest F Cand logw logc)
    (Sat : (Fin v7Hash1.tape → D) → Cand → Prop)
    (Ffam : ∀ pre : Fin v7Hash1.tape → D,
      RbrSplit.FieldData C F
        (LigeroV1LayerStep.Chal F Equations v7Hash1.params.nw v7Hash1.params.nq)
        (LigeroV1LayerStep.Qry v7Hash1.params.row) Cand Witness nc nv logw logc (H pre) (Sat pre))
    (hexact : ∀ pre : Fin v7Hash1.tape → D, (Ffam pre).Exact)
    (MD : ∀ pre : Fin v7Hash1.tape → D, MsgData C Msg (H pre))
    (hfail : ∀ pre : Fin v7Hash1.tape → D, Fails pre → ∀ cand : Cand, ¬ Sat pre cand)
    (hright : ∀ pre : Fin v7Hash1.tape → D, Fails pre →
      ∀ ro : MPoint Ctx Msg v7Hash1.params.nl v7Hash1.params.rounds → C,
        (CompiledAccepts K A codec (statement (pre, ro))
            (challengeOf (A.auxOf pre) ro) (queryOf (A.auxOf pre) ro) pre ∧
          ExtractionExplains codec dec n v7Hash1.commitFuel (revealFuel + respondFuel)
            v7Hash1.tape A.commit
            (A.openingStage (challengeOf (A.auxOf pre) ro) (queryOf (A.auxOf pre) ro)) pre) →
        RbrSplit.LayerStepAccepts
          (RbrSplit.stepsOf (nl := v7Hash1.params.nl) (w := v7Hash1.params.rounds)
            (withMsgs (Ffam pre) (MD pre) (msgOf (dProof (adv (A.auxOf pre)) ro)))
            (fun _ _ => LigeroV1LayerStep.accepting (Row.rowValid v7Hash1_valid) dom
              (Row.hkrow v7Hash1_valid) (lig pre)))
          (dChallenges (adv (A.auxOf pre)) (ctxOf (A.auxOf pre)) msgOf ro))
    (ht₁ : v7Hash1.commitFuel ≤ v7Hash1.tape)
    (hT : 2 * n + (revealFuel + respondFuel) + v7Hash1.commitFuel ≤ v7Hash1.tape)
    (hT1 : 1 ≤ v7Hash1.tape)
    (hcand : Fintype.card Cand = v7Hash1.cardCand)
    (hD : Fintype.card D = 2 ^ v7Hash1.params.digestBits) :
    ((univ.filter fun omega :
          (Fin v7Hash1.tape → D) × (MPoint Ctx Msg v7Hash1.params.nl v7Hash1.params.rounds → C) =>
        CompiledAccepts K A codec (statement omega)
            (challengeOf (A.auxOf omega.1) omega.2) (queryOf (A.auxOf omega.1) omega.2) omega.1 ∧
          Fails omega.1).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7Hash1.tape *
            Fintype.card (MPoint Ctx Msg v7Hash1.params.nl v7Hash1.params.rounds → C))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) :=
  le_trans
    (row_fs_ratio_le_bound v7Hash1_valid dec K A adv ctxOf msgOf challengeOf queryOf statement hF dom
      lig hfalse H Sat Ffam hexact MD hfail hright ht₁ hT hT1 hcand hD)
    (v7Hash1_fs_rhs_le N)

/-- **v7Hash2 against a prefix-only grinding Fiat–Shamir adversary**: `row_fs_ratio_le_bound` at
`CertifiedV1.v7Hash2` — the v7 2-attribute hash component (17 layers, 570 sumcheck slots, over `GF(2^128)`; Ligero V1 at `n = 3318`, `k = 474`, 132 openings) — with `CertifiedV1.v7Hash2_fs_rhs_le`:
`Pr[accept ∧ Fails] ≤ 2^-115 + N · 2^-116`, `N` the number of deployed hash queries. -/
theorem v7Hash2_fs_ratio_le
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
      n v7Hash2.commitFuel respondFuel revealFuel)
    (adv : Aux → Tree (MPoint Ctx Msg v7Hash2.params.nl v7Hash2.params.rounds) C Out N)
    (ctxOf : Aux → Ctx) (msgOf : Out → ℕ → Msg)
    (challengeOf : Aux → (MPoint Ctx Msg v7Hash2.params.nl v7Hash2.params.rounds → C) → Challenge)
    (queryOf : Aux → (MPoint Ctx Msg v7Hash2.params.nl v7Hash2.params.rounds → C) → Query)
    (statement : (Fin v7Hash2.tape → D) × (MPoint Ctx Msg v7Hash2.params.nl v7Hash2.params.rounds → C)
      → Statement)
    {Fails : (Fin v7Hash2.tape → D) → Prop}
    (hF : Fintype.card F = v7Hash2.params.row.fieldSize)
    (dom : LigeroFamily.ReedSolomon.Domain F v7Hash2.params.row.openings v7Hash2.params.q
      v7Hash2.params.row.n)
    (lig : ∀ _pre : Fin v7Hash2.tape → D,
      LigeroV1LayerStep.Instance v7Hash2.params.row F Equations v7Hash2.params.nw
        v7Hash2.params.nq v7Hash2.params.q)
    (hfalse : ∀ pre : Fin v7Hash2.tape → D, Fails pre → ¬ (lig pre).statement.Language)
    (H : ∀ _pre : Fin v7Hash2.tape → D, RbrLongfellow.Honest F Cand logw logc)
    (Sat : (Fin v7Hash2.tape → D) → Cand → Prop)
    (Ffam : ∀ pre : Fin v7Hash2.tape → D,
      RbrSplit.FieldData C F
        (LigeroV1LayerStep.Chal F Equations v7Hash2.params.nw v7Hash2.params.nq)
        (LigeroV1LayerStep.Qry v7Hash2.params.row) Cand Witness nc nv logw logc (H pre) (Sat pre))
    (hexact : ∀ pre : Fin v7Hash2.tape → D, (Ffam pre).Exact)
    (MD : ∀ pre : Fin v7Hash2.tape → D, MsgData C Msg (H pre))
    (hfail : ∀ pre : Fin v7Hash2.tape → D, Fails pre → ∀ cand : Cand, ¬ Sat pre cand)
    (hright : ∀ pre : Fin v7Hash2.tape → D, Fails pre →
      ∀ ro : MPoint Ctx Msg v7Hash2.params.nl v7Hash2.params.rounds → C,
        (CompiledAccepts K A codec (statement (pre, ro))
            (challengeOf (A.auxOf pre) ro) (queryOf (A.auxOf pre) ro) pre ∧
          ExtractionExplains codec dec n v7Hash2.commitFuel (revealFuel + respondFuel)
            v7Hash2.tape A.commit
            (A.openingStage (challengeOf (A.auxOf pre) ro) (queryOf (A.auxOf pre) ro)) pre) →
        RbrSplit.LayerStepAccepts
          (RbrSplit.stepsOf (nl := v7Hash2.params.nl) (w := v7Hash2.params.rounds)
            (withMsgs (Ffam pre) (MD pre) (msgOf (dProof (adv (A.auxOf pre)) ro)))
            (fun _ _ => LigeroV1LayerStep.accepting (Row.rowValid v7Hash2_valid) dom
              (Row.hkrow v7Hash2_valid) (lig pre)))
          (dChallenges (adv (A.auxOf pre)) (ctxOf (A.auxOf pre)) msgOf ro))
    (ht₁ : v7Hash2.commitFuel ≤ v7Hash2.tape)
    (hT : 2 * n + (revealFuel + respondFuel) + v7Hash2.commitFuel ≤ v7Hash2.tape)
    (hT1 : 1 ≤ v7Hash2.tape)
    (hcand : Fintype.card Cand = v7Hash2.cardCand)
    (hD : Fintype.card D = 2 ^ v7Hash2.params.digestBits) :
    ((univ.filter fun omega :
          (Fin v7Hash2.tape → D) × (MPoint Ctx Msg v7Hash2.params.nl v7Hash2.params.rounds → C) =>
        CompiledAccepts K A codec (statement omega)
            (challengeOf (A.auxOf omega.1) omega.2) (queryOf (A.auxOf omega.1) omega.2) omega.1 ∧
          Fails omega.1).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7Hash2.tape *
            Fintype.card (MPoint Ctx Msg v7Hash2.params.nl v7Hash2.params.rounds → C))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) :=
  le_trans
    (row_fs_ratio_le_bound v7Hash2_valid dec K A adv ctxOf msgOf challengeOf queryOf statement hF dom
      lig hfalse H Sat Ffam hexact MD hfail hright ht₁ hT hT1 hcand hD)
    (v7Hash2_fs_rhs_le N)

/-- **v7Hash3 against a prefix-only grinding Fiat–Shamir adversary**: `row_fs_ratio_le_bound` at
`CertifiedV1.v7Hash3` — the v7 3-attribute hash component (17 layers, 574 sumcheck slots, over `GF(2^128)`; Ligero V1 at `n = 3352`, `k = 478`, 132 openings) — with `CertifiedV1.v7Hash3_fs_rhs_le`:
`Pr[accept ∧ Fails] ≤ 2^-115 + N · 2^-116`, `N` the number of deployed hash queries. -/
theorem v7Hash3_fs_ratio_le
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
      n v7Hash3.commitFuel respondFuel revealFuel)
    (adv : Aux → Tree (MPoint Ctx Msg v7Hash3.params.nl v7Hash3.params.rounds) C Out N)
    (ctxOf : Aux → Ctx) (msgOf : Out → ℕ → Msg)
    (challengeOf : Aux → (MPoint Ctx Msg v7Hash3.params.nl v7Hash3.params.rounds → C) → Challenge)
    (queryOf : Aux → (MPoint Ctx Msg v7Hash3.params.nl v7Hash3.params.rounds → C) → Query)
    (statement : (Fin v7Hash3.tape → D) × (MPoint Ctx Msg v7Hash3.params.nl v7Hash3.params.rounds → C)
      → Statement)
    {Fails : (Fin v7Hash3.tape → D) → Prop}
    (hF : Fintype.card F = v7Hash3.params.row.fieldSize)
    (dom : LigeroFamily.ReedSolomon.Domain F v7Hash3.params.row.openings v7Hash3.params.q
      v7Hash3.params.row.n)
    (lig : ∀ _pre : Fin v7Hash3.tape → D,
      LigeroV1LayerStep.Instance v7Hash3.params.row F Equations v7Hash3.params.nw
        v7Hash3.params.nq v7Hash3.params.q)
    (hfalse : ∀ pre : Fin v7Hash3.tape → D, Fails pre → ¬ (lig pre).statement.Language)
    (H : ∀ _pre : Fin v7Hash3.tape → D, RbrLongfellow.Honest F Cand logw logc)
    (Sat : (Fin v7Hash3.tape → D) → Cand → Prop)
    (Ffam : ∀ pre : Fin v7Hash3.tape → D,
      RbrSplit.FieldData C F
        (LigeroV1LayerStep.Chal F Equations v7Hash3.params.nw v7Hash3.params.nq)
        (LigeroV1LayerStep.Qry v7Hash3.params.row) Cand Witness nc nv logw logc (H pre) (Sat pre))
    (hexact : ∀ pre : Fin v7Hash3.tape → D, (Ffam pre).Exact)
    (MD : ∀ pre : Fin v7Hash3.tape → D, MsgData C Msg (H pre))
    (hfail : ∀ pre : Fin v7Hash3.tape → D, Fails pre → ∀ cand : Cand, ¬ Sat pre cand)
    (hright : ∀ pre : Fin v7Hash3.tape → D, Fails pre →
      ∀ ro : MPoint Ctx Msg v7Hash3.params.nl v7Hash3.params.rounds → C,
        (CompiledAccepts K A codec (statement (pre, ro))
            (challengeOf (A.auxOf pre) ro) (queryOf (A.auxOf pre) ro) pre ∧
          ExtractionExplains codec dec n v7Hash3.commitFuel (revealFuel + respondFuel)
            v7Hash3.tape A.commit
            (A.openingStage (challengeOf (A.auxOf pre) ro) (queryOf (A.auxOf pre) ro)) pre) →
        RbrSplit.LayerStepAccepts
          (RbrSplit.stepsOf (nl := v7Hash3.params.nl) (w := v7Hash3.params.rounds)
            (withMsgs (Ffam pre) (MD pre) (msgOf (dProof (adv (A.auxOf pre)) ro)))
            (fun _ _ => LigeroV1LayerStep.accepting (Row.rowValid v7Hash3_valid) dom
              (Row.hkrow v7Hash3_valid) (lig pre)))
          (dChallenges (adv (A.auxOf pre)) (ctxOf (A.auxOf pre)) msgOf ro))
    (ht₁ : v7Hash3.commitFuel ≤ v7Hash3.tape)
    (hT : 2 * n + (revealFuel + respondFuel) + v7Hash3.commitFuel ≤ v7Hash3.tape)
    (hT1 : 1 ≤ v7Hash3.tape)
    (hcand : Fintype.card Cand = v7Hash3.cardCand)
    (hD : Fintype.card D = 2 ^ v7Hash3.params.digestBits) :
    ((univ.filter fun omega :
          (Fin v7Hash3.tape → D) × (MPoint Ctx Msg v7Hash3.params.nl v7Hash3.params.rounds → C) =>
        CompiledAccepts K A codec (statement omega)
            (challengeOf (A.auxOf omega.1) omega.2) (queryOf (A.auxOf omega.1) omega.2) omega.1 ∧
          Fails omega.1).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7Hash3.tape *
            Fintype.card (MPoint Ctx Msg v7Hash3.params.nl v7Hash3.params.rounds → C))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) :=
  le_trans
    (row_fs_ratio_le_bound v7Hash3_valid dec K A adv ctxOf msgOf challengeOf queryOf statement hF dom
      lig hfalse H Sat Ffam hexact MD hfail hright ht₁ hT hT1 hcand hD)
    (v7Hash3_fs_rhs_le N)

/-- **v7Hash4 against a prefix-only grinding Fiat–Shamir adversary**: `row_fs_ratio_le_bound` at
`CertifiedV1.v7Hash4` — the v7 4-attribute hash component (17 layers, 574 sumcheck slots, over `GF(2^128)`; Ligero V1 at `n = 3436`, `k = 490`, 132 openings) — with `CertifiedV1.v7Hash4_fs_rhs_le`:
`Pr[accept ∧ Fails] ≤ 2^-115 + N · 2^-116`, `N` the number of deployed hash queries. -/
theorem v7Hash4_fs_ratio_le
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
      n v7Hash4.commitFuel respondFuel revealFuel)
    (adv : Aux → Tree (MPoint Ctx Msg v7Hash4.params.nl v7Hash4.params.rounds) C Out N)
    (ctxOf : Aux → Ctx) (msgOf : Out → ℕ → Msg)
    (challengeOf : Aux → (MPoint Ctx Msg v7Hash4.params.nl v7Hash4.params.rounds → C) → Challenge)
    (queryOf : Aux → (MPoint Ctx Msg v7Hash4.params.nl v7Hash4.params.rounds → C) → Query)
    (statement : (Fin v7Hash4.tape → D) × (MPoint Ctx Msg v7Hash4.params.nl v7Hash4.params.rounds → C)
      → Statement)
    {Fails : (Fin v7Hash4.tape → D) → Prop}
    (hF : Fintype.card F = v7Hash4.params.row.fieldSize)
    (dom : LigeroFamily.ReedSolomon.Domain F v7Hash4.params.row.openings v7Hash4.params.q
      v7Hash4.params.row.n)
    (lig : ∀ _pre : Fin v7Hash4.tape → D,
      LigeroV1LayerStep.Instance v7Hash4.params.row F Equations v7Hash4.params.nw
        v7Hash4.params.nq v7Hash4.params.q)
    (hfalse : ∀ pre : Fin v7Hash4.tape → D, Fails pre → ¬ (lig pre).statement.Language)
    (H : ∀ _pre : Fin v7Hash4.tape → D, RbrLongfellow.Honest F Cand logw logc)
    (Sat : (Fin v7Hash4.tape → D) → Cand → Prop)
    (Ffam : ∀ pre : Fin v7Hash4.tape → D,
      RbrSplit.FieldData C F
        (LigeroV1LayerStep.Chal F Equations v7Hash4.params.nw v7Hash4.params.nq)
        (LigeroV1LayerStep.Qry v7Hash4.params.row) Cand Witness nc nv logw logc (H pre) (Sat pre))
    (hexact : ∀ pre : Fin v7Hash4.tape → D, (Ffam pre).Exact)
    (MD : ∀ pre : Fin v7Hash4.tape → D, MsgData C Msg (H pre))
    (hfail : ∀ pre : Fin v7Hash4.tape → D, Fails pre → ∀ cand : Cand, ¬ Sat pre cand)
    (hright : ∀ pre : Fin v7Hash4.tape → D, Fails pre →
      ∀ ro : MPoint Ctx Msg v7Hash4.params.nl v7Hash4.params.rounds → C,
        (CompiledAccepts K A codec (statement (pre, ro))
            (challengeOf (A.auxOf pre) ro) (queryOf (A.auxOf pre) ro) pre ∧
          ExtractionExplains codec dec n v7Hash4.commitFuel (revealFuel + respondFuel)
            v7Hash4.tape A.commit
            (A.openingStage (challengeOf (A.auxOf pre) ro) (queryOf (A.auxOf pre) ro)) pre) →
        RbrSplit.LayerStepAccepts
          (RbrSplit.stepsOf (nl := v7Hash4.params.nl) (w := v7Hash4.params.rounds)
            (withMsgs (Ffam pre) (MD pre) (msgOf (dProof (adv (A.auxOf pre)) ro)))
            (fun _ _ => LigeroV1LayerStep.accepting (Row.rowValid v7Hash4_valid) dom
              (Row.hkrow v7Hash4_valid) (lig pre)))
          (dChallenges (adv (A.auxOf pre)) (ctxOf (A.auxOf pre)) msgOf ro))
    (ht₁ : v7Hash4.commitFuel ≤ v7Hash4.tape)
    (hT : 2 * n + (revealFuel + respondFuel) + v7Hash4.commitFuel ≤ v7Hash4.tape)
    (hT1 : 1 ≤ v7Hash4.tape)
    (hcand : Fintype.card Cand = v7Hash4.cardCand)
    (hD : Fintype.card D = 2 ^ v7Hash4.params.digestBits) :
    ((univ.filter fun omega :
          (Fin v7Hash4.tape → D) × (MPoint Ctx Msg v7Hash4.params.nl v7Hash4.params.rounds → C) =>
        CompiledAccepts K A codec (statement omega)
            (challengeOf (A.auxOf omega.1) omega.2) (queryOf (A.auxOf omega.1) omega.2) omega.1 ∧
          Fails omega.1).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7Hash4.tape *
            Fintype.card (MPoint Ctx Msg v7Hash4.params.nl v7Hash4.params.rounds → C))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) :=
  le_trans
    (row_fs_ratio_le_bound v7Hash4_valid dec K A adv ctxOf msgOf challengeOf queryOf statement hF dom
      lig hfalse H Sat Ffam hexact MD hfail hright ht₁ hT hT1 hcand hD)
    (v7Hash4_fs_rhs_le N)

end Fs

/-! ## 2. Re-committing prover, abstract verifier -/

section Adaptive
/-- **v7Sig against a re-committing prefix-only Fiat–Shamir prover**: `row_adaptive_ratio_le` at
`CertifiedV1.v7Sig` — the v7 signature component (21 layers, 542 sumcheck slots, over P-256's base field; Ligero V1 at `n = 3187`, `k = 455`, 132 openings) — with `CertifiedV1.v7Sig_adaptive_rhs_le`:
`Pr[JointAccepts ∧ Fails] ≤ 2^-122 + N · 2^-122`. -/
theorem v7Sig_adaptive_ratio_le
    {C Cand : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
    {F Equations Witness : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype Equations] [DecidableEq Equations]
    {logw logc nc nv : ℕ}
    {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
    {Enc D Salt M : Type} {n : ℕ}
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    {Msg Out : Type} [Fintype Msg] [DecidableEq Msg] [Inhabited Msg] {tA N : ℕ}
    {codec : Codec Salt M D Enc} (dec : RoleDecoders codec)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (body : TwoOracleTree Enc D (MPoint D Msg v7Sig.params.nl v7Sig.params.rounds) C Out tA N)
    (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim n Salt M D)
    (statementOf : Out → (Fin (Rounds.Role.length v7Sig.params.nl v7Sig.params.rounds) → C)
      → Statement)
    (responseOf : Out → Response)
    (challengeOf : Out → (Fin (Rounds.Role.length v7Sig.params.nl v7Sig.params.rounds)
      → C) → Challenge)
    (queryOf : Out → (Fin (Rounds.Role.length v7Sig.params.nl v7Sig.params.rounds)
      → C) → Query)
    {Fails : D × List (Enc × D) → Prop}
    (hF : Fintype.card F = v7Sig.params.row.fieldSize)
    (accR : ∀ _κ : D × List (Enc × D), ∀ m : ℕ, (Fin m → C) → Msg →
      LigeroV1LayerStep.Chal F Equations v7Sig.params.nw v7Sig.params.nq →
        Finset (LigeroV1LayerStep.Qry v7Sig.params.row))
    (hlig : ∀ κ, Fails κ →
      ∃ (LigDoomed : LigeroV1LayerStep.Chal F Equations v7Sig.params.nw v7Sig.params.nq → Prop)
        (ML : MsgLigeroData C (LigeroV1LayerStep.Chal F Equations v7Sig.params.nw v7Sig.params.nq)
          (LigeroV1LayerStep.Qry v7Sig.params.row) Msg LigDoomed),
        ML.accepting = accR κ ∧
        (ML.escaping.card : ℚ) ≤ (v7Sig.params.row.fail + v7Sig.params.row.arith)
          * Fintype.card (LigeroV1LayerStep.Chal F Equations v7Sig.params.nw v7Sig.params.nq) ∧
        ML.bq = LigeroV1LayerStep.queryCount v7Sig.params.row)
    (H : ∀ _κ : D × List (Enc × D), RbrLongfellow.Honest F Cand logw logc)
    (Sat : D × List (Enc × D) → Cand → Prop)
    (Ffam : ∀ κ, RbrSplit.FieldData C F
        (LigeroV1LayerStep.Chal F Equations v7Sig.params.nw v7Sig.params.nq)
        (LigeroV1LayerStep.Qry v7Sig.params.row) Cand Witness nc nv logw logc (H κ) (Sat κ))
    (hexact : ∀ κ, (Ffam κ).Exact)
    (MD : ∀ κ, MsgData C Msg (H κ))
    (hfail : ∀ κ, Fails κ → ∀ cand : Cand, ¬ Sat κ cand)
    (hright : ∀ (mt : Fin v7Sig.tape → D)
        (ro : MPoint D Msg v7Sig.params.nl v7Sig.params.rounds → C),
      Fails ((lfSetup body rootOf msgOf).context mt ro) →
      JointAccepts K codec (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf
        claimOf statementOf responseOf challengeOf queryOf mt ro →
      (lfSetup body rootOf msgOf).Explains dec id claimOf mt ro →
      RbrSplit.LayerStepAccepts
        (RbrSplit.stepsOf (nl := v7Sig.params.nl) (w := v7Sig.params.rounds)
          (withMsgs (Ffam ((lfSetup body rootOf msgOf).context mt ro))
            (MD ((lfSetup body rootOf msgOf).context mt ro))
            (msgOf ((lfSetup body rootOf msgOf).proof mt ro)))
          (fun m pref => accR ((lfSetup body rootOf msgOf).context mt ro) m pref
            (msgOf ((lfSetup body rootOf msgOf).proof mt ro) m)))
        ((lfSetup body rootOf msgOf).challenges mt ro))
    (htA : tA ≤ v7Sig.commitFuel) (htape : 2 * n + tA ≤ v7Sig.tape)
    (hcand : Fintype.card Cand = v7Sig.cardCand)
    (hD : Fintype.card D = 2 ^ v7Sig.params.digestBits) :
    ((univ.filter fun ω :
          (Fin v7Sig.tape → D) × (MPoint D Msg v7Sig.params.nl v7Sig.params.rounds → C) =>
        JointAccepts K codec (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf
            claimOf statementOf responseOf challengeOf queryOf ω.1 ω.2 ∧
          Fails ((lfSetup body rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7Sig.tape
            * (Fintype.card C : ℚ) ^ Fintype.card (MPoint D Msg v7Sig.params.nl v7Sig.params.rounds))
      ≤ (1 : ℚ) / 2 ^ 122 + N * ((1 : ℚ) / 2 ^ 122) :=
  le_trans (row_adaptive_ratio_le v7Sig_valid dec K body rootOf msgOf claimOf statementOf
      responseOf challengeOf queryOf hF accR hlig H Sat Ffam hexact MD hfail hright htA htape hcand hD)
    (v7Sig_adaptive_rhs_le N)

/-- **v7Hash1 against a re-committing prefix-only Fiat–Shamir prover**: `row_adaptive_ratio_le` at
`CertifiedV1.v7Hash1` — the v7 1-attribute hash component (17 layers, 566 sumcheck slots, over `GF(2^128)`; Ligero V1 at `n = 3230`, `k = 461`, 132 openings) — with `CertifiedV1.v7Hash1_adaptive_rhs_le`:
`Pr[JointAccepts ∧ Fails] ≤ 2^-115 + N · 2^-116`. -/
theorem v7Hash1_adaptive_ratio_le
    {C Cand : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
    {F Equations Witness : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype Equations] [DecidableEq Equations]
    {logw logc nc nv : ℕ}
    {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
    {Enc D Salt M : Type} {n : ℕ}
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    {Msg Out : Type} [Fintype Msg] [DecidableEq Msg] [Inhabited Msg] {tA N : ℕ}
    {codec : Codec Salt M D Enc} (dec : RoleDecoders codec)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (body : TwoOracleTree Enc D (MPoint D Msg v7Hash1.params.nl v7Hash1.params.rounds) C Out tA N)
    (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim n Salt M D)
    (statementOf : Out → (Fin (Rounds.Role.length v7Hash1.params.nl v7Hash1.params.rounds) → C)
      → Statement)
    (responseOf : Out → Response)
    (challengeOf : Out → (Fin (Rounds.Role.length v7Hash1.params.nl v7Hash1.params.rounds)
      → C) → Challenge)
    (queryOf : Out → (Fin (Rounds.Role.length v7Hash1.params.nl v7Hash1.params.rounds)
      → C) → Query)
    {Fails : D × List (Enc × D) → Prop}
    (hF : Fintype.card F = v7Hash1.params.row.fieldSize)
    (accR : ∀ _κ : D × List (Enc × D), ∀ m : ℕ, (Fin m → C) → Msg →
      LigeroV1LayerStep.Chal F Equations v7Hash1.params.nw v7Hash1.params.nq →
        Finset (LigeroV1LayerStep.Qry v7Hash1.params.row))
    (hlig : ∀ κ, Fails κ →
      ∃ (LigDoomed : LigeroV1LayerStep.Chal F Equations v7Hash1.params.nw v7Hash1.params.nq → Prop)
        (ML : MsgLigeroData C (LigeroV1LayerStep.Chal F Equations v7Hash1.params.nw v7Hash1.params.nq)
          (LigeroV1LayerStep.Qry v7Hash1.params.row) Msg LigDoomed),
        ML.accepting = accR κ ∧
        (ML.escaping.card : ℚ) ≤ (v7Hash1.params.row.fail + v7Hash1.params.row.arith)
          * Fintype.card (LigeroV1LayerStep.Chal F Equations v7Hash1.params.nw v7Hash1.params.nq) ∧
        ML.bq = LigeroV1LayerStep.queryCount v7Hash1.params.row)
    (H : ∀ _κ : D × List (Enc × D), RbrLongfellow.Honest F Cand logw logc)
    (Sat : D × List (Enc × D) → Cand → Prop)
    (Ffam : ∀ κ, RbrSplit.FieldData C F
        (LigeroV1LayerStep.Chal F Equations v7Hash1.params.nw v7Hash1.params.nq)
        (LigeroV1LayerStep.Qry v7Hash1.params.row) Cand Witness nc nv logw logc (H κ) (Sat κ))
    (hexact : ∀ κ, (Ffam κ).Exact)
    (MD : ∀ κ, MsgData C Msg (H κ))
    (hfail : ∀ κ, Fails κ → ∀ cand : Cand, ¬ Sat κ cand)
    (hright : ∀ (mt : Fin v7Hash1.tape → D)
        (ro : MPoint D Msg v7Hash1.params.nl v7Hash1.params.rounds → C),
      Fails ((lfSetup body rootOf msgOf).context mt ro) →
      JointAccepts K codec (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf
        claimOf statementOf responseOf challengeOf queryOf mt ro →
      (lfSetup body rootOf msgOf).Explains dec id claimOf mt ro →
      RbrSplit.LayerStepAccepts
        (RbrSplit.stepsOf (nl := v7Hash1.params.nl) (w := v7Hash1.params.rounds)
          (withMsgs (Ffam ((lfSetup body rootOf msgOf).context mt ro))
            (MD ((lfSetup body rootOf msgOf).context mt ro))
            (msgOf ((lfSetup body rootOf msgOf).proof mt ro)))
          (fun m pref => accR ((lfSetup body rootOf msgOf).context mt ro) m pref
            (msgOf ((lfSetup body rootOf msgOf).proof mt ro) m)))
        ((lfSetup body rootOf msgOf).challenges mt ro))
    (htA : tA ≤ v7Hash1.commitFuel) (htape : 2 * n + tA ≤ v7Hash1.tape)
    (hcand : Fintype.card Cand = v7Hash1.cardCand)
    (hD : Fintype.card D = 2 ^ v7Hash1.params.digestBits) :
    ((univ.filter fun ω :
          (Fin v7Hash1.tape → D) × (MPoint D Msg v7Hash1.params.nl v7Hash1.params.rounds → C) =>
        JointAccepts K codec (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf
            claimOf statementOf responseOf challengeOf queryOf ω.1 ω.2 ∧
          Fails ((lfSetup body rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7Hash1.tape
            * (Fintype.card C : ℚ) ^ Fintype.card (MPoint D Msg v7Hash1.params.nl v7Hash1.params.rounds))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) :=
  le_trans (row_adaptive_ratio_le v7Hash1_valid dec K body rootOf msgOf claimOf statementOf
      responseOf challengeOf queryOf hF accR hlig H Sat Ffam hexact MD hfail hright htA htape hcand hD)
    (v7Hash1_adaptive_rhs_le N)

/-- **v7Hash2 against a re-committing prefix-only Fiat–Shamir prover**: `row_adaptive_ratio_le` at
`CertifiedV1.v7Hash2` — the v7 2-attribute hash component (17 layers, 570 sumcheck slots, over `GF(2^128)`; Ligero V1 at `n = 3318`, `k = 474`, 132 openings) — with `CertifiedV1.v7Hash2_adaptive_rhs_le`:
`Pr[JointAccepts ∧ Fails] ≤ 2^-115 + N · 2^-116`. -/
theorem v7Hash2_adaptive_ratio_le
    {C Cand : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
    {F Equations Witness : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype Equations] [DecidableEq Equations]
    {logw logc nc nv : ℕ}
    {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
    {Enc D Salt M : Type} {n : ℕ}
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    {Msg Out : Type} [Fintype Msg] [DecidableEq Msg] [Inhabited Msg] {tA N : ℕ}
    {codec : Codec Salt M D Enc} (dec : RoleDecoders codec)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (body : TwoOracleTree Enc D (MPoint D Msg v7Hash2.params.nl v7Hash2.params.rounds) C Out tA N)
    (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim n Salt M D)
    (statementOf : Out → (Fin (Rounds.Role.length v7Hash2.params.nl v7Hash2.params.rounds) → C)
      → Statement)
    (responseOf : Out → Response)
    (challengeOf : Out → (Fin (Rounds.Role.length v7Hash2.params.nl v7Hash2.params.rounds)
      → C) → Challenge)
    (queryOf : Out → (Fin (Rounds.Role.length v7Hash2.params.nl v7Hash2.params.rounds)
      → C) → Query)
    {Fails : D × List (Enc × D) → Prop}
    (hF : Fintype.card F = v7Hash2.params.row.fieldSize)
    (accR : ∀ _κ : D × List (Enc × D), ∀ m : ℕ, (Fin m → C) → Msg →
      LigeroV1LayerStep.Chal F Equations v7Hash2.params.nw v7Hash2.params.nq →
        Finset (LigeroV1LayerStep.Qry v7Hash2.params.row))
    (hlig : ∀ κ, Fails κ →
      ∃ (LigDoomed : LigeroV1LayerStep.Chal F Equations v7Hash2.params.nw v7Hash2.params.nq → Prop)
        (ML : MsgLigeroData C (LigeroV1LayerStep.Chal F Equations v7Hash2.params.nw v7Hash2.params.nq)
          (LigeroV1LayerStep.Qry v7Hash2.params.row) Msg LigDoomed),
        ML.accepting = accR κ ∧
        (ML.escaping.card : ℚ) ≤ (v7Hash2.params.row.fail + v7Hash2.params.row.arith)
          * Fintype.card (LigeroV1LayerStep.Chal F Equations v7Hash2.params.nw v7Hash2.params.nq) ∧
        ML.bq = LigeroV1LayerStep.queryCount v7Hash2.params.row)
    (H : ∀ _κ : D × List (Enc × D), RbrLongfellow.Honest F Cand logw logc)
    (Sat : D × List (Enc × D) → Cand → Prop)
    (Ffam : ∀ κ, RbrSplit.FieldData C F
        (LigeroV1LayerStep.Chal F Equations v7Hash2.params.nw v7Hash2.params.nq)
        (LigeroV1LayerStep.Qry v7Hash2.params.row) Cand Witness nc nv logw logc (H κ) (Sat κ))
    (hexact : ∀ κ, (Ffam κ).Exact)
    (MD : ∀ κ, MsgData C Msg (H κ))
    (hfail : ∀ κ, Fails κ → ∀ cand : Cand, ¬ Sat κ cand)
    (hright : ∀ (mt : Fin v7Hash2.tape → D)
        (ro : MPoint D Msg v7Hash2.params.nl v7Hash2.params.rounds → C),
      Fails ((lfSetup body rootOf msgOf).context mt ro) →
      JointAccepts K codec (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf
        claimOf statementOf responseOf challengeOf queryOf mt ro →
      (lfSetup body rootOf msgOf).Explains dec id claimOf mt ro →
      RbrSplit.LayerStepAccepts
        (RbrSplit.stepsOf (nl := v7Hash2.params.nl) (w := v7Hash2.params.rounds)
          (withMsgs (Ffam ((lfSetup body rootOf msgOf).context mt ro))
            (MD ((lfSetup body rootOf msgOf).context mt ro))
            (msgOf ((lfSetup body rootOf msgOf).proof mt ro)))
          (fun m pref => accR ((lfSetup body rootOf msgOf).context mt ro) m pref
            (msgOf ((lfSetup body rootOf msgOf).proof mt ro) m)))
        ((lfSetup body rootOf msgOf).challenges mt ro))
    (htA : tA ≤ v7Hash2.commitFuel) (htape : 2 * n + tA ≤ v7Hash2.tape)
    (hcand : Fintype.card Cand = v7Hash2.cardCand)
    (hD : Fintype.card D = 2 ^ v7Hash2.params.digestBits) :
    ((univ.filter fun ω :
          (Fin v7Hash2.tape → D) × (MPoint D Msg v7Hash2.params.nl v7Hash2.params.rounds → C) =>
        JointAccepts K codec (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf
            claimOf statementOf responseOf challengeOf queryOf ω.1 ω.2 ∧
          Fails ((lfSetup body rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7Hash2.tape
            * (Fintype.card C : ℚ) ^ Fintype.card (MPoint D Msg v7Hash2.params.nl v7Hash2.params.rounds))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) :=
  le_trans (row_adaptive_ratio_le v7Hash2_valid dec K body rootOf msgOf claimOf statementOf
      responseOf challengeOf queryOf hF accR hlig H Sat Ffam hexact MD hfail hright htA htape hcand hD)
    (v7Hash2_adaptive_rhs_le N)

/-- **v7Hash3 against a re-committing prefix-only Fiat–Shamir prover**: `row_adaptive_ratio_le` at
`CertifiedV1.v7Hash3` — the v7 3-attribute hash component (17 layers, 574 sumcheck slots, over `GF(2^128)`; Ligero V1 at `n = 3352`, `k = 478`, 132 openings) — with `CertifiedV1.v7Hash3_adaptive_rhs_le`:
`Pr[JointAccepts ∧ Fails] ≤ 2^-115 + N · 2^-116`. -/
theorem v7Hash3_adaptive_ratio_le
    {C Cand : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
    {F Equations Witness : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype Equations] [DecidableEq Equations]
    {logw logc nc nv : ℕ}
    {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
    {Enc D Salt M : Type} {n : ℕ}
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    {Msg Out : Type} [Fintype Msg] [DecidableEq Msg] [Inhabited Msg] {tA N : ℕ}
    {codec : Codec Salt M D Enc} (dec : RoleDecoders codec)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (body : TwoOracleTree Enc D (MPoint D Msg v7Hash3.params.nl v7Hash3.params.rounds) C Out tA N)
    (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim n Salt M D)
    (statementOf : Out → (Fin (Rounds.Role.length v7Hash3.params.nl v7Hash3.params.rounds) → C)
      → Statement)
    (responseOf : Out → Response)
    (challengeOf : Out → (Fin (Rounds.Role.length v7Hash3.params.nl v7Hash3.params.rounds)
      → C) → Challenge)
    (queryOf : Out → (Fin (Rounds.Role.length v7Hash3.params.nl v7Hash3.params.rounds)
      → C) → Query)
    {Fails : D × List (Enc × D) → Prop}
    (hF : Fintype.card F = v7Hash3.params.row.fieldSize)
    (accR : ∀ _κ : D × List (Enc × D), ∀ m : ℕ, (Fin m → C) → Msg →
      LigeroV1LayerStep.Chal F Equations v7Hash3.params.nw v7Hash3.params.nq →
        Finset (LigeroV1LayerStep.Qry v7Hash3.params.row))
    (hlig : ∀ κ, Fails κ →
      ∃ (LigDoomed : LigeroV1LayerStep.Chal F Equations v7Hash3.params.nw v7Hash3.params.nq → Prop)
        (ML : MsgLigeroData C (LigeroV1LayerStep.Chal F Equations v7Hash3.params.nw v7Hash3.params.nq)
          (LigeroV1LayerStep.Qry v7Hash3.params.row) Msg LigDoomed),
        ML.accepting = accR κ ∧
        (ML.escaping.card : ℚ) ≤ (v7Hash3.params.row.fail + v7Hash3.params.row.arith)
          * Fintype.card (LigeroV1LayerStep.Chal F Equations v7Hash3.params.nw v7Hash3.params.nq) ∧
        ML.bq = LigeroV1LayerStep.queryCount v7Hash3.params.row)
    (H : ∀ _κ : D × List (Enc × D), RbrLongfellow.Honest F Cand logw logc)
    (Sat : D × List (Enc × D) → Cand → Prop)
    (Ffam : ∀ κ, RbrSplit.FieldData C F
        (LigeroV1LayerStep.Chal F Equations v7Hash3.params.nw v7Hash3.params.nq)
        (LigeroV1LayerStep.Qry v7Hash3.params.row) Cand Witness nc nv logw logc (H κ) (Sat κ))
    (hexact : ∀ κ, (Ffam κ).Exact)
    (MD : ∀ κ, MsgData C Msg (H κ))
    (hfail : ∀ κ, Fails κ → ∀ cand : Cand, ¬ Sat κ cand)
    (hright : ∀ (mt : Fin v7Hash3.tape → D)
        (ro : MPoint D Msg v7Hash3.params.nl v7Hash3.params.rounds → C),
      Fails ((lfSetup body rootOf msgOf).context mt ro) →
      JointAccepts K codec (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf
        claimOf statementOf responseOf challengeOf queryOf mt ro →
      (lfSetup body rootOf msgOf).Explains dec id claimOf mt ro →
      RbrSplit.LayerStepAccepts
        (RbrSplit.stepsOf (nl := v7Hash3.params.nl) (w := v7Hash3.params.rounds)
          (withMsgs (Ffam ((lfSetup body rootOf msgOf).context mt ro))
            (MD ((lfSetup body rootOf msgOf).context mt ro))
            (msgOf ((lfSetup body rootOf msgOf).proof mt ro)))
          (fun m pref => accR ((lfSetup body rootOf msgOf).context mt ro) m pref
            (msgOf ((lfSetup body rootOf msgOf).proof mt ro) m)))
        ((lfSetup body rootOf msgOf).challenges mt ro))
    (htA : tA ≤ v7Hash3.commitFuel) (htape : 2 * n + tA ≤ v7Hash3.tape)
    (hcand : Fintype.card Cand = v7Hash3.cardCand)
    (hD : Fintype.card D = 2 ^ v7Hash3.params.digestBits) :
    ((univ.filter fun ω :
          (Fin v7Hash3.tape → D) × (MPoint D Msg v7Hash3.params.nl v7Hash3.params.rounds → C) =>
        JointAccepts K codec (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf
            claimOf statementOf responseOf challengeOf queryOf ω.1 ω.2 ∧
          Fails ((lfSetup body rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7Hash3.tape
            * (Fintype.card C : ℚ) ^ Fintype.card (MPoint D Msg v7Hash3.params.nl v7Hash3.params.rounds))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) :=
  le_trans (row_adaptive_ratio_le v7Hash3_valid dec K body rootOf msgOf claimOf statementOf
      responseOf challengeOf queryOf hF accR hlig H Sat Ffam hexact MD hfail hright htA htape hcand hD)
    (v7Hash3_adaptive_rhs_le N)

/-- **v7Hash4 against a re-committing prefix-only Fiat–Shamir prover**: `row_adaptive_ratio_le` at
`CertifiedV1.v7Hash4` — the v7 4-attribute hash component (17 layers, 574 sumcheck slots, over `GF(2^128)`; Ligero V1 at `n = 3436`, `k = 490`, 132 openings) — with `CertifiedV1.v7Hash4_adaptive_rhs_le`:
`Pr[JointAccepts ∧ Fails] ≤ 2^-115 + N · 2^-116`. -/
theorem v7Hash4_adaptive_ratio_le
    {C Cand : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
    {F Equations Witness : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype Equations] [DecidableEq Equations]
    {logw logc nc nv : ℕ}
    {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
    {Enc D Salt M : Type} {n : ℕ}
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    {Msg Out : Type} [Fintype Msg] [DecidableEq Msg] [Inhabited Msg] {tA N : ℕ}
    {codec : Codec Salt M D Enc} (dec : RoleDecoders codec)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (body : TwoOracleTree Enc D (MPoint D Msg v7Hash4.params.nl v7Hash4.params.rounds) C Out tA N)
    (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim n Salt M D)
    (statementOf : Out → (Fin (Rounds.Role.length v7Hash4.params.nl v7Hash4.params.rounds) → C)
      → Statement)
    (responseOf : Out → Response)
    (challengeOf : Out → (Fin (Rounds.Role.length v7Hash4.params.nl v7Hash4.params.rounds)
      → C) → Challenge)
    (queryOf : Out → (Fin (Rounds.Role.length v7Hash4.params.nl v7Hash4.params.rounds)
      → C) → Query)
    {Fails : D × List (Enc × D) → Prop}
    (hF : Fintype.card F = v7Hash4.params.row.fieldSize)
    (accR : ∀ _κ : D × List (Enc × D), ∀ m : ℕ, (Fin m → C) → Msg →
      LigeroV1LayerStep.Chal F Equations v7Hash4.params.nw v7Hash4.params.nq →
        Finset (LigeroV1LayerStep.Qry v7Hash4.params.row))
    (hlig : ∀ κ, Fails κ →
      ∃ (LigDoomed : LigeroV1LayerStep.Chal F Equations v7Hash4.params.nw v7Hash4.params.nq → Prop)
        (ML : MsgLigeroData C (LigeroV1LayerStep.Chal F Equations v7Hash4.params.nw v7Hash4.params.nq)
          (LigeroV1LayerStep.Qry v7Hash4.params.row) Msg LigDoomed),
        ML.accepting = accR κ ∧
        (ML.escaping.card : ℚ) ≤ (v7Hash4.params.row.fail + v7Hash4.params.row.arith)
          * Fintype.card (LigeroV1LayerStep.Chal F Equations v7Hash4.params.nw v7Hash4.params.nq) ∧
        ML.bq = LigeroV1LayerStep.queryCount v7Hash4.params.row)
    (H : ∀ _κ : D × List (Enc × D), RbrLongfellow.Honest F Cand logw logc)
    (Sat : D × List (Enc × D) → Cand → Prop)
    (Ffam : ∀ κ, RbrSplit.FieldData C F
        (LigeroV1LayerStep.Chal F Equations v7Hash4.params.nw v7Hash4.params.nq)
        (LigeroV1LayerStep.Qry v7Hash4.params.row) Cand Witness nc nv logw logc (H κ) (Sat κ))
    (hexact : ∀ κ, (Ffam κ).Exact)
    (MD : ∀ κ, MsgData C Msg (H κ))
    (hfail : ∀ κ, Fails κ → ∀ cand : Cand, ¬ Sat κ cand)
    (hright : ∀ (mt : Fin v7Hash4.tape → D)
        (ro : MPoint D Msg v7Hash4.params.nl v7Hash4.params.rounds → C),
      Fails ((lfSetup body rootOf msgOf).context mt ro) →
      JointAccepts K codec (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf
        claimOf statementOf responseOf challengeOf queryOf mt ro →
      (lfSetup body rootOf msgOf).Explains dec id claimOf mt ro →
      RbrSplit.LayerStepAccepts
        (RbrSplit.stepsOf (nl := v7Hash4.params.nl) (w := v7Hash4.params.rounds)
          (withMsgs (Ffam ((lfSetup body rootOf msgOf).context mt ro))
            (MD ((lfSetup body rootOf msgOf).context mt ro))
            (msgOf ((lfSetup body rootOf msgOf).proof mt ro)))
          (fun m pref => accR ((lfSetup body rootOf msgOf).context mt ro) m pref
            (msgOf ((lfSetup body rootOf msgOf).proof mt ro) m)))
        ((lfSetup body rootOf msgOf).challenges mt ro))
    (htA : tA ≤ v7Hash4.commitFuel) (htape : 2 * n + tA ≤ v7Hash4.tape)
    (hcand : Fintype.card Cand = v7Hash4.cardCand)
    (hD : Fintype.card D = 2 ^ v7Hash4.params.digestBits) :
    ((univ.filter fun ω :
          (Fin v7Hash4.tape → D) × (MPoint D Msg v7Hash4.params.nl v7Hash4.params.rounds → C) =>
        JointAccepts K codec (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf
            claimOf statementOf responseOf challengeOf queryOf ω.1 ω.2 ∧
          Fails ((lfSetup body rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7Hash4.tape
            * (Fintype.card C : ℚ) ^ Fintype.card (MPoint D Msg v7Hash4.params.nl v7Hash4.params.rounds))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) :=
  le_trans (row_adaptive_ratio_le v7Hash4_valid dec K body rootOf msgOf claimOf statementOf
      responseOf challengeOf queryOf hF accR hlig H Sat Ffam hexact MD hfail hright htA htape hcand hD)
    (v7Hash4_adaptive_rhs_le N)

end Adaptive

/-! ## 3. Re-committing prover, compiled Longfellow verifier -/

section RowCompiled

open Lfzk.CompiledLongfellow (Code Col guarded v1K Matches)
open Lfzk.CompiledLongfellowAdaptive (statementOfAt challengeOfAt queryOfAt responseOfAt
  rootStatement accR exists_msgLigeroData extractedInstance)

variable {C Cand : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
variable {F Equations Witness : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
  [Fintype Equations] [DecidableEq Equations]
variable {logw logc nc nv : ℕ}
variable {Enc D Salt : Type} [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc]
  [Inhabited Salt]
variable {Msg Out : Type} [Fintype Msg] [DecidableEq Msg] [Inhabited Msg] {tA N : ℕ}

/-- **v7Sig at the compiled Longfellow verifier, against a re-committing prefix-only Fiat–Shamir
prover**: `row_adaptive_ratio_le_v1` at `CertifiedV1.v7Sig` — the v7 signature component (21 layers, 542 sumcheck slots, over P-256's base field; Ligero V1 at `n = 3187`, `k = 455`, 132 openings) — with
`CertifiedV1.v7Sig_adaptive_rhs_le`: `Pr[AcceptsAt (v1K …) … ∧ Fails] ≤ 2^-122 + N · 2^-122`,
`hlig` and `hright` theorems. -/
theorem v7Sig_adaptive_compiled_ratio_le
    {codec : Codec Salt (Col F v7Sig.params.nw v7Sig.params.nq) D Enc} (dec : RoleDecoders codec)
    (V : Code C F (LigeroV1LayerStep.Chal F Equations v7Sig.params.nw v7Sig.params.nq)
      (LigeroV1LayerStep.Qry v7Sig.params.row) Msg logw logc)
    (dom : LigeroFamily.ReedSolomon.Domain F v7Sig.params.row.openings v7Sig.params.q
      v7Sig.params.row.n)
    (stmt : D → LigeroFamily.ConstraintSystem F v7Sig.params.nw v7Sig.params.nq v7Sig.params.q
      Equations)
    (respOf : Msg → LigeroFamily.Response F v7Sig.params.row.openings v7Sig.params.q
      v7Sig.params.row.n 1)
    (body : TwoOracleTree Enc D (MPoint D Msg v7Sig.params.nl v7Sig.params.rounds) C Out tA N)
    (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim v7Sig.params.row.n Salt
      (Col F v7Sig.params.nw v7Sig.params.nq) D)
    {Fails : D × List (Enc × D) → Prop}
    (hF : Fintype.card F = v7Sig.params.row.fieldSize)
    (hfalse : ∀ κ, Fails κ → ¬ (stmt κ.1).Language)
    (H : ∀ _κ : D × List (Enc × D), RbrLongfellow.Honest F Cand logw logc)
    (Sat : D × List (Enc × D) → Cand → Prop)
    (Ffam : ∀ κ, RbrSplit.FieldData C F
        (LigeroV1LayerStep.Chal F Equations v7Sig.params.nw v7Sig.params.nq)
        (LigeroV1LayerStep.Qry v7Sig.params.row) Cand Witness nc nv logw logc (H κ) (Sat κ))
    (hexact : ∀ κ, (Ffam κ).Exact)
    (MD : ∀ κ, MsgData C Msg (H κ))
    (hmatch : ∀ κ, Matches V (Ffam κ) (MD κ))
    (hfail : ∀ κ, Fails κ → ∀ cand : Cand, ¬ Sat κ cand)
    (htA : tA ≤ v7Sig.commitFuel) (htape : 2 * v7Sig.params.row.n + tA ≤ v7Sig.tape)
    (hcand : Fintype.card Cand = v7Sig.cardCand)
    (hD : Fintype.card D = 2 ^ v7Sig.params.digestBits) :
    ((univ.filter fun ω :
          (Fin v7Sig.tape → D) × (MPoint D Msg v7Sig.params.nl v7Sig.params.rounds → C) =>
        AcceptsAt (v1K (Row.rowValid v7Sig_valid) dom (Row.hkrow v7Sig_valid) v7Sig_openings_pos)
            V codec (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf msgOf
            claimOf (rootStatement rootOf stmt) respOf id ω.1 ω.2 ∧
          Fails ((lfSetup body rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7Sig.tape
            * (Fintype.card C : ℚ) ^ Fintype.card (MPoint D Msg v7Sig.params.nl v7Sig.params.rounds))
      ≤ (1 : ℚ) / 2 ^ 122 + N * ((1 : ℚ) / 2 ^ 122) :=
  le_trans
    (row_adaptive_ratio_le_v1 v7Sig_valid v7Sig_openings_pos dec V dom stmt respOf body
      rootOf msgOf claimOf hF hfalse H Sat Ffam hexact MD hmatch hfail htA htape hcand hD)
    (v7Sig_adaptive_rhs_le N)

/-- **v7Hash1 at the compiled Longfellow verifier, against a re-committing prefix-only Fiat–Shamir
prover**: `row_adaptive_ratio_le_v1` at `CertifiedV1.v7Hash1` — the v7 1-attribute hash component (17 layers, 566 sumcheck slots, over `GF(2^128)`; Ligero V1 at `n = 3230`, `k = 461`, 132 openings) — with
`CertifiedV1.v7Hash1_adaptive_rhs_le`: `Pr[AcceptsAt (v1K …) … ∧ Fails] ≤ 2^-115 + N · 2^-116`,
`hlig` and `hright` theorems. -/
theorem v7Hash1_adaptive_compiled_ratio_le
    {codec : Codec Salt (Col F v7Hash1.params.nw v7Hash1.params.nq) D Enc} (dec : RoleDecoders codec)
    (V : Code C F (LigeroV1LayerStep.Chal F Equations v7Hash1.params.nw v7Hash1.params.nq)
      (LigeroV1LayerStep.Qry v7Hash1.params.row) Msg logw logc)
    (dom : LigeroFamily.ReedSolomon.Domain F v7Hash1.params.row.openings v7Hash1.params.q
      v7Hash1.params.row.n)
    (stmt : D → LigeroFamily.ConstraintSystem F v7Hash1.params.nw v7Hash1.params.nq v7Hash1.params.q
      Equations)
    (respOf : Msg → LigeroFamily.Response F v7Hash1.params.row.openings v7Hash1.params.q
      v7Hash1.params.row.n 1)
    (body : TwoOracleTree Enc D (MPoint D Msg v7Hash1.params.nl v7Hash1.params.rounds) C Out tA N)
    (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim v7Hash1.params.row.n Salt
      (Col F v7Hash1.params.nw v7Hash1.params.nq) D)
    {Fails : D × List (Enc × D) → Prop}
    (hF : Fintype.card F = v7Hash1.params.row.fieldSize)
    (hfalse : ∀ κ, Fails κ → ¬ (stmt κ.1).Language)
    (H : ∀ _κ : D × List (Enc × D), RbrLongfellow.Honest F Cand logw logc)
    (Sat : D × List (Enc × D) → Cand → Prop)
    (Ffam : ∀ κ, RbrSplit.FieldData C F
        (LigeroV1LayerStep.Chal F Equations v7Hash1.params.nw v7Hash1.params.nq)
        (LigeroV1LayerStep.Qry v7Hash1.params.row) Cand Witness nc nv logw logc (H κ) (Sat κ))
    (hexact : ∀ κ, (Ffam κ).Exact)
    (MD : ∀ κ, MsgData C Msg (H κ))
    (hmatch : ∀ κ, Matches V (Ffam κ) (MD κ))
    (hfail : ∀ κ, Fails κ → ∀ cand : Cand, ¬ Sat κ cand)
    (htA : tA ≤ v7Hash1.commitFuel) (htape : 2 * v7Hash1.params.row.n + tA ≤ v7Hash1.tape)
    (hcand : Fintype.card Cand = v7Hash1.cardCand)
    (hD : Fintype.card D = 2 ^ v7Hash1.params.digestBits) :
    ((univ.filter fun ω :
          (Fin v7Hash1.tape → D) × (MPoint D Msg v7Hash1.params.nl v7Hash1.params.rounds → C) =>
        AcceptsAt (v1K (Row.rowValid v7Hash1_valid) dom (Row.hkrow v7Hash1_valid) v7Hash1_openings_pos)
            V codec (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf msgOf
            claimOf (rootStatement rootOf stmt) respOf id ω.1 ω.2 ∧
          Fails ((lfSetup body rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7Hash1.tape
            * (Fintype.card C : ℚ) ^ Fintype.card (MPoint D Msg v7Hash1.params.nl v7Hash1.params.rounds))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) :=
  le_trans
    (row_adaptive_ratio_le_v1 v7Hash1_valid v7Hash1_openings_pos dec V dom stmt respOf body
      rootOf msgOf claimOf hF hfalse H Sat Ffam hexact MD hmatch hfail htA htape hcand hD)
    (v7Hash1_adaptive_rhs_le N)

/-- **v7Hash2 at the compiled Longfellow verifier, against a re-committing prefix-only Fiat–Shamir
prover**: `row_adaptive_ratio_le_v1` at `CertifiedV1.v7Hash2` — the v7 2-attribute hash component (17 layers, 570 sumcheck slots, over `GF(2^128)`; Ligero V1 at `n = 3318`, `k = 474`, 132 openings) — with
`CertifiedV1.v7Hash2_adaptive_rhs_le`: `Pr[AcceptsAt (v1K …) … ∧ Fails] ≤ 2^-115 + N · 2^-116`,
`hlig` and `hright` theorems. -/
theorem v7Hash2_adaptive_compiled_ratio_le
    {codec : Codec Salt (Col F v7Hash2.params.nw v7Hash2.params.nq) D Enc} (dec : RoleDecoders codec)
    (V : Code C F (LigeroV1LayerStep.Chal F Equations v7Hash2.params.nw v7Hash2.params.nq)
      (LigeroV1LayerStep.Qry v7Hash2.params.row) Msg logw logc)
    (dom : LigeroFamily.ReedSolomon.Domain F v7Hash2.params.row.openings v7Hash2.params.q
      v7Hash2.params.row.n)
    (stmt : D → LigeroFamily.ConstraintSystem F v7Hash2.params.nw v7Hash2.params.nq v7Hash2.params.q
      Equations)
    (respOf : Msg → LigeroFamily.Response F v7Hash2.params.row.openings v7Hash2.params.q
      v7Hash2.params.row.n 1)
    (body : TwoOracleTree Enc D (MPoint D Msg v7Hash2.params.nl v7Hash2.params.rounds) C Out tA N)
    (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim v7Hash2.params.row.n Salt
      (Col F v7Hash2.params.nw v7Hash2.params.nq) D)
    {Fails : D × List (Enc × D) → Prop}
    (hF : Fintype.card F = v7Hash2.params.row.fieldSize)
    (hfalse : ∀ κ, Fails κ → ¬ (stmt κ.1).Language)
    (H : ∀ _κ : D × List (Enc × D), RbrLongfellow.Honest F Cand logw logc)
    (Sat : D × List (Enc × D) → Cand → Prop)
    (Ffam : ∀ κ, RbrSplit.FieldData C F
        (LigeroV1LayerStep.Chal F Equations v7Hash2.params.nw v7Hash2.params.nq)
        (LigeroV1LayerStep.Qry v7Hash2.params.row) Cand Witness nc nv logw logc (H κ) (Sat κ))
    (hexact : ∀ κ, (Ffam κ).Exact)
    (MD : ∀ κ, MsgData C Msg (H κ))
    (hmatch : ∀ κ, Matches V (Ffam κ) (MD κ))
    (hfail : ∀ κ, Fails κ → ∀ cand : Cand, ¬ Sat κ cand)
    (htA : tA ≤ v7Hash2.commitFuel) (htape : 2 * v7Hash2.params.row.n + tA ≤ v7Hash2.tape)
    (hcand : Fintype.card Cand = v7Hash2.cardCand)
    (hD : Fintype.card D = 2 ^ v7Hash2.params.digestBits) :
    ((univ.filter fun ω :
          (Fin v7Hash2.tape → D) × (MPoint D Msg v7Hash2.params.nl v7Hash2.params.rounds → C) =>
        AcceptsAt (v1K (Row.rowValid v7Hash2_valid) dom (Row.hkrow v7Hash2_valid) v7Hash2_openings_pos)
            V codec (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf msgOf
            claimOf (rootStatement rootOf stmt) respOf id ω.1 ω.2 ∧
          Fails ((lfSetup body rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7Hash2.tape
            * (Fintype.card C : ℚ) ^ Fintype.card (MPoint D Msg v7Hash2.params.nl v7Hash2.params.rounds))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) :=
  le_trans
    (row_adaptive_ratio_le_v1 v7Hash2_valid v7Hash2_openings_pos dec V dom stmt respOf body
      rootOf msgOf claimOf hF hfalse H Sat Ffam hexact MD hmatch hfail htA htape hcand hD)
    (v7Hash2_adaptive_rhs_le N)

/-- **v7Hash3 at the compiled Longfellow verifier, against a re-committing prefix-only Fiat–Shamir
prover**: `row_adaptive_ratio_le_v1` at `CertifiedV1.v7Hash3` — the v7 3-attribute hash component (17 layers, 574 sumcheck slots, over `GF(2^128)`; Ligero V1 at `n = 3352`, `k = 478`, 132 openings) — with
`CertifiedV1.v7Hash3_adaptive_rhs_le`: `Pr[AcceptsAt (v1K …) … ∧ Fails] ≤ 2^-115 + N · 2^-116`,
`hlig` and `hright` theorems. -/
theorem v7Hash3_adaptive_compiled_ratio_le
    {codec : Codec Salt (Col F v7Hash3.params.nw v7Hash3.params.nq) D Enc} (dec : RoleDecoders codec)
    (V : Code C F (LigeroV1LayerStep.Chal F Equations v7Hash3.params.nw v7Hash3.params.nq)
      (LigeroV1LayerStep.Qry v7Hash3.params.row) Msg logw logc)
    (dom : LigeroFamily.ReedSolomon.Domain F v7Hash3.params.row.openings v7Hash3.params.q
      v7Hash3.params.row.n)
    (stmt : D → LigeroFamily.ConstraintSystem F v7Hash3.params.nw v7Hash3.params.nq v7Hash3.params.q
      Equations)
    (respOf : Msg → LigeroFamily.Response F v7Hash3.params.row.openings v7Hash3.params.q
      v7Hash3.params.row.n 1)
    (body : TwoOracleTree Enc D (MPoint D Msg v7Hash3.params.nl v7Hash3.params.rounds) C Out tA N)
    (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim v7Hash3.params.row.n Salt
      (Col F v7Hash3.params.nw v7Hash3.params.nq) D)
    {Fails : D × List (Enc × D) → Prop}
    (hF : Fintype.card F = v7Hash3.params.row.fieldSize)
    (hfalse : ∀ κ, Fails κ → ¬ (stmt κ.1).Language)
    (H : ∀ _κ : D × List (Enc × D), RbrLongfellow.Honest F Cand logw logc)
    (Sat : D × List (Enc × D) → Cand → Prop)
    (Ffam : ∀ κ, RbrSplit.FieldData C F
        (LigeroV1LayerStep.Chal F Equations v7Hash3.params.nw v7Hash3.params.nq)
        (LigeroV1LayerStep.Qry v7Hash3.params.row) Cand Witness nc nv logw logc (H κ) (Sat κ))
    (hexact : ∀ κ, (Ffam κ).Exact)
    (MD : ∀ κ, MsgData C Msg (H κ))
    (hmatch : ∀ κ, Matches V (Ffam κ) (MD κ))
    (hfail : ∀ κ, Fails κ → ∀ cand : Cand, ¬ Sat κ cand)
    (htA : tA ≤ v7Hash3.commitFuel) (htape : 2 * v7Hash3.params.row.n + tA ≤ v7Hash3.tape)
    (hcand : Fintype.card Cand = v7Hash3.cardCand)
    (hD : Fintype.card D = 2 ^ v7Hash3.params.digestBits) :
    ((univ.filter fun ω :
          (Fin v7Hash3.tape → D) × (MPoint D Msg v7Hash3.params.nl v7Hash3.params.rounds → C) =>
        AcceptsAt (v1K (Row.rowValid v7Hash3_valid) dom (Row.hkrow v7Hash3_valid) v7Hash3_openings_pos)
            V codec (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf msgOf
            claimOf (rootStatement rootOf stmt) respOf id ω.1 ω.2 ∧
          Fails ((lfSetup body rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7Hash3.tape
            * (Fintype.card C : ℚ) ^ Fintype.card (MPoint D Msg v7Hash3.params.nl v7Hash3.params.rounds))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) :=
  le_trans
    (row_adaptive_ratio_le_v1 v7Hash3_valid v7Hash3_openings_pos dec V dom stmt respOf body
      rootOf msgOf claimOf hF hfalse H Sat Ffam hexact MD hmatch hfail htA htape hcand hD)
    (v7Hash3_adaptive_rhs_le N)

/-- **v7Hash4 at the compiled Longfellow verifier, against a re-committing prefix-only Fiat–Shamir
prover**: `row_adaptive_ratio_le_v1` at `CertifiedV1.v7Hash4` — the v7 4-attribute hash component (17 layers, 574 sumcheck slots, over `GF(2^128)`; Ligero V1 at `n = 3436`, `k = 490`, 132 openings) — with
`CertifiedV1.v7Hash4_adaptive_rhs_le`: `Pr[AcceptsAt (v1K …) … ∧ Fails] ≤ 2^-115 + N · 2^-116`,
`hlig` and `hright` theorems. -/
theorem v7Hash4_adaptive_compiled_ratio_le
    {codec : Codec Salt (Col F v7Hash4.params.nw v7Hash4.params.nq) D Enc} (dec : RoleDecoders codec)
    (V : Code C F (LigeroV1LayerStep.Chal F Equations v7Hash4.params.nw v7Hash4.params.nq)
      (LigeroV1LayerStep.Qry v7Hash4.params.row) Msg logw logc)
    (dom : LigeroFamily.ReedSolomon.Domain F v7Hash4.params.row.openings v7Hash4.params.q
      v7Hash4.params.row.n)
    (stmt : D → LigeroFamily.ConstraintSystem F v7Hash4.params.nw v7Hash4.params.nq v7Hash4.params.q
      Equations)
    (respOf : Msg → LigeroFamily.Response F v7Hash4.params.row.openings v7Hash4.params.q
      v7Hash4.params.row.n 1)
    (body : TwoOracleTree Enc D (MPoint D Msg v7Hash4.params.nl v7Hash4.params.rounds) C Out tA N)
    (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim v7Hash4.params.row.n Salt
      (Col F v7Hash4.params.nw v7Hash4.params.nq) D)
    {Fails : D × List (Enc × D) → Prop}
    (hF : Fintype.card F = v7Hash4.params.row.fieldSize)
    (hfalse : ∀ κ, Fails κ → ¬ (stmt κ.1).Language)
    (H : ∀ _κ : D × List (Enc × D), RbrLongfellow.Honest F Cand logw logc)
    (Sat : D × List (Enc × D) → Cand → Prop)
    (Ffam : ∀ κ, RbrSplit.FieldData C F
        (LigeroV1LayerStep.Chal F Equations v7Hash4.params.nw v7Hash4.params.nq)
        (LigeroV1LayerStep.Qry v7Hash4.params.row) Cand Witness nc nv logw logc (H κ) (Sat κ))
    (hexact : ∀ κ, (Ffam κ).Exact)
    (MD : ∀ κ, MsgData C Msg (H κ))
    (hmatch : ∀ κ, Matches V (Ffam κ) (MD κ))
    (hfail : ∀ κ, Fails κ → ∀ cand : Cand, ¬ Sat κ cand)
    (htA : tA ≤ v7Hash4.commitFuel) (htape : 2 * v7Hash4.params.row.n + tA ≤ v7Hash4.tape)
    (hcand : Fintype.card Cand = v7Hash4.cardCand)
    (hD : Fintype.card D = 2 ^ v7Hash4.params.digestBits) :
    ((univ.filter fun ω :
          (Fin v7Hash4.tape → D) × (MPoint D Msg v7Hash4.params.nl v7Hash4.params.rounds → C) =>
        AcceptsAt (v1K (Row.rowValid v7Hash4_valid) dom (Row.hkrow v7Hash4_valid) v7Hash4_openings_pos)
            V codec (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf msgOf
            claimOf (rootStatement rootOf stmt) respOf id ω.1 ω.2 ∧
          Fails ((lfSetup body rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7Hash4.tape
            * (Fintype.card C : ℚ) ^ Fintype.card (MPoint D Msg v7Hash4.params.nl v7Hash4.params.rounds))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) :=
  le_trans
    (row_adaptive_ratio_le_v1 v7Hash4_valid v7Hash4_openings_pos dec V dom stmt respOf body
      rootOf msgOf claimOf hF hfalse H Sat Ffam hexact MD hmatch hfail htA htape hcand hD)
    (v7Hash4_adaptive_rhs_le N)

end RowCompiled

/-! ## 4. Two fields, hash side first, compiled verifiers -/

section TwoField

open Lfzk.CompiledLongfellow (Col)
open Lfzk.CompiledLongfellowAdaptive (CompiledSide slice1 slice2)
open Lfzk.TwoFieldV1Rows

variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {D : Type} [Fintype D] [DecidableEq D] [Inhabited D]
variable {Enc X Out : Type} [DecidableEq Enc] [Fintype X]
variable {Fmac : Type} [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {nblk : ℕ}
variable {Cand₁ F₁ Equations₁ Witness₁ Msg₁ : Type} [Fintype Cand₁] [Nonempty Cand₁] [Field F₁]
  [Fintype F₁] [DecidableEq F₁] [SumcheckInterp F₁] [Fintype Equations₁] [DecidableEq Equations₁]
  [DecidableEq Msg₁] [Inhabited Msg₁] [Fintype Msg₁] {nc₁ nv₁ logw₁ logc₁ : ℕ}
variable {Cand₂ F₂ Equations₂ Witness₂ Msg₂ : Type} [Fintype Cand₂] [Nonempty Cand₂] [Field F₂]
  [Fintype F₂] [DecidableEq F₂] [SumcheckInterp F₂] [Fintype Equations₂] [DecidableEq Equations₂]
  [DecidableEq Msg₂] [Inhabited Msg₂] [Fintype Msg₂] {nc₂ nv₂ logw₂ logc₂ : ℕ}
variable {Salt₁ Salt₂ : Type} [Inhabited Salt₁] [Inhabited Salt₂]

/-- **Two-field Longfellow at `v7P256Sha1` (`v7Hash1` hash side first, then `v7Sig`), at the
compiled verifiers, with Fiat–Shamir hash inputs as deployed**: `twofield_adaptive_compiled_ratio_le`
with `TwoFieldV1Rows.v7P256Sha1_adaptive_rhs_le` (via `twofield_rhs_swap`):
`Pr[both accept ∧ av = ro(key point) ∧ no two good witnesses agree] ≤ 2^-115 + N · 2^-116`,
`N` deployed hash queries over all three roles. -/
theorem v7P256Sha1_adaptive_compiled_ratio_le {tA N : ℕ} (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha1.sha.params.nw v7P256Sha1.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha1.ecdsa.params.nw v7P256Sha1.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (L₁ : CompiledSide v7P256Sha1.sha (TwoFieldRowV1.sha_valid v7P256Sha1_valid)
      v7P256Sha1_sha_openings_pos C Cand₁ F₁ Equations₁ Witness₁ Msg₁ nc₁ nv₁ logw₁ logc₁ X dec₁
      Prod.fst)
    (L₂ : CompiledSide v7P256Sha1.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha1_valid)
      v7P256Sha1_ecdsa_openings_pos C Cand₂ F₂ Equations₂ Witness₂ Msg₂ nc₂ nv₂ logw₂ logc₂ X dec₂
      Prod.snd)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl
      v7P256Sha1.ecdsa.params.nl v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7P256Sha1.sha.params.row.n Salt₁
      (Col F₁ v7P256Sha1.sha.params.nw v7P256Sha1.sha.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7P256Sha1.ecdsa.params.row.n Salt₂
      (Col F₂ v7P256Sha1.ecdsa.params.nw v7P256Sha1.ecdsa.params.nq) D)
    (hcand₁ : Fintype.card Cand₁ = v7P256Sha1.sha.cardCand)
    (hcand₂ : Fintype.card Cand₂ = v7P256Sha1.ecdsa.cardCand)
    (hD : Fintype.card D = 2 ^ v7P256Sha1.ecdsa.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : Witness₁ → Fin nblk → Fmac) (common₂ : Witness₂ → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin v7P256Sha1.sha.tape → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds → C) (a : Witness₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      CompiledSide.accepts L₁ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁
        avOf pubOf (slice1 v7P256Sha1.sha v7P256Sha1.ecdsa) mt ro →
      L₁.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin v7P256Sha1.sha.tape → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds → C) (a : Witness₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      CompiledSide.accepts L₂ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂
        avOf pubOf (slice2 v7P256Sha1.sha v7P256Sha1.ecdsa) mt ro →
      L₂.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₂ a) = tagOf (S.proof mt ro))
    (htA : tA ≤ 2 ^ 60)
    (htape : 2 * v7P256Sha1.ecdsa.params.row.n + 2 * v7P256Sha1.sha.params.row.n + tA ≤ 2 ^ 62) :
    ((univ.filter fun ω : (Fin v7P256Sha1.sha.tape → D) ×
          (Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
            v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds → C) =>
        CompiledSide.accepts L₁ (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 v7P256Sha1.sha v7P256Sha1.ecdsa) ω.1 ω.2 ∧
          CompiledSide.accepts L₂ (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 v7P256Sha1.sha v7P256Sha1.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            L₁.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf pubOf
              ω.1 ω.2) a₁ ∧
            L₂.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf pubOf
              ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7P256Sha1.sha.tape * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
              v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) := by
  have hv := v7P256Sha1_valid
  refine le_trans
    (twofield_adaptive_compiled_ratio_le (TwoFieldRowV1.sha_valid hv)
      (TwoFieldRowV1.ecdsa_valid hv) v7P256Sha1_sha_openings_pos v7P256Sha1_ecdsa_openings_pos
      L₁ L₂ body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂ hcand₁ hcand₂
      (hD.trans (by rw [TwoFieldRowV1.digest_eq hv])) hD aP decode kmac hbal hmac keyB tagOf
      common₁ common₂ hrow₁ hrow₂ htA htA htape (TwoFieldRowV1.tape_eq hv).symm) ?_
  rw [twofield_rhs_swap _ _ _ N (TwoFieldRowV1.tape_eq hv).symm (TwoFieldRowV1.digest_eq hv).symm]
  exact v7P256Sha1_adaptive_rhs_le N hFmac

/-- **Two-field Longfellow at `v7P256Sha2` (`v7Hash2` hash side first, then `v7Sig`), at the
compiled verifiers, with Fiat–Shamir hash inputs as deployed**: `twofield_adaptive_compiled_ratio_le`
with `TwoFieldV1Rows.v7P256Sha2_adaptive_rhs_le` (via `twofield_rhs_swap`):
`Pr[both accept ∧ av = ro(key point) ∧ no two good witnesses agree] ≤ 2^-115 + N · 2^-116`,
`N` deployed hash queries over all three roles. -/
theorem v7P256Sha2_adaptive_compiled_ratio_le {tA N : ℕ} (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha2.sha.params.nw v7P256Sha2.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha2.ecdsa.params.nw v7P256Sha2.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (L₁ : CompiledSide v7P256Sha2.sha (TwoFieldRowV1.sha_valid v7P256Sha2_valid)
      v7P256Sha2_sha_openings_pos C Cand₁ F₁ Equations₁ Witness₁ Msg₁ nc₁ nv₁ logw₁ logc₁ X dec₁
      Prod.fst)
    (L₂ : CompiledSide v7P256Sha2.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha2_valid)
      v7P256Sha2_ecdsa_openings_pos C Cand₂ F₂ Equations₂ Witness₂ Msg₂ nc₂ nv₂ logw₂ logc₂ X dec₂
      Prod.snd)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ v7P256Sha2.sha.params.nl
      v7P256Sha2.ecdsa.params.nl v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7P256Sha2.sha.params.row.n Salt₁
      (Col F₁ v7P256Sha2.sha.params.nw v7P256Sha2.sha.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7P256Sha2.ecdsa.params.row.n Salt₂
      (Col F₂ v7P256Sha2.ecdsa.params.nw v7P256Sha2.ecdsa.params.nq) D)
    (hcand₁ : Fintype.card Cand₁ = v7P256Sha2.sha.cardCand)
    (hcand₂ : Fintype.card Cand₂ = v7P256Sha2.ecdsa.cardCand)
    (hD : Fintype.card D = 2 ^ v7P256Sha2.ecdsa.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : Witness₁ → Fin nblk → Fmac) (common₂ : Witness₂ → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin v7P256Sha2.sha.tape → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds → C) (a : Witness₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      CompiledSide.accepts L₁ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁
        avOf pubOf (slice1 v7P256Sha2.sha v7P256Sha2.ecdsa) mt ro →
      L₁.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin v7P256Sha2.sha.tape → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds → C) (a : Witness₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      CompiledSide.accepts L₂ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂
        avOf pubOf (slice2 v7P256Sha2.sha v7P256Sha2.ecdsa) mt ro →
      L₂.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₂ a) = tagOf (S.proof mt ro))
    (htA : tA ≤ 2 ^ 60)
    (htape : 2 * v7P256Sha2.ecdsa.params.row.n + 2 * v7P256Sha2.sha.params.row.n + tA ≤ 2 ^ 62) :
    ((univ.filter fun ω : (Fin v7P256Sha2.sha.tape → D) ×
          (Pt2 D C X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
            v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds → C) =>
        CompiledSide.accepts L₁ (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 v7P256Sha2.sha v7P256Sha2.ecdsa) ω.1 ω.2 ∧
          CompiledSide.accepts L₂ (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 v7P256Sha2.sha v7P256Sha2.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            L₁.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf pubOf
              ω.1 ω.2) a₁ ∧
            L₂.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf pubOf
              ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7P256Sha2.sha.tape * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
              v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) := by
  have hv := v7P256Sha2_valid
  refine le_trans
    (twofield_adaptive_compiled_ratio_le (TwoFieldRowV1.sha_valid hv)
      (TwoFieldRowV1.ecdsa_valid hv) v7P256Sha2_sha_openings_pos v7P256Sha2_ecdsa_openings_pos
      L₁ L₂ body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂ hcand₁ hcand₂
      (hD.trans (by rw [TwoFieldRowV1.digest_eq hv])) hD aP decode kmac hbal hmac keyB tagOf
      common₁ common₂ hrow₁ hrow₂ htA htA htape (TwoFieldRowV1.tape_eq hv).symm) ?_
  rw [twofield_rhs_swap _ _ _ N (TwoFieldRowV1.tape_eq hv).symm (TwoFieldRowV1.digest_eq hv).symm]
  exact v7P256Sha2_adaptive_rhs_le N hFmac

/-- **Two-field Longfellow at `v7P256Sha3` (`v7Hash3` hash side first, then `v7Sig`), at the
compiled verifiers, with Fiat–Shamir hash inputs as deployed**: `twofield_adaptive_compiled_ratio_le`
with `TwoFieldV1Rows.v7P256Sha3_adaptive_rhs_le` (via `twofield_rhs_swap`):
`Pr[both accept ∧ av = ro(key point) ∧ no two good witnesses agree] ≤ 2^-115 + N · 2^-116`,
`N` deployed hash queries over all three roles. -/
theorem v7P256Sha3_adaptive_compiled_ratio_le {tA N : ℕ} (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha3.sha.params.nw v7P256Sha3.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha3.ecdsa.params.nw v7P256Sha3.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (L₁ : CompiledSide v7P256Sha3.sha (TwoFieldRowV1.sha_valid v7P256Sha3_valid)
      v7P256Sha3_sha_openings_pos C Cand₁ F₁ Equations₁ Witness₁ Msg₁ nc₁ nv₁ logw₁ logc₁ X dec₁
      Prod.fst)
    (L₂ : CompiledSide v7P256Sha3.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha3_valid)
      v7P256Sha3_ecdsa_openings_pos C Cand₂ F₂ Equations₂ Witness₂ Msg₂ nc₂ nv₂ logw₂ logc₂ X dec₂
      Prod.snd)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ v7P256Sha3.sha.params.nl
      v7P256Sha3.ecdsa.params.nl v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7P256Sha3.sha.params.row.n Salt₁
      (Col F₁ v7P256Sha3.sha.params.nw v7P256Sha3.sha.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7P256Sha3.ecdsa.params.row.n Salt₂
      (Col F₂ v7P256Sha3.ecdsa.params.nw v7P256Sha3.ecdsa.params.nq) D)
    (hcand₁ : Fintype.card Cand₁ = v7P256Sha3.sha.cardCand)
    (hcand₂ : Fintype.card Cand₂ = v7P256Sha3.ecdsa.cardCand)
    (hD : Fintype.card D = 2 ^ v7P256Sha3.ecdsa.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : Witness₁ → Fin nblk → Fmac) (common₂ : Witness₂ → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin v7P256Sha3.sha.tape → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds → C) (a : Witness₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      CompiledSide.accepts L₁ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁
        avOf pubOf (slice1 v7P256Sha3.sha v7P256Sha3.ecdsa) mt ro →
      L₁.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin v7P256Sha3.sha.tape → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds → C) (a : Witness₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      CompiledSide.accepts L₂ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂
        avOf pubOf (slice2 v7P256Sha3.sha v7P256Sha3.ecdsa) mt ro →
      L₂.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₂ a) = tagOf (S.proof mt ro))
    (htA : tA ≤ 2 ^ 60)
    (htape : 2 * v7P256Sha3.ecdsa.params.row.n + 2 * v7P256Sha3.sha.params.row.n + tA ≤ 2 ^ 62) :
    ((univ.filter fun ω : (Fin v7P256Sha3.sha.tape → D) ×
          (Pt2 D C X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
            v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds → C) =>
        CompiledSide.accepts L₁ (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 v7P256Sha3.sha v7P256Sha3.ecdsa) ω.1 ω.2 ∧
          CompiledSide.accepts L₂ (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 v7P256Sha3.sha v7P256Sha3.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            L₁.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf pubOf
              ω.1 ω.2) a₁ ∧
            L₂.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf pubOf
              ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7P256Sha3.sha.tape * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
              v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) := by
  have hv := v7P256Sha3_valid
  refine le_trans
    (twofield_adaptive_compiled_ratio_le (TwoFieldRowV1.sha_valid hv)
      (TwoFieldRowV1.ecdsa_valid hv) v7P256Sha3_sha_openings_pos v7P256Sha3_ecdsa_openings_pos
      L₁ L₂ body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂ hcand₁ hcand₂
      (hD.trans (by rw [TwoFieldRowV1.digest_eq hv])) hD aP decode kmac hbal hmac keyB tagOf
      common₁ common₂ hrow₁ hrow₂ htA htA htape (TwoFieldRowV1.tape_eq hv).symm) ?_
  rw [twofield_rhs_swap _ _ _ N (TwoFieldRowV1.tape_eq hv).symm (TwoFieldRowV1.digest_eq hv).symm]
  exact v7P256Sha3_adaptive_rhs_le N hFmac

/-- **Two-field Longfellow at `v7P256Sha4` (`v7Hash4` hash side first, then `v7Sig`), at the
compiled verifiers, with Fiat–Shamir hash inputs as deployed**: `twofield_adaptive_compiled_ratio_le`
with `TwoFieldV1Rows.v7P256Sha4_adaptive_rhs_le` (via `twofield_rhs_swap`):
`Pr[both accept ∧ av = ro(key point) ∧ no two good witnesses agree] ≤ 2^-115 + N · 2^-116`,
`N` deployed hash queries over all three roles. -/
theorem v7P256Sha4_adaptive_compiled_ratio_le {tA N : ℕ} (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha4.sha.params.nw v7P256Sha4.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha4.ecdsa.params.nw v7P256Sha4.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (L₁ : CompiledSide v7P256Sha4.sha (TwoFieldRowV1.sha_valid v7P256Sha4_valid)
      v7P256Sha4_sha_openings_pos C Cand₁ F₁ Equations₁ Witness₁ Msg₁ nc₁ nv₁ logw₁ logc₁ X dec₁
      Prod.fst)
    (L₂ : CompiledSide v7P256Sha4.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha4_valid)
      v7P256Sha4_ecdsa_openings_pos C Cand₂ F₂ Equations₂ Witness₂ Msg₂ nc₂ nv₂ logw₂ logc₂ X dec₂
      Prod.snd)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ v7P256Sha4.sha.params.nl
      v7P256Sha4.ecdsa.params.nl v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7P256Sha4.sha.params.row.n Salt₁
      (Col F₁ v7P256Sha4.sha.params.nw v7P256Sha4.sha.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7P256Sha4.ecdsa.params.row.n Salt₂
      (Col F₂ v7P256Sha4.ecdsa.params.nw v7P256Sha4.ecdsa.params.nq) D)
    (hcand₁ : Fintype.card Cand₁ = v7P256Sha4.sha.cardCand)
    (hcand₂ : Fintype.card Cand₂ = v7P256Sha4.ecdsa.cardCand)
    (hD : Fintype.card D = 2 ^ v7P256Sha4.ecdsa.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : Witness₁ → Fin nblk → Fmac) (common₂ : Witness₂ → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin v7P256Sha4.sha.tape → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds → C) (a : Witness₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      CompiledSide.accepts L₁ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁
        avOf pubOf (slice1 v7P256Sha4.sha v7P256Sha4.ecdsa) mt ro →
      L₁.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin v7P256Sha4.sha.tape → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds → C) (a : Witness₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      CompiledSide.accepts L₂ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂
        avOf pubOf (slice2 v7P256Sha4.sha v7P256Sha4.ecdsa) mt ro →
      L₂.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₂ a) = tagOf (S.proof mt ro))
    (htA : tA ≤ 2 ^ 60)
    (htape : 2 * v7P256Sha4.ecdsa.params.row.n + 2 * v7P256Sha4.sha.params.row.n + tA ≤ 2 ^ 62) :
    ((univ.filter fun ω : (Fin v7P256Sha4.sha.tape → D) ×
          (Pt2 D C X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
            v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds → C) =>
        CompiledSide.accepts L₁ (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 v7P256Sha4.sha v7P256Sha4.ecdsa) ω.1 ω.2 ∧
          CompiledSide.accepts L₂ (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 v7P256Sha4.sha v7P256Sha4.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            L₁.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf pubOf
              ω.1 ω.2) a₁ ∧
            L₂.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf pubOf
              ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7P256Sha4.sha.tape * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
              v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) := by
  have hv := v7P256Sha4_valid
  refine le_trans
    (twofield_adaptive_compiled_ratio_le (TwoFieldRowV1.sha_valid hv)
      (TwoFieldRowV1.ecdsa_valid hv) v7P256Sha4_sha_openings_pos v7P256Sha4_ecdsa_openings_pos
      L₁ L₂ body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂ hcand₁ hcand₂
      (hD.trans (by rw [TwoFieldRowV1.digest_eq hv])) hD aP decode kmac hbal hmac keyB tagOf
      common₁ common₂ hrow₁ hrow₂ htA htA htape (TwoFieldRowV1.tape_eq hv).symm) ?_
  rw [twofield_rhs_swap _ _ _ N (TwoFieldRowV1.tape_eq hv).symm (TwoFieldRowV1.digest_eq hv).symm]
  exact v7P256Sha4_adaptive_rhs_le N hFmac

end TwoField

end Lfzk.NizkDeployedHashV7
