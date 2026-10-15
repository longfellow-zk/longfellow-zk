import Lfzk.CompiledLongfellowAdaptive
import Lfzk.CertifiedV7
import Lfzk.TwoFieldV7Rows

/-!
# The Longfellow headlines at the deployed v7 parameters

The headline theorems of `Lfzk.CertifiedV1`, `Lfzk.NizkGrinding`, `Lfzk.NizkAdaptive`,
`Lfzk.CompiledLongfellow`, `Lfzk.CompiledLongfellowAdaptive` and `Lfzk.NizkAdaptiveTwoField`,
restated at the deployed v7 rows (`Lfzk.CertifiedV7`, `Lfzk.TwoFieldV7Rows`) instead of the v8 ones.
Each is the corresponding abstract-row theorem (`Row.nizk_ratio_le`, `Row.fs_ratio_le_bound`,
`Row.adaptive_ratio_le`, `CompiledLongfellow.row_fs_ratio_le_v1`,
`CompiledLongfellowAdaptive.row_adaptive_ratio_le_v1`,
`NizkAdaptiveTwoField.twofield_adaptive_ratio_le`,
`CompiledLongfellowAdaptive.twofield_adaptive_compiled_ratio_le`) at the row, followed by the row's
certified right-hand-side numeral; the statements are the v8 ones with the row and the numerals
replaced (restated from the v8 theorems' text), so the premises are
exactly the v8 headlines' (listed in those files' docstrings).

| row | sequential | grinding / re-committing (`≤ 2^-a + N · 2^-b`) |
|---|---|---|
| `v7Sig` | `2^-122` | `a = 122`, `b = 122` |
| `v7Hash1` … `v7Hash4` | `2^-115` | `a = 115`, `b = 116` |
| `v7P256Sha1` … `v7P256Sha4` (two-field) | `2^-115` (`TwoFieldV7Rows`) | `a = 115`, `b = 116` |

(v8: hash `2^-114 + N · 2^-115`, sig `2^-121 + N · 2^-121`, two-field `2^-114 + N · 2^-115`.)

The main headlines are `v7Hash1_adaptive_compiled_ratio_le` … `v7Hash4_…`,
`v7Sig_adaptive_compiled_ratio_le` (the compiled Longfellow verifier against a re-committing
Fiat–Shamir prover, `hlig` and `hright` theorems) and `v7P256Sha1_adaptive_compiled_ratio_le` …
`v7P256Sha4_…` (the two-field composition at the compiled verifiers with a hashed MAC key). What is
still a hypothesis is what `CompiledLongfellowAdaptive`'s module docstring lists: the protocol
instance, `Matches`, `hfalse` (Ligero's extractor), `hfail`, and — two-field — the MAC rows.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.CertifiedV1

open Finset

section Sequential

open Bcs Merkle Merkle.MH Merkle.RandomOracle RbrLongfellow
open scoped Classical

/-- **v7Sig, end to end: `2^-122`.** `Row.nizk_ratio_le` at the v7 signature row (21 layers, 542
sumcheck slots, over P-256's base field, Ligero V1 at `n = 3187`, `k = 455` with 132 opened
columns); the premises are `Row.nizk_ratio_le`'s. -/
theorem v7Sig_nizk_ratio_le
    {C Cand : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
    {F Equations Witness : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype Equations] [DecidableEq Equations]
    {logw logc nc nv : ℕ}
    {H : RbrLongfellow.Honest F Cand logw logc} {Sat : Cand → Prop}
    {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
    {Enc D Salt M Aux Aux' : Type} {n respondFuel revealFuel : ℕ}
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    {codec : Codec Salt M D Enc} (dec : RoleDecoders codec)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (A : Adversary Enc D Salt M Challenge Response Query Aux Aux'
      n v7Sig.commitFuel respondFuel revealFuel)
    (challengeOf :
      (Fin (Rounds.Role.length v7Sig.params.nl v7Sig.params.rounds) → C) → Challenge)
    (queryOf :
      (Fin (Rounds.Role.length v7Sig.params.nl v7Sig.params.rounds) → C) → Query)
    (statement : (Fin v7Sig.tape → D) ×
      (Fin (Rounds.Role.length v7Sig.params.nl v7Sig.params.rounds) → C) → Statement)
    {Fails : (Fin v7Sig.tape → D) → Prop}
    -- the Ligero V1 step: the field, the code's domain, and one instance per commitment
    (hF : Fintype.card F = v7Sig.params.row.fieldSize)
    (dom : LigeroFamily.ReedSolomon.Domain F v7Sig.params.row.openings v7Sig.params.q
      v7Sig.params.row.n)
    (lig : ∀ _pre : Fin v7Sig.tape → D,
      LigeroV1LayerStep.Instance v7Sig.params.row F Equations v7Sig.params.nw
        v7Sig.params.nq v7Sig.params.q)
    (hfalse : ∀ pre : Fin v7Sig.tape → D, Fails pre → ¬ (lig pre).statement.Language)
    -- the field half of LayerStep, one per commitment, with exactly balanced decoders
    (Ffam : ∀ _pre : Fin v7Sig.tape → D,
      RbrSplit.FieldData C F
        (LigeroV1LayerStep.Chal F Equations v7Sig.params.nw v7Sig.params.nq)
        (LigeroV1LayerStep.Qry v7Sig.params.row) Cand Witness nc nv logw logc H Sat)
    (hexact : ∀ pre : Fin v7Sig.tape → D, (Ffam pre).Exact)
    -- extraction, and acceptance
    (hfail : ∀ pre : Fin v7Sig.tape → D, Fails pre → ∀ cand : Cand, ¬ Sat cand)
    (hright : ∀ pre : Fin v7Sig.tape → D, Fails pre →
      ∀ tape : Fin (Rounds.Role.length v7Sig.params.nl v7Sig.params.rounds) → C,
        (CompiledAccepts K A codec (statement (pre, tape))
            (challengeOf tape) (queryOf tape) pre ∧
          ExtractionExplains codec dec n v7Sig.commitFuel (revealFuel + respondFuel)
            v7Sig.tape
            A.commit (A.openingStage (challengeOf tape) (queryOf tape)) pre) →
        RbrSplit.LayerStepAccepts
          (RbrSplit.stepsOf (nl := v7Sig.params.nl) (w := v7Sig.params.rounds)
            (Ffam pre)
            (fun _ _ => LigeroV1LayerStep.accepting (Row.rowValid v7Sig_valid) dom
              (Row.hkrow v7Sig_valid) (lig pre)))
          tape)
    -- the Merkle extractor's fuels
    (ht₁ : v7Sig.commitFuel ≤ v7Sig.tape)
    (hT : 2 * n + (revealFuel + respondFuel) + v7Sig.commitFuel ≤ v7Sig.tape)
    (hT1 : 1 ≤ v7Sig.tape)
    (hcand : Fintype.card Cand = v7Sig.cardCand)
    (hD : Fintype.card D = 2 ^ v7Sig.params.digestBits) :
    ((univ.filter fun omega : (Fin v7Sig.tape → D) ×
          (Fin (Rounds.Role.length v7Sig.params.nl v7Sig.params.rounds) → C) =>
        CompiledAccepts K A codec (statement omega)
            (challengeOf omega.2) (queryOf omega.2) omega.1 ∧ Fails omega.1).card : ℚ)
        / (Fintype.card (Fin v7Sig.tape → D) *
            (Fintype.card C : ℚ) ^
              Rounds.Role.length v7Sig.params.nl v7Sig.params.rounds)
      ≤ (1 : ℚ) / 2 ^ 122 :=
  Row.nizk_ratio_le v7Sig_valid dec K A challengeOf queryOf statement hF dom lig hfalse Ffam
    hexact hfail hright ht₁ hT hT1 hcand hD

/-- **v7Hash1, end to end: `2^-115`.** `Row.nizk_ratio_le` at the v7 1-attribute hash row (17
layers, 566 sumcheck slots, over `GF(2^128)`, Ligero V1 at `n = 3230`, `k = 461` with 132 opened
columns); the premises are `Row.nizk_ratio_le`'s. -/
theorem v7Hash1_nizk_ratio_le
    {C Cand : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
    {F Equations Witness : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype Equations] [DecidableEq Equations]
    {logw logc nc nv : ℕ}
    {H : RbrLongfellow.Honest F Cand logw logc} {Sat : Cand → Prop}
    {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
    {Enc D Salt M Aux Aux' : Type} {n respondFuel revealFuel : ℕ}
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    {codec : Codec Salt M D Enc} (dec : RoleDecoders codec)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (A : Adversary Enc D Salt M Challenge Response Query Aux Aux'
      n v7Hash1.commitFuel respondFuel revealFuel)
    (challengeOf :
      (Fin (Rounds.Role.length v7Hash1.params.nl v7Hash1.params.rounds) → C) → Challenge)
    (queryOf :
      (Fin (Rounds.Role.length v7Hash1.params.nl v7Hash1.params.rounds) → C) → Query)
    (statement : (Fin v7Hash1.tape → D) ×
      (Fin (Rounds.Role.length v7Hash1.params.nl v7Hash1.params.rounds) → C) → Statement)
    {Fails : (Fin v7Hash1.tape → D) → Prop}
    -- the Ligero V1 step: the field, the code's domain, and one instance per commitment
    (hF : Fintype.card F = v7Hash1.params.row.fieldSize)
    (dom : LigeroFamily.ReedSolomon.Domain F v7Hash1.params.row.openings v7Hash1.params.q
      v7Hash1.params.row.n)
    (lig : ∀ _pre : Fin v7Hash1.tape → D,
      LigeroV1LayerStep.Instance v7Hash1.params.row F Equations v7Hash1.params.nw
        v7Hash1.params.nq v7Hash1.params.q)
    (hfalse : ∀ pre : Fin v7Hash1.tape → D, Fails pre → ¬ (lig pre).statement.Language)
    -- the field half of LayerStep, one per commitment, with exactly balanced decoders
    (Ffam : ∀ _pre : Fin v7Hash1.tape → D,
      RbrSplit.FieldData C F
        (LigeroV1LayerStep.Chal F Equations v7Hash1.params.nw v7Hash1.params.nq)
        (LigeroV1LayerStep.Qry v7Hash1.params.row) Cand Witness nc nv logw logc H Sat)
    (hexact : ∀ pre : Fin v7Hash1.tape → D, (Ffam pre).Exact)
    -- extraction, and acceptance
    (hfail : ∀ pre : Fin v7Hash1.tape → D, Fails pre → ∀ cand : Cand, ¬ Sat cand)
    (hright : ∀ pre : Fin v7Hash1.tape → D, Fails pre →
      ∀ tape : Fin (Rounds.Role.length v7Hash1.params.nl v7Hash1.params.rounds) → C,
        (CompiledAccepts K A codec (statement (pre, tape))
            (challengeOf tape) (queryOf tape) pre ∧
          ExtractionExplains codec dec n v7Hash1.commitFuel (revealFuel + respondFuel)
            v7Hash1.tape
            A.commit (A.openingStage (challengeOf tape) (queryOf tape)) pre) →
        RbrSplit.LayerStepAccepts
          (RbrSplit.stepsOf (nl := v7Hash1.params.nl) (w := v7Hash1.params.rounds)
            (Ffam pre)
            (fun _ _ => LigeroV1LayerStep.accepting (Row.rowValid v7Hash1_valid) dom
              (Row.hkrow v7Hash1_valid) (lig pre)))
          tape)
    -- the Merkle extractor's fuels
    (ht₁ : v7Hash1.commitFuel ≤ v7Hash1.tape)
    (hT : 2 * n + (revealFuel + respondFuel) + v7Hash1.commitFuel ≤ v7Hash1.tape)
    (hT1 : 1 ≤ v7Hash1.tape)
    (hcand : Fintype.card Cand = v7Hash1.cardCand)
    (hD : Fintype.card D = 2 ^ v7Hash1.params.digestBits) :
    ((univ.filter fun omega : (Fin v7Hash1.tape → D) ×
          (Fin (Rounds.Role.length v7Hash1.params.nl v7Hash1.params.rounds) → C) =>
        CompiledAccepts K A codec (statement omega)
            (challengeOf omega.2) (queryOf omega.2) omega.1 ∧ Fails omega.1).card : ℚ)
        / (Fintype.card (Fin v7Hash1.tape → D) *
            (Fintype.card C : ℚ) ^
              Rounds.Role.length v7Hash1.params.nl v7Hash1.params.rounds)
      ≤ (1 : ℚ) / 2 ^ 115 :=
  Row.nizk_ratio_le v7Hash1_valid dec K A challengeOf queryOf statement hF dom lig hfalse Ffam
    hexact hfail hright ht₁ hT hT1 hcand hD

/-- **v7Hash2, end to end: `2^-115`.** `Row.nizk_ratio_le` at the v7 2-attribute hash row (17
layers, 570 sumcheck slots, over `GF(2^128)`, Ligero V1 at `n = 3318`, `k = 474` with 132 opened
columns); the premises are `Row.nizk_ratio_le`'s. -/
theorem v7Hash2_nizk_ratio_le
    {C Cand : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
    {F Equations Witness : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype Equations] [DecidableEq Equations]
    {logw logc nc nv : ℕ}
    {H : RbrLongfellow.Honest F Cand logw logc} {Sat : Cand → Prop}
    {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
    {Enc D Salt M Aux Aux' : Type} {n respondFuel revealFuel : ℕ}
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    {codec : Codec Salt M D Enc} (dec : RoleDecoders codec)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (A : Adversary Enc D Salt M Challenge Response Query Aux Aux'
      n v7Hash2.commitFuel respondFuel revealFuel)
    (challengeOf :
      (Fin (Rounds.Role.length v7Hash2.params.nl v7Hash2.params.rounds) → C) → Challenge)
    (queryOf :
      (Fin (Rounds.Role.length v7Hash2.params.nl v7Hash2.params.rounds) → C) → Query)
    (statement : (Fin v7Hash2.tape → D) ×
      (Fin (Rounds.Role.length v7Hash2.params.nl v7Hash2.params.rounds) → C) → Statement)
    {Fails : (Fin v7Hash2.tape → D) → Prop}
    -- the Ligero V1 step: the field, the code's domain, and one instance per commitment
    (hF : Fintype.card F = v7Hash2.params.row.fieldSize)
    (dom : LigeroFamily.ReedSolomon.Domain F v7Hash2.params.row.openings v7Hash2.params.q
      v7Hash2.params.row.n)
    (lig : ∀ _pre : Fin v7Hash2.tape → D,
      LigeroV1LayerStep.Instance v7Hash2.params.row F Equations v7Hash2.params.nw
        v7Hash2.params.nq v7Hash2.params.q)
    (hfalse : ∀ pre : Fin v7Hash2.tape → D, Fails pre → ¬ (lig pre).statement.Language)
    -- the field half of LayerStep, one per commitment, with exactly balanced decoders
    (Ffam : ∀ _pre : Fin v7Hash2.tape → D,
      RbrSplit.FieldData C F
        (LigeroV1LayerStep.Chal F Equations v7Hash2.params.nw v7Hash2.params.nq)
        (LigeroV1LayerStep.Qry v7Hash2.params.row) Cand Witness nc nv logw logc H Sat)
    (hexact : ∀ pre : Fin v7Hash2.tape → D, (Ffam pre).Exact)
    -- extraction, and acceptance
    (hfail : ∀ pre : Fin v7Hash2.tape → D, Fails pre → ∀ cand : Cand, ¬ Sat cand)
    (hright : ∀ pre : Fin v7Hash2.tape → D, Fails pre →
      ∀ tape : Fin (Rounds.Role.length v7Hash2.params.nl v7Hash2.params.rounds) → C,
        (CompiledAccepts K A codec (statement (pre, tape))
            (challengeOf tape) (queryOf tape) pre ∧
          ExtractionExplains codec dec n v7Hash2.commitFuel (revealFuel + respondFuel)
            v7Hash2.tape
            A.commit (A.openingStage (challengeOf tape) (queryOf tape)) pre) →
        RbrSplit.LayerStepAccepts
          (RbrSplit.stepsOf (nl := v7Hash2.params.nl) (w := v7Hash2.params.rounds)
            (Ffam pre)
            (fun _ _ => LigeroV1LayerStep.accepting (Row.rowValid v7Hash2_valid) dom
              (Row.hkrow v7Hash2_valid) (lig pre)))
          tape)
    -- the Merkle extractor's fuels
    (ht₁ : v7Hash2.commitFuel ≤ v7Hash2.tape)
    (hT : 2 * n + (revealFuel + respondFuel) + v7Hash2.commitFuel ≤ v7Hash2.tape)
    (hT1 : 1 ≤ v7Hash2.tape)
    (hcand : Fintype.card Cand = v7Hash2.cardCand)
    (hD : Fintype.card D = 2 ^ v7Hash2.params.digestBits) :
    ((univ.filter fun omega : (Fin v7Hash2.tape → D) ×
          (Fin (Rounds.Role.length v7Hash2.params.nl v7Hash2.params.rounds) → C) =>
        CompiledAccepts K A codec (statement omega)
            (challengeOf omega.2) (queryOf omega.2) omega.1 ∧ Fails omega.1).card : ℚ)
        / (Fintype.card (Fin v7Hash2.tape → D) *
            (Fintype.card C : ℚ) ^
              Rounds.Role.length v7Hash2.params.nl v7Hash2.params.rounds)
      ≤ (1 : ℚ) / 2 ^ 115 :=
  Row.nizk_ratio_le v7Hash2_valid dec K A challengeOf queryOf statement hF dom lig hfalse Ffam
    hexact hfail hright ht₁ hT hT1 hcand hD

/-- **v7Hash3, end to end: `2^-115`.** `Row.nizk_ratio_le` at the v7 3-attribute hash row (17
layers, 574 sumcheck slots, over `GF(2^128)`, Ligero V1 at `n = 3352`, `k = 478` with 132 opened
columns); the premises are `Row.nizk_ratio_le`'s. -/
theorem v7Hash3_nizk_ratio_le
    {C Cand : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
    {F Equations Witness : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype Equations] [DecidableEq Equations]
    {logw logc nc nv : ℕ}
    {H : RbrLongfellow.Honest F Cand logw logc} {Sat : Cand → Prop}
    {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
    {Enc D Salt M Aux Aux' : Type} {n respondFuel revealFuel : ℕ}
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    {codec : Codec Salt M D Enc} (dec : RoleDecoders codec)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (A : Adversary Enc D Salt M Challenge Response Query Aux Aux'
      n v7Hash3.commitFuel respondFuel revealFuel)
    (challengeOf :
      (Fin (Rounds.Role.length v7Hash3.params.nl v7Hash3.params.rounds) → C) → Challenge)
    (queryOf :
      (Fin (Rounds.Role.length v7Hash3.params.nl v7Hash3.params.rounds) → C) → Query)
    (statement : (Fin v7Hash3.tape → D) ×
      (Fin (Rounds.Role.length v7Hash3.params.nl v7Hash3.params.rounds) → C) → Statement)
    {Fails : (Fin v7Hash3.tape → D) → Prop}
    -- the Ligero V1 step: the field, the code's domain, and one instance per commitment
    (hF : Fintype.card F = v7Hash3.params.row.fieldSize)
    (dom : LigeroFamily.ReedSolomon.Domain F v7Hash3.params.row.openings v7Hash3.params.q
      v7Hash3.params.row.n)
    (lig : ∀ _pre : Fin v7Hash3.tape → D,
      LigeroV1LayerStep.Instance v7Hash3.params.row F Equations v7Hash3.params.nw
        v7Hash3.params.nq v7Hash3.params.q)
    (hfalse : ∀ pre : Fin v7Hash3.tape → D, Fails pre → ¬ (lig pre).statement.Language)
    -- the field half of LayerStep, one per commitment, with exactly balanced decoders
    (Ffam : ∀ _pre : Fin v7Hash3.tape → D,
      RbrSplit.FieldData C F
        (LigeroV1LayerStep.Chal F Equations v7Hash3.params.nw v7Hash3.params.nq)
        (LigeroV1LayerStep.Qry v7Hash3.params.row) Cand Witness nc nv logw logc H Sat)
    (hexact : ∀ pre : Fin v7Hash3.tape → D, (Ffam pre).Exact)
    -- extraction, and acceptance
    (hfail : ∀ pre : Fin v7Hash3.tape → D, Fails pre → ∀ cand : Cand, ¬ Sat cand)
    (hright : ∀ pre : Fin v7Hash3.tape → D, Fails pre →
      ∀ tape : Fin (Rounds.Role.length v7Hash3.params.nl v7Hash3.params.rounds) → C,
        (CompiledAccepts K A codec (statement (pre, tape))
            (challengeOf tape) (queryOf tape) pre ∧
          ExtractionExplains codec dec n v7Hash3.commitFuel (revealFuel + respondFuel)
            v7Hash3.tape
            A.commit (A.openingStage (challengeOf tape) (queryOf tape)) pre) →
        RbrSplit.LayerStepAccepts
          (RbrSplit.stepsOf (nl := v7Hash3.params.nl) (w := v7Hash3.params.rounds)
            (Ffam pre)
            (fun _ _ => LigeroV1LayerStep.accepting (Row.rowValid v7Hash3_valid) dom
              (Row.hkrow v7Hash3_valid) (lig pre)))
          tape)
    -- the Merkle extractor's fuels
    (ht₁ : v7Hash3.commitFuel ≤ v7Hash3.tape)
    (hT : 2 * n + (revealFuel + respondFuel) + v7Hash3.commitFuel ≤ v7Hash3.tape)
    (hT1 : 1 ≤ v7Hash3.tape)
    (hcand : Fintype.card Cand = v7Hash3.cardCand)
    (hD : Fintype.card D = 2 ^ v7Hash3.params.digestBits) :
    ((univ.filter fun omega : (Fin v7Hash3.tape → D) ×
          (Fin (Rounds.Role.length v7Hash3.params.nl v7Hash3.params.rounds) → C) =>
        CompiledAccepts K A codec (statement omega)
            (challengeOf omega.2) (queryOf omega.2) omega.1 ∧ Fails omega.1).card : ℚ)
        / (Fintype.card (Fin v7Hash3.tape → D) *
            (Fintype.card C : ℚ) ^
              Rounds.Role.length v7Hash3.params.nl v7Hash3.params.rounds)
      ≤ (1 : ℚ) / 2 ^ 115 :=
  Row.nizk_ratio_le v7Hash3_valid dec K A challengeOf queryOf statement hF dom lig hfalse Ffam
    hexact hfail hright ht₁ hT hT1 hcand hD

/-- **v7Hash4, end to end: `2^-115`.** `Row.nizk_ratio_le` at the v7 4-attribute hash row (17
layers, 574 sumcheck slots, over `GF(2^128)`, Ligero V1 at `n = 3436`, `k = 490` with 132 opened
columns); the premises are `Row.nizk_ratio_le`'s. -/
theorem v7Hash4_nizk_ratio_le
    {C Cand : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
    {F Equations Witness : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype Equations] [DecidableEq Equations]
    {logw logc nc nv : ℕ}
    {H : RbrLongfellow.Honest F Cand logw logc} {Sat : Cand → Prop}
    {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
    {Enc D Salt M Aux Aux' : Type} {n respondFuel revealFuel : ℕ}
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    {codec : Codec Salt M D Enc} (dec : RoleDecoders codec)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (A : Adversary Enc D Salt M Challenge Response Query Aux Aux'
      n v7Hash4.commitFuel respondFuel revealFuel)
    (challengeOf :
      (Fin (Rounds.Role.length v7Hash4.params.nl v7Hash4.params.rounds) → C) → Challenge)
    (queryOf :
      (Fin (Rounds.Role.length v7Hash4.params.nl v7Hash4.params.rounds) → C) → Query)
    (statement : (Fin v7Hash4.tape → D) ×
      (Fin (Rounds.Role.length v7Hash4.params.nl v7Hash4.params.rounds) → C) → Statement)
    {Fails : (Fin v7Hash4.tape → D) → Prop}
    -- the Ligero V1 step: the field, the code's domain, and one instance per commitment
    (hF : Fintype.card F = v7Hash4.params.row.fieldSize)
    (dom : LigeroFamily.ReedSolomon.Domain F v7Hash4.params.row.openings v7Hash4.params.q
      v7Hash4.params.row.n)
    (lig : ∀ _pre : Fin v7Hash4.tape → D,
      LigeroV1LayerStep.Instance v7Hash4.params.row F Equations v7Hash4.params.nw
        v7Hash4.params.nq v7Hash4.params.q)
    (hfalse : ∀ pre : Fin v7Hash4.tape → D, Fails pre → ¬ (lig pre).statement.Language)
    -- the field half of LayerStep, one per commitment, with exactly balanced decoders
    (Ffam : ∀ _pre : Fin v7Hash4.tape → D,
      RbrSplit.FieldData C F
        (LigeroV1LayerStep.Chal F Equations v7Hash4.params.nw v7Hash4.params.nq)
        (LigeroV1LayerStep.Qry v7Hash4.params.row) Cand Witness nc nv logw logc H Sat)
    (hexact : ∀ pre : Fin v7Hash4.tape → D, (Ffam pre).Exact)
    -- extraction, and acceptance
    (hfail : ∀ pre : Fin v7Hash4.tape → D, Fails pre → ∀ cand : Cand, ¬ Sat cand)
    (hright : ∀ pre : Fin v7Hash4.tape → D, Fails pre →
      ∀ tape : Fin (Rounds.Role.length v7Hash4.params.nl v7Hash4.params.rounds) → C,
        (CompiledAccepts K A codec (statement (pre, tape))
            (challengeOf tape) (queryOf tape) pre ∧
          ExtractionExplains codec dec n v7Hash4.commitFuel (revealFuel + respondFuel)
            v7Hash4.tape
            A.commit (A.openingStage (challengeOf tape) (queryOf tape)) pre) →
        RbrSplit.LayerStepAccepts
          (RbrSplit.stepsOf (nl := v7Hash4.params.nl) (w := v7Hash4.params.rounds)
            (Ffam pre)
            (fun _ _ => LigeroV1LayerStep.accepting (Row.rowValid v7Hash4_valid) dom
              (Row.hkrow v7Hash4_valid) (lig pre)))
          tape)
    -- the Merkle extractor's fuels
    (ht₁ : v7Hash4.commitFuel ≤ v7Hash4.tape)
    (hT : 2 * n + (revealFuel + respondFuel) + v7Hash4.commitFuel ≤ v7Hash4.tape)
    (hT1 : 1 ≤ v7Hash4.tape)
    (hcand : Fintype.card Cand = v7Hash4.cardCand)
    (hD : Fintype.card D = 2 ^ v7Hash4.params.digestBits) :
    ((univ.filter fun omega : (Fin v7Hash4.tape → D) ×
          (Fin (Rounds.Role.length v7Hash4.params.nl v7Hash4.params.rounds) → C) =>
        CompiledAccepts K A codec (statement omega)
            (challengeOf omega.2) (queryOf omega.2) omega.1 ∧ Fails omega.1).card : ℚ)
        / (Fintype.card (Fin v7Hash4.tape → D) *
            (Fintype.card C : ℚ) ^
              Rounds.Role.length v7Hash4.params.nl v7Hash4.params.rounds)
      ≤ (1 : ℚ) / 2 ^ 115 :=
  Row.nizk_ratio_le v7Hash4_valid dec K A challengeOf queryOf statement hF dom lig hfalse Ffam
    hexact hfail hright ht₁ hT hT1 hcand hD

end Sequential

section Grinding

open Bcs Merkle Merkle.MH Merkle.RandomOracle RbrLongfellow Lfzk.NizkGrinding
open scoped Classical

/-- **v7Sig against a grinding Fiat–Shamir adversary**: `2^-122 + N · 2^-122`.
`Row.fs_ratio_le_bound` at the v7 signature row (21 layers, 542 sumcheck slots, over P-256's base
field, Ligero V1 at `n = 3187`, `k = 455` with 132 opened columns), over the hash tape and a
challenge tape of `566 + N` slots; the premises are `Row.fs_ratio_le_bound`'s. -/
theorem v7Sig_fs_ratio_le
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
      n v7Sig.commitFuel respondFuel revealFuel)
    -- the Fiat–Shamir search, run after the commitment, and how its proof is read
    (adv : Aux → Tree (Point Ctx Msg C v7Sig.params.nl v7Sig.params.rounds) C Out N)
    (dflt : C) (ctxOf : Aux → Ctx) (msgOf : Out → ℕ → Msg)
    -- the compiled verifier's Ligero challenge and query, read after the commitment
    (challengeOf : Aux → (Fin (v7Sig.fsLen N) → C) →
      Challenge)
    (queryOf : Aux → (Fin (v7Sig.fsLen N) → C) → Query)
    (statement : (Fin v7Sig.tape → D) ×
      (Fin (v7Sig.fsLen N) → C) → Statement)
    {Fails : (Fin v7Sig.tape → D) → Prop}
    -- the Ligero V1 step: the field, the code's domain, and one instance per commitment
    (hF : Fintype.card F = v7Sig.params.row.fieldSize)
    (dom : LigeroFamily.ReedSolomon.Domain F v7Sig.params.row.openings v7Sig.params.q
      v7Sig.params.row.n)
    (lig : ∀ _pre : Fin v7Sig.tape → D,
      LigeroV1LayerStep.Instance v7Sig.params.row F Equations v7Sig.params.nw
        v7Sig.params.nq v7Sig.params.q)
    (hfalse : ∀ pre : Fin v7Sig.tape → D, Fails pre → ¬ (lig pre).statement.Language)
    -- the field half of LayerStep, one per commitment, with exactly balanced decoders
    (H : ∀ _pre : Fin v7Sig.tape → D, RbrLongfellow.Honest F Cand logw logc)
    (Sat : (Fin v7Sig.tape → D) → Cand → Prop)
    (Ffam : ∀ pre : Fin v7Sig.tape → D,
      RbrSplit.FieldData C F
        (LigeroV1LayerStep.Chal F Equations v7Sig.params.nw v7Sig.params.nq)
        (LigeroV1LayerStep.Qry v7Sig.params.row) Cand Witness nc nv logw logc (H pre) (Sat pre))
    (hexact : ∀ pre : Fin v7Sig.tape → D, (Ffam pre).Exact)
    (MD : ∀ pre : Fin v7Sig.tape → D, MsgData C Msg (H pre))
    -- extraction, and acceptance
    (hfail : ∀ pre : Fin v7Sig.tape → D, Fails pre → ∀ cand : Cand, ¬ Sat pre cand)
    (hright : ∀ pre : Fin v7Sig.tape → D, Fails pre →
      ∀ ct : Fin (v7Sig.fsLen N) → C,
        (CompiledAccepts K A codec (statement (pre, ct))
            (challengeOf (A.auxOf pre) ct) (queryOf (A.auxOf pre) ct) pre ∧
          ExtractionExplains codec dec n v7Sig.commitFuel (revealFuel + respondFuel)
            v7Sig.tape A.commit
            (A.openingStage (challengeOf (A.auxOf pre) ct) (queryOf (A.auxOf pre) ct)) pre) →
        RbrSplit.LayerStepAccepts
          (RbrSplit.stepsOf (nl := v7Sig.params.nl) (w := v7Sig.params.rounds)
            (withMsgs (Ffam pre) (MD pre)
              (msgOf (fsProof (adv (A.auxOf pre)) dflt (ctxOf (A.auxOf pre)) msgOf ct)))
            (fun _ _ => LigeroV1LayerStep.accepting (Row.rowValid v7Sig_valid) dom
              (Row.hkrow v7Sig_valid) (lig pre)))
          (fsChallenges (adv (A.auxOf pre)) dflt (ctxOf (A.auxOf pre)) msgOf ct))
    -- the Merkle extractor's fuels
    (ht₁ : v7Sig.commitFuel ≤ v7Sig.tape)
    (hT : 2 * n + (revealFuel + respondFuel) + v7Sig.commitFuel ≤ v7Sig.tape)
    (hT1 : 1 ≤ v7Sig.tape)
    (hcand : Fintype.card Cand = v7Sig.cardCand)
    (hD : Fintype.card D = 2 ^ v7Sig.params.digestBits) :
    ((univ.filter fun omega : (Fin v7Sig.tape → D) ×
          (Fin (v7Sig.fsLen N) → C) =>
        CompiledAccepts K A codec (statement omega)
            (challengeOf (A.auxOf omega.1) omega.2) (queryOf (A.auxOf omega.1) omega.2) omega.1 ∧
          Fails omega.1).card : ℚ)
        / (Fintype.card (Fin v7Sig.tape → D) *
            (Fintype.card C : ℚ) ^ (v7Sig.fsLen N))
      ≤ (1 : ℚ) / 2 ^ 122 + N * ((1 : ℚ) / 2 ^ 122) :=
  le_trans
    (Row.fs_ratio_le_bound v7Sig_valid dec K A adv dflt ctxOf msgOf challengeOf queryOf
      statement hF dom lig hfalse H Sat Ffam hexact MD hfail hright ht₁ hT hT1 hcand hD)
    (add_le_add (Row.target v7Sig_valid)
      (mul_le_mul_of_nonneg_left v7Sig_fsCoefficient (Nat.cast_nonneg N)))

/-- **v7Hash1 against a grinding Fiat–Shamir adversary**: `2^-115 + N · 2^-116`.
`Row.fs_ratio_le_bound` at the v7 1-attribute hash row (17 layers, 566 sumcheck slots, over
`GF(2^128)`, Ligero V1 at `n = 3230`, `k = 461` with 132 opened columns), over the hash tape and a
challenge tape of `586 + N` slots; the premises are `Row.fs_ratio_le_bound`'s. -/
theorem v7Hash1_fs_ratio_le
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
      n v7Hash1.commitFuel respondFuel revealFuel)
    -- the Fiat–Shamir search, run after the commitment, and how its proof is read
    (adv : Aux → Tree (Point Ctx Msg C v7Hash1.params.nl v7Hash1.params.rounds) C Out N)
    (dflt : C) (ctxOf : Aux → Ctx) (msgOf : Out → ℕ → Msg)
    -- the compiled verifier's Ligero challenge and query, read after the commitment
    (challengeOf : Aux → (Fin (v7Hash1.fsLen N) → C) →
      Challenge)
    (queryOf : Aux → (Fin (v7Hash1.fsLen N) → C) → Query)
    (statement : (Fin v7Hash1.tape → D) ×
      (Fin (v7Hash1.fsLen N) → C) → Statement)
    {Fails : (Fin v7Hash1.tape → D) → Prop}
    -- the Ligero V1 step: the field, the code's domain, and one instance per commitment
    (hF : Fintype.card F = v7Hash1.params.row.fieldSize)
    (dom : LigeroFamily.ReedSolomon.Domain F v7Hash1.params.row.openings v7Hash1.params.q
      v7Hash1.params.row.n)
    (lig : ∀ _pre : Fin v7Hash1.tape → D,
      LigeroV1LayerStep.Instance v7Hash1.params.row F Equations v7Hash1.params.nw
        v7Hash1.params.nq v7Hash1.params.q)
    (hfalse : ∀ pre : Fin v7Hash1.tape → D, Fails pre → ¬ (lig pre).statement.Language)
    -- the field half of LayerStep, one per commitment, with exactly balanced decoders
    (H : ∀ _pre : Fin v7Hash1.tape → D, RbrLongfellow.Honest F Cand logw logc)
    (Sat : (Fin v7Hash1.tape → D) → Cand → Prop)
    (Ffam : ∀ pre : Fin v7Hash1.tape → D,
      RbrSplit.FieldData C F
        (LigeroV1LayerStep.Chal F Equations v7Hash1.params.nw v7Hash1.params.nq)
        (LigeroV1LayerStep.Qry v7Hash1.params.row) Cand Witness nc nv logw logc (H pre) (Sat pre))
    (hexact : ∀ pre : Fin v7Hash1.tape → D, (Ffam pre).Exact)
    (MD : ∀ pre : Fin v7Hash1.tape → D, MsgData C Msg (H pre))
    -- extraction, and acceptance
    (hfail : ∀ pre : Fin v7Hash1.tape → D, Fails pre → ∀ cand : Cand, ¬ Sat pre cand)
    (hright : ∀ pre : Fin v7Hash1.tape → D, Fails pre →
      ∀ ct : Fin (v7Hash1.fsLen N) → C,
        (CompiledAccepts K A codec (statement (pre, ct))
            (challengeOf (A.auxOf pre) ct) (queryOf (A.auxOf pre) ct) pre ∧
          ExtractionExplains codec dec n v7Hash1.commitFuel (revealFuel + respondFuel)
            v7Hash1.tape A.commit
            (A.openingStage (challengeOf (A.auxOf pre) ct) (queryOf (A.auxOf pre) ct)) pre) →
        RbrSplit.LayerStepAccepts
          (RbrSplit.stepsOf (nl := v7Hash1.params.nl) (w := v7Hash1.params.rounds)
            (withMsgs (Ffam pre) (MD pre)
              (msgOf (fsProof (adv (A.auxOf pre)) dflt (ctxOf (A.auxOf pre)) msgOf ct)))
            (fun _ _ => LigeroV1LayerStep.accepting (Row.rowValid v7Hash1_valid) dom
              (Row.hkrow v7Hash1_valid) (lig pre)))
          (fsChallenges (adv (A.auxOf pre)) dflt (ctxOf (A.auxOf pre)) msgOf ct))
    -- the Merkle extractor's fuels
    (ht₁ : v7Hash1.commitFuel ≤ v7Hash1.tape)
    (hT : 2 * n + (revealFuel + respondFuel) + v7Hash1.commitFuel ≤ v7Hash1.tape)
    (hT1 : 1 ≤ v7Hash1.tape)
    (hcand : Fintype.card Cand = v7Hash1.cardCand)
    (hD : Fintype.card D = 2 ^ v7Hash1.params.digestBits) :
    ((univ.filter fun omega : (Fin v7Hash1.tape → D) ×
          (Fin (v7Hash1.fsLen N) → C) =>
        CompiledAccepts K A codec (statement omega)
            (challengeOf (A.auxOf omega.1) omega.2) (queryOf (A.auxOf omega.1) omega.2) omega.1 ∧
          Fails omega.1).card : ℚ)
        / (Fintype.card (Fin v7Hash1.tape → D) *
            (Fintype.card C : ℚ) ^ (v7Hash1.fsLen N))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) :=
  le_trans
    (Row.fs_ratio_le_bound v7Hash1_valid dec K A adv dflt ctxOf msgOf challengeOf queryOf
      statement hF dom lig hfalse H Sat Ffam hexact MD hfail hright ht₁ hT hT1 hcand hD)
    (add_le_add (Row.target v7Hash1_valid)
      (mul_le_mul_of_nonneg_left v7Hash1_fsCoefficient (Nat.cast_nonneg N)))

/-- **v7Hash2 against a grinding Fiat–Shamir adversary**: `2^-115 + N · 2^-116`.
`Row.fs_ratio_le_bound` at the v7 2-attribute hash row (17 layers, 570 sumcheck slots, over
`GF(2^128)`, Ligero V1 at `n = 3318`, `k = 474` with 132 opened columns), over the hash tape and a
challenge tape of `590 + N` slots; the premises are `Row.fs_ratio_le_bound`'s. -/
theorem v7Hash2_fs_ratio_le
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
      n v7Hash2.commitFuel respondFuel revealFuel)
    -- the Fiat–Shamir search, run after the commitment, and how its proof is read
    (adv : Aux → Tree (Point Ctx Msg C v7Hash2.params.nl v7Hash2.params.rounds) C Out N)
    (dflt : C) (ctxOf : Aux → Ctx) (msgOf : Out → ℕ → Msg)
    -- the compiled verifier's Ligero challenge and query, read after the commitment
    (challengeOf : Aux → (Fin (v7Hash2.fsLen N) → C) →
      Challenge)
    (queryOf : Aux → (Fin (v7Hash2.fsLen N) → C) → Query)
    (statement : (Fin v7Hash2.tape → D) ×
      (Fin (v7Hash2.fsLen N) → C) → Statement)
    {Fails : (Fin v7Hash2.tape → D) → Prop}
    -- the Ligero V1 step: the field, the code's domain, and one instance per commitment
    (hF : Fintype.card F = v7Hash2.params.row.fieldSize)
    (dom : LigeroFamily.ReedSolomon.Domain F v7Hash2.params.row.openings v7Hash2.params.q
      v7Hash2.params.row.n)
    (lig : ∀ _pre : Fin v7Hash2.tape → D,
      LigeroV1LayerStep.Instance v7Hash2.params.row F Equations v7Hash2.params.nw
        v7Hash2.params.nq v7Hash2.params.q)
    (hfalse : ∀ pre : Fin v7Hash2.tape → D, Fails pre → ¬ (lig pre).statement.Language)
    -- the field half of LayerStep, one per commitment, with exactly balanced decoders
    (H : ∀ _pre : Fin v7Hash2.tape → D, RbrLongfellow.Honest F Cand logw logc)
    (Sat : (Fin v7Hash2.tape → D) → Cand → Prop)
    (Ffam : ∀ pre : Fin v7Hash2.tape → D,
      RbrSplit.FieldData C F
        (LigeroV1LayerStep.Chal F Equations v7Hash2.params.nw v7Hash2.params.nq)
        (LigeroV1LayerStep.Qry v7Hash2.params.row) Cand Witness nc nv logw logc (H pre) (Sat pre))
    (hexact : ∀ pre : Fin v7Hash2.tape → D, (Ffam pre).Exact)
    (MD : ∀ pre : Fin v7Hash2.tape → D, MsgData C Msg (H pre))
    -- extraction, and acceptance
    (hfail : ∀ pre : Fin v7Hash2.tape → D, Fails pre → ∀ cand : Cand, ¬ Sat pre cand)
    (hright : ∀ pre : Fin v7Hash2.tape → D, Fails pre →
      ∀ ct : Fin (v7Hash2.fsLen N) → C,
        (CompiledAccepts K A codec (statement (pre, ct))
            (challengeOf (A.auxOf pre) ct) (queryOf (A.auxOf pre) ct) pre ∧
          ExtractionExplains codec dec n v7Hash2.commitFuel (revealFuel + respondFuel)
            v7Hash2.tape A.commit
            (A.openingStage (challengeOf (A.auxOf pre) ct) (queryOf (A.auxOf pre) ct)) pre) →
        RbrSplit.LayerStepAccepts
          (RbrSplit.stepsOf (nl := v7Hash2.params.nl) (w := v7Hash2.params.rounds)
            (withMsgs (Ffam pre) (MD pre)
              (msgOf (fsProof (adv (A.auxOf pre)) dflt (ctxOf (A.auxOf pre)) msgOf ct)))
            (fun _ _ => LigeroV1LayerStep.accepting (Row.rowValid v7Hash2_valid) dom
              (Row.hkrow v7Hash2_valid) (lig pre)))
          (fsChallenges (adv (A.auxOf pre)) dflt (ctxOf (A.auxOf pre)) msgOf ct))
    -- the Merkle extractor's fuels
    (ht₁ : v7Hash2.commitFuel ≤ v7Hash2.tape)
    (hT : 2 * n + (revealFuel + respondFuel) + v7Hash2.commitFuel ≤ v7Hash2.tape)
    (hT1 : 1 ≤ v7Hash2.tape)
    (hcand : Fintype.card Cand = v7Hash2.cardCand)
    (hD : Fintype.card D = 2 ^ v7Hash2.params.digestBits) :
    ((univ.filter fun omega : (Fin v7Hash2.tape → D) ×
          (Fin (v7Hash2.fsLen N) → C) =>
        CompiledAccepts K A codec (statement omega)
            (challengeOf (A.auxOf omega.1) omega.2) (queryOf (A.auxOf omega.1) omega.2) omega.1 ∧
          Fails omega.1).card : ℚ)
        / (Fintype.card (Fin v7Hash2.tape → D) *
            (Fintype.card C : ℚ) ^ (v7Hash2.fsLen N))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) :=
  le_trans
    (Row.fs_ratio_le_bound v7Hash2_valid dec K A adv dflt ctxOf msgOf challengeOf queryOf
      statement hF dom lig hfalse H Sat Ffam hexact MD hfail hright ht₁ hT hT1 hcand hD)
    (add_le_add (Row.target v7Hash2_valid)
      (mul_le_mul_of_nonneg_left v7Hash2_fsCoefficient (Nat.cast_nonneg N)))

/-- **v7Hash3 against a grinding Fiat–Shamir adversary**: `2^-115 + N · 2^-116`.
`Row.fs_ratio_le_bound` at the v7 3-attribute hash row (17 layers, 574 sumcheck slots, over
`GF(2^128)`, Ligero V1 at `n = 3352`, `k = 478` with 132 opened columns), over the hash tape and a
challenge tape of `594 + N` slots; the premises are `Row.fs_ratio_le_bound`'s. -/
theorem v7Hash3_fs_ratio_le
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
      n v7Hash3.commitFuel respondFuel revealFuel)
    -- the Fiat–Shamir search, run after the commitment, and how its proof is read
    (adv : Aux → Tree (Point Ctx Msg C v7Hash3.params.nl v7Hash3.params.rounds) C Out N)
    (dflt : C) (ctxOf : Aux → Ctx) (msgOf : Out → ℕ → Msg)
    -- the compiled verifier's Ligero challenge and query, read after the commitment
    (challengeOf : Aux → (Fin (v7Hash3.fsLen N) → C) →
      Challenge)
    (queryOf : Aux → (Fin (v7Hash3.fsLen N) → C) → Query)
    (statement : (Fin v7Hash3.tape → D) ×
      (Fin (v7Hash3.fsLen N) → C) → Statement)
    {Fails : (Fin v7Hash3.tape → D) → Prop}
    -- the Ligero V1 step: the field, the code's domain, and one instance per commitment
    (hF : Fintype.card F = v7Hash3.params.row.fieldSize)
    (dom : LigeroFamily.ReedSolomon.Domain F v7Hash3.params.row.openings v7Hash3.params.q
      v7Hash3.params.row.n)
    (lig : ∀ _pre : Fin v7Hash3.tape → D,
      LigeroV1LayerStep.Instance v7Hash3.params.row F Equations v7Hash3.params.nw
        v7Hash3.params.nq v7Hash3.params.q)
    (hfalse : ∀ pre : Fin v7Hash3.tape → D, Fails pre → ¬ (lig pre).statement.Language)
    -- the field half of LayerStep, one per commitment, with exactly balanced decoders
    (H : ∀ _pre : Fin v7Hash3.tape → D, RbrLongfellow.Honest F Cand logw logc)
    (Sat : (Fin v7Hash3.tape → D) → Cand → Prop)
    (Ffam : ∀ pre : Fin v7Hash3.tape → D,
      RbrSplit.FieldData C F
        (LigeroV1LayerStep.Chal F Equations v7Hash3.params.nw v7Hash3.params.nq)
        (LigeroV1LayerStep.Qry v7Hash3.params.row) Cand Witness nc nv logw logc (H pre) (Sat pre))
    (hexact : ∀ pre : Fin v7Hash3.tape → D, (Ffam pre).Exact)
    (MD : ∀ pre : Fin v7Hash3.tape → D, MsgData C Msg (H pre))
    -- extraction, and acceptance
    (hfail : ∀ pre : Fin v7Hash3.tape → D, Fails pre → ∀ cand : Cand, ¬ Sat pre cand)
    (hright : ∀ pre : Fin v7Hash3.tape → D, Fails pre →
      ∀ ct : Fin (v7Hash3.fsLen N) → C,
        (CompiledAccepts K A codec (statement (pre, ct))
            (challengeOf (A.auxOf pre) ct) (queryOf (A.auxOf pre) ct) pre ∧
          ExtractionExplains codec dec n v7Hash3.commitFuel (revealFuel + respondFuel)
            v7Hash3.tape A.commit
            (A.openingStage (challengeOf (A.auxOf pre) ct) (queryOf (A.auxOf pre) ct)) pre) →
        RbrSplit.LayerStepAccepts
          (RbrSplit.stepsOf (nl := v7Hash3.params.nl) (w := v7Hash3.params.rounds)
            (withMsgs (Ffam pre) (MD pre)
              (msgOf (fsProof (adv (A.auxOf pre)) dflt (ctxOf (A.auxOf pre)) msgOf ct)))
            (fun _ _ => LigeroV1LayerStep.accepting (Row.rowValid v7Hash3_valid) dom
              (Row.hkrow v7Hash3_valid) (lig pre)))
          (fsChallenges (adv (A.auxOf pre)) dflt (ctxOf (A.auxOf pre)) msgOf ct))
    -- the Merkle extractor's fuels
    (ht₁ : v7Hash3.commitFuel ≤ v7Hash3.tape)
    (hT : 2 * n + (revealFuel + respondFuel) + v7Hash3.commitFuel ≤ v7Hash3.tape)
    (hT1 : 1 ≤ v7Hash3.tape)
    (hcand : Fintype.card Cand = v7Hash3.cardCand)
    (hD : Fintype.card D = 2 ^ v7Hash3.params.digestBits) :
    ((univ.filter fun omega : (Fin v7Hash3.tape → D) ×
          (Fin (v7Hash3.fsLen N) → C) =>
        CompiledAccepts K A codec (statement omega)
            (challengeOf (A.auxOf omega.1) omega.2) (queryOf (A.auxOf omega.1) omega.2) omega.1 ∧
          Fails omega.1).card : ℚ)
        / (Fintype.card (Fin v7Hash3.tape → D) *
            (Fintype.card C : ℚ) ^ (v7Hash3.fsLen N))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) :=
  le_trans
    (Row.fs_ratio_le_bound v7Hash3_valid dec K A adv dflt ctxOf msgOf challengeOf queryOf
      statement hF dom lig hfalse H Sat Ffam hexact MD hfail hright ht₁ hT hT1 hcand hD)
    (add_le_add (Row.target v7Hash3_valid)
      (mul_le_mul_of_nonneg_left v7Hash3_fsCoefficient (Nat.cast_nonneg N)))

/-- **v7Hash4 against a grinding Fiat–Shamir adversary**: `2^-115 + N · 2^-116`.
`Row.fs_ratio_le_bound` at the v7 4-attribute hash row (17 layers, 574 sumcheck slots, over
`GF(2^128)`, Ligero V1 at `n = 3436`, `k = 490` with 132 opened columns), over the hash tape and a
challenge tape of `594 + N` slots; the premises are `Row.fs_ratio_le_bound`'s. -/
theorem v7Hash4_fs_ratio_le
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
      n v7Hash4.commitFuel respondFuel revealFuel)
    -- the Fiat–Shamir search, run after the commitment, and how its proof is read
    (adv : Aux → Tree (Point Ctx Msg C v7Hash4.params.nl v7Hash4.params.rounds) C Out N)
    (dflt : C) (ctxOf : Aux → Ctx) (msgOf : Out → ℕ → Msg)
    -- the compiled verifier's Ligero challenge and query, read after the commitment
    (challengeOf : Aux → (Fin (v7Hash4.fsLen N) → C) →
      Challenge)
    (queryOf : Aux → (Fin (v7Hash4.fsLen N) → C) → Query)
    (statement : (Fin v7Hash4.tape → D) ×
      (Fin (v7Hash4.fsLen N) → C) → Statement)
    {Fails : (Fin v7Hash4.tape → D) → Prop}
    -- the Ligero V1 step: the field, the code's domain, and one instance per commitment
    (hF : Fintype.card F = v7Hash4.params.row.fieldSize)
    (dom : LigeroFamily.ReedSolomon.Domain F v7Hash4.params.row.openings v7Hash4.params.q
      v7Hash4.params.row.n)
    (lig : ∀ _pre : Fin v7Hash4.tape → D,
      LigeroV1LayerStep.Instance v7Hash4.params.row F Equations v7Hash4.params.nw
        v7Hash4.params.nq v7Hash4.params.q)
    (hfalse : ∀ pre : Fin v7Hash4.tape → D, Fails pre → ¬ (lig pre).statement.Language)
    -- the field half of LayerStep, one per commitment, with exactly balanced decoders
    (H : ∀ _pre : Fin v7Hash4.tape → D, RbrLongfellow.Honest F Cand logw logc)
    (Sat : (Fin v7Hash4.tape → D) → Cand → Prop)
    (Ffam : ∀ pre : Fin v7Hash4.tape → D,
      RbrSplit.FieldData C F
        (LigeroV1LayerStep.Chal F Equations v7Hash4.params.nw v7Hash4.params.nq)
        (LigeroV1LayerStep.Qry v7Hash4.params.row) Cand Witness nc nv logw logc (H pre) (Sat pre))
    (hexact : ∀ pre : Fin v7Hash4.tape → D, (Ffam pre).Exact)
    (MD : ∀ pre : Fin v7Hash4.tape → D, MsgData C Msg (H pre))
    -- extraction, and acceptance
    (hfail : ∀ pre : Fin v7Hash4.tape → D, Fails pre → ∀ cand : Cand, ¬ Sat pre cand)
    (hright : ∀ pre : Fin v7Hash4.tape → D, Fails pre →
      ∀ ct : Fin (v7Hash4.fsLen N) → C,
        (CompiledAccepts K A codec (statement (pre, ct))
            (challengeOf (A.auxOf pre) ct) (queryOf (A.auxOf pre) ct) pre ∧
          ExtractionExplains codec dec n v7Hash4.commitFuel (revealFuel + respondFuel)
            v7Hash4.tape A.commit
            (A.openingStage (challengeOf (A.auxOf pre) ct) (queryOf (A.auxOf pre) ct)) pre) →
        RbrSplit.LayerStepAccepts
          (RbrSplit.stepsOf (nl := v7Hash4.params.nl) (w := v7Hash4.params.rounds)
            (withMsgs (Ffam pre) (MD pre)
              (msgOf (fsProof (adv (A.auxOf pre)) dflt (ctxOf (A.auxOf pre)) msgOf ct)))
            (fun _ _ => LigeroV1LayerStep.accepting (Row.rowValid v7Hash4_valid) dom
              (Row.hkrow v7Hash4_valid) (lig pre)))
          (fsChallenges (adv (A.auxOf pre)) dflt (ctxOf (A.auxOf pre)) msgOf ct))
    -- the Merkle extractor's fuels
    (ht₁ : v7Hash4.commitFuel ≤ v7Hash4.tape)
    (hT : 2 * n + (revealFuel + respondFuel) + v7Hash4.commitFuel ≤ v7Hash4.tape)
    (hT1 : 1 ≤ v7Hash4.tape)
    (hcand : Fintype.card Cand = v7Hash4.cardCand)
    (hD : Fintype.card D = 2 ^ v7Hash4.params.digestBits) :
    ((univ.filter fun omega : (Fin v7Hash4.tape → D) ×
          (Fin (v7Hash4.fsLen N) → C) =>
        CompiledAccepts K A codec (statement omega)
            (challengeOf (A.auxOf omega.1) omega.2) (queryOf (A.auxOf omega.1) omega.2) omega.1 ∧
          Fails omega.1).card : ℚ)
        / (Fintype.card (Fin v7Hash4.tape → D) *
            (Fintype.card C : ℚ) ^ (v7Hash4.fsLen N))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) :=
  le_trans
    (Row.fs_ratio_le_bound v7Hash4_valid dec K A adv dflt ctxOf msgOf challengeOf queryOf
      statement hF dom lig hfalse H Sat Ffam hexact MD hfail hright ht₁ hT hT1 hcand hD)
    (add_le_add (Row.target v7Hash4_valid)
      (mul_le_mul_of_nonneg_left v7Hash4_fsCoefficient (Nat.cast_nonneg N)))

end Grinding

section Adaptive

open Bcs Bcs.AdaptiveCommit Merkle Merkle.MH Merkle.RandomOracle
  Merkle.RandomOracle.TwoOracleTree RbrLongfellow Lfzk.NizkGrinding Lfzk.NizkAdaptive
open scoped Classical

/-- **v7Sig against a re-committing Fiat–Shamir prover**: `2^-122 + N · 2^-122`.
`Row.adaptive_ratio_le` at the v7 signature row (21 layers, 542 sumcheck slots, over P-256's base
field, Ligero V1 at `n = 3187`, `k = 455` with 132 opened columns), against one adaptive program
making at most `tA ≤ 2^60` Merkle-oracle and `N` challenge-oracle queries, over the Merkle tape
(`2^62` slots) and a challenge tape of `566 + N` slots; the re-commitment term is absorbed by the
certified slack (`v7Sig_adaptive_slack_bound`, `v7Sig_adaptive_slack_coeff`). The premises are
`Row.adaptive_ratio_le`'s. -/
theorem v7Sig_adaptive_ratio_le
    {C Cand : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
    {F Equations Witness : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype Equations] [DecidableEq Equations]
    {logw logc nc nv : ℕ}
    {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
    {Enc D Salt M : Type} {n : ℕ}
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    {Msg Out : Type} [DecidableEq Msg] [Inhabited Msg] {tA N : ℕ}
    {codec : Codec Salt M D Enc} (dec : RoleDecoders codec)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (body : TwoOracleTree Enc D (Point D Msg C v7Sig.params.nl v7Sig.params.rounds) C
      Out tA N)
    (dflt : C) (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
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
    (hright : ∀ (mt : Fin v7Sig.tape → D) (ct : Fin (v7Sig.fsLen N) → C),
      Fails ((lfSetup body dflt rootOf msgOf).context mt ct) →
      JointAccepts K codec (lfSetup body dflt rootOf msgOf) (lfCheck codec claimOf) rootOf claimOf
        statementOf responseOf challengeOf queryOf mt ct →
      (lfSetup body dflt rootOf msgOf).Explains dec id claimOf mt ct →
      RbrSplit.LayerStepAccepts
        (RbrSplit.stepsOf (nl := v7Sig.params.nl) (w := v7Sig.params.rounds)
          (withMsgs (Ffam ((lfSetup body dflt rootOf msgOf).context mt ct))
            (MD ((lfSetup body dflt rootOf msgOf).context mt ct))
            (msgOf ((lfSetup body dflt rootOf msgOf).proof mt ct)))
          (fun m pref => accR ((lfSetup body dflt rootOf msgOf).context mt ct) m pref
            (msgOf ((lfSetup body dflt rootOf msgOf).proof mt ct) m)))
        ((lfSetup body dflt rootOf msgOf).challenges mt ct))
    (htA : tA ≤ v7Sig.commitFuel) (htape : 2 * n + tA ≤ v7Sig.tape)
    (hcand : Fintype.card Cand = v7Sig.cardCand)
    (hD : Fintype.card D = 2 ^ v7Sig.params.digestBits) :
    ((univ.filter fun ω : (Fin v7Sig.tape → D) × (Fin (v7Sig.fsLen N) → C) =>
        JointAccepts K codec (lfSetup body dflt rootOf msgOf) (lfCheck codec claimOf) rootOf
            claimOf statementOf responseOf challengeOf queryOf ω.1 ω.2 ∧
          Fails ((lfSetup body dflt rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7Sig.tape * (Fintype.card C : ℚ) ^ v7Sig.fsLen N)
      ≤ (1 : ℚ) / 2 ^ 122 + N * ((1 : ℚ) / 2 ^ 122) := by
  refine le_trans (Row.adaptive_ratio_le v7Sig_valid dec K body dflt rootOf msgOf claimOf
    statementOf responseOf challengeOf queryOf hF accR hlig H Sat Ffam hexact MD hfail hright
    htA htape hcand hD) ?_
  have hsb := v7Sig_adaptive_slack_bound
  have hsc := v7Sig_adaptive_slack_coeff
  have hsplit : ((v7Sig.tape
        * (Rounds.Role.length v7Sig.params.nl v7Sig.params.rounds + N) : ℕ) : ℚ)
        / 2 ^ v7Sig.params.digestBits
      = ((v7Sig.tape * Rounds.Role.length v7Sig.params.nl v7Sig.params.rounds
          : ℕ) : ℚ) / 2 ^ v7Sig.params.digestBits
        + N * ((v7Sig.tape : ℚ) / 2 ^ v7Sig.params.digestBits) := by
    push_cast
    ring
  rw [hsplit]
  have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg N
  have := mul_le_mul_of_nonneg_left hsc hN
  nlinarith

/-- **v7Hash1 against a re-committing Fiat–Shamir prover**: `2^-115 + N · 2^-116`.
`Row.adaptive_ratio_le` at the v7 1-attribute hash row (17 layers, 566 sumcheck slots, over
`GF(2^128)`, Ligero V1 at `n = 3230`, `k = 461` with 132 opened columns), against one adaptive
program making at most `tA ≤ 2^60` Merkle-oracle and `N` challenge-oracle queries, over the Merkle
tape (`2^62` slots) and a challenge tape of `586 + N` slots; the re-commitment term is absorbed by
the certified slack (`v7Hash1_adaptive_slack_bound`, `v7Hash1_adaptive_slack_coeff`). The premises
are `Row.adaptive_ratio_le`'s. -/
theorem v7Hash1_adaptive_ratio_le
    {C Cand : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
    {F Equations Witness : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype Equations] [DecidableEq Equations]
    {logw logc nc nv : ℕ}
    {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
    {Enc D Salt M : Type} {n : ℕ}
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    {Msg Out : Type} [DecidableEq Msg] [Inhabited Msg] {tA N : ℕ}
    {codec : Codec Salt M D Enc} (dec : RoleDecoders codec)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (body : TwoOracleTree Enc D (Point D Msg C v7Hash1.params.nl v7Hash1.params.rounds) C
      Out tA N)
    (dflt : C) (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
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
    (hright : ∀ (mt : Fin v7Hash1.tape → D) (ct : Fin (v7Hash1.fsLen N) → C),
      Fails ((lfSetup body dflt rootOf msgOf).context mt ct) →
      JointAccepts K codec (lfSetup body dflt rootOf msgOf) (lfCheck codec claimOf) rootOf claimOf
        statementOf responseOf challengeOf queryOf mt ct →
      (lfSetup body dflt rootOf msgOf).Explains dec id claimOf mt ct →
      RbrSplit.LayerStepAccepts
        (RbrSplit.stepsOf (nl := v7Hash1.params.nl) (w := v7Hash1.params.rounds)
          (withMsgs (Ffam ((lfSetup body dflt rootOf msgOf).context mt ct))
            (MD ((lfSetup body dflt rootOf msgOf).context mt ct))
            (msgOf ((lfSetup body dflt rootOf msgOf).proof mt ct)))
          (fun m pref => accR ((lfSetup body dflt rootOf msgOf).context mt ct) m pref
            (msgOf ((lfSetup body dflt rootOf msgOf).proof mt ct) m)))
        ((lfSetup body dflt rootOf msgOf).challenges mt ct))
    (htA : tA ≤ v7Hash1.commitFuel) (htape : 2 * n + tA ≤ v7Hash1.tape)
    (hcand : Fintype.card Cand = v7Hash1.cardCand)
    (hD : Fintype.card D = 2 ^ v7Hash1.params.digestBits) :
    ((univ.filter fun ω : (Fin v7Hash1.tape → D) × (Fin (v7Hash1.fsLen N) → C) =>
        JointAccepts K codec (lfSetup body dflt rootOf msgOf) (lfCheck codec claimOf) rootOf
            claimOf statementOf responseOf challengeOf queryOf ω.1 ω.2 ∧
          Fails ((lfSetup body dflt rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7Hash1.tape * (Fintype.card C : ℚ) ^ v7Hash1.fsLen N)
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) := by
  refine le_trans (Row.adaptive_ratio_le v7Hash1_valid dec K body dflt rootOf msgOf claimOf
    statementOf responseOf challengeOf queryOf hF accR hlig H Sat Ffam hexact MD hfail hright
    htA htape hcand hD) ?_
  have hsb := v7Hash1_adaptive_slack_bound
  have hsc := v7Hash1_adaptive_slack_coeff
  have hsplit : ((v7Hash1.tape
        * (Rounds.Role.length v7Hash1.params.nl v7Hash1.params.rounds + N) : ℕ) : ℚ)
        / 2 ^ v7Hash1.params.digestBits
      = ((v7Hash1.tape * Rounds.Role.length v7Hash1.params.nl v7Hash1.params.rounds
          : ℕ) : ℚ) / 2 ^ v7Hash1.params.digestBits
        + N * ((v7Hash1.tape : ℚ) / 2 ^ v7Hash1.params.digestBits) := by
    push_cast
    ring
  rw [hsplit]
  have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg N
  have := mul_le_mul_of_nonneg_left hsc hN
  nlinarith

/-- **v7Hash2 against a re-committing Fiat–Shamir prover**: `2^-115 + N · 2^-116`.
`Row.adaptive_ratio_le` at the v7 2-attribute hash row (17 layers, 570 sumcheck slots, over
`GF(2^128)`, Ligero V1 at `n = 3318`, `k = 474` with 132 opened columns), against one adaptive
program making at most `tA ≤ 2^60` Merkle-oracle and `N` challenge-oracle queries, over the Merkle
tape (`2^62` slots) and a challenge tape of `590 + N` slots; the re-commitment term is absorbed by
the certified slack (`v7Hash2_adaptive_slack_bound`, `v7Hash2_adaptive_slack_coeff`). The premises
are `Row.adaptive_ratio_le`'s. -/
theorem v7Hash2_adaptive_ratio_le
    {C Cand : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
    {F Equations Witness : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype Equations] [DecidableEq Equations]
    {logw logc nc nv : ℕ}
    {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
    {Enc D Salt M : Type} {n : ℕ}
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    {Msg Out : Type} [DecidableEq Msg] [Inhabited Msg] {tA N : ℕ}
    {codec : Codec Salt M D Enc} (dec : RoleDecoders codec)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (body : TwoOracleTree Enc D (Point D Msg C v7Hash2.params.nl v7Hash2.params.rounds) C
      Out tA N)
    (dflt : C) (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
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
    (hright : ∀ (mt : Fin v7Hash2.tape → D) (ct : Fin (v7Hash2.fsLen N) → C),
      Fails ((lfSetup body dflt rootOf msgOf).context mt ct) →
      JointAccepts K codec (lfSetup body dflt rootOf msgOf) (lfCheck codec claimOf) rootOf claimOf
        statementOf responseOf challengeOf queryOf mt ct →
      (lfSetup body dflt rootOf msgOf).Explains dec id claimOf mt ct →
      RbrSplit.LayerStepAccepts
        (RbrSplit.stepsOf (nl := v7Hash2.params.nl) (w := v7Hash2.params.rounds)
          (withMsgs (Ffam ((lfSetup body dflt rootOf msgOf).context mt ct))
            (MD ((lfSetup body dflt rootOf msgOf).context mt ct))
            (msgOf ((lfSetup body dflt rootOf msgOf).proof mt ct)))
          (fun m pref => accR ((lfSetup body dflt rootOf msgOf).context mt ct) m pref
            (msgOf ((lfSetup body dflt rootOf msgOf).proof mt ct) m)))
        ((lfSetup body dflt rootOf msgOf).challenges mt ct))
    (htA : tA ≤ v7Hash2.commitFuel) (htape : 2 * n + tA ≤ v7Hash2.tape)
    (hcand : Fintype.card Cand = v7Hash2.cardCand)
    (hD : Fintype.card D = 2 ^ v7Hash2.params.digestBits) :
    ((univ.filter fun ω : (Fin v7Hash2.tape → D) × (Fin (v7Hash2.fsLen N) → C) =>
        JointAccepts K codec (lfSetup body dflt rootOf msgOf) (lfCheck codec claimOf) rootOf
            claimOf statementOf responseOf challengeOf queryOf ω.1 ω.2 ∧
          Fails ((lfSetup body dflt rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7Hash2.tape * (Fintype.card C : ℚ) ^ v7Hash2.fsLen N)
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) := by
  refine le_trans (Row.adaptive_ratio_le v7Hash2_valid dec K body dflt rootOf msgOf claimOf
    statementOf responseOf challengeOf queryOf hF accR hlig H Sat Ffam hexact MD hfail hright
    htA htape hcand hD) ?_
  have hsb := v7Hash2_adaptive_slack_bound
  have hsc := v7Hash2_adaptive_slack_coeff
  have hsplit : ((v7Hash2.tape
        * (Rounds.Role.length v7Hash2.params.nl v7Hash2.params.rounds + N) : ℕ) : ℚ)
        / 2 ^ v7Hash2.params.digestBits
      = ((v7Hash2.tape * Rounds.Role.length v7Hash2.params.nl v7Hash2.params.rounds
          : ℕ) : ℚ) / 2 ^ v7Hash2.params.digestBits
        + N * ((v7Hash2.tape : ℚ) / 2 ^ v7Hash2.params.digestBits) := by
    push_cast
    ring
  rw [hsplit]
  have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg N
  have := mul_le_mul_of_nonneg_left hsc hN
  nlinarith

/-- **v7Hash3 against a re-committing Fiat–Shamir prover**: `2^-115 + N · 2^-116`.
`Row.adaptive_ratio_le` at the v7 3-attribute hash row (17 layers, 574 sumcheck slots, over
`GF(2^128)`, Ligero V1 at `n = 3352`, `k = 478` with 132 opened columns), against one adaptive
program making at most `tA ≤ 2^60` Merkle-oracle and `N` challenge-oracle queries, over the Merkle
tape (`2^62` slots) and a challenge tape of `594 + N` slots; the re-commitment term is absorbed by
the certified slack (`v7Hash3_adaptive_slack_bound`, `v7Hash3_adaptive_slack_coeff`). The premises
are `Row.adaptive_ratio_le`'s. -/
theorem v7Hash3_adaptive_ratio_le
    {C Cand : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
    {F Equations Witness : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype Equations] [DecidableEq Equations]
    {logw logc nc nv : ℕ}
    {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
    {Enc D Salt M : Type} {n : ℕ}
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    {Msg Out : Type} [DecidableEq Msg] [Inhabited Msg] {tA N : ℕ}
    {codec : Codec Salt M D Enc} (dec : RoleDecoders codec)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (body : TwoOracleTree Enc D (Point D Msg C v7Hash3.params.nl v7Hash3.params.rounds) C
      Out tA N)
    (dflt : C) (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
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
    (hright : ∀ (mt : Fin v7Hash3.tape → D) (ct : Fin (v7Hash3.fsLen N) → C),
      Fails ((lfSetup body dflt rootOf msgOf).context mt ct) →
      JointAccepts K codec (lfSetup body dflt rootOf msgOf) (lfCheck codec claimOf) rootOf claimOf
        statementOf responseOf challengeOf queryOf mt ct →
      (lfSetup body dflt rootOf msgOf).Explains dec id claimOf mt ct →
      RbrSplit.LayerStepAccepts
        (RbrSplit.stepsOf (nl := v7Hash3.params.nl) (w := v7Hash3.params.rounds)
          (withMsgs (Ffam ((lfSetup body dflt rootOf msgOf).context mt ct))
            (MD ((lfSetup body dflt rootOf msgOf).context mt ct))
            (msgOf ((lfSetup body dflt rootOf msgOf).proof mt ct)))
          (fun m pref => accR ((lfSetup body dflt rootOf msgOf).context mt ct) m pref
            (msgOf ((lfSetup body dflt rootOf msgOf).proof mt ct) m)))
        ((lfSetup body dflt rootOf msgOf).challenges mt ct))
    (htA : tA ≤ v7Hash3.commitFuel) (htape : 2 * n + tA ≤ v7Hash3.tape)
    (hcand : Fintype.card Cand = v7Hash3.cardCand)
    (hD : Fintype.card D = 2 ^ v7Hash3.params.digestBits) :
    ((univ.filter fun ω : (Fin v7Hash3.tape → D) × (Fin (v7Hash3.fsLen N) → C) =>
        JointAccepts K codec (lfSetup body dflt rootOf msgOf) (lfCheck codec claimOf) rootOf
            claimOf statementOf responseOf challengeOf queryOf ω.1 ω.2 ∧
          Fails ((lfSetup body dflt rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7Hash3.tape * (Fintype.card C : ℚ) ^ v7Hash3.fsLen N)
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) := by
  refine le_trans (Row.adaptive_ratio_le v7Hash3_valid dec K body dflt rootOf msgOf claimOf
    statementOf responseOf challengeOf queryOf hF accR hlig H Sat Ffam hexact MD hfail hright
    htA htape hcand hD) ?_
  have hsb := v7Hash3_adaptive_slack_bound
  have hsc := v7Hash3_adaptive_slack_coeff
  have hsplit : ((v7Hash3.tape
        * (Rounds.Role.length v7Hash3.params.nl v7Hash3.params.rounds + N) : ℕ) : ℚ)
        / 2 ^ v7Hash3.params.digestBits
      = ((v7Hash3.tape * Rounds.Role.length v7Hash3.params.nl v7Hash3.params.rounds
          : ℕ) : ℚ) / 2 ^ v7Hash3.params.digestBits
        + N * ((v7Hash3.tape : ℚ) / 2 ^ v7Hash3.params.digestBits) := by
    push_cast
    ring
  rw [hsplit]
  have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg N
  have := mul_le_mul_of_nonneg_left hsc hN
  nlinarith

/-- **v7Hash4 against a re-committing Fiat–Shamir prover**: `2^-115 + N · 2^-116`.
`Row.adaptive_ratio_le` at the v7 4-attribute hash row (17 layers, 574 sumcheck slots, over
`GF(2^128)`, Ligero V1 at `n = 3436`, `k = 490` with 132 opened columns), against one adaptive
program making at most `tA ≤ 2^60` Merkle-oracle and `N` challenge-oracle queries, over the Merkle
tape (`2^62` slots) and a challenge tape of `594 + N` slots; the re-commitment term is absorbed by
the certified slack (`v7Hash4_adaptive_slack_bound`, `v7Hash4_adaptive_slack_coeff`). The premises
are `Row.adaptive_ratio_le`'s. -/
theorem v7Hash4_adaptive_ratio_le
    {C Cand : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
    {F Equations Witness : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype Equations] [DecidableEq Equations]
    {logw logc nc nv : ℕ}
    {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
    {Enc D Salt M : Type} {n : ℕ}
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    {Msg Out : Type} [DecidableEq Msg] [Inhabited Msg] {tA N : ℕ}
    {codec : Codec Salt M D Enc} (dec : RoleDecoders codec)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (body : TwoOracleTree Enc D (Point D Msg C v7Hash4.params.nl v7Hash4.params.rounds) C
      Out tA N)
    (dflt : C) (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
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
    (hright : ∀ (mt : Fin v7Hash4.tape → D) (ct : Fin (v7Hash4.fsLen N) → C),
      Fails ((lfSetup body dflt rootOf msgOf).context mt ct) →
      JointAccepts K codec (lfSetup body dflt rootOf msgOf) (lfCheck codec claimOf) rootOf claimOf
        statementOf responseOf challengeOf queryOf mt ct →
      (lfSetup body dflt rootOf msgOf).Explains dec id claimOf mt ct →
      RbrSplit.LayerStepAccepts
        (RbrSplit.stepsOf (nl := v7Hash4.params.nl) (w := v7Hash4.params.rounds)
          (withMsgs (Ffam ((lfSetup body dflt rootOf msgOf).context mt ct))
            (MD ((lfSetup body dflt rootOf msgOf).context mt ct))
            (msgOf ((lfSetup body dflt rootOf msgOf).proof mt ct)))
          (fun m pref => accR ((lfSetup body dflt rootOf msgOf).context mt ct) m pref
            (msgOf ((lfSetup body dflt rootOf msgOf).proof mt ct) m)))
        ((lfSetup body dflt rootOf msgOf).challenges mt ct))
    (htA : tA ≤ v7Hash4.commitFuel) (htape : 2 * n + tA ≤ v7Hash4.tape)
    (hcand : Fintype.card Cand = v7Hash4.cardCand)
    (hD : Fintype.card D = 2 ^ v7Hash4.params.digestBits) :
    ((univ.filter fun ω : (Fin v7Hash4.tape → D) × (Fin (v7Hash4.fsLen N) → C) =>
        JointAccepts K codec (lfSetup body dflt rootOf msgOf) (lfCheck codec claimOf) rootOf
            claimOf statementOf responseOf challengeOf queryOf ω.1 ω.2 ∧
          Fails ((lfSetup body dflt rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7Hash4.tape * (Fintype.card C : ℚ) ^ v7Hash4.fsLen N)
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) := by
  refine le_trans (Row.adaptive_ratio_le v7Hash4_valid dec K body dflt rootOf msgOf claimOf
    statementOf responseOf challengeOf queryOf hF accR hlig H Sat Ffam hexact MD hfail hright
    htA htape hcand hD) ?_
  have hsb := v7Hash4_adaptive_slack_bound
  have hsc := v7Hash4_adaptive_slack_coeff
  have hsplit : ((v7Hash4.tape
        * (Rounds.Role.length v7Hash4.params.nl v7Hash4.params.rounds + N) : ℕ) : ℚ)
        / 2 ^ v7Hash4.params.digestBits
      = ((v7Hash4.tape * Rounds.Role.length v7Hash4.params.nl v7Hash4.params.rounds
          : ℕ) : ℚ) / 2 ^ v7Hash4.params.digestBits
        + N * ((v7Hash4.tape : ℚ) / 2 ^ v7Hash4.params.digestBits) := by
    push_cast
    ring
  rw [hsplit]
  have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg N
  have := mul_le_mul_of_nonneg_left hsc hN
  nlinarith

end Adaptive

end Lfzk.CertifiedV1

namespace Lfzk.CompiledLongfellow

open Finset Bcs Merkle Merkle.MH Merkle.RandomOracle RbrLongfellow Lfzk.NizkGrinding
open scoped Classical

section Row

open Lfzk.CertifiedV1

/-- **v7Sig at the compiled Longfellow verifier, against a grinding Fiat–Shamir adversary**:
`2^-122 + N · 2^-122`. `row_fs_ratio_le_v1` at the v7 signature row (21 layers, 542 sumcheck slots,
over P-256's base field, Ligero V1 at `n = 3187`, `k = 455` with 132 opened columns); the premises
are `row_fs_ratio_le_v1`'s, `hr` discharged. -/
theorem v7Sig_compiled_fs_ratio_le
    {C Cand : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
    {F Equations Witness : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype Equations] [DecidableEq Equations]
    {logw logc nc nv : ℕ}
    {Enc D Salt Aux Aux' : Type} {respondFuel revealFuel : ℕ}
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt]
    {Ctx Msg Out : Type} [DecidableEq Ctx] [DecidableEq Msg] [Inhabited Msg] {N : ℕ}
    {codec : Codec Salt (Col F v7Sig.params.nw v7Sig.params.nq) D Enc}
    (dec : RoleDecoders codec)
    -- the verifier: its field code, the code's domain, and the Ligero statement
    (V : Code C F (LigeroV1LayerStep.Chal F Equations v7Sig.params.nw v7Sig.params.nq)
      (LigeroV1LayerStep.Qry v7Sig.params.row) Msg logw logc)
    (dom : LigeroFamily.ReedSolomon.Domain F v7Sig.params.row.openings v7Sig.params.q
      v7Sig.params.row.n)
    (stmt : (Fin v7Sig.tape → D) →
      LigeroFamily.ConstraintSystem F v7Sig.params.nw v7Sig.params.nq
        v7Sig.params.q Equations)
    -- the Merkle adversary and the Fiat–Shamir search, run after the commitment
    (A : Adversary Enc D Salt (Col F v7Sig.params.nw v7Sig.params.nq)
      (LigeroV1LayerStep.Chal F Equations v7Sig.params.nw v7Sig.params.nq)
      (LigeroFamily.Response F v7Sig.params.row.openings v7Sig.params.q
        v7Sig.params.row.n 1)
      (LigeroV1LayerStep.Qry v7Sig.params.row) Aux Aux' v7Sig.params.row.n
      v7Sig.commitFuel respondFuel revealFuel)
    (adv : Aux → Tree (Point Ctx Msg C v7Sig.params.nl v7Sig.params.rounds) C Out N)
    (dflt : C) (ctxOf : Aux → Ctx) (msgOf : Out → ℕ → Msg)
    {Fails : (Fin v7Sig.tape → D) → Prop}
    (hF : Fintype.card F = v7Sig.params.row.fieldSize)
    (hfalse : ∀ pre : Fin v7Sig.tape → D, Fails pre → ¬ (stmt pre).Language)
    -- the field half of LayerStep, one per commitment, with exactly balanced decoders
    (H : ∀ _pre : Fin v7Sig.tape → D, RbrLongfellow.Honest F Cand logw logc)
    (Sat : (Fin v7Sig.tape → D) → Cand → Prop)
    (Ffam : ∀ pre : Fin v7Sig.tape → D,
      RbrSplit.FieldData C F
        (LigeroV1LayerStep.Chal F Equations v7Sig.params.nw v7Sig.params.nq)
        (LigeroV1LayerStep.Qry v7Sig.params.row) Cand Witness nc nv logw logc (H pre) (Sat pre))
    (hexact : ∀ pre : Fin v7Sig.tape → D, (Ffam pre).Exact)
    (MD : ∀ pre : Fin v7Sig.tape → D, MsgData C Msg (H pre))
    (hmatch : ∀ pre : Fin v7Sig.tape → D, Matches V (Ffam pre) (MD pre))
    (hfail : ∀ pre : Fin v7Sig.tape → D, Fails pre → ∀ cand : Cand, ¬ Sat pre cand)
    -- the Merkle extractor's fuels
    (ht₁ : v7Sig.commitFuel ≤ v7Sig.tape)
    (hT : 2 * v7Sig.params.row.n + (revealFuel + respondFuel) + v7Sig.commitFuel
      ≤ v7Sig.tape)
    (hT1 : 1 ≤ v7Sig.tape)
    (hcand : Fintype.card Cand = v7Sig.cardCand)
    (hD : Fintype.card D = 2 ^ v7Sig.params.digestBits) :
    ((univ.filter fun omega : (Fin v7Sig.tape → D) × (Fin (v7Sig.fsLen N) → C) =>
        Accepts (v1K (Row.rowValid v7Sig_valid) dom (Row.hkrow v7Sig_valid)
            v7Sig_openings_pos) V A codec adv dflt ctxOf msgOf stmt omega ∧
          Fails omega.1).card : ℚ)
        / (Fintype.card (Fin v7Sig.tape → D) *
            (Fintype.card C : ℚ) ^ (v7Sig.fsLen N))
      ≤ (1 : ℚ) / 2 ^ 122 + N * ((1 : ℚ) / 2 ^ 122) :=
  le_trans
    (row_fs_ratio_le_v1 v7Sig_valid v7Sig_openings_pos dec V dom stmt A adv dflt ctxOf
      msgOf hF hfalse H Sat Ffam hexact MD hmatch hfail ht₁ hT hT1 hcand hD)
    (add_le_add (Row.target v7Sig_valid)
      (mul_le_mul_of_nonneg_left v7Sig_fsCoefficient (Nat.cast_nonneg N)))

/-- **v7Hash1 at the compiled Longfellow verifier, against a grinding Fiat–Shamir adversary**:
`2^-115 + N · 2^-116`. `row_fs_ratio_le_v1` at the v7 1-attribute hash row (17 layers, 566 sumcheck
slots, over `GF(2^128)`, Ligero V1 at `n = 3230`, `k = 461` with 132 opened columns); the premises
are `row_fs_ratio_le_v1`'s, `hr` discharged. -/
theorem v7Hash1_compiled_fs_ratio_le
    {C Cand : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
    {F Equations Witness : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype Equations] [DecidableEq Equations]
    {logw logc nc nv : ℕ}
    {Enc D Salt Aux Aux' : Type} {respondFuel revealFuel : ℕ}
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt]
    {Ctx Msg Out : Type} [DecidableEq Ctx] [DecidableEq Msg] [Inhabited Msg] {N : ℕ}
    {codec : Codec Salt (Col F v7Hash1.params.nw v7Hash1.params.nq) D Enc}
    (dec : RoleDecoders codec)
    -- the verifier: its field code, the code's domain, and the Ligero statement
    (V : Code C F (LigeroV1LayerStep.Chal F Equations v7Hash1.params.nw v7Hash1.params.nq)
      (LigeroV1LayerStep.Qry v7Hash1.params.row) Msg logw logc)
    (dom : LigeroFamily.ReedSolomon.Domain F v7Hash1.params.row.openings v7Hash1.params.q
      v7Hash1.params.row.n)
    (stmt : (Fin v7Hash1.tape → D) →
      LigeroFamily.ConstraintSystem F v7Hash1.params.nw v7Hash1.params.nq
        v7Hash1.params.q Equations)
    -- the Merkle adversary and the Fiat–Shamir search, run after the commitment
    (A : Adversary Enc D Salt (Col F v7Hash1.params.nw v7Hash1.params.nq)
      (LigeroV1LayerStep.Chal F Equations v7Hash1.params.nw v7Hash1.params.nq)
      (LigeroFamily.Response F v7Hash1.params.row.openings v7Hash1.params.q
        v7Hash1.params.row.n 1)
      (LigeroV1LayerStep.Qry v7Hash1.params.row) Aux Aux' v7Hash1.params.row.n
      v7Hash1.commitFuel respondFuel revealFuel)
    (adv : Aux → Tree (Point Ctx Msg C v7Hash1.params.nl v7Hash1.params.rounds) C Out N)
    (dflt : C) (ctxOf : Aux → Ctx) (msgOf : Out → ℕ → Msg)
    {Fails : (Fin v7Hash1.tape → D) → Prop}
    (hF : Fintype.card F = v7Hash1.params.row.fieldSize)
    (hfalse : ∀ pre : Fin v7Hash1.tape → D, Fails pre → ¬ (stmt pre).Language)
    -- the field half of LayerStep, one per commitment, with exactly balanced decoders
    (H : ∀ _pre : Fin v7Hash1.tape → D, RbrLongfellow.Honest F Cand logw logc)
    (Sat : (Fin v7Hash1.tape → D) → Cand → Prop)
    (Ffam : ∀ pre : Fin v7Hash1.tape → D,
      RbrSplit.FieldData C F
        (LigeroV1LayerStep.Chal F Equations v7Hash1.params.nw v7Hash1.params.nq)
        (LigeroV1LayerStep.Qry v7Hash1.params.row) Cand Witness nc nv logw logc (H pre) (Sat pre))
    (hexact : ∀ pre : Fin v7Hash1.tape → D, (Ffam pre).Exact)
    (MD : ∀ pre : Fin v7Hash1.tape → D, MsgData C Msg (H pre))
    (hmatch : ∀ pre : Fin v7Hash1.tape → D, Matches V (Ffam pre) (MD pre))
    (hfail : ∀ pre : Fin v7Hash1.tape → D, Fails pre → ∀ cand : Cand, ¬ Sat pre cand)
    -- the Merkle extractor's fuels
    (ht₁ : v7Hash1.commitFuel ≤ v7Hash1.tape)
    (hT : 2 * v7Hash1.params.row.n + (revealFuel + respondFuel) + v7Hash1.commitFuel
      ≤ v7Hash1.tape)
    (hT1 : 1 ≤ v7Hash1.tape)
    (hcand : Fintype.card Cand = v7Hash1.cardCand)
    (hD : Fintype.card D = 2 ^ v7Hash1.params.digestBits) :
    ((univ.filter fun omega : (Fin v7Hash1.tape → D) × (Fin (v7Hash1.fsLen N) → C) =>
        Accepts (v1K (Row.rowValid v7Hash1_valid) dom (Row.hkrow v7Hash1_valid)
            v7Hash1_openings_pos) V A codec adv dflt ctxOf msgOf stmt omega ∧
          Fails omega.1).card : ℚ)
        / (Fintype.card (Fin v7Hash1.tape → D) *
            (Fintype.card C : ℚ) ^ (v7Hash1.fsLen N))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) :=
  le_trans
    (row_fs_ratio_le_v1 v7Hash1_valid v7Hash1_openings_pos dec V dom stmt A adv dflt ctxOf
      msgOf hF hfalse H Sat Ffam hexact MD hmatch hfail ht₁ hT hT1 hcand hD)
    (add_le_add (Row.target v7Hash1_valid)
      (mul_le_mul_of_nonneg_left v7Hash1_fsCoefficient (Nat.cast_nonneg N)))

/-- **v7Hash2 at the compiled Longfellow verifier, against a grinding Fiat–Shamir adversary**:
`2^-115 + N · 2^-116`. `row_fs_ratio_le_v1` at the v7 2-attribute hash row (17 layers, 570 sumcheck
slots, over `GF(2^128)`, Ligero V1 at `n = 3318`, `k = 474` with 132 opened columns); the premises
are `row_fs_ratio_le_v1`'s, `hr` discharged. -/
theorem v7Hash2_compiled_fs_ratio_le
    {C Cand : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
    {F Equations Witness : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype Equations] [DecidableEq Equations]
    {logw logc nc nv : ℕ}
    {Enc D Salt Aux Aux' : Type} {respondFuel revealFuel : ℕ}
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt]
    {Ctx Msg Out : Type} [DecidableEq Ctx] [DecidableEq Msg] [Inhabited Msg] {N : ℕ}
    {codec : Codec Salt (Col F v7Hash2.params.nw v7Hash2.params.nq) D Enc}
    (dec : RoleDecoders codec)
    -- the verifier: its field code, the code's domain, and the Ligero statement
    (V : Code C F (LigeroV1LayerStep.Chal F Equations v7Hash2.params.nw v7Hash2.params.nq)
      (LigeroV1LayerStep.Qry v7Hash2.params.row) Msg logw logc)
    (dom : LigeroFamily.ReedSolomon.Domain F v7Hash2.params.row.openings v7Hash2.params.q
      v7Hash2.params.row.n)
    (stmt : (Fin v7Hash2.tape → D) →
      LigeroFamily.ConstraintSystem F v7Hash2.params.nw v7Hash2.params.nq
        v7Hash2.params.q Equations)
    -- the Merkle adversary and the Fiat–Shamir search, run after the commitment
    (A : Adversary Enc D Salt (Col F v7Hash2.params.nw v7Hash2.params.nq)
      (LigeroV1LayerStep.Chal F Equations v7Hash2.params.nw v7Hash2.params.nq)
      (LigeroFamily.Response F v7Hash2.params.row.openings v7Hash2.params.q
        v7Hash2.params.row.n 1)
      (LigeroV1LayerStep.Qry v7Hash2.params.row) Aux Aux' v7Hash2.params.row.n
      v7Hash2.commitFuel respondFuel revealFuel)
    (adv : Aux → Tree (Point Ctx Msg C v7Hash2.params.nl v7Hash2.params.rounds) C Out N)
    (dflt : C) (ctxOf : Aux → Ctx) (msgOf : Out → ℕ → Msg)
    {Fails : (Fin v7Hash2.tape → D) → Prop}
    (hF : Fintype.card F = v7Hash2.params.row.fieldSize)
    (hfalse : ∀ pre : Fin v7Hash2.tape → D, Fails pre → ¬ (stmt pre).Language)
    -- the field half of LayerStep, one per commitment, with exactly balanced decoders
    (H : ∀ _pre : Fin v7Hash2.tape → D, RbrLongfellow.Honest F Cand logw logc)
    (Sat : (Fin v7Hash2.tape → D) → Cand → Prop)
    (Ffam : ∀ pre : Fin v7Hash2.tape → D,
      RbrSplit.FieldData C F
        (LigeroV1LayerStep.Chal F Equations v7Hash2.params.nw v7Hash2.params.nq)
        (LigeroV1LayerStep.Qry v7Hash2.params.row) Cand Witness nc nv logw logc (H pre) (Sat pre))
    (hexact : ∀ pre : Fin v7Hash2.tape → D, (Ffam pre).Exact)
    (MD : ∀ pre : Fin v7Hash2.tape → D, MsgData C Msg (H pre))
    (hmatch : ∀ pre : Fin v7Hash2.tape → D, Matches V (Ffam pre) (MD pre))
    (hfail : ∀ pre : Fin v7Hash2.tape → D, Fails pre → ∀ cand : Cand, ¬ Sat pre cand)
    -- the Merkle extractor's fuels
    (ht₁ : v7Hash2.commitFuel ≤ v7Hash2.tape)
    (hT : 2 * v7Hash2.params.row.n + (revealFuel + respondFuel) + v7Hash2.commitFuel
      ≤ v7Hash2.tape)
    (hT1 : 1 ≤ v7Hash2.tape)
    (hcand : Fintype.card Cand = v7Hash2.cardCand)
    (hD : Fintype.card D = 2 ^ v7Hash2.params.digestBits) :
    ((univ.filter fun omega : (Fin v7Hash2.tape → D) × (Fin (v7Hash2.fsLen N) → C) =>
        Accepts (v1K (Row.rowValid v7Hash2_valid) dom (Row.hkrow v7Hash2_valid)
            v7Hash2_openings_pos) V A codec adv dflt ctxOf msgOf stmt omega ∧
          Fails omega.1).card : ℚ)
        / (Fintype.card (Fin v7Hash2.tape → D) *
            (Fintype.card C : ℚ) ^ (v7Hash2.fsLen N))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) :=
  le_trans
    (row_fs_ratio_le_v1 v7Hash2_valid v7Hash2_openings_pos dec V dom stmt A adv dflt ctxOf
      msgOf hF hfalse H Sat Ffam hexact MD hmatch hfail ht₁ hT hT1 hcand hD)
    (add_le_add (Row.target v7Hash2_valid)
      (mul_le_mul_of_nonneg_left v7Hash2_fsCoefficient (Nat.cast_nonneg N)))

/-- **v7Hash3 at the compiled Longfellow verifier, against a grinding Fiat–Shamir adversary**:
`2^-115 + N · 2^-116`. `row_fs_ratio_le_v1` at the v7 3-attribute hash row (17 layers, 574 sumcheck
slots, over `GF(2^128)`, Ligero V1 at `n = 3352`, `k = 478` with 132 opened columns); the premises
are `row_fs_ratio_le_v1`'s, `hr` discharged. -/
theorem v7Hash3_compiled_fs_ratio_le
    {C Cand : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
    {F Equations Witness : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype Equations] [DecidableEq Equations]
    {logw logc nc nv : ℕ}
    {Enc D Salt Aux Aux' : Type} {respondFuel revealFuel : ℕ}
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt]
    {Ctx Msg Out : Type} [DecidableEq Ctx] [DecidableEq Msg] [Inhabited Msg] {N : ℕ}
    {codec : Codec Salt (Col F v7Hash3.params.nw v7Hash3.params.nq) D Enc}
    (dec : RoleDecoders codec)
    -- the verifier: its field code, the code's domain, and the Ligero statement
    (V : Code C F (LigeroV1LayerStep.Chal F Equations v7Hash3.params.nw v7Hash3.params.nq)
      (LigeroV1LayerStep.Qry v7Hash3.params.row) Msg logw logc)
    (dom : LigeroFamily.ReedSolomon.Domain F v7Hash3.params.row.openings v7Hash3.params.q
      v7Hash3.params.row.n)
    (stmt : (Fin v7Hash3.tape → D) →
      LigeroFamily.ConstraintSystem F v7Hash3.params.nw v7Hash3.params.nq
        v7Hash3.params.q Equations)
    -- the Merkle adversary and the Fiat–Shamir search, run after the commitment
    (A : Adversary Enc D Salt (Col F v7Hash3.params.nw v7Hash3.params.nq)
      (LigeroV1LayerStep.Chal F Equations v7Hash3.params.nw v7Hash3.params.nq)
      (LigeroFamily.Response F v7Hash3.params.row.openings v7Hash3.params.q
        v7Hash3.params.row.n 1)
      (LigeroV1LayerStep.Qry v7Hash3.params.row) Aux Aux' v7Hash3.params.row.n
      v7Hash3.commitFuel respondFuel revealFuel)
    (adv : Aux → Tree (Point Ctx Msg C v7Hash3.params.nl v7Hash3.params.rounds) C Out N)
    (dflt : C) (ctxOf : Aux → Ctx) (msgOf : Out → ℕ → Msg)
    {Fails : (Fin v7Hash3.tape → D) → Prop}
    (hF : Fintype.card F = v7Hash3.params.row.fieldSize)
    (hfalse : ∀ pre : Fin v7Hash3.tape → D, Fails pre → ¬ (stmt pre).Language)
    -- the field half of LayerStep, one per commitment, with exactly balanced decoders
    (H : ∀ _pre : Fin v7Hash3.tape → D, RbrLongfellow.Honest F Cand logw logc)
    (Sat : (Fin v7Hash3.tape → D) → Cand → Prop)
    (Ffam : ∀ pre : Fin v7Hash3.tape → D,
      RbrSplit.FieldData C F
        (LigeroV1LayerStep.Chal F Equations v7Hash3.params.nw v7Hash3.params.nq)
        (LigeroV1LayerStep.Qry v7Hash3.params.row) Cand Witness nc nv logw logc (H pre) (Sat pre))
    (hexact : ∀ pre : Fin v7Hash3.tape → D, (Ffam pre).Exact)
    (MD : ∀ pre : Fin v7Hash3.tape → D, MsgData C Msg (H pre))
    (hmatch : ∀ pre : Fin v7Hash3.tape → D, Matches V (Ffam pre) (MD pre))
    (hfail : ∀ pre : Fin v7Hash3.tape → D, Fails pre → ∀ cand : Cand, ¬ Sat pre cand)
    -- the Merkle extractor's fuels
    (ht₁ : v7Hash3.commitFuel ≤ v7Hash3.tape)
    (hT : 2 * v7Hash3.params.row.n + (revealFuel + respondFuel) + v7Hash3.commitFuel
      ≤ v7Hash3.tape)
    (hT1 : 1 ≤ v7Hash3.tape)
    (hcand : Fintype.card Cand = v7Hash3.cardCand)
    (hD : Fintype.card D = 2 ^ v7Hash3.params.digestBits) :
    ((univ.filter fun omega : (Fin v7Hash3.tape → D) × (Fin (v7Hash3.fsLen N) → C) =>
        Accepts (v1K (Row.rowValid v7Hash3_valid) dom (Row.hkrow v7Hash3_valid)
            v7Hash3_openings_pos) V A codec adv dflt ctxOf msgOf stmt omega ∧
          Fails omega.1).card : ℚ)
        / (Fintype.card (Fin v7Hash3.tape → D) *
            (Fintype.card C : ℚ) ^ (v7Hash3.fsLen N))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) :=
  le_trans
    (row_fs_ratio_le_v1 v7Hash3_valid v7Hash3_openings_pos dec V dom stmt A adv dflt ctxOf
      msgOf hF hfalse H Sat Ffam hexact MD hmatch hfail ht₁ hT hT1 hcand hD)
    (add_le_add (Row.target v7Hash3_valid)
      (mul_le_mul_of_nonneg_left v7Hash3_fsCoefficient (Nat.cast_nonneg N)))

/-- **v7Hash4 at the compiled Longfellow verifier, against a grinding Fiat–Shamir adversary**:
`2^-115 + N · 2^-116`. `row_fs_ratio_le_v1` at the v7 4-attribute hash row (17 layers, 574 sumcheck
slots, over `GF(2^128)`, Ligero V1 at `n = 3436`, `k = 490` with 132 opened columns); the premises
are `row_fs_ratio_le_v1`'s, `hr` discharged. -/
theorem v7Hash4_compiled_fs_ratio_le
    {C Cand : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
    {F Equations Witness : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype Equations] [DecidableEq Equations]
    {logw logc nc nv : ℕ}
    {Enc D Salt Aux Aux' : Type} {respondFuel revealFuel : ℕ}
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt]
    {Ctx Msg Out : Type} [DecidableEq Ctx] [DecidableEq Msg] [Inhabited Msg] {N : ℕ}
    {codec : Codec Salt (Col F v7Hash4.params.nw v7Hash4.params.nq) D Enc}
    (dec : RoleDecoders codec)
    -- the verifier: its field code, the code's domain, and the Ligero statement
    (V : Code C F (LigeroV1LayerStep.Chal F Equations v7Hash4.params.nw v7Hash4.params.nq)
      (LigeroV1LayerStep.Qry v7Hash4.params.row) Msg logw logc)
    (dom : LigeroFamily.ReedSolomon.Domain F v7Hash4.params.row.openings v7Hash4.params.q
      v7Hash4.params.row.n)
    (stmt : (Fin v7Hash4.tape → D) →
      LigeroFamily.ConstraintSystem F v7Hash4.params.nw v7Hash4.params.nq
        v7Hash4.params.q Equations)
    -- the Merkle adversary and the Fiat–Shamir search, run after the commitment
    (A : Adversary Enc D Salt (Col F v7Hash4.params.nw v7Hash4.params.nq)
      (LigeroV1LayerStep.Chal F Equations v7Hash4.params.nw v7Hash4.params.nq)
      (LigeroFamily.Response F v7Hash4.params.row.openings v7Hash4.params.q
        v7Hash4.params.row.n 1)
      (LigeroV1LayerStep.Qry v7Hash4.params.row) Aux Aux' v7Hash4.params.row.n
      v7Hash4.commitFuel respondFuel revealFuel)
    (adv : Aux → Tree (Point Ctx Msg C v7Hash4.params.nl v7Hash4.params.rounds) C Out N)
    (dflt : C) (ctxOf : Aux → Ctx) (msgOf : Out → ℕ → Msg)
    {Fails : (Fin v7Hash4.tape → D) → Prop}
    (hF : Fintype.card F = v7Hash4.params.row.fieldSize)
    (hfalse : ∀ pre : Fin v7Hash4.tape → D, Fails pre → ¬ (stmt pre).Language)
    -- the field half of LayerStep, one per commitment, with exactly balanced decoders
    (H : ∀ _pre : Fin v7Hash4.tape → D, RbrLongfellow.Honest F Cand logw logc)
    (Sat : (Fin v7Hash4.tape → D) → Cand → Prop)
    (Ffam : ∀ pre : Fin v7Hash4.tape → D,
      RbrSplit.FieldData C F
        (LigeroV1LayerStep.Chal F Equations v7Hash4.params.nw v7Hash4.params.nq)
        (LigeroV1LayerStep.Qry v7Hash4.params.row) Cand Witness nc nv logw logc (H pre) (Sat pre))
    (hexact : ∀ pre : Fin v7Hash4.tape → D, (Ffam pre).Exact)
    (MD : ∀ pre : Fin v7Hash4.tape → D, MsgData C Msg (H pre))
    (hmatch : ∀ pre : Fin v7Hash4.tape → D, Matches V (Ffam pre) (MD pre))
    (hfail : ∀ pre : Fin v7Hash4.tape → D, Fails pre → ∀ cand : Cand, ¬ Sat pre cand)
    -- the Merkle extractor's fuels
    (ht₁ : v7Hash4.commitFuel ≤ v7Hash4.tape)
    (hT : 2 * v7Hash4.params.row.n + (revealFuel + respondFuel) + v7Hash4.commitFuel
      ≤ v7Hash4.tape)
    (hT1 : 1 ≤ v7Hash4.tape)
    (hcand : Fintype.card Cand = v7Hash4.cardCand)
    (hD : Fintype.card D = 2 ^ v7Hash4.params.digestBits) :
    ((univ.filter fun omega : (Fin v7Hash4.tape → D) × (Fin (v7Hash4.fsLen N) → C) =>
        Accepts (v1K (Row.rowValid v7Hash4_valid) dom (Row.hkrow v7Hash4_valid)
            v7Hash4_openings_pos) V A codec adv dflt ctxOf msgOf stmt omega ∧
          Fails omega.1).card : ℚ)
        / (Fintype.card (Fin v7Hash4.tape → D) *
            (Fintype.card C : ℚ) ^ (v7Hash4.fsLen N))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) :=
  le_trans
    (row_fs_ratio_le_v1 v7Hash4_valid v7Hash4_openings_pos dec V dom stmt A adv dflt ctxOf
      msgOf hF hfalse H Sat Ffam hexact MD hmatch hfail ht₁ hT hT1 hcand hD)
    (add_le_add (Row.target v7Hash4_valid)
      (mul_le_mul_of_nonneg_left v7Hash4_fsCoefficient (Nat.cast_nonneg N)))

end Row

end Lfzk.CompiledLongfellow

namespace Lfzk.NizkAdaptiveTwoField

open Finset Bcs Bcs.AdaptiveCommit Merkle Merkle.MH Merkle.RandomOracle
  Merkle.RandomOracle.TwoOracleTree RbrLongfellow Lfzk.NizkGrinding Lfzk.NizkAdaptive
  Lfzk.CertifiedV1 Lfzk.Mac
open scoped Classical
open Lfzk.TwoFieldV1Rows

section Headline

variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {D : Type} [Fintype D] [DecidableEq D] [Inhabited D]
variable {Enc X Out : Type} [DecidableEq Enc]
variable {Fmac : Type} [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {nblk : ℕ}
variable {Cand₁ F₁ Equations₁ Witness₁ Msg₁ : Type} [Fintype Cand₁] [Nonempty Cand₁] [Field F₁]
  [Fintype F₁] [DecidableEq F₁] [SumcheckInterp F₁] [Fintype Equations₁] [DecidableEq Equations₁]
  [Inhabited Msg₁] {nc₁ nv₁ logw₁ logc₁ : ℕ}
variable {Cand₂ F₂ Equations₂ Witness₂ Msg₂ : Type} [Fintype Cand₂] [Nonempty Cand₂] [Field F₂]
  [Fintype F₂] [DecidableEq F₂] [SumcheckInterp F₂] [Fintype Equations₂] [DecidableEq Equations₂]
  [Inhabited Msg₂] {nc₂ nv₂ logw₂ logc₂ : ℕ}
variable {Statement₁ Oracle₁ Challenge₁ Response₁ Query₁ : Type} {Opening₁ : Query₁ → Type}
variable {Statement₂ Oracle₂ Challenge₂ Response₂ Query₂ : Type} {Opening₂ : Query₂ → Type}
variable {Salt₁ M₁ Salt₂ M₂ : Type} [Inhabited Salt₁] [Inhabited M₁] [Inhabited Salt₂]
  [Inhabited M₂] {n₁ n₂ : ℕ}

/-- **Two-field Longfellow at `v7P256Sha1` against one re-committing Fiat–Shamir prover, with a
hashed MAC key**: `2^-115 + N · 2^-116`. `twofield_adaptive_ratio_le` at the v7 signature row and
the v7 1-attribute hash row, over one Merkle tape of `2^62` slots and one challenge tape of
`1153 + N` slots; the premises are `twofield_adaptive_ratio_le`'s. -/
theorem v7P256Sha1_adaptive_ratio_le {tA N : ℕ} (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ M₁ D Enc} (dec₁ : RoleDecoders codec₁)
    {codec₂ : Codec Salt₂ M₂ D Enc} (dec₂ : RoleDecoders codec₂)
    (K₁ : Compiler Statement₁ Oracle₁ Challenge₁ Response₁ Query₁ Opening₁ M₁ n₁)
    (K₂ : Compiler Statement₂ Oracle₂ Challenge₂ Response₂ Query₂ Opening₂ M₂ n₂)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ v7P256Sha1.ecdsa.params.nl
      v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.rounds v7P256Sha1.sha.params.rounds) C Out tA N)
    (dflt : C) (rootOf₁ rootOf₂ : Out → D) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim n₁ Salt₁ M₁ D) (claimOf₂ : Out → OpeningClaim n₂ Salt₂ M₂ D)
    (statementOf₁ : Out → (Fin (len2 v7P256Sha1.ecdsa v7P256Sha1.sha) → C) → Statement₁)
    (responseOf₁ : Out → Response₁)
    (challengeOf₁ : Out → (Fin (len2 v7P256Sha1.ecdsa v7P256Sha1.sha) → C) → Challenge₁)
    (queryOf₁ : Out → (Fin (len2 v7P256Sha1.ecdsa v7P256Sha1.sha) → C) → Query₁)
    (statementOf₂ : Out → (Fin (len2 v7P256Sha1.ecdsa v7P256Sha1.sha) → C) → Statement₂)
    (responseOf₂ : Out → Response₂)
    (challengeOf₂ : Out → (Fin (len2 v7P256Sha1.ecdsa v7P256Sha1.sha) → C) → Challenge₂)
    (queryOf₂ : Out → (Fin (len2 v7P256Sha1.ecdsa v7P256Sha1.sha) → C) → Query₂)
    (S₁ : Side v7P256Sha1.ecdsa (((D × D) × List (Enc × D)) × C × X) C Cand₁ F₁ Equations₁ Witness₁
      Msg₁ nc₁ nv₁ logw₁ logc₁)
    (S₂ : Side v7P256Sha1.sha (((D × D) × List (Enc × D)) × C × X) C Cand₂ F₂ Equations₂ Witness₂
      Msg₂ nc₂ nv₂ logw₂ logc₂)
    (hF₁ : Fintype.card F₁ = v7P256Sha1.ecdsa.params.row.fieldSize)
    (hF₂ : Fintype.card F₂ = v7P256Sha1.sha.params.row.fieldSize)
    (hcand₁ : Fintype.card Cand₁ = v7P256Sha1.ecdsa.cardCand)
    (hcand₂ : Fintype.card Cand₂ = v7P256Sha1.sha.cardCand)
    (hD : Fintype.card D = 2 ^ v7P256Sha1.ecdsa.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : Witness₁ → Fin nblk → Fmac) (common₂ : Witness₂ → Fin nblk → Fmac)
    (hright₁ : ∀ (mt : Fin v7P256Sha1.ecdsa.tape → D)
      (ct : Fin (len2 v7P256Sha1.ecdsa v7P256Sha1.sha + N) → C),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      let σ := (S.context mt ct, S.challenges mt ct ⟨0, by omega⟩, pubOf (S.proof mt ct))
      (∀ cand, ¬ S₁.Sat σ cand) →
      JointAccepts K₁ codec₁ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ claimOf₁
        statementOf₁ responseOf₁ challengeOf₁ queryOf₁ mt ct →
      S.Explains dec₁ Prod.fst claimOf₁ mt ct →
      RbrSplit.LayerStepAccepts
        (RbrSplit.stepsOf (nl := v7P256Sha1.ecdsa.params.nl) (w := v7P256Sha1.ecdsa.params.rounds)
          (withMsgs (S₁.field σ) (S₁.MD σ) (msgOf₁ (S.proof mt ct)))
          (fun m pref => S₁.accR σ m pref (msgOf₁ (S.proof mt ct) m)))
        (fun i => S.challenges mt ct ⟨1 + i.val, by omega⟩))
    (hright₂ : ∀ (mt : Fin v7P256Sha1.ecdsa.tape → D)
      (ct : Fin (len2 v7P256Sha1.ecdsa v7P256Sha1.sha + N) → C),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      let σ := (S.context mt ct, S.challenges mt ct ⟨0, by omega⟩, pubOf (S.proof mt ct))
      (∀ cand, ¬ S₂.Sat σ cand) →
      JointAccepts K₂ codec₂ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂
        statementOf₂ responseOf₂ challengeOf₂ queryOf₂ mt ct →
      S.Explains dec₂ Prod.snd claimOf₂ mt ct →
      RbrSplit.LayerStepAccepts
        (RbrSplit.stepsOf (nl := v7P256Sha1.sha.params.nl) (w := v7P256Sha1.sha.params.rounds)
          (withMsgs (S₂.field σ) (S₂.MD σ) (msgOf₂ (S.proof mt ct)))
          (fun m pref => S₂.accR σ m pref (msgOf₂ (S.proof mt ct) m)))
        (fun i => S.challenges mt ct
          ⟨1 + Rounds.Role.length v7P256Sha1.ecdsa.params.nl v7P256Sha1.ecdsa.params.rounds + i.val,
            by omega⟩))
    (hrow₁ : ∀ (mt : Fin v7P256Sha1.ecdsa.tape → D)
      (ct : Fin (len2 v7P256Sha1.ecdsa v7P256Sha1.sha + N) → C) (a : Witness₁),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      JointAccepts K₁ codec₁ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ claimOf₁
        statementOf₁ responseOf₁ challengeOf₁ queryOf₁ mt ct →
      S₁.Good (S.context mt ct, S.challenges mt ct ⟨0, by omega⟩, pubOf (S.proof mt ct)) a →
      macTag (aP (S.context mt ct) + decode (S.challenges mt ct ⟨0, by omega⟩))
        (keyB (S.proof mt ct)) (common₁ a) = tagOf (S.proof mt ct))
    (hrow₂ : ∀ (mt : Fin v7P256Sha1.ecdsa.tape → D)
      (ct : Fin (len2 v7P256Sha1.ecdsa v7P256Sha1.sha + N) → C) (a : Witness₂),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      JointAccepts K₂ codec₂ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂
        statementOf₂ responseOf₂ challengeOf₂ queryOf₂ mt ct →
      S₂.Good (S.context mt ct, S.challenges mt ct ⟨0, by omega⟩, pubOf (S.proof mt ct)) a →
      macTag (aP (S.context mt ct) + decode (S.challenges mt ct ⟨0, by omega⟩))
        (keyB (S.proof mt ct)) (common₂ a) = tagOf (S.proof mt ct))
    (htA : tA ≤ 2 ^ 60) (htape : 2 * n₂ + 2 * n₁ + tA ≤ 2 ^ 62) :
    ((univ.filter fun ω : (Fin v7P256Sha1.ecdsa.tape → D) ×
          (Fin (len2 v7P256Sha1.ecdsa v7P256Sha1.sha + N) → C) =>
        JointAccepts K₁ codec₁ (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ claimOf₁ statementOf₁ responseOf₁
            challengeOf₁ queryOf₁ ω.1 ω.2 ∧
          JointAccepts K₂ codec₂ (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂ statementOf₂ responseOf₂
            challengeOf₂ queryOf₂ ω.1 ω.2 ∧
          ¬ ∃ a₁ a₂,
            S₁.Good ((setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).context ω.1 ω.2,
              (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
                ⟨0, by omega⟩,
              pubOf ((setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).proof ω.1 ω.2)) a₁ ∧
            S₂.Good ((setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).context ω.1 ω.2,
              (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
                ⟨0, by omega⟩,
              pubOf ((setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).proof ω.1 ω.2)) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7P256Sha1.ecdsa.tape *
            (Fintype.card C : ℚ) ^ (len2 v7P256Sha1.ecdsa v7P256Sha1.sha + N))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) := by
  have hv := v7P256Sha1_valid
  refine le_trans (twofield_adaptive_ratio_le (TwoFieldRowV1.ecdsa_valid hv)
    dec₁ dec₂ K₁ K₂ body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
    claimOf₁ claimOf₂ statementOf₁ responseOf₁ challengeOf₁ queryOf₁ statementOf₂ responseOf₂
    challengeOf₂ queryOf₂ S₁ S₂ hF₁ hF₂ hcand₁ hcand₂ hD hD aP decode kmac hbal hmac keyB tagOf
    common₁ common₂ hright₁ hright₂ hrow₁ hrow₂ htA htA htape rfl) ?_
  have hsb := v7P256Sha1_adaptive_slack_bound
  have hsc := v7P256Sha1_adaptive_slack_coeff
  have hmf : (Fintype.card Fmac : ℚ) = (v7P256Sha1.macFieldSize : ℚ) := by
    rw [hFmac]; rfl
  rw [hmf]
  have hsplit : 2 * (((v7P256Sha1.ecdsa.tape * (len2 v7P256Sha1.ecdsa v7P256Sha1.sha + N) : ℕ) : ℚ)
        / 2 ^ v7P256Sha1.ecdsa.params.digestBits)
      = 2 * (((v7P256Sha1.ecdsa.tape * len2 v7P256Sha1.ecdsa v7P256Sha1.sha : ℕ) : ℚ)
          / 2 ^ v7P256Sha1.ecdsa.params.digestBits)
        + N * (2 * ((v7P256Sha1.ecdsa.tape : ℚ) / 2 ^ v7P256Sha1.ecdsa.params.digestBits)) := by
    push_cast
    ring
  rw [hsplit]
  have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg N
  have := mul_le_mul_of_nonneg_left hsc hN
  nlinarith

/-- **Two-field Longfellow at `v7P256Sha2` against one re-committing Fiat–Shamir prover, with a
hashed MAC key**: `2^-115 + N · 2^-116`. `twofield_adaptive_ratio_le` at the v7 signature row and
the v7 2-attribute hash row, over one Merkle tape of `2^62` slots and one challenge tape of
`1157 + N` slots; the premises are `twofield_adaptive_ratio_le`'s. -/
theorem v7P256Sha2_adaptive_ratio_le {tA N : ℕ} (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ M₁ D Enc} (dec₁ : RoleDecoders codec₁)
    {codec₂ : Codec Salt₂ M₂ D Enc} (dec₂ : RoleDecoders codec₂)
    (K₁ : Compiler Statement₁ Oracle₁ Challenge₁ Response₁ Query₁ Opening₁ M₁ n₁)
    (K₂ : Compiler Statement₂ Oracle₂ Challenge₂ Response₂ Query₂ Opening₂ M₂ n₂)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ v7P256Sha2.ecdsa.params.nl
      v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.rounds v7P256Sha2.sha.params.rounds) C Out tA N)
    (dflt : C) (rootOf₁ rootOf₂ : Out → D) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim n₁ Salt₁ M₁ D) (claimOf₂ : Out → OpeningClaim n₂ Salt₂ M₂ D)
    (statementOf₁ : Out → (Fin (len2 v7P256Sha2.ecdsa v7P256Sha2.sha) → C) → Statement₁)
    (responseOf₁ : Out → Response₁)
    (challengeOf₁ : Out → (Fin (len2 v7P256Sha2.ecdsa v7P256Sha2.sha) → C) → Challenge₁)
    (queryOf₁ : Out → (Fin (len2 v7P256Sha2.ecdsa v7P256Sha2.sha) → C) → Query₁)
    (statementOf₂ : Out → (Fin (len2 v7P256Sha2.ecdsa v7P256Sha2.sha) → C) → Statement₂)
    (responseOf₂ : Out → Response₂)
    (challengeOf₂ : Out → (Fin (len2 v7P256Sha2.ecdsa v7P256Sha2.sha) → C) → Challenge₂)
    (queryOf₂ : Out → (Fin (len2 v7P256Sha2.ecdsa v7P256Sha2.sha) → C) → Query₂)
    (S₁ : Side v7P256Sha2.ecdsa (((D × D) × List (Enc × D)) × C × X) C Cand₁ F₁ Equations₁ Witness₁
      Msg₁ nc₁ nv₁ logw₁ logc₁)
    (S₂ : Side v7P256Sha2.sha (((D × D) × List (Enc × D)) × C × X) C Cand₂ F₂ Equations₂ Witness₂
      Msg₂ nc₂ nv₂ logw₂ logc₂)
    (hF₁ : Fintype.card F₁ = v7P256Sha2.ecdsa.params.row.fieldSize)
    (hF₂ : Fintype.card F₂ = v7P256Sha2.sha.params.row.fieldSize)
    (hcand₁ : Fintype.card Cand₁ = v7P256Sha2.ecdsa.cardCand)
    (hcand₂ : Fintype.card Cand₂ = v7P256Sha2.sha.cardCand)
    (hD : Fintype.card D = 2 ^ v7P256Sha2.ecdsa.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : Witness₁ → Fin nblk → Fmac) (common₂ : Witness₂ → Fin nblk → Fmac)
    (hright₁ : ∀ (mt : Fin v7P256Sha2.ecdsa.tape → D)
      (ct : Fin (len2 v7P256Sha2.ecdsa v7P256Sha2.sha + N) → C),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      let σ := (S.context mt ct, S.challenges mt ct ⟨0, by omega⟩, pubOf (S.proof mt ct))
      (∀ cand, ¬ S₁.Sat σ cand) →
      JointAccepts K₁ codec₁ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ claimOf₁
        statementOf₁ responseOf₁ challengeOf₁ queryOf₁ mt ct →
      S.Explains dec₁ Prod.fst claimOf₁ mt ct →
      RbrSplit.LayerStepAccepts
        (RbrSplit.stepsOf (nl := v7P256Sha2.ecdsa.params.nl) (w := v7P256Sha2.ecdsa.params.rounds)
          (withMsgs (S₁.field σ) (S₁.MD σ) (msgOf₁ (S.proof mt ct)))
          (fun m pref => S₁.accR σ m pref (msgOf₁ (S.proof mt ct) m)))
        (fun i => S.challenges mt ct ⟨1 + i.val, by omega⟩))
    (hright₂ : ∀ (mt : Fin v7P256Sha2.ecdsa.tape → D)
      (ct : Fin (len2 v7P256Sha2.ecdsa v7P256Sha2.sha + N) → C),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      let σ := (S.context mt ct, S.challenges mt ct ⟨0, by omega⟩, pubOf (S.proof mt ct))
      (∀ cand, ¬ S₂.Sat σ cand) →
      JointAccepts K₂ codec₂ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂
        statementOf₂ responseOf₂ challengeOf₂ queryOf₂ mt ct →
      S.Explains dec₂ Prod.snd claimOf₂ mt ct →
      RbrSplit.LayerStepAccepts
        (RbrSplit.stepsOf (nl := v7P256Sha2.sha.params.nl) (w := v7P256Sha2.sha.params.rounds)
          (withMsgs (S₂.field σ) (S₂.MD σ) (msgOf₂ (S.proof mt ct)))
          (fun m pref => S₂.accR σ m pref (msgOf₂ (S.proof mt ct) m)))
        (fun i => S.challenges mt ct
          ⟨1 + Rounds.Role.length v7P256Sha2.ecdsa.params.nl v7P256Sha2.ecdsa.params.rounds + i.val,
            by omega⟩))
    (hrow₁ : ∀ (mt : Fin v7P256Sha2.ecdsa.tape → D)
      (ct : Fin (len2 v7P256Sha2.ecdsa v7P256Sha2.sha + N) → C) (a : Witness₁),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      JointAccepts K₁ codec₁ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ claimOf₁
        statementOf₁ responseOf₁ challengeOf₁ queryOf₁ mt ct →
      S₁.Good (S.context mt ct, S.challenges mt ct ⟨0, by omega⟩, pubOf (S.proof mt ct)) a →
      macTag (aP (S.context mt ct) + decode (S.challenges mt ct ⟨0, by omega⟩))
        (keyB (S.proof mt ct)) (common₁ a) = tagOf (S.proof mt ct))
    (hrow₂ : ∀ (mt : Fin v7P256Sha2.ecdsa.tape → D)
      (ct : Fin (len2 v7P256Sha2.ecdsa v7P256Sha2.sha + N) → C) (a : Witness₂),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      JointAccepts K₂ codec₂ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂
        statementOf₂ responseOf₂ challengeOf₂ queryOf₂ mt ct →
      S₂.Good (S.context mt ct, S.challenges mt ct ⟨0, by omega⟩, pubOf (S.proof mt ct)) a →
      macTag (aP (S.context mt ct) + decode (S.challenges mt ct ⟨0, by omega⟩))
        (keyB (S.proof mt ct)) (common₂ a) = tagOf (S.proof mt ct))
    (htA : tA ≤ 2 ^ 60) (htape : 2 * n₂ + 2 * n₁ + tA ≤ 2 ^ 62) :
    ((univ.filter fun ω : (Fin v7P256Sha2.ecdsa.tape → D) ×
          (Fin (len2 v7P256Sha2.ecdsa v7P256Sha2.sha + N) → C) =>
        JointAccepts K₁ codec₁ (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ claimOf₁ statementOf₁ responseOf₁
            challengeOf₁ queryOf₁ ω.1 ω.2 ∧
          JointAccepts K₂ codec₂ (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂ statementOf₂ responseOf₂
            challengeOf₂ queryOf₂ ω.1 ω.2 ∧
          ¬ ∃ a₁ a₂,
            S₁.Good ((setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).context ω.1 ω.2,
              (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
                ⟨0, by omega⟩,
              pubOf ((setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).proof ω.1 ω.2)) a₁ ∧
            S₂.Good ((setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).context ω.1 ω.2,
              (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
                ⟨0, by omega⟩,
              pubOf ((setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).proof ω.1 ω.2)) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7P256Sha2.ecdsa.tape *
            (Fintype.card C : ℚ) ^ (len2 v7P256Sha2.ecdsa v7P256Sha2.sha + N))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) := by
  have hv := v7P256Sha2_valid
  refine le_trans (twofield_adaptive_ratio_le (TwoFieldRowV1.ecdsa_valid hv)
    dec₁ dec₂ K₁ K₂ body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
    claimOf₁ claimOf₂ statementOf₁ responseOf₁ challengeOf₁ queryOf₁ statementOf₂ responseOf₂
    challengeOf₂ queryOf₂ S₁ S₂ hF₁ hF₂ hcand₁ hcand₂ hD hD aP decode kmac hbal hmac keyB tagOf
    common₁ common₂ hright₁ hright₂ hrow₁ hrow₂ htA htA htape rfl) ?_
  have hsb := v7P256Sha2_adaptive_slack_bound
  have hsc := v7P256Sha2_adaptive_slack_coeff
  have hmf : (Fintype.card Fmac : ℚ) = (v7P256Sha2.macFieldSize : ℚ) := by
    rw [hFmac]; rfl
  rw [hmf]
  have hsplit : 2 * (((v7P256Sha2.ecdsa.tape * (len2 v7P256Sha2.ecdsa v7P256Sha2.sha + N) : ℕ) : ℚ)
        / 2 ^ v7P256Sha2.ecdsa.params.digestBits)
      = 2 * (((v7P256Sha2.ecdsa.tape * len2 v7P256Sha2.ecdsa v7P256Sha2.sha : ℕ) : ℚ)
          / 2 ^ v7P256Sha2.ecdsa.params.digestBits)
        + N * (2 * ((v7P256Sha2.ecdsa.tape : ℚ) / 2 ^ v7P256Sha2.ecdsa.params.digestBits)) := by
    push_cast
    ring
  rw [hsplit]
  have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg N
  have := mul_le_mul_of_nonneg_left hsc hN
  nlinarith

/-- **Two-field Longfellow at `v7P256Sha3` against one re-committing Fiat–Shamir prover, with a
hashed MAC key**: `2^-115 + N · 2^-116`. `twofield_adaptive_ratio_le` at the v7 signature row and
the v7 3-attribute hash row, over one Merkle tape of `2^62` slots and one challenge tape of
`1161 + N` slots; the premises are `twofield_adaptive_ratio_le`'s. -/
theorem v7P256Sha3_adaptive_ratio_le {tA N : ℕ} (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ M₁ D Enc} (dec₁ : RoleDecoders codec₁)
    {codec₂ : Codec Salt₂ M₂ D Enc} (dec₂ : RoleDecoders codec₂)
    (K₁ : Compiler Statement₁ Oracle₁ Challenge₁ Response₁ Query₁ Opening₁ M₁ n₁)
    (K₂ : Compiler Statement₂ Oracle₂ Challenge₂ Response₂ Query₂ Opening₂ M₂ n₂)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ v7P256Sha3.ecdsa.params.nl
      v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.rounds v7P256Sha3.sha.params.rounds) C Out tA N)
    (dflt : C) (rootOf₁ rootOf₂ : Out → D) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim n₁ Salt₁ M₁ D) (claimOf₂ : Out → OpeningClaim n₂ Salt₂ M₂ D)
    (statementOf₁ : Out → (Fin (len2 v7P256Sha3.ecdsa v7P256Sha3.sha) → C) → Statement₁)
    (responseOf₁ : Out → Response₁)
    (challengeOf₁ : Out → (Fin (len2 v7P256Sha3.ecdsa v7P256Sha3.sha) → C) → Challenge₁)
    (queryOf₁ : Out → (Fin (len2 v7P256Sha3.ecdsa v7P256Sha3.sha) → C) → Query₁)
    (statementOf₂ : Out → (Fin (len2 v7P256Sha3.ecdsa v7P256Sha3.sha) → C) → Statement₂)
    (responseOf₂ : Out → Response₂)
    (challengeOf₂ : Out → (Fin (len2 v7P256Sha3.ecdsa v7P256Sha3.sha) → C) → Challenge₂)
    (queryOf₂ : Out → (Fin (len2 v7P256Sha3.ecdsa v7P256Sha3.sha) → C) → Query₂)
    (S₁ : Side v7P256Sha3.ecdsa (((D × D) × List (Enc × D)) × C × X) C Cand₁ F₁ Equations₁ Witness₁
      Msg₁ nc₁ nv₁ logw₁ logc₁)
    (S₂ : Side v7P256Sha3.sha (((D × D) × List (Enc × D)) × C × X) C Cand₂ F₂ Equations₂ Witness₂
      Msg₂ nc₂ nv₂ logw₂ logc₂)
    (hF₁ : Fintype.card F₁ = v7P256Sha3.ecdsa.params.row.fieldSize)
    (hF₂ : Fintype.card F₂ = v7P256Sha3.sha.params.row.fieldSize)
    (hcand₁ : Fintype.card Cand₁ = v7P256Sha3.ecdsa.cardCand)
    (hcand₂ : Fintype.card Cand₂ = v7P256Sha3.sha.cardCand)
    (hD : Fintype.card D = 2 ^ v7P256Sha3.ecdsa.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : Witness₁ → Fin nblk → Fmac) (common₂ : Witness₂ → Fin nblk → Fmac)
    (hright₁ : ∀ (mt : Fin v7P256Sha3.ecdsa.tape → D)
      (ct : Fin (len2 v7P256Sha3.ecdsa v7P256Sha3.sha + N) → C),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      let σ := (S.context mt ct, S.challenges mt ct ⟨0, by omega⟩, pubOf (S.proof mt ct))
      (∀ cand, ¬ S₁.Sat σ cand) →
      JointAccepts K₁ codec₁ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ claimOf₁
        statementOf₁ responseOf₁ challengeOf₁ queryOf₁ mt ct →
      S.Explains dec₁ Prod.fst claimOf₁ mt ct →
      RbrSplit.LayerStepAccepts
        (RbrSplit.stepsOf (nl := v7P256Sha3.ecdsa.params.nl) (w := v7P256Sha3.ecdsa.params.rounds)
          (withMsgs (S₁.field σ) (S₁.MD σ) (msgOf₁ (S.proof mt ct)))
          (fun m pref => S₁.accR σ m pref (msgOf₁ (S.proof mt ct) m)))
        (fun i => S.challenges mt ct ⟨1 + i.val, by omega⟩))
    (hright₂ : ∀ (mt : Fin v7P256Sha3.ecdsa.tape → D)
      (ct : Fin (len2 v7P256Sha3.ecdsa v7P256Sha3.sha + N) → C),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      let σ := (S.context mt ct, S.challenges mt ct ⟨0, by omega⟩, pubOf (S.proof mt ct))
      (∀ cand, ¬ S₂.Sat σ cand) →
      JointAccepts K₂ codec₂ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂
        statementOf₂ responseOf₂ challengeOf₂ queryOf₂ mt ct →
      S.Explains dec₂ Prod.snd claimOf₂ mt ct →
      RbrSplit.LayerStepAccepts
        (RbrSplit.stepsOf (nl := v7P256Sha3.sha.params.nl) (w := v7P256Sha3.sha.params.rounds)
          (withMsgs (S₂.field σ) (S₂.MD σ) (msgOf₂ (S.proof mt ct)))
          (fun m pref => S₂.accR σ m pref (msgOf₂ (S.proof mt ct) m)))
        (fun i => S.challenges mt ct
          ⟨1 + Rounds.Role.length v7P256Sha3.ecdsa.params.nl v7P256Sha3.ecdsa.params.rounds + i.val,
            by omega⟩))
    (hrow₁ : ∀ (mt : Fin v7P256Sha3.ecdsa.tape → D)
      (ct : Fin (len2 v7P256Sha3.ecdsa v7P256Sha3.sha + N) → C) (a : Witness₁),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      JointAccepts K₁ codec₁ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ claimOf₁
        statementOf₁ responseOf₁ challengeOf₁ queryOf₁ mt ct →
      S₁.Good (S.context mt ct, S.challenges mt ct ⟨0, by omega⟩, pubOf (S.proof mt ct)) a →
      macTag (aP (S.context mt ct) + decode (S.challenges mt ct ⟨0, by omega⟩))
        (keyB (S.proof mt ct)) (common₁ a) = tagOf (S.proof mt ct))
    (hrow₂ : ∀ (mt : Fin v7P256Sha3.ecdsa.tape → D)
      (ct : Fin (len2 v7P256Sha3.ecdsa v7P256Sha3.sha + N) → C) (a : Witness₂),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      JointAccepts K₂ codec₂ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂
        statementOf₂ responseOf₂ challengeOf₂ queryOf₂ mt ct →
      S₂.Good (S.context mt ct, S.challenges mt ct ⟨0, by omega⟩, pubOf (S.proof mt ct)) a →
      macTag (aP (S.context mt ct) + decode (S.challenges mt ct ⟨0, by omega⟩))
        (keyB (S.proof mt ct)) (common₂ a) = tagOf (S.proof mt ct))
    (htA : tA ≤ 2 ^ 60) (htape : 2 * n₂ + 2 * n₁ + tA ≤ 2 ^ 62) :
    ((univ.filter fun ω : (Fin v7P256Sha3.ecdsa.tape → D) ×
          (Fin (len2 v7P256Sha3.ecdsa v7P256Sha3.sha + N) → C) =>
        JointAccepts K₁ codec₁ (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ claimOf₁ statementOf₁ responseOf₁
            challengeOf₁ queryOf₁ ω.1 ω.2 ∧
          JointAccepts K₂ codec₂ (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂ statementOf₂ responseOf₂
            challengeOf₂ queryOf₂ ω.1 ω.2 ∧
          ¬ ∃ a₁ a₂,
            S₁.Good ((setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).context ω.1 ω.2,
              (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
                ⟨0, by omega⟩,
              pubOf ((setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).proof ω.1 ω.2)) a₁ ∧
            S₂.Good ((setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).context ω.1 ω.2,
              (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
                ⟨0, by omega⟩,
              pubOf ((setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).proof ω.1 ω.2)) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7P256Sha3.ecdsa.tape *
            (Fintype.card C : ℚ) ^ (len2 v7P256Sha3.ecdsa v7P256Sha3.sha + N))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) := by
  have hv := v7P256Sha3_valid
  refine le_trans (twofield_adaptive_ratio_le (TwoFieldRowV1.ecdsa_valid hv)
    dec₁ dec₂ K₁ K₂ body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
    claimOf₁ claimOf₂ statementOf₁ responseOf₁ challengeOf₁ queryOf₁ statementOf₂ responseOf₂
    challengeOf₂ queryOf₂ S₁ S₂ hF₁ hF₂ hcand₁ hcand₂ hD hD aP decode kmac hbal hmac keyB tagOf
    common₁ common₂ hright₁ hright₂ hrow₁ hrow₂ htA htA htape rfl) ?_
  have hsb := v7P256Sha3_adaptive_slack_bound
  have hsc := v7P256Sha3_adaptive_slack_coeff
  have hmf : (Fintype.card Fmac : ℚ) = (v7P256Sha3.macFieldSize : ℚ) := by
    rw [hFmac]; rfl
  rw [hmf]
  have hsplit : 2 * (((v7P256Sha3.ecdsa.tape * (len2 v7P256Sha3.ecdsa v7P256Sha3.sha + N) : ℕ) : ℚ)
        / 2 ^ v7P256Sha3.ecdsa.params.digestBits)
      = 2 * (((v7P256Sha3.ecdsa.tape * len2 v7P256Sha3.ecdsa v7P256Sha3.sha : ℕ) : ℚ)
          / 2 ^ v7P256Sha3.ecdsa.params.digestBits)
        + N * (2 * ((v7P256Sha3.ecdsa.tape : ℚ) / 2 ^ v7P256Sha3.ecdsa.params.digestBits)) := by
    push_cast
    ring
  rw [hsplit]
  have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg N
  have := mul_le_mul_of_nonneg_left hsc hN
  nlinarith

/-- **Two-field Longfellow at `v7P256Sha4` against one re-committing Fiat–Shamir prover, with a
hashed MAC key**: `2^-115 + N · 2^-116`. `twofield_adaptive_ratio_le` at the v7 signature row and
the v7 4-attribute hash row, over one Merkle tape of `2^62` slots and one challenge tape of
`1161 + N` slots; the premises are `twofield_adaptive_ratio_le`'s. -/
theorem v7P256Sha4_adaptive_ratio_le {tA N : ℕ} (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ M₁ D Enc} (dec₁ : RoleDecoders codec₁)
    {codec₂ : Codec Salt₂ M₂ D Enc} (dec₂ : RoleDecoders codec₂)
    (K₁ : Compiler Statement₁ Oracle₁ Challenge₁ Response₁ Query₁ Opening₁ M₁ n₁)
    (K₂ : Compiler Statement₂ Oracle₂ Challenge₂ Response₂ Query₂ Opening₂ M₂ n₂)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ v7P256Sha4.ecdsa.params.nl
      v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.rounds v7P256Sha4.sha.params.rounds) C Out tA N)
    (dflt : C) (rootOf₁ rootOf₂ : Out → D) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim n₁ Salt₁ M₁ D) (claimOf₂ : Out → OpeningClaim n₂ Salt₂ M₂ D)
    (statementOf₁ : Out → (Fin (len2 v7P256Sha4.ecdsa v7P256Sha4.sha) → C) → Statement₁)
    (responseOf₁ : Out → Response₁)
    (challengeOf₁ : Out → (Fin (len2 v7P256Sha4.ecdsa v7P256Sha4.sha) → C) → Challenge₁)
    (queryOf₁ : Out → (Fin (len2 v7P256Sha4.ecdsa v7P256Sha4.sha) → C) → Query₁)
    (statementOf₂ : Out → (Fin (len2 v7P256Sha4.ecdsa v7P256Sha4.sha) → C) → Statement₂)
    (responseOf₂ : Out → Response₂)
    (challengeOf₂ : Out → (Fin (len2 v7P256Sha4.ecdsa v7P256Sha4.sha) → C) → Challenge₂)
    (queryOf₂ : Out → (Fin (len2 v7P256Sha4.ecdsa v7P256Sha4.sha) → C) → Query₂)
    (S₁ : Side v7P256Sha4.ecdsa (((D × D) × List (Enc × D)) × C × X) C Cand₁ F₁ Equations₁ Witness₁
      Msg₁ nc₁ nv₁ logw₁ logc₁)
    (S₂ : Side v7P256Sha4.sha (((D × D) × List (Enc × D)) × C × X) C Cand₂ F₂ Equations₂ Witness₂
      Msg₂ nc₂ nv₂ logw₂ logc₂)
    (hF₁ : Fintype.card F₁ = v7P256Sha4.ecdsa.params.row.fieldSize)
    (hF₂ : Fintype.card F₂ = v7P256Sha4.sha.params.row.fieldSize)
    (hcand₁ : Fintype.card Cand₁ = v7P256Sha4.ecdsa.cardCand)
    (hcand₂ : Fintype.card Cand₂ = v7P256Sha4.sha.cardCand)
    (hD : Fintype.card D = 2 ^ v7P256Sha4.ecdsa.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : Witness₁ → Fin nblk → Fmac) (common₂ : Witness₂ → Fin nblk → Fmac)
    (hright₁ : ∀ (mt : Fin v7P256Sha4.ecdsa.tape → D)
      (ct : Fin (len2 v7P256Sha4.ecdsa v7P256Sha4.sha + N) → C),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      let σ := (S.context mt ct, S.challenges mt ct ⟨0, by omega⟩, pubOf (S.proof mt ct))
      (∀ cand, ¬ S₁.Sat σ cand) →
      JointAccepts K₁ codec₁ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ claimOf₁
        statementOf₁ responseOf₁ challengeOf₁ queryOf₁ mt ct →
      S.Explains dec₁ Prod.fst claimOf₁ mt ct →
      RbrSplit.LayerStepAccepts
        (RbrSplit.stepsOf (nl := v7P256Sha4.ecdsa.params.nl) (w := v7P256Sha4.ecdsa.params.rounds)
          (withMsgs (S₁.field σ) (S₁.MD σ) (msgOf₁ (S.proof mt ct)))
          (fun m pref => S₁.accR σ m pref (msgOf₁ (S.proof mt ct) m)))
        (fun i => S.challenges mt ct ⟨1 + i.val, by omega⟩))
    (hright₂ : ∀ (mt : Fin v7P256Sha4.ecdsa.tape → D)
      (ct : Fin (len2 v7P256Sha4.ecdsa v7P256Sha4.sha + N) → C),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      let σ := (S.context mt ct, S.challenges mt ct ⟨0, by omega⟩, pubOf (S.proof mt ct))
      (∀ cand, ¬ S₂.Sat σ cand) →
      JointAccepts K₂ codec₂ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂
        statementOf₂ responseOf₂ challengeOf₂ queryOf₂ mt ct →
      S.Explains dec₂ Prod.snd claimOf₂ mt ct →
      RbrSplit.LayerStepAccepts
        (RbrSplit.stepsOf (nl := v7P256Sha4.sha.params.nl) (w := v7P256Sha4.sha.params.rounds)
          (withMsgs (S₂.field σ) (S₂.MD σ) (msgOf₂ (S.proof mt ct)))
          (fun m pref => S₂.accR σ m pref (msgOf₂ (S.proof mt ct) m)))
        (fun i => S.challenges mt ct
          ⟨1 + Rounds.Role.length v7P256Sha4.ecdsa.params.nl v7P256Sha4.ecdsa.params.rounds + i.val,
            by omega⟩))
    (hrow₁ : ∀ (mt : Fin v7P256Sha4.ecdsa.tape → D)
      (ct : Fin (len2 v7P256Sha4.ecdsa v7P256Sha4.sha + N) → C) (a : Witness₁),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      JointAccepts K₁ codec₁ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ claimOf₁
        statementOf₁ responseOf₁ challengeOf₁ queryOf₁ mt ct →
      S₁.Good (S.context mt ct, S.challenges mt ct ⟨0, by omega⟩, pubOf (S.proof mt ct)) a →
      macTag (aP (S.context mt ct) + decode (S.challenges mt ct ⟨0, by omega⟩))
        (keyB (S.proof mt ct)) (common₁ a) = tagOf (S.proof mt ct))
    (hrow₂ : ∀ (mt : Fin v7P256Sha4.ecdsa.tape → D)
      (ct : Fin (len2 v7P256Sha4.ecdsa v7P256Sha4.sha + N) → C) (a : Witness₂),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      JointAccepts K₂ codec₂ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂
        statementOf₂ responseOf₂ challengeOf₂ queryOf₂ mt ct →
      S₂.Good (S.context mt ct, S.challenges mt ct ⟨0, by omega⟩, pubOf (S.proof mt ct)) a →
      macTag (aP (S.context mt ct) + decode (S.challenges mt ct ⟨0, by omega⟩))
        (keyB (S.proof mt ct)) (common₂ a) = tagOf (S.proof mt ct))
    (htA : tA ≤ 2 ^ 60) (htape : 2 * n₂ + 2 * n₁ + tA ≤ 2 ^ 62) :
    ((univ.filter fun ω : (Fin v7P256Sha4.ecdsa.tape → D) ×
          (Fin (len2 v7P256Sha4.ecdsa v7P256Sha4.sha + N) → C) =>
        JointAccepts K₁ codec₁ (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ claimOf₁ statementOf₁ responseOf₁
            challengeOf₁ queryOf₁ ω.1 ω.2 ∧
          JointAccepts K₂ codec₂ (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂ statementOf₂ responseOf₂
            challengeOf₂ queryOf₂ ω.1 ω.2 ∧
          ¬ ∃ a₁ a₂,
            S₁.Good ((setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).context ω.1 ω.2,
              (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
                ⟨0, by omega⟩,
              pubOf ((setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).proof ω.1 ω.2)) a₁ ∧
            S₂.Good ((setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).context ω.1 ω.2,
              (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
                ⟨0, by omega⟩,
              pubOf ((setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).proof ω.1 ω.2)) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7P256Sha4.ecdsa.tape *
            (Fintype.card C : ℚ) ^ (len2 v7P256Sha4.ecdsa v7P256Sha4.sha + N))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) := by
  have hv := v7P256Sha4_valid
  refine le_trans (twofield_adaptive_ratio_le (TwoFieldRowV1.ecdsa_valid hv)
    dec₁ dec₂ K₁ K₂ body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
    claimOf₁ claimOf₂ statementOf₁ responseOf₁ challengeOf₁ queryOf₁ statementOf₂ responseOf₂
    challengeOf₂ queryOf₂ S₁ S₂ hF₁ hF₂ hcand₁ hcand₂ hD hD aP decode kmac hbal hmac keyB tagOf
    common₁ common₂ hright₁ hright₂ hrow₁ hrow₂ htA htA htape rfl) ?_
  have hsb := v7P256Sha4_adaptive_slack_bound
  have hsc := v7P256Sha4_adaptive_slack_coeff
  have hmf : (Fintype.card Fmac : ℚ) = (v7P256Sha4.macFieldSize : ℚ) := by
    rw [hFmac]; rfl
  rw [hmf]
  have hsplit : 2 * (((v7P256Sha4.ecdsa.tape * (len2 v7P256Sha4.ecdsa v7P256Sha4.sha + N) : ℕ) : ℚ)
        / 2 ^ v7P256Sha4.ecdsa.params.digestBits)
      = 2 * (((v7P256Sha4.ecdsa.tape * len2 v7P256Sha4.ecdsa v7P256Sha4.sha : ℕ) : ℚ)
          / 2 ^ v7P256Sha4.ecdsa.params.digestBits)
        + N * (2 * ((v7P256Sha4.ecdsa.tape : ℚ) / 2 ^ v7P256Sha4.ecdsa.params.digestBits)) := by
    push_cast
    ring
  rw [hsplit]
  have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg N
  have := mul_le_mul_of_nonneg_left hsc hN
  nlinarith

end Headline

end Lfzk.NizkAdaptiveTwoField

namespace Lfzk.CompiledLongfellowAdaptive

open Finset Bcs Bcs.AdaptiveCommit Merkle Merkle.MH Merkle.RandomOracle
  Merkle.RandomOracle.TwoOracleTree RbrLongfellow Lfzk.NizkGrinding Lfzk.NizkAdaptive
  Lfzk.CompiledLongfellow
open scoped Classical

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
**v7Sig at the compiled Longfellow verifier, against a re-committing Fiat–Shamir prover.**

`row_adaptive_ratio_le_v1` at `CertifiedV1.v7Sig` — the v7 signature row (21 layers, 542 sumcheck
slots, over P-256's base field, Ligero V1 at `n = 3187`, `k = 455` with 132 opened columns) — with
the numerals `CertifiedV1.v7Sig_adaptive_rhs_le`: against one adaptive program making at most
`tA ≤ 2^60` Merkle-oracle and `N` challenge-oracle queries, interleaved as it likes,

```text
Pr[ AcceptsAt (v1K …) …  ∧  Fails(context of the proof's root) ]  ≤  2^-122  +  N · 2^-122
```

over the Merkle tape (`2^62` slots) and a challenge tape of `566 + N` slots. The premises are
`row_adaptive_ratio_le_v1`'s; `hr` is discharged.
-/
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
    (body : TwoOracleTree Enc D (Point D Msg C v7Sig.params.nl v7Sig.params.rounds) C Out tA N)
    (dflt : C) (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim v7Sig.params.row.n Salt (Col F v7Sig.params.nw v7Sig.params.nq) D)
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
    ((univ.filter fun ω : (Fin v7Sig.tape → D) × (Fin (v7Sig.fsLen N) → C) =>
        AcceptsAt (v1K (Row.rowValid v7Sig_valid) dom (Row.hkrow v7Sig_valid) v7Sig_openings_pos)
            V codec (lfSetup body dflt rootOf msgOf) (lfCheck codec claimOf) rootOf msgOf claimOf
            (rootStatement rootOf stmt) respOf id ω.1 ω.2 ∧
          Fails ((lfSetup body dflt rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7Sig.tape * (Fintype.card C : ℚ) ^ v7Sig.fsLen N)
      ≤ (1 : ℚ) / 2 ^ 122 + N * ((1 : ℚ) / 2 ^ 122) :=
  le_trans
    (row_adaptive_ratio_le_v1 v7Sig_valid v7Sig_openings_pos dec V dom stmt respOf body dflt
      rootOf msgOf claimOf hF hfalse H Sat Ffam hexact MD hmatch hfail htA htape hcand hD)
    (v7Sig_adaptive_rhs_le N)

/--
**v7Hash1 at the compiled Longfellow verifier, against a re-committing Fiat–Shamir prover.**

`row_adaptive_ratio_le_v1` at `CertifiedV1.v7Hash1` — the v7 1-attribute hash row (17 layers, 566
sumcheck slots, over `GF(2^128)`, Ligero V1 at `n = 3230`, `k = 461` with 132 opened columns) — with
the numerals `CertifiedV1.v7Hash1_adaptive_rhs_le`: against one adaptive program making at most
`tA ≤ 2^60` Merkle-oracle and `N` challenge-oracle queries, interleaved as it likes,

```text
Pr[ AcceptsAt (v1K …) …  ∧  Fails(context of the proof's root) ]  ≤  2^-115  +  N · 2^-116
```

over the Merkle tape (`2^62` slots) and a challenge tape of `586 + N` slots. The premises are
`row_adaptive_ratio_le_v1`'s; `hr` is discharged.
-/
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
    (body : TwoOracleTree Enc D (Point D Msg C v7Hash1.params.nl v7Hash1.params.rounds) C Out tA N)
    (dflt : C) (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim v7Hash1.params.row.n Salt (Col F v7Hash1.params.nw v7Hash1.params.nq) D)
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
    ((univ.filter fun ω : (Fin v7Hash1.tape → D) × (Fin (v7Hash1.fsLen N) → C) =>
        AcceptsAt (v1K (Row.rowValid v7Hash1_valid) dom (Row.hkrow v7Hash1_valid) v7Hash1_openings_pos)
            V codec (lfSetup body dflt rootOf msgOf) (lfCheck codec claimOf) rootOf msgOf claimOf
            (rootStatement rootOf stmt) respOf id ω.1 ω.2 ∧
          Fails ((lfSetup body dflt rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7Hash1.tape * (Fintype.card C : ℚ) ^ v7Hash1.fsLen N)
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) :=
  le_trans
    (row_adaptive_ratio_le_v1 v7Hash1_valid v7Hash1_openings_pos dec V dom stmt respOf body dflt
      rootOf msgOf claimOf hF hfalse H Sat Ffam hexact MD hmatch hfail htA htape hcand hD)
    (v7Hash1_adaptive_rhs_le N)

/--
**v7Hash2 at the compiled Longfellow verifier, against a re-committing Fiat–Shamir prover.**

`row_adaptive_ratio_le_v1` at `CertifiedV1.v7Hash2` — the v7 2-attribute hash row (17 layers, 570
sumcheck slots, over `GF(2^128)`, Ligero V1 at `n = 3318`, `k = 474` with 132 opened columns) — with
the numerals `CertifiedV1.v7Hash2_adaptive_rhs_le`: against one adaptive program making at most
`tA ≤ 2^60` Merkle-oracle and `N` challenge-oracle queries, interleaved as it likes,

```text
Pr[ AcceptsAt (v1K …) …  ∧  Fails(context of the proof's root) ]  ≤  2^-115  +  N · 2^-116
```

over the Merkle tape (`2^62` slots) and a challenge tape of `590 + N` slots. The premises are
`row_adaptive_ratio_le_v1`'s; `hr` is discharged.
-/
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
    (body : TwoOracleTree Enc D (Point D Msg C v7Hash2.params.nl v7Hash2.params.rounds) C Out tA N)
    (dflt : C) (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim v7Hash2.params.row.n Salt (Col F v7Hash2.params.nw v7Hash2.params.nq) D)
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
    ((univ.filter fun ω : (Fin v7Hash2.tape → D) × (Fin (v7Hash2.fsLen N) → C) =>
        AcceptsAt (v1K (Row.rowValid v7Hash2_valid) dom (Row.hkrow v7Hash2_valid) v7Hash2_openings_pos)
            V codec (lfSetup body dflt rootOf msgOf) (lfCheck codec claimOf) rootOf msgOf claimOf
            (rootStatement rootOf stmt) respOf id ω.1 ω.2 ∧
          Fails ((lfSetup body dflt rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7Hash2.tape * (Fintype.card C : ℚ) ^ v7Hash2.fsLen N)
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) :=
  le_trans
    (row_adaptive_ratio_le_v1 v7Hash2_valid v7Hash2_openings_pos dec V dom stmt respOf body dflt
      rootOf msgOf claimOf hF hfalse H Sat Ffam hexact MD hmatch hfail htA htape hcand hD)
    (v7Hash2_adaptive_rhs_le N)

/--
**v7Hash3 at the compiled Longfellow verifier, against a re-committing Fiat–Shamir prover.**

`row_adaptive_ratio_le_v1` at `CertifiedV1.v7Hash3` — the v7 3-attribute hash row (17 layers, 574
sumcheck slots, over `GF(2^128)`, Ligero V1 at `n = 3352`, `k = 478` with 132 opened columns) — with
the numerals `CertifiedV1.v7Hash3_adaptive_rhs_le`: against one adaptive program making at most
`tA ≤ 2^60` Merkle-oracle and `N` challenge-oracle queries, interleaved as it likes,

```text
Pr[ AcceptsAt (v1K …) …  ∧  Fails(context of the proof's root) ]  ≤  2^-115  +  N · 2^-116
```

over the Merkle tape (`2^62` slots) and a challenge tape of `594 + N` slots. The premises are
`row_adaptive_ratio_le_v1`'s; `hr` is discharged.
-/
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
    (body : TwoOracleTree Enc D (Point D Msg C v7Hash3.params.nl v7Hash3.params.rounds) C Out tA N)
    (dflt : C) (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim v7Hash3.params.row.n Salt (Col F v7Hash3.params.nw v7Hash3.params.nq) D)
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
    ((univ.filter fun ω : (Fin v7Hash3.tape → D) × (Fin (v7Hash3.fsLen N) → C) =>
        AcceptsAt (v1K (Row.rowValid v7Hash3_valid) dom (Row.hkrow v7Hash3_valid) v7Hash3_openings_pos)
            V codec (lfSetup body dflt rootOf msgOf) (lfCheck codec claimOf) rootOf msgOf claimOf
            (rootStatement rootOf stmt) respOf id ω.1 ω.2 ∧
          Fails ((lfSetup body dflt rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7Hash3.tape * (Fintype.card C : ℚ) ^ v7Hash3.fsLen N)
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) :=
  le_trans
    (row_adaptive_ratio_le_v1 v7Hash3_valid v7Hash3_openings_pos dec V dom stmt respOf body dflt
      rootOf msgOf claimOf hF hfalse H Sat Ffam hexact MD hmatch hfail htA htape hcand hD)
    (v7Hash3_adaptive_rhs_le N)

/--
**v7Hash4 at the compiled Longfellow verifier, against a re-committing Fiat–Shamir prover.**

`row_adaptive_ratio_le_v1` at `CertifiedV1.v7Hash4` — the v7 4-attribute hash row (17 layers, 574
sumcheck slots, over `GF(2^128)`, Ligero V1 at `n = 3436`, `k = 490` with 132 opened columns) — with
the numerals `CertifiedV1.v7Hash4_adaptive_rhs_le`: against one adaptive program making at most
`tA ≤ 2^60` Merkle-oracle and `N` challenge-oracle queries, interleaved as it likes,

```text
Pr[ AcceptsAt (v1K …) …  ∧  Fails(context of the proof's root) ]  ≤  2^-115  +  N · 2^-116
```

over the Merkle tape (`2^62` slots) and a challenge tape of `594 + N` slots. The premises are
`row_adaptive_ratio_le_v1`'s; `hr` is discharged.
-/
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
    (body : TwoOracleTree Enc D (Point D Msg C v7Hash4.params.nl v7Hash4.params.rounds) C Out tA N)
    (dflt : C) (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim v7Hash4.params.row.n Salt (Col F v7Hash4.params.nw v7Hash4.params.nq) D)
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
    ((univ.filter fun ω : (Fin v7Hash4.tape → D) × (Fin (v7Hash4.fsLen N) → C) =>
        AcceptsAt (v1K (Row.rowValid v7Hash4_valid) dom (Row.hkrow v7Hash4_valid) v7Hash4_openings_pos)
            V codec (lfSetup body dflt rootOf msgOf) (lfCheck codec claimOf) rootOf msgOf claimOf
            (rootStatement rootOf stmt) respOf id ω.1 ω.2 ∧
          Fails ((lfSetup body dflt rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7Hash4.tape * (Fintype.card C : ℚ) ^ v7Hash4.fsLen N)
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) :=
  le_trans
    (row_adaptive_ratio_le_v1 v7Hash4_valid v7Hash4_openings_pos dec V dom stmt respOf body dflt
      rootOf msgOf claimOf hF hfalse H Sat Ffam hexact MD hmatch hfail htA htape hcand hD)
    (v7Hash4_adaptive_rhs_le N)

end Row

section TwoField

open Lfzk.CertifiedV1 Lfzk.NizkAdaptiveTwoField Lfzk.TwoFieldV1Rows Lfzk.Mac

variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {D : Type} [Fintype D] [DecidableEq D] [Inhabited D]
variable {Enc X Out : Type} [DecidableEq Enc]

variable {Fmac : Type} [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {nblk : ℕ}
variable {Cand₁ F₁ Equations₁ Witness₁ Msg₁ : Type} [Fintype Cand₁] [Nonempty Cand₁] [Field F₁]
  [Fintype F₁] [DecidableEq F₁] [SumcheckInterp F₁] [Fintype Equations₁] [DecidableEq Equations₁]
  [DecidableEq Msg₁] [Inhabited Msg₁] {nc₁ nv₁ logw₁ logc₁ : ℕ}
variable {Cand₂ F₂ Equations₂ Witness₂ Msg₂ : Type} [Fintype Cand₂] [Nonempty Cand₂] [Field F₂]
  [Fintype F₂] [DecidableEq F₂] [SumcheckInterp F₂] [Fintype Equations₂] [DecidableEq Equations₂]
  [DecidableEq Msg₂] [Inhabited Msg₂] {nc₂ nv₂ logw₂ logc₂ : ℕ}
variable {Salt₁ Salt₂ : Type} [Inhabited Salt₁] [Inhabited Salt₂]

/--
**Two-field Longfellow at `v7P256Sha1`, at the compiled verifiers, against one re-committing
Fiat–Shamir prover with a hashed MAC key.**

`twofield_adaptive_compiled_ratio_le` at `TwoFieldV1Rows.v7P256Sha1` — ECDSA over `P-256`'s base
field (`CertifiedV1.v7Sig`) and SHA-256 over `GF(2^128)` (`CertifiedV1.v7Hash1`), the deployed v7
circuits proved with Ligero V1 at 132 openings, composed through the MAC over a field of `2^128`
elements — with the numerals `TwoFieldV1Rows.v7P256Sha1_adaptive_rhs_le`: against one adaptive
program making at most `tA ≤ 2^60` Merkle-oracle and `N` challenge-oracle queries, over all roles,

```text
Pr [ both compiled verifiers accept  ∧  no two good witnesses agree on the common value ]
    ≤  2^-115  +  N · 2^-116
```

over one Merkle tape of `2^62` slots and one challenge tape of `1153 + N` slots. The premises are
`twofield_adaptive_compiled_ratio_le`'s; `hr₁`, `hr₂` are discharged.
-/
theorem v7P256Sha1_adaptive_compiled_ratio_le {tA N : ℕ} (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha1.ecdsa.params.nw v7P256Sha1.ecdsa.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha1.sha.params.nw v7P256Sha1.sha.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (L₁ : CompiledSide v7P256Sha1.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha1_valid)
      v7P256Sha1_ecdsa_openings_pos C Cand₁ F₁ Equations₁ Witness₁ Msg₁ nc₁ nv₁ logw₁ logc₁ X dec₁
      Prod.fst)
    (L₂ : CompiledSide v7P256Sha1.sha (TwoFieldRowV1.sha_valid v7P256Sha1_valid)
      v7P256Sha1_sha_openings_pos C Cand₂ F₂ Equations₂ Witness₂ Msg₂ nc₂ nv₂ logw₂ logc₂ X dec₂
      Prod.snd)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ v7P256Sha1.ecdsa.params.nl
      v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.rounds v7P256Sha1.sha.params.rounds) C Out tA N)
    (dflt : C) (rootOf₁ rootOf₂ : Out → D) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7P256Sha1.ecdsa.params.row.n Salt₁
      (Col F₁ v7P256Sha1.ecdsa.params.nw v7P256Sha1.ecdsa.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7P256Sha1.sha.params.row.n Salt₂
      (Col F₂ v7P256Sha1.sha.params.nw v7P256Sha1.sha.params.nq) D)
    (hcand₁ : Fintype.card Cand₁ = v7P256Sha1.ecdsa.cardCand)
    (hcand₂ : Fintype.card Cand₂ = v7P256Sha1.sha.cardCand)
    (hD : Fintype.card D = 2 ^ v7P256Sha1.ecdsa.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : Witness₁ → Fin nblk → Fmac) (common₂ : Witness₂ → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin v7P256Sha1.ecdsa.tape → D)
      (ct : Fin (len2 v7P256Sha1.ecdsa v7P256Sha1.sha + N) → C) (a : Witness₁),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      L₁.accepts S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ pubOf
        (len2_pos _ _) (slice1 v7P256Sha1.ecdsa v7P256Sha1.sha) mt ct →
      L₁.Good (sideCtx S pubOf (len2_pos _ _) mt ct) a →
      macTag (aP (S.context mt ct) + decode (S.challenges mt ct ⟨0, len2_pos _ _⟩))
        (keyB (S.proof mt ct)) (common₁ a) = tagOf (S.proof mt ct))
    (hrow₂ : ∀ (mt : Fin v7P256Sha1.ecdsa.tape → D)
      (ct : Fin (len2 v7P256Sha1.ecdsa v7P256Sha1.sha + N) → C) (a : Witness₂),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      L₂.accepts S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ pubOf
        (len2_pos _ _) (slice2 v7P256Sha1.ecdsa v7P256Sha1.sha) mt ct →
      L₂.Good (sideCtx S pubOf (len2_pos _ _) mt ct) a →
      macTag (aP (S.context mt ct) + decode (S.challenges mt ct ⟨0, len2_pos _ _⟩))
        (keyB (S.proof mt ct)) (common₂ a) = tagOf (S.proof mt ct))
    (htA : tA ≤ 2 ^ 60)
    (htape : 2 * v7P256Sha1.sha.params.row.n + 2 * v7P256Sha1.ecdsa.params.row.n + tA ≤ 2 ^ 62) :
    ((univ.filter fun ω : (Fin v7P256Sha1.ecdsa.tape → D) ×
          (Fin (len2 v7P256Sha1.ecdsa v7P256Sha1.sha + N) → C) =>
        L₁.accepts (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ pubOf (len2_pos _ _)
            (slice1 v7P256Sha1.ecdsa v7P256Sha1.sha) ω.1 ω.2 ∧
          L₂.accepts (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ pubOf (len2_pos _ _)
            (slice2 v7P256Sha1.ecdsa v7P256Sha1.sha) ω.1 ω.2 ∧
          ¬ ∃ a₁ a₂,
            L₁.Good (sideCtx (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂) pubOf
              (len2_pos _ _) ω.1 ω.2) a₁ ∧
            L₂.Good (sideCtx (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂) pubOf
              (len2_pos _ _) ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7P256Sha1.ecdsa.tape *
            (Fintype.card C : ℚ) ^ (len2 v7P256Sha1.ecdsa v7P256Sha1.sha + N))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) :=
  le_trans
    (twofield_adaptive_compiled_ratio_le (TwoFieldRowV1.ecdsa_valid v7P256Sha1_valid)
      (TwoFieldRowV1.sha_valid v7P256Sha1_valid) v7P256Sha1_ecdsa_openings_pos v7P256Sha1_sha_openings_pos
      L₁ L₂ body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂ hcand₁ hcand₂ hD hD
      aP decode kmac hbal hmac keyB tagOf common₁ common₂ hrow₁ hrow₂ htA htA htape rfl)
    (v7P256Sha1_adaptive_rhs_le N hFmac)

/--
**Two-field Longfellow at `v7P256Sha2`, at the compiled verifiers, against one re-committing
Fiat–Shamir prover with a hashed MAC key.**

`twofield_adaptive_compiled_ratio_le` at `TwoFieldV1Rows.v7P256Sha2` — ECDSA over `P-256`'s base
field (`CertifiedV1.v7Sig`) and SHA-256 over `GF(2^128)` (`CertifiedV1.v7Hash2`), the deployed v7
circuits proved with Ligero V1 at 132 openings, composed through the MAC over a field of `2^128`
elements — with the numerals `TwoFieldV1Rows.v7P256Sha2_adaptive_rhs_le`: against one adaptive
program making at most `tA ≤ 2^60` Merkle-oracle and `N` challenge-oracle queries, over all roles,

```text
Pr [ both compiled verifiers accept  ∧  no two good witnesses agree on the common value ]
    ≤  2^-115  +  N · 2^-116
```

over one Merkle tape of `2^62` slots and one challenge tape of `1157 + N` slots. The premises are
`twofield_adaptive_compiled_ratio_le`'s; `hr₁`, `hr₂` are discharged.
-/
theorem v7P256Sha2_adaptive_compiled_ratio_le {tA N : ℕ} (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha2.ecdsa.params.nw v7P256Sha2.ecdsa.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha2.sha.params.nw v7P256Sha2.sha.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (L₁ : CompiledSide v7P256Sha2.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha2_valid)
      v7P256Sha2_ecdsa_openings_pos C Cand₁ F₁ Equations₁ Witness₁ Msg₁ nc₁ nv₁ logw₁ logc₁ X dec₁
      Prod.fst)
    (L₂ : CompiledSide v7P256Sha2.sha (TwoFieldRowV1.sha_valid v7P256Sha2_valid)
      v7P256Sha2_sha_openings_pos C Cand₂ F₂ Equations₂ Witness₂ Msg₂ nc₂ nv₂ logw₂ logc₂ X dec₂
      Prod.snd)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ v7P256Sha2.ecdsa.params.nl
      v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.rounds v7P256Sha2.sha.params.rounds) C Out tA N)
    (dflt : C) (rootOf₁ rootOf₂ : Out → D) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7P256Sha2.ecdsa.params.row.n Salt₁
      (Col F₁ v7P256Sha2.ecdsa.params.nw v7P256Sha2.ecdsa.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7P256Sha2.sha.params.row.n Salt₂
      (Col F₂ v7P256Sha2.sha.params.nw v7P256Sha2.sha.params.nq) D)
    (hcand₁ : Fintype.card Cand₁ = v7P256Sha2.ecdsa.cardCand)
    (hcand₂ : Fintype.card Cand₂ = v7P256Sha2.sha.cardCand)
    (hD : Fintype.card D = 2 ^ v7P256Sha2.ecdsa.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : Witness₁ → Fin nblk → Fmac) (common₂ : Witness₂ → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin v7P256Sha2.ecdsa.tape → D)
      (ct : Fin (len2 v7P256Sha2.ecdsa v7P256Sha2.sha + N) → C) (a : Witness₁),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      L₁.accepts S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ pubOf
        (len2_pos _ _) (slice1 v7P256Sha2.ecdsa v7P256Sha2.sha) mt ct →
      L₁.Good (sideCtx S pubOf (len2_pos _ _) mt ct) a →
      macTag (aP (S.context mt ct) + decode (S.challenges mt ct ⟨0, len2_pos _ _⟩))
        (keyB (S.proof mt ct)) (common₁ a) = tagOf (S.proof mt ct))
    (hrow₂ : ∀ (mt : Fin v7P256Sha2.ecdsa.tape → D)
      (ct : Fin (len2 v7P256Sha2.ecdsa v7P256Sha2.sha + N) → C) (a : Witness₂),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      L₂.accepts S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ pubOf
        (len2_pos _ _) (slice2 v7P256Sha2.ecdsa v7P256Sha2.sha) mt ct →
      L₂.Good (sideCtx S pubOf (len2_pos _ _) mt ct) a →
      macTag (aP (S.context mt ct) + decode (S.challenges mt ct ⟨0, len2_pos _ _⟩))
        (keyB (S.proof mt ct)) (common₂ a) = tagOf (S.proof mt ct))
    (htA : tA ≤ 2 ^ 60)
    (htape : 2 * v7P256Sha2.sha.params.row.n + 2 * v7P256Sha2.ecdsa.params.row.n + tA ≤ 2 ^ 62) :
    ((univ.filter fun ω : (Fin v7P256Sha2.ecdsa.tape → D) ×
          (Fin (len2 v7P256Sha2.ecdsa v7P256Sha2.sha + N) → C) =>
        L₁.accepts (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ pubOf (len2_pos _ _)
            (slice1 v7P256Sha2.ecdsa v7P256Sha2.sha) ω.1 ω.2 ∧
          L₂.accepts (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ pubOf (len2_pos _ _)
            (slice2 v7P256Sha2.ecdsa v7P256Sha2.sha) ω.1 ω.2 ∧
          ¬ ∃ a₁ a₂,
            L₁.Good (sideCtx (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂) pubOf
              (len2_pos _ _) ω.1 ω.2) a₁ ∧
            L₂.Good (sideCtx (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂) pubOf
              (len2_pos _ _) ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7P256Sha2.ecdsa.tape *
            (Fintype.card C : ℚ) ^ (len2 v7P256Sha2.ecdsa v7P256Sha2.sha + N))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) :=
  le_trans
    (twofield_adaptive_compiled_ratio_le (TwoFieldRowV1.ecdsa_valid v7P256Sha2_valid)
      (TwoFieldRowV1.sha_valid v7P256Sha2_valid) v7P256Sha2_ecdsa_openings_pos v7P256Sha2_sha_openings_pos
      L₁ L₂ body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂ hcand₁ hcand₂ hD hD
      aP decode kmac hbal hmac keyB tagOf common₁ common₂ hrow₁ hrow₂ htA htA htape rfl)
    (v7P256Sha2_adaptive_rhs_le N hFmac)

/--
**Two-field Longfellow at `v7P256Sha3`, at the compiled verifiers, against one re-committing
Fiat–Shamir prover with a hashed MAC key.**

`twofield_adaptive_compiled_ratio_le` at `TwoFieldV1Rows.v7P256Sha3` — ECDSA over `P-256`'s base
field (`CertifiedV1.v7Sig`) and SHA-256 over `GF(2^128)` (`CertifiedV1.v7Hash3`), the deployed v7
circuits proved with Ligero V1 at 132 openings, composed through the MAC over a field of `2^128`
elements — with the numerals `TwoFieldV1Rows.v7P256Sha3_adaptive_rhs_le`: against one adaptive
program making at most `tA ≤ 2^60` Merkle-oracle and `N` challenge-oracle queries, over all roles,

```text
Pr [ both compiled verifiers accept  ∧  no two good witnesses agree on the common value ]
    ≤  2^-115  +  N · 2^-116
```

over one Merkle tape of `2^62` slots and one challenge tape of `1161 + N` slots. The premises are
`twofield_adaptive_compiled_ratio_le`'s; `hr₁`, `hr₂` are discharged.
-/
theorem v7P256Sha3_adaptive_compiled_ratio_le {tA N : ℕ} (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha3.ecdsa.params.nw v7P256Sha3.ecdsa.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha3.sha.params.nw v7P256Sha3.sha.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (L₁ : CompiledSide v7P256Sha3.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha3_valid)
      v7P256Sha3_ecdsa_openings_pos C Cand₁ F₁ Equations₁ Witness₁ Msg₁ nc₁ nv₁ logw₁ logc₁ X dec₁
      Prod.fst)
    (L₂ : CompiledSide v7P256Sha3.sha (TwoFieldRowV1.sha_valid v7P256Sha3_valid)
      v7P256Sha3_sha_openings_pos C Cand₂ F₂ Equations₂ Witness₂ Msg₂ nc₂ nv₂ logw₂ logc₂ X dec₂
      Prod.snd)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ v7P256Sha3.ecdsa.params.nl
      v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.rounds v7P256Sha3.sha.params.rounds) C Out tA N)
    (dflt : C) (rootOf₁ rootOf₂ : Out → D) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7P256Sha3.ecdsa.params.row.n Salt₁
      (Col F₁ v7P256Sha3.ecdsa.params.nw v7P256Sha3.ecdsa.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7P256Sha3.sha.params.row.n Salt₂
      (Col F₂ v7P256Sha3.sha.params.nw v7P256Sha3.sha.params.nq) D)
    (hcand₁ : Fintype.card Cand₁ = v7P256Sha3.ecdsa.cardCand)
    (hcand₂ : Fintype.card Cand₂ = v7P256Sha3.sha.cardCand)
    (hD : Fintype.card D = 2 ^ v7P256Sha3.ecdsa.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : Witness₁ → Fin nblk → Fmac) (common₂ : Witness₂ → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin v7P256Sha3.ecdsa.tape → D)
      (ct : Fin (len2 v7P256Sha3.ecdsa v7P256Sha3.sha + N) → C) (a : Witness₁),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      L₁.accepts S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ pubOf
        (len2_pos _ _) (slice1 v7P256Sha3.ecdsa v7P256Sha3.sha) mt ct →
      L₁.Good (sideCtx S pubOf (len2_pos _ _) mt ct) a →
      macTag (aP (S.context mt ct) + decode (S.challenges mt ct ⟨0, len2_pos _ _⟩))
        (keyB (S.proof mt ct)) (common₁ a) = tagOf (S.proof mt ct))
    (hrow₂ : ∀ (mt : Fin v7P256Sha3.ecdsa.tape → D)
      (ct : Fin (len2 v7P256Sha3.ecdsa v7P256Sha3.sha + N) → C) (a : Witness₂),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      L₂.accepts S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ pubOf
        (len2_pos _ _) (slice2 v7P256Sha3.ecdsa v7P256Sha3.sha) mt ct →
      L₂.Good (sideCtx S pubOf (len2_pos _ _) mt ct) a →
      macTag (aP (S.context mt ct) + decode (S.challenges mt ct ⟨0, len2_pos _ _⟩))
        (keyB (S.proof mt ct)) (common₂ a) = tagOf (S.proof mt ct))
    (htA : tA ≤ 2 ^ 60)
    (htape : 2 * v7P256Sha3.sha.params.row.n + 2 * v7P256Sha3.ecdsa.params.row.n + tA ≤ 2 ^ 62) :
    ((univ.filter fun ω : (Fin v7P256Sha3.ecdsa.tape → D) ×
          (Fin (len2 v7P256Sha3.ecdsa v7P256Sha3.sha + N) → C) =>
        L₁.accepts (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ pubOf (len2_pos _ _)
            (slice1 v7P256Sha3.ecdsa v7P256Sha3.sha) ω.1 ω.2 ∧
          L₂.accepts (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ pubOf (len2_pos _ _)
            (slice2 v7P256Sha3.ecdsa v7P256Sha3.sha) ω.1 ω.2 ∧
          ¬ ∃ a₁ a₂,
            L₁.Good (sideCtx (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂) pubOf
              (len2_pos _ _) ω.1 ω.2) a₁ ∧
            L₂.Good (sideCtx (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂) pubOf
              (len2_pos _ _) ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7P256Sha3.ecdsa.tape *
            (Fintype.card C : ℚ) ^ (len2 v7P256Sha3.ecdsa v7P256Sha3.sha + N))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) :=
  le_trans
    (twofield_adaptive_compiled_ratio_le (TwoFieldRowV1.ecdsa_valid v7P256Sha3_valid)
      (TwoFieldRowV1.sha_valid v7P256Sha3_valid) v7P256Sha3_ecdsa_openings_pos v7P256Sha3_sha_openings_pos
      L₁ L₂ body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂ hcand₁ hcand₂ hD hD
      aP decode kmac hbal hmac keyB tagOf common₁ common₂ hrow₁ hrow₂ htA htA htape rfl)
    (v7P256Sha3_adaptive_rhs_le N hFmac)

/--
**Two-field Longfellow at `v7P256Sha4`, at the compiled verifiers, against one re-committing
Fiat–Shamir prover with a hashed MAC key.**

`twofield_adaptive_compiled_ratio_le` at `TwoFieldV1Rows.v7P256Sha4` — ECDSA over `P-256`'s base
field (`CertifiedV1.v7Sig`) and SHA-256 over `GF(2^128)` (`CertifiedV1.v7Hash4`), the deployed v7
circuits proved with Ligero V1 at 132 openings, composed through the MAC over a field of `2^128`
elements — with the numerals `TwoFieldV1Rows.v7P256Sha4_adaptive_rhs_le`: against one adaptive
program making at most `tA ≤ 2^60` Merkle-oracle and `N` challenge-oracle queries, over all roles,

```text
Pr [ both compiled verifiers accept  ∧  no two good witnesses agree on the common value ]
    ≤  2^-115  +  N · 2^-116
```

over one Merkle tape of `2^62` slots and one challenge tape of `1161 + N` slots. The premises are
`twofield_adaptive_compiled_ratio_le`'s; `hr₁`, `hr₂` are discharged.
-/
theorem v7P256Sha4_adaptive_compiled_ratio_le {tA N : ℕ} (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha4.ecdsa.params.nw v7P256Sha4.ecdsa.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha4.sha.params.nw v7P256Sha4.sha.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (L₁ : CompiledSide v7P256Sha4.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha4_valid)
      v7P256Sha4_ecdsa_openings_pos C Cand₁ F₁ Equations₁ Witness₁ Msg₁ nc₁ nv₁ logw₁ logc₁ X dec₁
      Prod.fst)
    (L₂ : CompiledSide v7P256Sha4.sha (TwoFieldRowV1.sha_valid v7P256Sha4_valid)
      v7P256Sha4_sha_openings_pos C Cand₂ F₂ Equations₂ Witness₂ Msg₂ nc₂ nv₂ logw₂ logc₂ X dec₂
      Prod.snd)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ v7P256Sha4.ecdsa.params.nl
      v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.rounds v7P256Sha4.sha.params.rounds) C Out tA N)
    (dflt : C) (rootOf₁ rootOf₂ : Out → D) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7P256Sha4.ecdsa.params.row.n Salt₁
      (Col F₁ v7P256Sha4.ecdsa.params.nw v7P256Sha4.ecdsa.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7P256Sha4.sha.params.row.n Salt₂
      (Col F₂ v7P256Sha4.sha.params.nw v7P256Sha4.sha.params.nq) D)
    (hcand₁ : Fintype.card Cand₁ = v7P256Sha4.ecdsa.cardCand)
    (hcand₂ : Fintype.card Cand₂ = v7P256Sha4.sha.cardCand)
    (hD : Fintype.card D = 2 ^ v7P256Sha4.ecdsa.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : Witness₁ → Fin nblk → Fmac) (common₂ : Witness₂ → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin v7P256Sha4.ecdsa.tape → D)
      (ct : Fin (len2 v7P256Sha4.ecdsa v7P256Sha4.sha + N) → C) (a : Witness₁),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      L₁.accepts S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ pubOf
        (len2_pos _ _) (slice1 v7P256Sha4.ecdsa v7P256Sha4.sha) mt ct →
      L₁.Good (sideCtx S pubOf (len2_pos _ _) mt ct) a →
      macTag (aP (S.context mt ct) + decode (S.challenges mt ct ⟨0, len2_pos _ _⟩))
        (keyB (S.proof mt ct)) (common₁ a) = tagOf (S.proof mt ct))
    (hrow₂ : ∀ (mt : Fin v7P256Sha4.ecdsa.tape → D)
      (ct : Fin (len2 v7P256Sha4.ecdsa v7P256Sha4.sha + N) → C) (a : Witness₂),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      L₂.accepts S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ pubOf
        (len2_pos _ _) (slice2 v7P256Sha4.ecdsa v7P256Sha4.sha) mt ct →
      L₂.Good (sideCtx S pubOf (len2_pos _ _) mt ct) a →
      macTag (aP (S.context mt ct) + decode (S.challenges mt ct ⟨0, len2_pos _ _⟩))
        (keyB (S.proof mt ct)) (common₂ a) = tagOf (S.proof mt ct))
    (htA : tA ≤ 2 ^ 60)
    (htape : 2 * v7P256Sha4.sha.params.row.n + 2 * v7P256Sha4.ecdsa.params.row.n + tA ≤ 2 ^ 62) :
    ((univ.filter fun ω : (Fin v7P256Sha4.ecdsa.tape → D) ×
          (Fin (len2 v7P256Sha4.ecdsa v7P256Sha4.sha + N) → C) =>
        L₁.accepts (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ pubOf (len2_pos _ _)
            (slice1 v7P256Sha4.ecdsa v7P256Sha4.sha) ω.1 ω.2 ∧
          L₂.accepts (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ pubOf (len2_pos _ _)
            (slice2 v7P256Sha4.ecdsa v7P256Sha4.sha) ω.1 ω.2 ∧
          ¬ ∃ a₁ a₂,
            L₁.Good (sideCtx (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂) pubOf
              (len2_pos _ _) ω.1 ω.2) a₁ ∧
            L₂.Good (sideCtx (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂) pubOf
              (len2_pos _ _) ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7P256Sha4.ecdsa.tape *
            (Fintype.card C : ℚ) ^ (len2 v7P256Sha4.ecdsa v7P256Sha4.sha + N))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) :=
  le_trans
    (twofield_adaptive_compiled_ratio_le (TwoFieldRowV1.ecdsa_valid v7P256Sha4_valid)
      (TwoFieldRowV1.sha_valid v7P256Sha4_valid) v7P256Sha4_ecdsa_openings_pos v7P256Sha4_sha_openings_pos
      L₁ L₂ body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂ hcand₁ hcand₂ hD hD
      aP decode kmac hbal hmac keyB tagOf common₁ common₂ hrow₁ hrow₂ htA htA htape rfl)
    (v7P256Sha4_adaptive_rhs_le N hFmac)

end TwoField

end Lfzk.CompiledLongfellowAdaptive
