import Lfzk.CertifiedV1
import Lfzk.NizkGrinding
import Lfzk.LigeroV1RowsV7

/-!
# The certified table at the deployed v7 parameters

`Lfzk.CertifiedV1` certifies `CertifiedV1.Row`s at the v8 circuit profiles and Ligero geometry (the
current generator, not in the registry). This file certifies the rows of the **deployed** version:
the registered v7 circuits (`ZK_SPECS` version 7 in
`rust/applications/mdoc_zk/runtime/src/zk_spec.rs`) at their Ligero configurations (`rateinv 7`,
`nreq 132`; Ligero rows `Lfzk.LigeroV1Rows.v7Sig`, `v7Hash1` … `v7Hash4`).

| row | field | circuit | `nl` | sumcheck slots | `ninp` | Ligero `n / k / w` | Ligero RBR | `lam` | `κ` |
|---|---|---|---|---|---|---|---|---|---|
| `v7Sig` | P-256 base | signature | 21 | 542 | 3739 | 3187 / 455 / 323 | 122 | 122 | 122 |
| `v7Hash1` | `GF(2^128)` | hash, 1 attribute | 17 | 566 | 85118 | 3230 / 461 / 329 | 115 | 115 | 116 |
| `v7Hash2` | `GF(2^128)` | hash, 2 attributes | 17 | 570 | 90022 | 3318 / 474 / 342 | 115 | 115 | 116 |
| `v7Hash3` | `GF(2^128)` | hash, 3 attributes | 17 | 574 | 94926 | 3352 / 478 / 346 | 115 | 115 | 116 |
| `v7Hash4` | `GF(2^128)` | hash, 4 attributes | 17 | 574 | 99830 | 3436 / 490 / 358 | 115 | 115 | 116 |

`lam` is the composed bound's exact integer bit level (`Row.Valid`, `Row.Sharp`); `κ` the
work-normalized coefficient `R.fsCoefficient = cardCand · maxDensity` (`_fsCoefficient`,
`_fsCoefficient_sharp`). For comparison, v8: hash `lam` 114, `κ` 115; sig `lam` 121, `κ` 121.

## Where the profiles come from

`nl`, the per-layer `logw` and `ninp` (the input layer's wire count, as for v8) are read from the
**stored, registered** v7 circuits by `lfzk/scripts/inspect_v7_circuit_profile.py`
(`v7-circuit-profiles.json`): the archives
`rust/applications/mdoc_zk/artifacts/circuits/<combined_hash>.lfa2` are loaded through the runtime's
own `mdoc_zk_runtime::materialize`, their combined IDs are checked against the registry's
`combined_hash`, each circuit's ID is recomputed from the parsed circuit, and the deployed
verifier's `ZkVerifier::geometry` gives the Ligero geometry. Unlike v8, v7 has one Ligero geometry
per attribute count, so there are four hash rows rather than one dominating profile. The signature
circuit is the same in all four archives.

The rows are derived and re-checked by `lfzk/scripts/v7_rows.py` (`--check`), which mirrors
`CostV1.Params` definition for definition; nothing is a result until `native_decide` checks it
here.

## What is proved and what is reused

For each row: `_valid` (`CertifiedV1.Row.Valid`, all eight conjuncts) and `_sharp`, the named facts
a headline instantiation needs (`_openings_pos`, `_lam`, `_bound_le`, `_shape`, `_length`), the
grinding coefficient (`_fsCoefficient`, `_fsCoefficient_sharp`, `_maxDensity_eq`), and the
right-hand-side numerals of the Fiat–Shamir headlines: `_fs_rhs_le N`
(`R.bound + N·κ ≤ 2^-lam + N·2^-κbits`, the shape of `NizkGrinding`/`CompiledLongfellow`) and
`_adaptive_rhs_le N` (the same with the re-commitment term `tape·(L + N)/2^256` absorbed, the shape
of `NizkAdaptive` / `CompiledLongfellowAdaptive`), from the two generic lemmas `Row.fs_rhs_le_of`
and `Row.adaptive_rhs_le_of_slack`. For bounds of other shapes (for example one that charges the
list factor at the field slots only), the three parts of `R.bound` are certified separately:
`_fieldDensity_le`, `_ligeroDensity_le` (per candidate) and `_merkleTerm_le`. Every theorem of
`CertifiedV1`, `NizkGrinding`, `NizkAdaptive`, `CompiledLongfellow` and `CompiledLongfellowAdaptive`
that is stated for an abstract `R : Row` with `h : R.Valid` applies at these rows verbatim;
`Lfzk.CompiledV7` states the headlines.

Nothing here is a hypothesis: the numerals are closed `native_decide` facts. The modelling premises
of the theorems these rows instantiate are those theorems' (see `CertifiedV1`,
`CompiledLongfellowAdaptive`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.CertifiedV1

/-! ## The right-hand sides, generically -/

/-- **The grinding right-hand side from two certified numerals**: if the row's bound is at most
`2^-a` and its coefficient at most `2^-b`, then
`R.bound + N · R.fsCoefficient ≤ 2^-a + N · 2^-b`. -/
theorem Row.fs_rhs_le_of {R : Row} {a b : ℕ} (hb : R.bound ≤ (1 : ℚ) / 2 ^ a)
    (hc : R.fsCoefficient ≤ (1 : ℚ) / 2 ^ b) (N : ℕ) :
    R.bound + N * R.fsCoefficient ≤ (1 : ℚ) / 2 ^ a + N * ((1 : ℚ) / 2 ^ b) :=
  add_le_add hb (mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg N))

/-- **The re-committing right-hand side from two certified slack numerals**: if the bound plus the
re-commitment term at `N = 0` is at most `2^-a`, and the coefficient plus the per-query
re-commitment term is at most `2^-b`, then the full right-hand side of
`Row.adaptive_ratio_le` (and `CompiledLongfellowAdaptive.row_adaptive_ratio_le_v1`) is at most
`2^-a + N · 2^-b`. -/
theorem Row.adaptive_rhs_le_of_slack {R : Row} {a b : ℕ}
    (hsb : R.bound + ((R.tape * Rounds.Role.length R.params.nl R.params.rounds : ℕ) : ℚ)
        / 2 ^ R.params.digestBits ≤ (1 : ℚ) / 2 ^ a)
    (hsc : R.fsCoefficient + (R.tape : ℚ) / 2 ^ R.params.digestBits ≤ (1 : ℚ) / 2 ^ b)
    (N : ℕ) :
    R.bound + N * R.fsCoefficient
        + ((R.tape * (Rounds.Role.length R.params.nl R.params.rounds + N) : ℕ) : ℚ)
          / 2 ^ R.params.digestBits
      ≤ (1 : ℚ) / 2 ^ a + N * ((1 : ℚ) / 2 ^ b) := by
  have hsplit : ((R.tape * (Rounds.Role.length R.params.nl R.params.rounds + N) : ℕ) : ℚ)
        / 2 ^ R.params.digestBits
      = ((R.tape * Rounds.Role.length R.params.nl R.params.rounds : ℕ) : ℚ)
          / 2 ^ R.params.digestBits
        + N * ((R.tape : ℚ) / 2 ^ R.params.digestBits) := by
    push_cast
    ring
  rw [hsplit]
  have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg N
  have := mul_le_mul_of_nonneg_left hsc hN
  nlinarith

/-! ## The rows

Derived by `lfzk/scripts/v7_rows.py`, whose `--check` re-derives every numeral below;
`native_decide` checks each. -/

/-- The v7 signature component at its registered profile (21 layers, 542 sumcheck slots, 3739 input
wires): Ligero V1 at `n = 3187`, `k = 455`, 132 openings over P-256's base field
(`LigeroV1Rows.v7Sig`, `2^-122`); composed `2^-122`. -/
def v7Sig : Row :=
  { params :=
      { row := Lfzk.LigeroV1Rows.v7Sig
        q := 323, nl := 21,
        logw := fun ly => [9, 10, 11, 11, 12, 12, 12, 12, 13, 13, 13, 13, 14, 15, 15, 16, 16, 14, 14, 14, 12].getD ly 0,
        logc := 0, digestBits := 256, ninp := 3739,
        colBytes := 32, nfullWit := 1 }
    lam := 122, cardCand := 2,
    commitFuel := 2 ^ 60, tape := 2 ^ 62,
    sizeBound := 148224 }

theorem v7Sig_valid : v7Sig.Valid := of_decide_eq_true (by native_decide)
theorem v7Sig_sharp : v7Sig.Sharp := of_decide_eq_true (by native_decide)
theorem v7Sig_lam : v7Sig.lam = 122 := rfl
/-- The certified bound, `2^-122`. -/
theorem v7Sig_bound_le : v7Sig.bound ≤ (1 : ℚ) / 2 ^ 122 := Row.target v7Sig_valid
/-- The row opens `132` columns, so its compiler opens something. -/
theorem v7Sig_openings_pos : 0 < v7Sig.params.row.openings := by decide
/-- The profile: 21 layers, `542` sumcheck slots, 132 openings, over P-256's base field. -/
theorem v7Sig_shape :
    v7Sig.params.nl = 21 ∧ v7Sig.params.totalRounds = 542 ∧
      v7Sig.params.row.openings = 132 ∧
      v7Sig.params.row.fieldSize = Lfzk.LigeroV1Rows.p256Order := by
  refine ⟨rfl, by native_decide, rfl, by native_decide⟩
/-- The schedule length: `21 + 542 + 3`. -/
theorem v7Sig_length :
    Rounds.Role.length v7Sig.params.nl v7Sig.params.rounds = 566 := by
  native_decide
/-- **The work-normalized coefficient is at most `2^-122`.** -/
theorem v7Sig_fsCoefficient : v7Sig.fsCoefficient ≤ (1 : ℚ) / 2 ^ 122 := by
  native_decide
/-- …and `122` is its exact integer bit level. -/
theorem v7Sig_fsCoefficient_sharp : ¬ v7Sig.fsCoefficient ≤ (1 : ℚ) / 2 ^ 123 := by
  native_decide
/-- The worst slot at the row is the Ligero query slot, `cover`. -/
theorem v7Sig_maxDensity_eq :
    v7Sig.maxDensity = v7Sig.params.row.cover := by
  native_decide
/-- The grinding right-hand side: `2^-122 + N · 2^-122`. -/
theorem v7Sig_fs_rhs_le (N : ℕ) :
    v7Sig.bound + N * v7Sig.fsCoefficient ≤ (1 : ℚ) / 2 ^ 122 + N * ((1 : ℚ) / 2 ^ 122) :=
  Row.fs_rhs_le_of v7Sig_bound_le v7Sig_fsCoefficient N
/-- The re-commitment term at `N = 0` fits in the bound's slack. -/
theorem v7Sig_adaptive_slack_bound :
    v7Sig.bound
        + ((v7Sig.tape * Rounds.Role.length v7Sig.params.nl v7Sig.params.rounds : ℕ) : ℚ)
          / 2 ^ v7Sig.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 122 := by
  native_decide
/-- The per-query re-commitment term fits in the coefficient's slack. -/
theorem v7Sig_adaptive_slack_coeff :
    v7Sig.fsCoefficient + (v7Sig.tape : ℚ) / 2 ^ v7Sig.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 122 := by
  native_decide
/-- The re-committing right-hand side: `2^-122 + N · 2^-122`. -/
theorem v7Sig_adaptive_rhs_le (N : ℕ) :
    v7Sig.bound + N * v7Sig.fsCoefficient
        + ((v7Sig.tape
            * (Rounds.Role.length v7Sig.params.nl v7Sig.params.rounds + N) : ℕ) : ℚ)
          / 2 ^ v7Sig.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 122 + N * ((1 : ℚ) / 2 ^ 122) :=
  Row.adaptive_rhs_le_of_slack v7Sig_adaptive_slack_bound v7Sig_adaptive_slack_coeff N
/-- The bound's field-round part, `(2·nl + 2·Σ rounds + 1) / |F|`, per candidate: `2^-245`. -/
theorem v7Sig_fieldDensity_le : v7Sig.params.fieldDensity ≤ (1 : ℚ) / 2 ^ 245 := by
  native_decide
/-- The bound's Ligero part, `(fail + arith) + cover`, per candidate: `2^-123`. -/
theorem v7Sig_ligeroDensity_le : v7Sig.params.ligeroDensity ≤ (1 : ℚ) / 2 ^ 123 := by
  native_decide
/-- The bound's Merkle part: `2^-132`. -/
theorem v7Sig_merkleTerm_le :
    v7Sig.params.merkleTerm v7Sig.commitFuel v7Sig.tape ≤ (1 : ℚ) / 2 ^ 132 := by
  native_decide

/-- The v7 hash component for 1 attribute at its registered profile (17 layers, 566 sumcheck slots,
85118 input wires): Ligero V1 at `n = 3230`, `k = 461`, 132 openings over `GF(2^128)`
(`LigeroV1Rows.v7Hash1`, `2^-115`); composed `2^-115`. -/
def v7Hash1 : Row :=
  { params :=
      { row := Lfzk.LigeroV1Rows.v7Hash1
        q := 329, nl := 17,
        logw := fun ly => [13, 13, 14, 15, 16, 16, 16, 16, 17, 16, 17, 19, 20, 20, 19, 19, 17].getD ly 0,
        logc := 0, digestBits := 256, ninp := 85118,
        colBytes := 2, nfullWit := 1 }
    lam := 115, cardCand := 2,
    commitFuel := 2 ^ 60, tape := 2 ^ 62,
    sizeBound := 155056 }

theorem v7Hash1_valid : v7Hash1.Valid := of_decide_eq_true (by native_decide)
theorem v7Hash1_sharp : v7Hash1.Sharp := of_decide_eq_true (by native_decide)
theorem v7Hash1_lam : v7Hash1.lam = 115 := rfl
/-- The certified bound, `2^-115`. -/
theorem v7Hash1_bound_le : v7Hash1.bound ≤ (1 : ℚ) / 2 ^ 115 := Row.target v7Hash1_valid
/-- The row opens `132` columns, so its compiler opens something. -/
theorem v7Hash1_openings_pos : 0 < v7Hash1.params.row.openings := by decide
/-- The profile: 17 layers, `566` sumcheck slots, 132 openings, over `GF(2^128)`. -/
theorem v7Hash1_shape :
    v7Hash1.params.nl = 17 ∧ v7Hash1.params.totalRounds = 566 ∧
      v7Hash1.params.row.openings = 132 ∧
      v7Hash1.params.row.fieldSize = 2 ^ 128 := by
  refine ⟨rfl, by native_decide, rfl, by native_decide⟩
/-- The schedule length: `17 + 566 + 3`. -/
theorem v7Hash1_length :
    Rounds.Role.length v7Hash1.params.nl v7Hash1.params.rounds = 586 := by
  native_decide
/-- **The work-normalized coefficient is at most `2^-116`.** -/
theorem v7Hash1_fsCoefficient : v7Hash1.fsCoefficient ≤ (1 : ℚ) / 2 ^ 116 := by
  native_decide
/-- …and `116` is its exact integer bit level. -/
theorem v7Hash1_fsCoefficient_sharp : ¬ v7Hash1.fsCoefficient ≤ (1 : ℚ) / 2 ^ 117 := by
  native_decide
/-- The worst slot at the row is the Ligero challenge slot, `fail + arith`. -/
theorem v7Hash1_maxDensity_eq :
    v7Hash1.maxDensity = v7Hash1.params.row.fail + v7Hash1.params.row.arith := by
  native_decide
/-- The grinding right-hand side: `2^-115 + N · 2^-116`. -/
theorem v7Hash1_fs_rhs_le (N : ℕ) :
    v7Hash1.bound + N * v7Hash1.fsCoefficient ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) :=
  Row.fs_rhs_le_of v7Hash1_bound_le v7Hash1_fsCoefficient N
/-- The re-commitment term at `N = 0` fits in the bound's slack. -/
theorem v7Hash1_adaptive_slack_bound :
    v7Hash1.bound
        + ((v7Hash1.tape * Rounds.Role.length v7Hash1.params.nl v7Hash1.params.rounds : ℕ) : ℚ)
          / 2 ^ v7Hash1.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 115 := by
  native_decide
/-- The per-query re-commitment term fits in the coefficient's slack. -/
theorem v7Hash1_adaptive_slack_coeff :
    v7Hash1.fsCoefficient + (v7Hash1.tape : ℚ) / 2 ^ v7Hash1.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 116 := by
  native_decide
/-- The re-committing right-hand side: `2^-115 + N · 2^-116`. -/
theorem v7Hash1_adaptive_rhs_le (N : ℕ) :
    v7Hash1.bound + N * v7Hash1.fsCoefficient
        + ((v7Hash1.tape
            * (Rounds.Role.length v7Hash1.params.nl v7Hash1.params.rounds + N) : ℕ) : ℚ)
          / 2 ^ v7Hash1.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) :=
  Row.adaptive_rhs_le_of_slack v7Hash1_adaptive_slack_bound v7Hash1_adaptive_slack_coeff N
/-- The bound's field-round part, `(2·nl + 2·Σ rounds + 1) / |F|`, per candidate: `2^-117`. -/
theorem v7Hash1_fieldDensity_le : v7Hash1.params.fieldDensity ≤ (1 : ℚ) / 2 ^ 117 := by
  native_decide
/-- The bound's Ligero part, `(fail + arith) + cover`, per candidate: `2^-116`. -/
theorem v7Hash1_ligeroDensity_le : v7Hash1.params.ligeroDensity ≤ (1 : ℚ) / 2 ^ 116 := by
  native_decide
/-- The bound's Merkle part: `2^-132`. -/
theorem v7Hash1_merkleTerm_le :
    v7Hash1.params.merkleTerm v7Hash1.commitFuel v7Hash1.tape ≤ (1 : ℚ) / 2 ^ 132 := by
  native_decide

/-- The v7 hash component for 2 attributes at its registered profile (17 layers, 570 sumcheck slots,
90022 input wires): Ligero V1 at `n = 3318`, `k = 474`, 132 openings over `GF(2^128)`
(`LigeroV1Rows.v7Hash2`, `2^-115`); composed `2^-115`. -/
def v7Hash2 : Row :=
  { params :=
      { row := Lfzk.LigeroV1Rows.v7Hash2
        q := 342, nl := 17,
        logw := fun ly => [13, 13, 14, 15, 16, 16, 16, 17, 17, 17, 17, 19, 20, 20, 19, 19, 17].getD ly 0,
        logc := 0, digestBits := 256, ninp := 90022,
        colBytes := 2, nfullWit := 1 }
    lam := 115, cardCand := 2,
    commitFuel := 2 ^ 60, tape := 2 ^ 62,
    sizeBound := 157072 }

theorem v7Hash2_valid : v7Hash2.Valid := of_decide_eq_true (by native_decide)
theorem v7Hash2_sharp : v7Hash2.Sharp := of_decide_eq_true (by native_decide)
theorem v7Hash2_lam : v7Hash2.lam = 115 := rfl
/-- The certified bound, `2^-115`. -/
theorem v7Hash2_bound_le : v7Hash2.bound ≤ (1 : ℚ) / 2 ^ 115 := Row.target v7Hash2_valid
/-- The row opens `132` columns, so its compiler opens something. -/
theorem v7Hash2_openings_pos : 0 < v7Hash2.params.row.openings := by decide
/-- The profile: 17 layers, `570` sumcheck slots, 132 openings, over `GF(2^128)`. -/
theorem v7Hash2_shape :
    v7Hash2.params.nl = 17 ∧ v7Hash2.params.totalRounds = 570 ∧
      v7Hash2.params.row.openings = 132 ∧
      v7Hash2.params.row.fieldSize = 2 ^ 128 := by
  refine ⟨rfl, by native_decide, rfl, by native_decide⟩
/-- The schedule length: `17 + 570 + 3`. -/
theorem v7Hash2_length :
    Rounds.Role.length v7Hash2.params.nl v7Hash2.params.rounds = 590 := by
  native_decide
/-- **The work-normalized coefficient is at most `2^-116`.** -/
theorem v7Hash2_fsCoefficient : v7Hash2.fsCoefficient ≤ (1 : ℚ) / 2 ^ 116 := by
  native_decide
/-- …and `116` is its exact integer bit level. -/
theorem v7Hash2_fsCoefficient_sharp : ¬ v7Hash2.fsCoefficient ≤ (1 : ℚ) / 2 ^ 117 := by
  native_decide
/-- The worst slot at the row is the Ligero challenge slot, `fail + arith`. -/
theorem v7Hash2_maxDensity_eq :
    v7Hash2.maxDensity = v7Hash2.params.row.fail + v7Hash2.params.row.arith := by
  native_decide
/-- The grinding right-hand side: `2^-115 + N · 2^-116`. -/
theorem v7Hash2_fs_rhs_le (N : ℕ) :
    v7Hash2.bound + N * v7Hash2.fsCoefficient ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) :=
  Row.fs_rhs_le_of v7Hash2_bound_le v7Hash2_fsCoefficient N
/-- The re-commitment term at `N = 0` fits in the bound's slack. -/
theorem v7Hash2_adaptive_slack_bound :
    v7Hash2.bound
        + ((v7Hash2.tape * Rounds.Role.length v7Hash2.params.nl v7Hash2.params.rounds : ℕ) : ℚ)
          / 2 ^ v7Hash2.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 115 := by
  native_decide
/-- The per-query re-commitment term fits in the coefficient's slack. -/
theorem v7Hash2_adaptive_slack_coeff :
    v7Hash2.fsCoefficient + (v7Hash2.tape : ℚ) / 2 ^ v7Hash2.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 116 := by
  native_decide
/-- The re-committing right-hand side: `2^-115 + N · 2^-116`. -/
theorem v7Hash2_adaptive_rhs_le (N : ℕ) :
    v7Hash2.bound + N * v7Hash2.fsCoefficient
        + ((v7Hash2.tape
            * (Rounds.Role.length v7Hash2.params.nl v7Hash2.params.rounds + N) : ℕ) : ℚ)
          / 2 ^ v7Hash2.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) :=
  Row.adaptive_rhs_le_of_slack v7Hash2_adaptive_slack_bound v7Hash2_adaptive_slack_coeff N
/-- The bound's field-round part, `(2·nl + 2·Σ rounds + 1) / |F|`, per candidate: `2^-117`. -/
theorem v7Hash2_fieldDensity_le : v7Hash2.params.fieldDensity ≤ (1 : ℚ) / 2 ^ 117 := by
  native_decide
/-- The bound's Ligero part, `(fail + arith) + cover`, per candidate: `2^-116`. -/
theorem v7Hash2_ligeroDensity_le : v7Hash2.params.ligeroDensity ≤ (1 : ℚ) / 2 ^ 116 := by
  native_decide
/-- The bound's Merkle part: `2^-132`. -/
theorem v7Hash2_merkleTerm_le :
    v7Hash2.params.merkleTerm v7Hash2.commitFuel v7Hash2.tape ≤ (1 : ℚ) / 2 ^ 132 := by
  native_decide

/-- The v7 hash component for 3 attributes at its registered profile (17 layers, 574 sumcheck slots,
94926 input wires): Ligero V1 at `n = 3352`, `k = 478`, 132 openings over `GF(2^128)`
(`LigeroV1Rows.v7Hash3`, `2^-115`); composed `2^-115`. -/
def v7Hash3 : Row :=
  { params :=
      { row := Lfzk.LigeroV1Rows.v7Hash3
        q := 346, nl := 17,
        logw := fun ly => [13, 13, 14, 15, 16, 16, 16, 17, 17, 17, 18, 20, 20, 20, 19, 19, 17].getD ly 0,
        logc := 0, digestBits := 256, ninp := 94926,
        colBytes := 2, nfullWit := 1 }
    lam := 115, cardCand := 2,
    commitFuel := 2 ^ 60, tape := 2 ^ 62,
    sizeBound := 160360 }

theorem v7Hash3_valid : v7Hash3.Valid := of_decide_eq_true (by native_decide)
theorem v7Hash3_sharp : v7Hash3.Sharp := of_decide_eq_true (by native_decide)
theorem v7Hash3_lam : v7Hash3.lam = 115 := rfl
/-- The certified bound, `2^-115`. -/
theorem v7Hash3_bound_le : v7Hash3.bound ≤ (1 : ℚ) / 2 ^ 115 := Row.target v7Hash3_valid
/-- The row opens `132` columns, so its compiler opens something. -/
theorem v7Hash3_openings_pos : 0 < v7Hash3.params.row.openings := by decide
/-- The profile: 17 layers, `574` sumcheck slots, 132 openings, over `GF(2^128)`. -/
theorem v7Hash3_shape :
    v7Hash3.params.nl = 17 ∧ v7Hash3.params.totalRounds = 574 ∧
      v7Hash3.params.row.openings = 132 ∧
      v7Hash3.params.row.fieldSize = 2 ^ 128 := by
  refine ⟨rfl, by native_decide, rfl, by native_decide⟩
/-- The schedule length: `17 + 574 + 3`. -/
theorem v7Hash3_length :
    Rounds.Role.length v7Hash3.params.nl v7Hash3.params.rounds = 594 := by
  native_decide
/-- **The work-normalized coefficient is at most `2^-116`.** -/
theorem v7Hash3_fsCoefficient : v7Hash3.fsCoefficient ≤ (1 : ℚ) / 2 ^ 116 := by
  native_decide
/-- …and `116` is its exact integer bit level. -/
theorem v7Hash3_fsCoefficient_sharp : ¬ v7Hash3.fsCoefficient ≤ (1 : ℚ) / 2 ^ 117 := by
  native_decide
/-- The worst slot at the row is the Ligero challenge slot, `fail + arith`. -/
theorem v7Hash3_maxDensity_eq :
    v7Hash3.maxDensity = v7Hash3.params.row.fail + v7Hash3.params.row.arith := by
  native_decide
/-- The grinding right-hand side: `2^-115 + N · 2^-116`. -/
theorem v7Hash3_fs_rhs_le (N : ℕ) :
    v7Hash3.bound + N * v7Hash3.fsCoefficient ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) :=
  Row.fs_rhs_le_of v7Hash3_bound_le v7Hash3_fsCoefficient N
/-- The re-commitment term at `N = 0` fits in the bound's slack. -/
theorem v7Hash3_adaptive_slack_bound :
    v7Hash3.bound
        + ((v7Hash3.tape * Rounds.Role.length v7Hash3.params.nl v7Hash3.params.rounds : ℕ) : ℚ)
          / 2 ^ v7Hash3.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 115 := by
  native_decide
/-- The per-query re-commitment term fits in the coefficient's slack. -/
theorem v7Hash3_adaptive_slack_coeff :
    v7Hash3.fsCoefficient + (v7Hash3.tape : ℚ) / 2 ^ v7Hash3.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 116 := by
  native_decide
/-- The re-committing right-hand side: `2^-115 + N · 2^-116`. -/
theorem v7Hash3_adaptive_rhs_le (N : ℕ) :
    v7Hash3.bound + N * v7Hash3.fsCoefficient
        + ((v7Hash3.tape
            * (Rounds.Role.length v7Hash3.params.nl v7Hash3.params.rounds + N) : ℕ) : ℚ)
          / 2 ^ v7Hash3.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) :=
  Row.adaptive_rhs_le_of_slack v7Hash3_adaptive_slack_bound v7Hash3_adaptive_slack_coeff N
/-- The bound's field-round part, `(2·nl + 2·Σ rounds + 1) / |F|`, per candidate: `2^-117`. -/
theorem v7Hash3_fieldDensity_le : v7Hash3.params.fieldDensity ≤ (1 : ℚ) / 2 ^ 117 := by
  native_decide
/-- The bound's Ligero part, `(fail + arith) + cover`, per candidate: `2^-116`. -/
theorem v7Hash3_ligeroDensity_le : v7Hash3.params.ligeroDensity ≤ (1 : ℚ) / 2 ^ 116 := by
  native_decide
/-- The bound's Merkle part: `2^-132`. -/
theorem v7Hash3_merkleTerm_le :
    v7Hash3.params.merkleTerm v7Hash3.commitFuel v7Hash3.tape ≤ (1 : ℚ) / 2 ^ 132 := by
  native_decide

/-- The v7 hash component for 4 attributes at its registered profile (17 layers, 574 sumcheck slots,
99830 input wires): Ligero V1 at `n = 3436`, `k = 490`, 132 openings over `GF(2^128)`
(`LigeroV1Rows.v7Hash4`, `2^-115`); composed `2^-115`. -/
def v7Hash4 : Row :=
  { params :=
      { row := Lfzk.LigeroV1Rows.v7Hash4
        q := 358, nl := 17,
        logw := fun ly => [13, 13, 14, 15, 16, 16, 16, 17, 17, 17, 18, 20, 20, 20, 19, 19, 17].getD ly 0,
        logc := 0, digestBits := 256, ninp := 99830,
        colBytes := 2, nfullWit := 1 }
    lam := 115, cardCand := 2,
    commitFuel := 2 ^ 60, tape := 2 ^ 62,
    sizeBound := 162448 }

theorem v7Hash4_valid : v7Hash4.Valid := of_decide_eq_true (by native_decide)
theorem v7Hash4_sharp : v7Hash4.Sharp := of_decide_eq_true (by native_decide)
theorem v7Hash4_lam : v7Hash4.lam = 115 := rfl
/-- The certified bound, `2^-115`. -/
theorem v7Hash4_bound_le : v7Hash4.bound ≤ (1 : ℚ) / 2 ^ 115 := Row.target v7Hash4_valid
/-- The row opens `132` columns, so its compiler opens something. -/
theorem v7Hash4_openings_pos : 0 < v7Hash4.params.row.openings := by decide
/-- The profile: 17 layers, `574` sumcheck slots, 132 openings, over `GF(2^128)`. -/
theorem v7Hash4_shape :
    v7Hash4.params.nl = 17 ∧ v7Hash4.params.totalRounds = 574 ∧
      v7Hash4.params.row.openings = 132 ∧
      v7Hash4.params.row.fieldSize = 2 ^ 128 := by
  refine ⟨rfl, by native_decide, rfl, by native_decide⟩
/-- The schedule length: `17 + 574 + 3`. -/
theorem v7Hash4_length :
    Rounds.Role.length v7Hash4.params.nl v7Hash4.params.rounds = 594 := by
  native_decide
/-- **The work-normalized coefficient is at most `2^-116`.** -/
theorem v7Hash4_fsCoefficient : v7Hash4.fsCoefficient ≤ (1 : ℚ) / 2 ^ 116 := by
  native_decide
/-- …and `116` is its exact integer bit level. -/
theorem v7Hash4_fsCoefficient_sharp : ¬ v7Hash4.fsCoefficient ≤ (1 : ℚ) / 2 ^ 117 := by
  native_decide
/-- The worst slot at the row is the Ligero challenge slot, `fail + arith`. -/
theorem v7Hash4_maxDensity_eq :
    v7Hash4.maxDensity = v7Hash4.params.row.fail + v7Hash4.params.row.arith := by
  native_decide
/-- The grinding right-hand side: `2^-115 + N · 2^-116`. -/
theorem v7Hash4_fs_rhs_le (N : ℕ) :
    v7Hash4.bound + N * v7Hash4.fsCoefficient ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) :=
  Row.fs_rhs_le_of v7Hash4_bound_le v7Hash4_fsCoefficient N
/-- The re-commitment term at `N = 0` fits in the bound's slack. -/
theorem v7Hash4_adaptive_slack_bound :
    v7Hash4.bound
        + ((v7Hash4.tape * Rounds.Role.length v7Hash4.params.nl v7Hash4.params.rounds : ℕ) : ℚ)
          / 2 ^ v7Hash4.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 115 := by
  native_decide
/-- The per-query re-commitment term fits in the coefficient's slack. -/
theorem v7Hash4_adaptive_slack_coeff :
    v7Hash4.fsCoefficient + (v7Hash4.tape : ℚ) / 2 ^ v7Hash4.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 116 := by
  native_decide
/-- The re-committing right-hand side: `2^-115 + N · 2^-116`. -/
theorem v7Hash4_adaptive_rhs_le (N : ℕ) :
    v7Hash4.bound + N * v7Hash4.fsCoefficient
        + ((v7Hash4.tape
            * (Rounds.Role.length v7Hash4.params.nl v7Hash4.params.rounds + N) : ℕ) : ℚ)
          / 2 ^ v7Hash4.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) :=
  Row.adaptive_rhs_le_of_slack v7Hash4_adaptive_slack_bound v7Hash4_adaptive_slack_coeff N
/-- The bound's field-round part, `(2·nl + 2·Σ rounds + 1) / |F|`, per candidate: `2^-117`. -/
theorem v7Hash4_fieldDensity_le : v7Hash4.params.fieldDensity ≤ (1 : ℚ) / 2 ^ 117 := by
  native_decide
/-- The bound's Ligero part, `(fail + arith) + cover`, per candidate: `2^-116`. -/
theorem v7Hash4_ligeroDensity_le : v7Hash4.params.ligeroDensity ≤ (1 : ℚ) / 2 ^ 116 := by
  native_decide
/-- The bound's Merkle part: `2^-132`. -/
theorem v7Hash4_merkleTerm_le :
    v7Hash4.params.merkleTerm v7Hash4.commitFuel v7Hash4.tape ≤ (1 : ℚ) / 2 ^ 132 := by
  native_decide

/-- The five v7 rows. -/
def v7Rows : List Row := [v7Sig, v7Hash1, v7Hash2, v7Hash3, v7Hash4]

theorem v7Rows_count : v7Rows.length = 5 := rfl

end Lfzk.CertifiedV1
