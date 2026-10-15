import Lfzk.TwoFieldV1Rows
import Lfzk.NizkAdaptiveTwoField
import Lfzk.CertifiedV7

/-!
# Certified two-field V1 rows at the deployed v7 parameters

`Lfzk.TwoFieldV1Rows.p256sha` pairs the v8 signature and hash rows. This file pairs the deployed v7
rows: the signature row `CertifiedV1.v7Sig` (P-256 base field) with each of the four hash rows
`CertifiedV1.v7Hash1` … `v7Hash4` (`GF(2^128)`), composed through the MAC over a field of `2^128`
elements — one pair per registered v7 circuit archive (`ZK_SPECS` version 7, 1–4 attributes):

| pair | ECDSA side | SHA side | composed `lam` | adaptive coefficient | `len2` | modelled bytes |
|---|---|---|---|---|---|---|
| `v7P256Sha1` | `v7Sig` (122) | `v7Hash1` (115) | 115 | 116 | 1153 | 303280 |
| `v7P256Sha2` | `v7Sig` (122) | `v7Hash2` (115) | 115 | 116 | 1157 | 305296 |
| `v7P256Sha3` | `v7Sig` (122) | `v7Hash3` (115) | 115 | 116 | 1161 | 308584 |
| `v7P256Sha4` | `v7Sig` (122) | `v7Hash4` (115) | 115 | 116 | 1161 | 310672 |

`lam` is the exact integer bit level of `ecdsa.bound + sha.bound + 1/2^128` (`_valid`, `_sharp`);
the adaptive coefficient is that of `max(κ₁, κ₂, 2^-128) + 2·tape/2^256` (`_adaptive_slack_coeff`),
the per-query factor of the re-committing headline. For comparison, v8 (`p256sha`): `lam` 114,
coefficient 115.

What is proved, per pair: `TwoFieldRowV1.Valid` (all twelve conjuncts, both sides included) and
`Sharp` by `native_decide`; the non-vacuity facts of `p256sha` (`_fieldSizes`,
`_commitFuel_lt_tape`, `_fuel`, `_premises_satisfiable`) at the pair; the composed statement at
Protocol 3.8's schedule `_nizk_ratio_le_keyFirst` (`≤ 2^-115`); and the numerals of the
re-committing two-field headline (`_len2`, `_adaptive_slack_bound`, `_adaptive_slack_coeff`,
`_adaptive_rhs_le`) through the generic `TwoFieldRowV1.adaptive_rhs_le_of_slack`. `Lfzk.CompiledV7`
states the compiled-verifier headlines.

What remains a hypothesis is exactly what `TwoFieldRowV1.nizk_ratio_le` /
`NizkAdaptiveTwoField.twofield_adaptive_ratio_le` take (per side a `V1Family` / `Side`: `hfalse`,
`hright`, `hexact`, the field half of LayerStep; the MAC slot's `decode`, `hbal`, `hmac`,
`|Fmac| = 2^128`; the MAC rows `hrow₁`, `hrow₂`); see `Lfzk.TwoFieldV1Rows`. Numerals are re-derived
by `lfzk/scripts/v7_rows.py --check`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.TwoFieldV1Rows

open Finset

/-! ## Generic: the schedule length and the re-committing right-hand side -/

/-- The tape length of Protocol 3.8's schedule at a two-field row: the key slot, then both
sides. -/
abbrev TwoFieldRowV1.keyFirstLen (R : TwoFieldRowV1) : ℕ :=
  1 + Rounds.Role.length R.ecdsa.params.nl R.ecdsa.params.rounds
    + Rounds.Role.length R.sha.params.nl R.sha.params.rounds

open Lfzk.NizkAdaptiveTwoField in
/-- **The re-committing two-field right-hand side from two certified slack numerals**: if the
composed bound plus the two cut-trace extractions' term at `N = 0` is at most `2^-a`, and the worst
role's coefficient plus the per-query term is at most `2^-b`, then the right-hand side of
`NizkAdaptiveTwoField.twofield_adaptive_ratio_le` (and
`CompiledLongfellowAdaptive.twofield_adaptive_compiled_ratio_le`) is at most `2^-a + N · 2^-b`. -/
theorem TwoFieldRowV1.adaptive_rhs_le_of_slack {R : TwoFieldRowV1} {a b : ℕ}
    {Fmac : Type} [Fintype Fmac] (hFmac : Fintype.card Fmac = R.macFieldSize)
    (hsb : R.ecdsa.bound + R.sha.bound + 1 / (R.macFieldSize : ℚ)
        + 2 * (((R.ecdsa.tape * len2 R.ecdsa R.sha : ℕ) : ℚ) / 2 ^ R.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ a)
    (hsc : max (max R.ecdsa.fsCoefficient R.sha.fsCoefficient) (1 / (R.macFieldSize : ℚ))
        + 2 * ((R.ecdsa.tape : ℚ) / 2 ^ R.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ b)
    (N : ℕ) :
    R.ecdsa.bound + R.sha.bound + 1 / (Fintype.card Fmac : ℚ)
        + N * max (max R.ecdsa.fsCoefficient R.sha.fsCoefficient) (1 / (Fintype.card Fmac : ℚ))
        + 2 * (((R.ecdsa.tape * (len2 R.ecdsa R.sha + N) : ℕ) : ℚ)
          / 2 ^ R.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ a + N * ((1 : ℚ) / 2 ^ b) := by
  have hmf : (Fintype.card Fmac : ℚ) = (R.macFieldSize : ℚ) := by rw [hFmac]
  rw [hmf]
  have hsplit : 2 * (((R.ecdsa.tape * (len2 R.ecdsa R.sha + N) : ℕ) : ℚ)
        / 2 ^ R.ecdsa.params.digestBits)
      = 2 * (((R.ecdsa.tape * len2 R.ecdsa R.sha : ℕ) : ℚ) / 2 ^ R.ecdsa.params.digestBits)
        + N * (2 * ((R.ecdsa.tape : ℚ) / 2 ^ R.ecdsa.params.digestBits)) := by
    push_cast
    ring
  rw [hsplit]
  have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg N
  have := mul_le_mul_of_nonneg_left hsc hN
  nlinarith

/-! ## The rows

Derived by `lfzk/scripts/v7_rows.py`, whose `--check` re-derives every numeral below;
`native_decide` checks each. -/

/-- The deployed v7 pair for 1 attribute: ECDSA over `P-256`'s base field (`CertifiedV1.v7Sig`) and
SHA over `GF(2^128)` (`CertifiedV1.v7Hash1`), V1 at 132 openings on both fields, one shared hash
tape of `2^62` slots: `2^-115`. -/
def v7P256Sha1 : TwoFieldRowV1 :=
  { ecdsa := CertifiedV1.v7Sig, sha := CertifiedV1.v7Hash1,
    macFieldSize := 2 ^ 128, lam := 115, sizeBound := 303280 }

theorem v7P256Sha1_valid : v7P256Sha1.Valid := of_decide_eq_true (by native_decide)
theorem v7P256Sha1_sharp : v7P256Sha1.Sharp := of_decide_eq_true (by native_decide)
theorem v7P256Sha1_lam : v7P256Sha1.lam = 115 := rfl
/-- The certified composed bound, `2^-115`. -/
theorem v7P256Sha1_bound_le : v7P256Sha1.bound ≤ (1 : ℚ) / 2 ^ 115 :=
  TwoFieldRowV1.target v7P256Sha1_valid
theorem v7P256Sha1_ecdsa_valid : v7P256Sha1.ecdsa.Valid :=
  TwoFieldRowV1.ecdsa_valid v7P256Sha1_valid
theorem v7P256Sha1_sha_valid : v7P256Sha1.sha.Valid :=
  TwoFieldRowV1.sha_valid v7P256Sha1_valid
/-- The `P-256` side opens `132` columns. -/
theorem v7P256Sha1_ecdsa_openings_pos : 0 < v7P256Sha1.ecdsa.params.row.openings := by decide
/-- The `GF(2^128)` side opens `132` columns. -/
theorem v7P256Sha1_sha_openings_pos : 0 < v7P256Sha1.sha.params.row.openings := by decide

/-- The two sides' fields: `p` and `2^128`. -/
theorem v7P256Sha1_fieldSizes :
    v7P256Sha1.ecdsa.params.row.fieldSize = Lfzk.LigeroV1Rows.p256Order ∧
      v7P256Sha1.sha.params.row.fieldSize = 2 ^ 128 ∧ v7P256Sha1.macFieldSize = 2 ^ 128 := by
  refine ⟨?_, ?_, rfl⟩ <;> decide

/-- **The V3 fuel failure does not occur**: neither side records `commitFuel = tape`. -/
theorem v7P256Sha1_commitFuel_lt_tape :
    v7P256Sha1.ecdsa.commitFuel < v7P256Sha1.ecdsa.tape ∧
      v7P256Sha1.sha.commitFuel < v7P256Sha1.sha.tape :=
  ⟨(TwoFieldRowV1.fuel_satisfiable v7P256Sha1_valid).2.2.2.2.2.2.2.1,
    (TwoFieldRowV1.fuel_satisfiable v7P256Sha1_valid).2.2.2.2.2.2.2.2⟩

/-- **The fuel premises hold at `v7P256Sha1` with real fuel on both sides**: at the two sides'
column counts (`3187` and `3230`) and `2^59 - 3230` opening fuel for each of the four reveal/respond
stages, both sides' `ht₁`, `hT`, `hT1` hold on the shared `2^62`-slot tape, and so does the joint
budget. -/
theorem v7P256Sha1_fuel :
    let n₁ := 3187
    let n₂ := 3230
    let f := 2 ^ 59 - 3230
    v7P256Sha1.ecdsa.params.row.n = n₁ ∧ v7P256Sha1.sha.params.row.n = n₂ ∧
      v7P256Sha1.ecdsa.tape = v7P256Sha1.sha.tape ∧
      v7P256Sha1.ecdsa.commitFuel ≤ v7P256Sha1.sha.tape ∧
      v7P256Sha1.sha.commitFuel ≤ v7P256Sha1.sha.tape ∧
      1 ≤ v7P256Sha1.sha.tape ∧
      2 * n₁ + (f + f) + v7P256Sha1.ecdsa.commitFuel ≤ v7P256Sha1.sha.tape ∧
      2 * n₂ + (f + f) + v7P256Sha1.sha.commitFuel ≤ v7P256Sha1.sha.tape ∧
      (2 * n₁ + (f + f) + v7P256Sha1.ecdsa.commitFuel)
        + (2 * n₂ + (f + f) + v7P256Sha1.sha.commitFuel) ≤ v7P256Sha1.sha.tape ∧ 0 < f := by
  intro n₁ n₂ f
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [n₁, n₂, f, v7P256Sha1, CertifiedV1.v7Sig, CertifiedV1.v7Hash1] <;> norm_num

open Lfzk.TwoFieldV1Fields in
/-- **Every numeric and type-level premise of the composed theorem is satisfiable at `v7P256Sha1`**,
as `p256sha_premises_satisfiable` is at `p256sha`: the fields `ZMod p` and `GaloisField 2 128` with
the sides' cardinalities, both Reed–Solomon domains, the candidate and digest types, the MAC key
decoder's balance and the pair budgets' room on the shared coin alphabet. -/
theorem v7P256Sha1_premises_satisfiable :
    Fintype.card FP256 = v7P256Sha1.ecdsa.params.row.fieldSize ∧
      Fintype.card GF128 = v7P256Sha1.sha.params.row.fieldSize ∧
      Fintype.card GF128 = v7P256Sha1.macFieldSize ∧
      Nonempty (LigeroFamily.ReedSolomon.Domain FP256 v7P256Sha1.ecdsa.params.row.openings
        v7P256Sha1.ecdsa.params.q v7P256Sha1.ecdsa.params.row.n) ∧
      Nonempty (LigeroFamily.ReedSolomon.Domain GF128 v7P256Sha1.sha.params.row.openings
        v7P256Sha1.sha.params.q v7P256Sha1.sha.params.row.n) ∧
      Fintype.card (Fin 2) = v7P256Sha1.ecdsa.cardCand ∧
      Fintype.card (Fin 2) = v7P256Sha1.sha.cardCand ∧
      Fintype.card (Fin (2 ^ 256)) = 2 ^ v7P256Sha1.ecdsa.params.digestBits ∧
      Fintype.card (Fin (2 ^ 256)) = 2 ^ v7P256Sha1.sha.params.digestBits ∧
      (macD FP256 (LigeroV1LayerStep.Chal FP256 Unit v7P256Sha1.ecdsa.params.nw
              v7P256Sha1.ecdsa.params.nq)
          (LigeroV1LayerStep.Qry v7P256Sha1.ecdsa.params.row) GF128
          (LigeroV1LayerStep.Chal GF128 Unit v7P256Sha1.sha.params.nw v7P256Sha1.sha.params.nq)
          (LigeroV1LayerStep.Qry v7P256Sha1.sha.params.row) GF128).k * Fintype.card GF128
        ≤ Fintype.card (TwoFieldCoins FP256
            (LigeroV1LayerStep.Chal FP256 Unit v7P256Sha1.ecdsa.params.nw
              v7P256Sha1.ecdsa.params.nq)
            (LigeroV1LayerStep.Qry v7P256Sha1.ecdsa.params.row) GF128
            (LigeroV1LayerStep.Chal GF128 Unit v7P256Sha1.sha.params.nw v7P256Sha1.sha.params.nq)
            (LigeroV1LayerStep.Qry v7P256Sha1.sha.params.row) GF128) ∧
      2 * Fintype.card FP256 ≤ CertifiedV1.pairBudget
        (Fintype.card (TwoFieldCoins FP256
            (LigeroV1LayerStep.Chal FP256 Unit v7P256Sha1.ecdsa.params.nw
              v7P256Sha1.ecdsa.params.nq)
            (LigeroV1LayerStep.Qry v7P256Sha1.ecdsa.params.row) GF128
            (LigeroV1LayerStep.Chal GF128 Unit v7P256Sha1.sha.params.nw v7P256Sha1.sha.params.nq)
            (LigeroV1LayerStep.Qry v7P256Sha1.sha.params.row) GF128))
        (Fintype.card FP256) ∧
      2 * Fintype.card GF128 ≤ CertifiedV1.pairBudget
        (Fintype.card (TwoFieldCoins FP256
            (LigeroV1LayerStep.Chal FP256 Unit v7P256Sha1.ecdsa.params.nw
              v7P256Sha1.ecdsa.params.nq)
            (LigeroV1LayerStep.Qry v7P256Sha1.ecdsa.params.row) GF128
            (LigeroV1LayerStep.Chal GF128 Unit v7P256Sha1.sha.params.nw v7P256Sha1.sha.params.nq)
            (LigeroV1LayerStep.Qry v7P256Sha1.sha.params.row) GF128))
        (Fintype.card GF128) := by
  have hF₁ : Fintype.card FP256 = v7P256Sha1.ecdsa.params.row.fieldSize := by
    rw [p256_card]; exact v7P256Sha1_fieldSizes.1.symm
  have hF₂ : Fintype.card GF128 = v7P256Sha1.sha.params.row.fieldSize := by
    rw [gf128_card]; exact v7P256Sha1_fieldSizes.2.1.symm
  haveI : Nonempty (LigeroV1LayerStep.Qry v7P256Sha1.ecdsa.params.row) :=
    LigeroFamily.QuerySet.nonempty (by decide)
  haveI : Nonempty (LigeroV1LayerStep.Qry v7P256Sha1.sha.params.row) :=
    LigeroFamily.QuerySet.nonempty (by decide)
  refine ⟨hF₁, hF₂, by rw [gf128_card]; rfl,
    TwoFieldRowV1.domain_exists_ecdsa v7P256Sha1_valid hF₁,
    TwoFieldRowV1.domain_exists_sha v7P256Sha1_valid hF₂,
    by simp [v7P256Sha1, CertifiedV1.v7Sig], by simp [v7P256Sha1, CertifiedV1.v7Hash1],
    by simp [v7P256Sha1, CertifiedV1.v7Sig], by simp [v7P256Sha1, CertifiedV1.v7Hash1],
    (macD _ _ _ _ _ _ _).hexact, pair_room (side₁ _ _ _ _ _ _ _).1,
    pair_room (side₂ _ _ _ _ _ _ _).1⟩

open Lfzk.NizkAdaptiveTwoField in
/-- The two-field schedule at `v7P256Sha1`: the key round, then `566` and `586` slots. -/
theorem v7P256Sha1_len2 : len2 v7P256Sha1.ecdsa v7P256Sha1.sha = 1153 := by
  native_decide

open Lfzk.NizkAdaptiveTwoField in
/-- **The re-commitment terms at `N = 0` fit in the row's slack**: the composed bound plus two
cut-trace extractions' `tape · 1153 / 2^256` is still at most `2^-115`. -/
theorem v7P256Sha1_adaptive_slack_bound :
    v7P256Sha1.ecdsa.bound + v7P256Sha1.sha.bound + 1 / (v7P256Sha1.macFieldSize : ℚ)
        + 2 * (((v7P256Sha1.ecdsa.tape * len2 v7P256Sha1.ecdsa v7P256Sha1.sha : ℕ) : ℚ)
          / 2 ^ v7P256Sha1.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 115 := by
  native_decide

/-- **The per-query coefficient fits too**: the worst role's coefficient (the `GF(2^128)` side's
`κ₂ ≤ 2^-116`, above `κ₁ ≤ 2^-122` and the key slot's `2^-128`) plus `2 · tape / 2^256` is at most
`2^-116`. -/
theorem v7P256Sha1_adaptive_slack_coeff :
    max (max v7P256Sha1.ecdsa.fsCoefficient v7P256Sha1.sha.fsCoefficient)
        (1 / (v7P256Sha1.macFieldSize : ℚ))
      + 2 * ((v7P256Sha1.ecdsa.tape : ℚ) / 2 ^ v7P256Sha1.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 116 := by
  native_decide

open Lfzk.NizkAdaptiveTwoField in
/-- The re-committing two-field right-hand side at `v7P256Sha1`:
`2^-115 + N · 2^-116`. -/
theorem v7P256Sha1_adaptive_rhs_le (N : ℕ) {Fmac : Type} [Fintype Fmac]
    (hFmac : Fintype.card Fmac = 2 ^ 128) :
    v7P256Sha1.ecdsa.bound + v7P256Sha1.sha.bound + 1 / (Fintype.card Fmac : ℚ)
        + N * max (max v7P256Sha1.ecdsa.fsCoefficient v7P256Sha1.sha.fsCoefficient)
            (1 / (Fintype.card Fmac : ℚ))
        + 2 * (((v7P256Sha1.ecdsa.tape * (len2 v7P256Sha1.ecdsa v7P256Sha1.sha + N) : ℕ) : ℚ)
          / 2 ^ v7P256Sha1.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) :=
  TwoFieldRowV1.adaptive_rhs_le_of_slack hFmac v7P256Sha1_adaptive_slack_bound
    v7P256Sha1_adaptive_slack_coeff N

/-- The deployed v7 pair for 2 attributes: ECDSA over `P-256`'s base field (`CertifiedV1.v7Sig`) and
SHA over `GF(2^128)` (`CertifiedV1.v7Hash2`), V1 at 132 openings on both fields, one shared hash
tape of `2^62` slots: `2^-115`. -/
def v7P256Sha2 : TwoFieldRowV1 :=
  { ecdsa := CertifiedV1.v7Sig, sha := CertifiedV1.v7Hash2,
    macFieldSize := 2 ^ 128, lam := 115, sizeBound := 305296 }

theorem v7P256Sha2_valid : v7P256Sha2.Valid := of_decide_eq_true (by native_decide)
theorem v7P256Sha2_sharp : v7P256Sha2.Sharp := of_decide_eq_true (by native_decide)
theorem v7P256Sha2_lam : v7P256Sha2.lam = 115 := rfl
/-- The certified composed bound, `2^-115`. -/
theorem v7P256Sha2_bound_le : v7P256Sha2.bound ≤ (1 : ℚ) / 2 ^ 115 :=
  TwoFieldRowV1.target v7P256Sha2_valid
theorem v7P256Sha2_ecdsa_valid : v7P256Sha2.ecdsa.Valid :=
  TwoFieldRowV1.ecdsa_valid v7P256Sha2_valid
theorem v7P256Sha2_sha_valid : v7P256Sha2.sha.Valid :=
  TwoFieldRowV1.sha_valid v7P256Sha2_valid
/-- The `P-256` side opens `132` columns. -/
theorem v7P256Sha2_ecdsa_openings_pos : 0 < v7P256Sha2.ecdsa.params.row.openings := by decide
/-- The `GF(2^128)` side opens `132` columns. -/
theorem v7P256Sha2_sha_openings_pos : 0 < v7P256Sha2.sha.params.row.openings := by decide

/-- The two sides' fields: `p` and `2^128`. -/
theorem v7P256Sha2_fieldSizes :
    v7P256Sha2.ecdsa.params.row.fieldSize = Lfzk.LigeroV1Rows.p256Order ∧
      v7P256Sha2.sha.params.row.fieldSize = 2 ^ 128 ∧ v7P256Sha2.macFieldSize = 2 ^ 128 := by
  refine ⟨?_, ?_, rfl⟩ <;> decide

/-- **The V3 fuel failure does not occur**: neither side records `commitFuel = tape`. -/
theorem v7P256Sha2_commitFuel_lt_tape :
    v7P256Sha2.ecdsa.commitFuel < v7P256Sha2.ecdsa.tape ∧
      v7P256Sha2.sha.commitFuel < v7P256Sha2.sha.tape :=
  ⟨(TwoFieldRowV1.fuel_satisfiable v7P256Sha2_valid).2.2.2.2.2.2.2.1,
    (TwoFieldRowV1.fuel_satisfiable v7P256Sha2_valid).2.2.2.2.2.2.2.2⟩

/-- **The fuel premises hold at `v7P256Sha2` with real fuel on both sides**: at the two sides'
column counts (`3187` and `3318`) and `2^59 - 3318` opening fuel for each of the four reveal/respond
stages, both sides' `ht₁`, `hT`, `hT1` hold on the shared `2^62`-slot tape, and so does the joint
budget. -/
theorem v7P256Sha2_fuel :
    let n₁ := 3187
    let n₂ := 3318
    let f := 2 ^ 59 - 3318
    v7P256Sha2.ecdsa.params.row.n = n₁ ∧ v7P256Sha2.sha.params.row.n = n₂ ∧
      v7P256Sha2.ecdsa.tape = v7P256Sha2.sha.tape ∧
      v7P256Sha2.ecdsa.commitFuel ≤ v7P256Sha2.sha.tape ∧
      v7P256Sha2.sha.commitFuel ≤ v7P256Sha2.sha.tape ∧
      1 ≤ v7P256Sha2.sha.tape ∧
      2 * n₁ + (f + f) + v7P256Sha2.ecdsa.commitFuel ≤ v7P256Sha2.sha.tape ∧
      2 * n₂ + (f + f) + v7P256Sha2.sha.commitFuel ≤ v7P256Sha2.sha.tape ∧
      (2 * n₁ + (f + f) + v7P256Sha2.ecdsa.commitFuel)
        + (2 * n₂ + (f + f) + v7P256Sha2.sha.commitFuel) ≤ v7P256Sha2.sha.tape ∧ 0 < f := by
  intro n₁ n₂ f
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [n₁, n₂, f, v7P256Sha2, CertifiedV1.v7Sig, CertifiedV1.v7Hash2] <;> norm_num

open Lfzk.TwoFieldV1Fields in
/-- **Every numeric and type-level premise of the composed theorem is satisfiable at `v7P256Sha2`**,
as `p256sha_premises_satisfiable` is at `p256sha`: the fields `ZMod p` and `GaloisField 2 128` with
the sides' cardinalities, both Reed–Solomon domains, the candidate and digest types, the MAC key
decoder's balance and the pair budgets' room on the shared coin alphabet. -/
theorem v7P256Sha2_premises_satisfiable :
    Fintype.card FP256 = v7P256Sha2.ecdsa.params.row.fieldSize ∧
      Fintype.card GF128 = v7P256Sha2.sha.params.row.fieldSize ∧
      Fintype.card GF128 = v7P256Sha2.macFieldSize ∧
      Nonempty (LigeroFamily.ReedSolomon.Domain FP256 v7P256Sha2.ecdsa.params.row.openings
        v7P256Sha2.ecdsa.params.q v7P256Sha2.ecdsa.params.row.n) ∧
      Nonempty (LigeroFamily.ReedSolomon.Domain GF128 v7P256Sha2.sha.params.row.openings
        v7P256Sha2.sha.params.q v7P256Sha2.sha.params.row.n) ∧
      Fintype.card (Fin 2) = v7P256Sha2.ecdsa.cardCand ∧
      Fintype.card (Fin 2) = v7P256Sha2.sha.cardCand ∧
      Fintype.card (Fin (2 ^ 256)) = 2 ^ v7P256Sha2.ecdsa.params.digestBits ∧
      Fintype.card (Fin (2 ^ 256)) = 2 ^ v7P256Sha2.sha.params.digestBits ∧
      (macD FP256 (LigeroV1LayerStep.Chal FP256 Unit v7P256Sha2.ecdsa.params.nw
              v7P256Sha2.ecdsa.params.nq)
          (LigeroV1LayerStep.Qry v7P256Sha2.ecdsa.params.row) GF128
          (LigeroV1LayerStep.Chal GF128 Unit v7P256Sha2.sha.params.nw v7P256Sha2.sha.params.nq)
          (LigeroV1LayerStep.Qry v7P256Sha2.sha.params.row) GF128).k * Fintype.card GF128
        ≤ Fintype.card (TwoFieldCoins FP256
            (LigeroV1LayerStep.Chal FP256 Unit v7P256Sha2.ecdsa.params.nw
              v7P256Sha2.ecdsa.params.nq)
            (LigeroV1LayerStep.Qry v7P256Sha2.ecdsa.params.row) GF128
            (LigeroV1LayerStep.Chal GF128 Unit v7P256Sha2.sha.params.nw v7P256Sha2.sha.params.nq)
            (LigeroV1LayerStep.Qry v7P256Sha2.sha.params.row) GF128) ∧
      2 * Fintype.card FP256 ≤ CertifiedV1.pairBudget
        (Fintype.card (TwoFieldCoins FP256
            (LigeroV1LayerStep.Chal FP256 Unit v7P256Sha2.ecdsa.params.nw
              v7P256Sha2.ecdsa.params.nq)
            (LigeroV1LayerStep.Qry v7P256Sha2.ecdsa.params.row) GF128
            (LigeroV1LayerStep.Chal GF128 Unit v7P256Sha2.sha.params.nw v7P256Sha2.sha.params.nq)
            (LigeroV1LayerStep.Qry v7P256Sha2.sha.params.row) GF128))
        (Fintype.card FP256) ∧
      2 * Fintype.card GF128 ≤ CertifiedV1.pairBudget
        (Fintype.card (TwoFieldCoins FP256
            (LigeroV1LayerStep.Chal FP256 Unit v7P256Sha2.ecdsa.params.nw
              v7P256Sha2.ecdsa.params.nq)
            (LigeroV1LayerStep.Qry v7P256Sha2.ecdsa.params.row) GF128
            (LigeroV1LayerStep.Chal GF128 Unit v7P256Sha2.sha.params.nw v7P256Sha2.sha.params.nq)
            (LigeroV1LayerStep.Qry v7P256Sha2.sha.params.row) GF128))
        (Fintype.card GF128) := by
  have hF₁ : Fintype.card FP256 = v7P256Sha2.ecdsa.params.row.fieldSize := by
    rw [p256_card]; exact v7P256Sha2_fieldSizes.1.symm
  have hF₂ : Fintype.card GF128 = v7P256Sha2.sha.params.row.fieldSize := by
    rw [gf128_card]; exact v7P256Sha2_fieldSizes.2.1.symm
  haveI : Nonempty (LigeroV1LayerStep.Qry v7P256Sha2.ecdsa.params.row) :=
    LigeroFamily.QuerySet.nonempty (by decide)
  haveI : Nonempty (LigeroV1LayerStep.Qry v7P256Sha2.sha.params.row) :=
    LigeroFamily.QuerySet.nonempty (by decide)
  refine ⟨hF₁, hF₂, by rw [gf128_card]; rfl,
    TwoFieldRowV1.domain_exists_ecdsa v7P256Sha2_valid hF₁,
    TwoFieldRowV1.domain_exists_sha v7P256Sha2_valid hF₂,
    by simp [v7P256Sha2, CertifiedV1.v7Sig], by simp [v7P256Sha2, CertifiedV1.v7Hash2],
    by simp [v7P256Sha2, CertifiedV1.v7Sig], by simp [v7P256Sha2, CertifiedV1.v7Hash2],
    (macD _ _ _ _ _ _ _).hexact, pair_room (side₁ _ _ _ _ _ _ _).1,
    pair_room (side₂ _ _ _ _ _ _ _).1⟩

open Lfzk.NizkAdaptiveTwoField in
/-- The two-field schedule at `v7P256Sha2`: the key round, then `566` and `590` slots. -/
theorem v7P256Sha2_len2 : len2 v7P256Sha2.ecdsa v7P256Sha2.sha = 1157 := by
  native_decide

open Lfzk.NizkAdaptiveTwoField in
/-- **The re-commitment terms at `N = 0` fit in the row's slack**: the composed bound plus two
cut-trace extractions' `tape · 1157 / 2^256` is still at most `2^-115`. -/
theorem v7P256Sha2_adaptive_slack_bound :
    v7P256Sha2.ecdsa.bound + v7P256Sha2.sha.bound + 1 / (v7P256Sha2.macFieldSize : ℚ)
        + 2 * (((v7P256Sha2.ecdsa.tape * len2 v7P256Sha2.ecdsa v7P256Sha2.sha : ℕ) : ℚ)
          / 2 ^ v7P256Sha2.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 115 := by
  native_decide

/-- **The per-query coefficient fits too**: the worst role's coefficient (the `GF(2^128)` side's
`κ₂ ≤ 2^-116`, above `κ₁ ≤ 2^-122` and the key slot's `2^-128`) plus `2 · tape / 2^256` is at most
`2^-116`. -/
theorem v7P256Sha2_adaptive_slack_coeff :
    max (max v7P256Sha2.ecdsa.fsCoefficient v7P256Sha2.sha.fsCoefficient)
        (1 / (v7P256Sha2.macFieldSize : ℚ))
      + 2 * ((v7P256Sha2.ecdsa.tape : ℚ) / 2 ^ v7P256Sha2.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 116 := by
  native_decide

open Lfzk.NizkAdaptiveTwoField in
/-- The re-committing two-field right-hand side at `v7P256Sha2`:
`2^-115 + N · 2^-116`. -/
theorem v7P256Sha2_adaptive_rhs_le (N : ℕ) {Fmac : Type} [Fintype Fmac]
    (hFmac : Fintype.card Fmac = 2 ^ 128) :
    v7P256Sha2.ecdsa.bound + v7P256Sha2.sha.bound + 1 / (Fintype.card Fmac : ℚ)
        + N * max (max v7P256Sha2.ecdsa.fsCoefficient v7P256Sha2.sha.fsCoefficient)
            (1 / (Fintype.card Fmac : ℚ))
        + 2 * (((v7P256Sha2.ecdsa.tape * (len2 v7P256Sha2.ecdsa v7P256Sha2.sha + N) : ℕ) : ℚ)
          / 2 ^ v7P256Sha2.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) :=
  TwoFieldRowV1.adaptive_rhs_le_of_slack hFmac v7P256Sha2_adaptive_slack_bound
    v7P256Sha2_adaptive_slack_coeff N

/-- The deployed v7 pair for 3 attributes: ECDSA over `P-256`'s base field (`CertifiedV1.v7Sig`) and
SHA over `GF(2^128)` (`CertifiedV1.v7Hash3`), V1 at 132 openings on both fields, one shared hash
tape of `2^62` slots: `2^-115`. -/
def v7P256Sha3 : TwoFieldRowV1 :=
  { ecdsa := CertifiedV1.v7Sig, sha := CertifiedV1.v7Hash3,
    macFieldSize := 2 ^ 128, lam := 115, sizeBound := 308584 }

theorem v7P256Sha3_valid : v7P256Sha3.Valid := of_decide_eq_true (by native_decide)
theorem v7P256Sha3_sharp : v7P256Sha3.Sharp := of_decide_eq_true (by native_decide)
theorem v7P256Sha3_lam : v7P256Sha3.lam = 115 := rfl
/-- The certified composed bound, `2^-115`. -/
theorem v7P256Sha3_bound_le : v7P256Sha3.bound ≤ (1 : ℚ) / 2 ^ 115 :=
  TwoFieldRowV1.target v7P256Sha3_valid
theorem v7P256Sha3_ecdsa_valid : v7P256Sha3.ecdsa.Valid :=
  TwoFieldRowV1.ecdsa_valid v7P256Sha3_valid
theorem v7P256Sha3_sha_valid : v7P256Sha3.sha.Valid :=
  TwoFieldRowV1.sha_valid v7P256Sha3_valid
/-- The `P-256` side opens `132` columns. -/
theorem v7P256Sha3_ecdsa_openings_pos : 0 < v7P256Sha3.ecdsa.params.row.openings := by decide
/-- The `GF(2^128)` side opens `132` columns. -/
theorem v7P256Sha3_sha_openings_pos : 0 < v7P256Sha3.sha.params.row.openings := by decide

/-- The two sides' fields: `p` and `2^128`. -/
theorem v7P256Sha3_fieldSizes :
    v7P256Sha3.ecdsa.params.row.fieldSize = Lfzk.LigeroV1Rows.p256Order ∧
      v7P256Sha3.sha.params.row.fieldSize = 2 ^ 128 ∧ v7P256Sha3.macFieldSize = 2 ^ 128 := by
  refine ⟨?_, ?_, rfl⟩ <;> decide

/-- **The V3 fuel failure does not occur**: neither side records `commitFuel = tape`. -/
theorem v7P256Sha3_commitFuel_lt_tape :
    v7P256Sha3.ecdsa.commitFuel < v7P256Sha3.ecdsa.tape ∧
      v7P256Sha3.sha.commitFuel < v7P256Sha3.sha.tape :=
  ⟨(TwoFieldRowV1.fuel_satisfiable v7P256Sha3_valid).2.2.2.2.2.2.2.1,
    (TwoFieldRowV1.fuel_satisfiable v7P256Sha3_valid).2.2.2.2.2.2.2.2⟩

/-- **The fuel premises hold at `v7P256Sha3` with real fuel on both sides**: at the two sides'
column counts (`3187` and `3352`) and `2^59 - 3352` opening fuel for each of the four reveal/respond
stages, both sides' `ht₁`, `hT`, `hT1` hold on the shared `2^62`-slot tape, and so does the joint
budget. -/
theorem v7P256Sha3_fuel :
    let n₁ := 3187
    let n₂ := 3352
    let f := 2 ^ 59 - 3352
    v7P256Sha3.ecdsa.params.row.n = n₁ ∧ v7P256Sha3.sha.params.row.n = n₂ ∧
      v7P256Sha3.ecdsa.tape = v7P256Sha3.sha.tape ∧
      v7P256Sha3.ecdsa.commitFuel ≤ v7P256Sha3.sha.tape ∧
      v7P256Sha3.sha.commitFuel ≤ v7P256Sha3.sha.tape ∧
      1 ≤ v7P256Sha3.sha.tape ∧
      2 * n₁ + (f + f) + v7P256Sha3.ecdsa.commitFuel ≤ v7P256Sha3.sha.tape ∧
      2 * n₂ + (f + f) + v7P256Sha3.sha.commitFuel ≤ v7P256Sha3.sha.tape ∧
      (2 * n₁ + (f + f) + v7P256Sha3.ecdsa.commitFuel)
        + (2 * n₂ + (f + f) + v7P256Sha3.sha.commitFuel) ≤ v7P256Sha3.sha.tape ∧ 0 < f := by
  intro n₁ n₂ f
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [n₁, n₂, f, v7P256Sha3, CertifiedV1.v7Sig, CertifiedV1.v7Hash3] <;> norm_num

open Lfzk.TwoFieldV1Fields in
/-- **Every numeric and type-level premise of the composed theorem is satisfiable at `v7P256Sha3`**,
as `p256sha_premises_satisfiable` is at `p256sha`: the fields `ZMod p` and `GaloisField 2 128` with
the sides' cardinalities, both Reed–Solomon domains, the candidate and digest types, the MAC key
decoder's balance and the pair budgets' room on the shared coin alphabet. -/
theorem v7P256Sha3_premises_satisfiable :
    Fintype.card FP256 = v7P256Sha3.ecdsa.params.row.fieldSize ∧
      Fintype.card GF128 = v7P256Sha3.sha.params.row.fieldSize ∧
      Fintype.card GF128 = v7P256Sha3.macFieldSize ∧
      Nonempty (LigeroFamily.ReedSolomon.Domain FP256 v7P256Sha3.ecdsa.params.row.openings
        v7P256Sha3.ecdsa.params.q v7P256Sha3.ecdsa.params.row.n) ∧
      Nonempty (LigeroFamily.ReedSolomon.Domain GF128 v7P256Sha3.sha.params.row.openings
        v7P256Sha3.sha.params.q v7P256Sha3.sha.params.row.n) ∧
      Fintype.card (Fin 2) = v7P256Sha3.ecdsa.cardCand ∧
      Fintype.card (Fin 2) = v7P256Sha3.sha.cardCand ∧
      Fintype.card (Fin (2 ^ 256)) = 2 ^ v7P256Sha3.ecdsa.params.digestBits ∧
      Fintype.card (Fin (2 ^ 256)) = 2 ^ v7P256Sha3.sha.params.digestBits ∧
      (macD FP256 (LigeroV1LayerStep.Chal FP256 Unit v7P256Sha3.ecdsa.params.nw
              v7P256Sha3.ecdsa.params.nq)
          (LigeroV1LayerStep.Qry v7P256Sha3.ecdsa.params.row) GF128
          (LigeroV1LayerStep.Chal GF128 Unit v7P256Sha3.sha.params.nw v7P256Sha3.sha.params.nq)
          (LigeroV1LayerStep.Qry v7P256Sha3.sha.params.row) GF128).k * Fintype.card GF128
        ≤ Fintype.card (TwoFieldCoins FP256
            (LigeroV1LayerStep.Chal FP256 Unit v7P256Sha3.ecdsa.params.nw
              v7P256Sha3.ecdsa.params.nq)
            (LigeroV1LayerStep.Qry v7P256Sha3.ecdsa.params.row) GF128
            (LigeroV1LayerStep.Chal GF128 Unit v7P256Sha3.sha.params.nw v7P256Sha3.sha.params.nq)
            (LigeroV1LayerStep.Qry v7P256Sha3.sha.params.row) GF128) ∧
      2 * Fintype.card FP256 ≤ CertifiedV1.pairBudget
        (Fintype.card (TwoFieldCoins FP256
            (LigeroV1LayerStep.Chal FP256 Unit v7P256Sha3.ecdsa.params.nw
              v7P256Sha3.ecdsa.params.nq)
            (LigeroV1LayerStep.Qry v7P256Sha3.ecdsa.params.row) GF128
            (LigeroV1LayerStep.Chal GF128 Unit v7P256Sha3.sha.params.nw v7P256Sha3.sha.params.nq)
            (LigeroV1LayerStep.Qry v7P256Sha3.sha.params.row) GF128))
        (Fintype.card FP256) ∧
      2 * Fintype.card GF128 ≤ CertifiedV1.pairBudget
        (Fintype.card (TwoFieldCoins FP256
            (LigeroV1LayerStep.Chal FP256 Unit v7P256Sha3.ecdsa.params.nw
              v7P256Sha3.ecdsa.params.nq)
            (LigeroV1LayerStep.Qry v7P256Sha3.ecdsa.params.row) GF128
            (LigeroV1LayerStep.Chal GF128 Unit v7P256Sha3.sha.params.nw v7P256Sha3.sha.params.nq)
            (LigeroV1LayerStep.Qry v7P256Sha3.sha.params.row) GF128))
        (Fintype.card GF128) := by
  have hF₁ : Fintype.card FP256 = v7P256Sha3.ecdsa.params.row.fieldSize := by
    rw [p256_card]; exact v7P256Sha3_fieldSizes.1.symm
  have hF₂ : Fintype.card GF128 = v7P256Sha3.sha.params.row.fieldSize := by
    rw [gf128_card]; exact v7P256Sha3_fieldSizes.2.1.symm
  haveI : Nonempty (LigeroV1LayerStep.Qry v7P256Sha3.ecdsa.params.row) :=
    LigeroFamily.QuerySet.nonempty (by decide)
  haveI : Nonempty (LigeroV1LayerStep.Qry v7P256Sha3.sha.params.row) :=
    LigeroFamily.QuerySet.nonempty (by decide)
  refine ⟨hF₁, hF₂, by rw [gf128_card]; rfl,
    TwoFieldRowV1.domain_exists_ecdsa v7P256Sha3_valid hF₁,
    TwoFieldRowV1.domain_exists_sha v7P256Sha3_valid hF₂,
    by simp [v7P256Sha3, CertifiedV1.v7Sig], by simp [v7P256Sha3, CertifiedV1.v7Hash3],
    by simp [v7P256Sha3, CertifiedV1.v7Sig], by simp [v7P256Sha3, CertifiedV1.v7Hash3],
    (macD _ _ _ _ _ _ _).hexact, pair_room (side₁ _ _ _ _ _ _ _).1,
    pair_room (side₂ _ _ _ _ _ _ _).1⟩

open Lfzk.NizkAdaptiveTwoField in
/-- The two-field schedule at `v7P256Sha3`: the key round, then `566` and `594` slots. -/
theorem v7P256Sha3_len2 : len2 v7P256Sha3.ecdsa v7P256Sha3.sha = 1161 := by
  native_decide

open Lfzk.NizkAdaptiveTwoField in
/-- **The re-commitment terms at `N = 0` fit in the row's slack**: the composed bound plus two
cut-trace extractions' `tape · 1161 / 2^256` is still at most `2^-115`. -/
theorem v7P256Sha3_adaptive_slack_bound :
    v7P256Sha3.ecdsa.bound + v7P256Sha3.sha.bound + 1 / (v7P256Sha3.macFieldSize : ℚ)
        + 2 * (((v7P256Sha3.ecdsa.tape * len2 v7P256Sha3.ecdsa v7P256Sha3.sha : ℕ) : ℚ)
          / 2 ^ v7P256Sha3.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 115 := by
  native_decide

/-- **The per-query coefficient fits too**: the worst role's coefficient (the `GF(2^128)` side's
`κ₂ ≤ 2^-116`, above `κ₁ ≤ 2^-122` and the key slot's `2^-128`) plus `2 · tape / 2^256` is at most
`2^-116`. -/
theorem v7P256Sha3_adaptive_slack_coeff :
    max (max v7P256Sha3.ecdsa.fsCoefficient v7P256Sha3.sha.fsCoefficient)
        (1 / (v7P256Sha3.macFieldSize : ℚ))
      + 2 * ((v7P256Sha3.ecdsa.tape : ℚ) / 2 ^ v7P256Sha3.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 116 := by
  native_decide

open Lfzk.NizkAdaptiveTwoField in
/-- The re-committing two-field right-hand side at `v7P256Sha3`:
`2^-115 + N · 2^-116`. -/
theorem v7P256Sha3_adaptive_rhs_le (N : ℕ) {Fmac : Type} [Fintype Fmac]
    (hFmac : Fintype.card Fmac = 2 ^ 128) :
    v7P256Sha3.ecdsa.bound + v7P256Sha3.sha.bound + 1 / (Fintype.card Fmac : ℚ)
        + N * max (max v7P256Sha3.ecdsa.fsCoefficient v7P256Sha3.sha.fsCoefficient)
            (1 / (Fintype.card Fmac : ℚ))
        + 2 * (((v7P256Sha3.ecdsa.tape * (len2 v7P256Sha3.ecdsa v7P256Sha3.sha + N) : ℕ) : ℚ)
          / 2 ^ v7P256Sha3.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) :=
  TwoFieldRowV1.adaptive_rhs_le_of_slack hFmac v7P256Sha3_adaptive_slack_bound
    v7P256Sha3_adaptive_slack_coeff N

/-- The deployed v7 pair for 4 attributes: ECDSA over `P-256`'s base field (`CertifiedV1.v7Sig`) and
SHA over `GF(2^128)` (`CertifiedV1.v7Hash4`), V1 at 132 openings on both fields, one shared hash
tape of `2^62` slots: `2^-115`. -/
def v7P256Sha4 : TwoFieldRowV1 :=
  { ecdsa := CertifiedV1.v7Sig, sha := CertifiedV1.v7Hash4,
    macFieldSize := 2 ^ 128, lam := 115, sizeBound := 310672 }

theorem v7P256Sha4_valid : v7P256Sha4.Valid := of_decide_eq_true (by native_decide)
theorem v7P256Sha4_sharp : v7P256Sha4.Sharp := of_decide_eq_true (by native_decide)
theorem v7P256Sha4_lam : v7P256Sha4.lam = 115 := rfl
/-- The certified composed bound, `2^-115`. -/
theorem v7P256Sha4_bound_le : v7P256Sha4.bound ≤ (1 : ℚ) / 2 ^ 115 :=
  TwoFieldRowV1.target v7P256Sha4_valid
theorem v7P256Sha4_ecdsa_valid : v7P256Sha4.ecdsa.Valid :=
  TwoFieldRowV1.ecdsa_valid v7P256Sha4_valid
theorem v7P256Sha4_sha_valid : v7P256Sha4.sha.Valid :=
  TwoFieldRowV1.sha_valid v7P256Sha4_valid
/-- The `P-256` side opens `132` columns. -/
theorem v7P256Sha4_ecdsa_openings_pos : 0 < v7P256Sha4.ecdsa.params.row.openings := by decide
/-- The `GF(2^128)` side opens `132` columns. -/
theorem v7P256Sha4_sha_openings_pos : 0 < v7P256Sha4.sha.params.row.openings := by decide

/-- The two sides' fields: `p` and `2^128`. -/
theorem v7P256Sha4_fieldSizes :
    v7P256Sha4.ecdsa.params.row.fieldSize = Lfzk.LigeroV1Rows.p256Order ∧
      v7P256Sha4.sha.params.row.fieldSize = 2 ^ 128 ∧ v7P256Sha4.macFieldSize = 2 ^ 128 := by
  refine ⟨?_, ?_, rfl⟩ <;> decide

/-- **The V3 fuel failure does not occur**: neither side records `commitFuel = tape`. -/
theorem v7P256Sha4_commitFuel_lt_tape :
    v7P256Sha4.ecdsa.commitFuel < v7P256Sha4.ecdsa.tape ∧
      v7P256Sha4.sha.commitFuel < v7P256Sha4.sha.tape :=
  ⟨(TwoFieldRowV1.fuel_satisfiable v7P256Sha4_valid).2.2.2.2.2.2.2.1,
    (TwoFieldRowV1.fuel_satisfiable v7P256Sha4_valid).2.2.2.2.2.2.2.2⟩

/-- **The fuel premises hold at `v7P256Sha4` with real fuel on both sides**: at the two sides'
column counts (`3187` and `3436`) and `2^59 - 3436` opening fuel for each of the four reveal/respond
stages, both sides' `ht₁`, `hT`, `hT1` hold on the shared `2^62`-slot tape, and so does the joint
budget. -/
theorem v7P256Sha4_fuel :
    let n₁ := 3187
    let n₂ := 3436
    let f := 2 ^ 59 - 3436
    v7P256Sha4.ecdsa.params.row.n = n₁ ∧ v7P256Sha4.sha.params.row.n = n₂ ∧
      v7P256Sha4.ecdsa.tape = v7P256Sha4.sha.tape ∧
      v7P256Sha4.ecdsa.commitFuel ≤ v7P256Sha4.sha.tape ∧
      v7P256Sha4.sha.commitFuel ≤ v7P256Sha4.sha.tape ∧
      1 ≤ v7P256Sha4.sha.tape ∧
      2 * n₁ + (f + f) + v7P256Sha4.ecdsa.commitFuel ≤ v7P256Sha4.sha.tape ∧
      2 * n₂ + (f + f) + v7P256Sha4.sha.commitFuel ≤ v7P256Sha4.sha.tape ∧
      (2 * n₁ + (f + f) + v7P256Sha4.ecdsa.commitFuel)
        + (2 * n₂ + (f + f) + v7P256Sha4.sha.commitFuel) ≤ v7P256Sha4.sha.tape ∧ 0 < f := by
  intro n₁ n₂ f
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [n₁, n₂, f, v7P256Sha4, CertifiedV1.v7Sig, CertifiedV1.v7Hash4] <;> norm_num

open Lfzk.TwoFieldV1Fields in
/-- **Every numeric and type-level premise of the composed theorem is satisfiable at `v7P256Sha4`**,
as `p256sha_premises_satisfiable` is at `p256sha`: the fields `ZMod p` and `GaloisField 2 128` with
the sides' cardinalities, both Reed–Solomon domains, the candidate and digest types, the MAC key
decoder's balance and the pair budgets' room on the shared coin alphabet. -/
theorem v7P256Sha4_premises_satisfiable :
    Fintype.card FP256 = v7P256Sha4.ecdsa.params.row.fieldSize ∧
      Fintype.card GF128 = v7P256Sha4.sha.params.row.fieldSize ∧
      Fintype.card GF128 = v7P256Sha4.macFieldSize ∧
      Nonempty (LigeroFamily.ReedSolomon.Domain FP256 v7P256Sha4.ecdsa.params.row.openings
        v7P256Sha4.ecdsa.params.q v7P256Sha4.ecdsa.params.row.n) ∧
      Nonempty (LigeroFamily.ReedSolomon.Domain GF128 v7P256Sha4.sha.params.row.openings
        v7P256Sha4.sha.params.q v7P256Sha4.sha.params.row.n) ∧
      Fintype.card (Fin 2) = v7P256Sha4.ecdsa.cardCand ∧
      Fintype.card (Fin 2) = v7P256Sha4.sha.cardCand ∧
      Fintype.card (Fin (2 ^ 256)) = 2 ^ v7P256Sha4.ecdsa.params.digestBits ∧
      Fintype.card (Fin (2 ^ 256)) = 2 ^ v7P256Sha4.sha.params.digestBits ∧
      (macD FP256 (LigeroV1LayerStep.Chal FP256 Unit v7P256Sha4.ecdsa.params.nw
              v7P256Sha4.ecdsa.params.nq)
          (LigeroV1LayerStep.Qry v7P256Sha4.ecdsa.params.row) GF128
          (LigeroV1LayerStep.Chal GF128 Unit v7P256Sha4.sha.params.nw v7P256Sha4.sha.params.nq)
          (LigeroV1LayerStep.Qry v7P256Sha4.sha.params.row) GF128).k * Fintype.card GF128
        ≤ Fintype.card (TwoFieldCoins FP256
            (LigeroV1LayerStep.Chal FP256 Unit v7P256Sha4.ecdsa.params.nw
              v7P256Sha4.ecdsa.params.nq)
            (LigeroV1LayerStep.Qry v7P256Sha4.ecdsa.params.row) GF128
            (LigeroV1LayerStep.Chal GF128 Unit v7P256Sha4.sha.params.nw v7P256Sha4.sha.params.nq)
            (LigeroV1LayerStep.Qry v7P256Sha4.sha.params.row) GF128) ∧
      2 * Fintype.card FP256 ≤ CertifiedV1.pairBudget
        (Fintype.card (TwoFieldCoins FP256
            (LigeroV1LayerStep.Chal FP256 Unit v7P256Sha4.ecdsa.params.nw
              v7P256Sha4.ecdsa.params.nq)
            (LigeroV1LayerStep.Qry v7P256Sha4.ecdsa.params.row) GF128
            (LigeroV1LayerStep.Chal GF128 Unit v7P256Sha4.sha.params.nw v7P256Sha4.sha.params.nq)
            (LigeroV1LayerStep.Qry v7P256Sha4.sha.params.row) GF128))
        (Fintype.card FP256) ∧
      2 * Fintype.card GF128 ≤ CertifiedV1.pairBudget
        (Fintype.card (TwoFieldCoins FP256
            (LigeroV1LayerStep.Chal FP256 Unit v7P256Sha4.ecdsa.params.nw
              v7P256Sha4.ecdsa.params.nq)
            (LigeroV1LayerStep.Qry v7P256Sha4.ecdsa.params.row) GF128
            (LigeroV1LayerStep.Chal GF128 Unit v7P256Sha4.sha.params.nw v7P256Sha4.sha.params.nq)
            (LigeroV1LayerStep.Qry v7P256Sha4.sha.params.row) GF128))
        (Fintype.card GF128) := by
  have hF₁ : Fintype.card FP256 = v7P256Sha4.ecdsa.params.row.fieldSize := by
    rw [p256_card]; exact v7P256Sha4_fieldSizes.1.symm
  have hF₂ : Fintype.card GF128 = v7P256Sha4.sha.params.row.fieldSize := by
    rw [gf128_card]; exact v7P256Sha4_fieldSizes.2.1.symm
  haveI : Nonempty (LigeroV1LayerStep.Qry v7P256Sha4.ecdsa.params.row) :=
    LigeroFamily.QuerySet.nonempty (by decide)
  haveI : Nonempty (LigeroV1LayerStep.Qry v7P256Sha4.sha.params.row) :=
    LigeroFamily.QuerySet.nonempty (by decide)
  refine ⟨hF₁, hF₂, by rw [gf128_card]; rfl,
    TwoFieldRowV1.domain_exists_ecdsa v7P256Sha4_valid hF₁,
    TwoFieldRowV1.domain_exists_sha v7P256Sha4_valid hF₂,
    by simp [v7P256Sha4, CertifiedV1.v7Sig], by simp [v7P256Sha4, CertifiedV1.v7Hash4],
    by simp [v7P256Sha4, CertifiedV1.v7Sig], by simp [v7P256Sha4, CertifiedV1.v7Hash4],
    (macD _ _ _ _ _ _ _).hexact, pair_room (side₁ _ _ _ _ _ _ _).1,
    pair_room (side₂ _ _ _ _ _ _ _).1⟩

open Lfzk.NizkAdaptiveTwoField in
/-- The two-field schedule at `v7P256Sha4`: the key round, then `566` and `594` slots. -/
theorem v7P256Sha4_len2 : len2 v7P256Sha4.ecdsa v7P256Sha4.sha = 1161 := by
  native_decide

open Lfzk.NizkAdaptiveTwoField in
/-- **The re-commitment terms at `N = 0` fit in the row's slack**: the composed bound plus two
cut-trace extractions' `tape · 1161 / 2^256` is still at most `2^-115`. -/
theorem v7P256Sha4_adaptive_slack_bound :
    v7P256Sha4.ecdsa.bound + v7P256Sha4.sha.bound + 1 / (v7P256Sha4.macFieldSize : ℚ)
        + 2 * (((v7P256Sha4.ecdsa.tape * len2 v7P256Sha4.ecdsa v7P256Sha4.sha : ℕ) : ℚ)
          / 2 ^ v7P256Sha4.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 115 := by
  native_decide

/-- **The per-query coefficient fits too**: the worst role's coefficient (the `GF(2^128)` side's
`κ₂ ≤ 2^-116`, above `κ₁ ≤ 2^-122` and the key slot's `2^-128`) plus `2 · tape / 2^256` is at most
`2^-116`. -/
theorem v7P256Sha4_adaptive_slack_coeff :
    max (max v7P256Sha4.ecdsa.fsCoefficient v7P256Sha4.sha.fsCoefficient)
        (1 / (v7P256Sha4.macFieldSize : ℚ))
      + 2 * ((v7P256Sha4.ecdsa.tape : ℚ) / 2 ^ v7P256Sha4.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 116 := by
  native_decide

open Lfzk.NizkAdaptiveTwoField in
/-- The re-committing two-field right-hand side at `v7P256Sha4`:
`2^-115 + N · 2^-116`. -/
theorem v7P256Sha4_adaptive_rhs_le (N : ℕ) {Fmac : Type} [Fintype Fmac]
    (hFmac : Fintype.card Fmac = 2 ^ 128) :
    v7P256Sha4.ecdsa.bound + v7P256Sha4.sha.bound + 1 / (Fintype.card Fmac : ℚ)
        + N * max (max v7P256Sha4.ecdsa.fsCoefficient v7P256Sha4.sha.fsCoefficient)
            (1 / (Fintype.card Fmac : ℚ))
        + 2 * (((v7P256Sha4.ecdsa.tape * (len2 v7P256Sha4.ecdsa v7P256Sha4.sha + N) : ℕ) : ℚ)
          / 2 ^ v7P256Sha4.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) :=
  TwoFieldRowV1.adaptive_rhs_le_of_slack hFmac v7P256Sha4_adaptive_slack_bound
    v7P256Sha4_adaptive_slack_coeff N

/-- The four v7 pairs. -/
def v7Rows : List TwoFieldRowV1 := [v7P256Sha1, v7P256Sha2, v7P256Sha3, v7P256Sha4]

/-- **Every v7 pair checks**, both sides included. -/
theorem v7Rows_valid : v7Rows.all TwoFieldRowV1.validBool = true := by native_decide

/-- Every v7 pair's `lam` is its exact integer bit level. -/
theorem v7Rows_sharp : v7Rows.all TwoFieldRowV1.sharpBool = true := by native_decide

/-! ## The two-field statement at the v7 pairs: `2^-115` -/

section Headline

open Bcs Merkle Merkle.MH Merkle.RandomOracle
open scoped Classical
open Lfzk.Mac Lfzk.TwoField Lfzk.TwoFieldBridge Lfzk.TwoFieldV1

variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {D : Type} [Fintype D] [DecidableEq D] [Inhabited D]
variable {Fmac : Type} [Field Fmac] [Fintype Fmac] {nblk tlen : ℕ}
variable {Cand₁ F₁ Equations₁ Witness₁ : Type} [Fintype Cand₁] [Nonempty Cand₁] [Field F₁]
  [Fintype F₁] [DecidableEq F₁] [SumcheckInterp F₁] [Fintype Equations₁] [DecidableEq Equations₁]
variable {nc₁ nv₁ logw₁ logc₁ : ℕ}
variable {Statement₁ Oracle₁ Challenge₁ Response₁ Query₁ : Type} {Opening₁ : Query₁ → Type}
variable {Enc₁ Salt₁ M₁ : Type} [DecidableEq Enc₁] [Inhabited Salt₁] [Inhabited M₁]
variable {Aux₁ Aux₁' : Type} {n₁ respondFuel₁ revealFuel₁ : ℕ}
variable {codec₁ : Codec Salt₁ M₁ D Enc₁} {dec₁ : RoleDecoders codec₁}
variable {K₁ : Compiler Statement₁ Oracle₁ Challenge₁ Response₁ Query₁ Opening₁ M₁ n₁}
variable {Cand₂ F₂ Equations₂ Witness₂ : Type} [Fintype Cand₂] [Nonempty Cand₂] [Field F₂]
  [Fintype F₂] [DecidableEq F₂] [SumcheckInterp F₂] [Fintype Equations₂] [DecidableEq Equations₂]
variable {nc₂ nv₂ logw₂ logc₂ : ℕ}
variable {Statement₂ Oracle₂ Challenge₂ Response₂ Query₂ : Type} {Opening₂ : Query₂ → Type}
variable {Enc₂ Salt₂ M₂ : Type} [DecidableEq Enc₂] [Inhabited Salt₂] [Inhabited M₂]
variable {Aux₂ Aux₂' : Type} {n₂ respondFuel₂ revealFuel₂ : ℕ}
variable {codec₂ : Codec Salt₂ M₂ D Enc₂} {dec₂ : RoleDecoders codec₂}
variable {K₂ : Compiler Statement₂ Oracle₂ Challenge₂ Response₂ Query₂ Opening₂ M₂ n₂}


/--
**Two-field Longfellow at `v7P256Sha1`, end to end: `2^-115`.**

ECDSA over `P-256`'s base field and SHA-256 over `GF(2^128)`, at the deployed v7 circuits
(`CertifiedV1.v7Sig`, `CertifiedV1.v7Hash1`) proved with Ligero V1 at 132 openings, composed through
the MAC over a field of `2^128` elements, at Protocol 3.8's schedule (`k_v`, then the ECDSA side's
coins, then the SHA side's):

```text
Pr over (pre, tape) [ both compiled verifiers accept  ∧  the composed extractor fails ]  ≤  2^-115
```

The premises are `TwoFieldRowV1.nizk_ratio_le`'s at `v7P256Sha1` and `Schedule.keyFirst`, exactly as
for `p256sha_nizk_ratio_le_keyFirst`; their numeric and type-level parts are jointly satisfiable
(`v7P256Sha1_premises_satisfiable`, `v7P256Sha1_fuel`).
-/
theorem v7P256Sha1_nizk_ratio_le_keyFirst
    (hFmac : Fintype.card Fmac = 2 ^ 128)
    {challengeOf₁ :
      (Fin (Rounds.Role.length v7P256Sha1.ecdsa.params.nl v7P256Sha1.ecdsa.params.rounds) → C) →
        Challenge₁}
    {queryOf₁ :
      (Fin (Rounds.Role.length v7P256Sha1.ecdsa.params.nl v7P256Sha1.ecdsa.params.rounds) → C) → Query₁}
    {dom₁ : LigeroFamily.ReedSolomon.Domain F₁ v7P256Sha1.ecdsa.params.row.openings
      v7P256Sha1.ecdsa.params.q v7P256Sha1.ecdsa.params.row.n}
    {challengeOf₂ :
      (Fin (Rounds.Role.length v7P256Sha1.sha.params.nl v7P256Sha1.sha.params.rounds) → C) → Challenge₂}
    {queryOf₂ :
      (Fin (Rounds.Role.length v7P256Sha1.sha.params.nl v7P256Sha1.sha.params.rounds) → C) → Query₂}
    {dom₂ : LigeroFamily.ReedSolomon.Domain F₂ v7P256Sha1.sha.params.row.openings
      v7P256Sha1.sha.params.q v7P256Sha1.sha.params.row.n}
    (L₁ : V1Family v7P256Sha1.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha1_valid)
      (Rest (Schedule.keyFirst
        (Rounds.Role.length v7P256Sha1.ecdsa.params.nl v7P256Sha1.ecdsa.params.rounds)
        (Rounds.Role.length v7P256Sha1.sha.params.nl v7P256Sha1.sha.params.rounds)).ι₁ → C)
      C Cand₁ F₁ Equations₁ Witness₁ nc₁ nv₁ logw₁ logc₁ Aux₁ Aux₁' tlen n₁ respondFuel₁
      revealFuel₁ dec₁ K₁ challengeOf₁ queryOf₁ dom₁)
    (L₂ : V1Family v7P256Sha1.sha (TwoFieldRowV1.sha_valid v7P256Sha1_valid)
      (Rest (Schedule.keyFirst
        (Rounds.Role.length v7P256Sha1.ecdsa.params.nl v7P256Sha1.ecdsa.params.rounds)
        (Rounds.Role.length v7P256Sha1.sha.params.nl v7P256Sha1.sha.params.rounds)).ι₂ → C)
      C Cand₂ F₂ Equations₂ Witness₂ nc₂ nv₂ logw₂ logc₂ Aux₂ Aux₂' tlen n₂ respondFuel₂
      revealFuel₂ dec₂ K₂ challengeOf₂ queryOf₂ dom₂)
    (decode : C → Fmac) (aP : (Fin tlen → D) → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    {keyB tag : (Fin tlen → D) × (Fin v7P256Sha1.keyFirstLen → C) → Fin nblk → Fmac}
    (common₁ : Witness₁ → Fin nblk → Fmac)
    (hrow₁ : ∀ (ω : (Fin tlen → D) × (Fin v7P256Sha1.keyFirstLen → C)) (cand : Cand₁),
      L₁.accepts (restOf (Schedule.keyFirst _ _).ι₁ ω.2) (ω.1, ω.2 ∘ (Schedule.keyFirst _ _).ι₁) →
      L₁.Sat (restOf (Schedule.keyFirst _ _).ι₁ ω.2) ω.1 cand →
      macTag (aP ω.1 + decode (ω.2 (Schedule.keyFirst _ _).s)) (keyB ω)
        (common₁ ((L₁.field (restOf (Schedule.keyFirst _ _).ι₁ ω.2) ω.1).wOf cand)) = tag ω)
    (common₂ : Witness₂ → Fin nblk → Fmac)
    (hrow₂ : ∀ (ω : (Fin tlen → D) × (Fin v7P256Sha1.keyFirstLen → C)) (cand : Cand₂),
      L₂.accepts (restOf (Schedule.keyFirst _ _).ι₂ ω.2) (ω.1, ω.2 ∘ (Schedule.keyFirst _ _).ι₂) →
      L₂.Sat (restOf (Schedule.keyFirst _ _).ι₂ ω.2) ω.1 cand →
      macTag (aP ω.1 + decode (ω.2 (Schedule.keyFirst _ _).s)) (keyB ω)
        (common₂ ((L₂.field (restOf (Schedule.keyFirst _ _).ι₂ ω.2) ω.1).wOf cand)) = tag ω) :
    ((univ.filter fun ω : (Fin tlen → D) × (Fin v7P256Sha1.keyFirstLen → C) =>
        (L₁.macSide common₁ hrow₁).accepts ω ∧ (L₂.macSide common₂ hrow₂).accepts ω ∧
          composedE (L₁.macSide common₁ hrow₁) (L₂.macSide common₂ hrow₂) ω = none).card : ℚ)
        / (Fintype.card (Fin tlen → D) * (Fintype.card C : ℚ) ^ v7P256Sha1.keyFirstLen)
      ≤ (1 : ℚ) / 2 ^ 115 :=
  TwoFieldRowV1.nizk_ratio_le v7P256Sha1_valid hFmac (Schedule.keyFirst _ _) L₁ L₂ decode aP kmac hbal
    hmac common₁ hrow₁ common₂ hrow₂ (by omega)

/--
**Two-field Longfellow at `v7P256Sha2`, end to end: `2^-115`.**

ECDSA over `P-256`'s base field and SHA-256 over `GF(2^128)`, at the deployed v7 circuits
(`CertifiedV1.v7Sig`, `CertifiedV1.v7Hash2`) proved with Ligero V1 at 132 openings, composed through
the MAC over a field of `2^128` elements, at Protocol 3.8's schedule (`k_v`, then the ECDSA side's
coins, then the SHA side's):

```text
Pr over (pre, tape) [ both compiled verifiers accept  ∧  the composed extractor fails ]  ≤  2^-115
```

The premises are `TwoFieldRowV1.nizk_ratio_le`'s at `v7P256Sha2` and `Schedule.keyFirst`, exactly as
for `p256sha_nizk_ratio_le_keyFirst`; their numeric and type-level parts are jointly satisfiable
(`v7P256Sha2_premises_satisfiable`, `v7P256Sha2_fuel`).
-/
theorem v7P256Sha2_nizk_ratio_le_keyFirst
    (hFmac : Fintype.card Fmac = 2 ^ 128)
    {challengeOf₁ :
      (Fin (Rounds.Role.length v7P256Sha2.ecdsa.params.nl v7P256Sha2.ecdsa.params.rounds) → C) →
        Challenge₁}
    {queryOf₁ :
      (Fin (Rounds.Role.length v7P256Sha2.ecdsa.params.nl v7P256Sha2.ecdsa.params.rounds) → C) → Query₁}
    {dom₁ : LigeroFamily.ReedSolomon.Domain F₁ v7P256Sha2.ecdsa.params.row.openings
      v7P256Sha2.ecdsa.params.q v7P256Sha2.ecdsa.params.row.n}
    {challengeOf₂ :
      (Fin (Rounds.Role.length v7P256Sha2.sha.params.nl v7P256Sha2.sha.params.rounds) → C) → Challenge₂}
    {queryOf₂ :
      (Fin (Rounds.Role.length v7P256Sha2.sha.params.nl v7P256Sha2.sha.params.rounds) → C) → Query₂}
    {dom₂ : LigeroFamily.ReedSolomon.Domain F₂ v7P256Sha2.sha.params.row.openings
      v7P256Sha2.sha.params.q v7P256Sha2.sha.params.row.n}
    (L₁ : V1Family v7P256Sha2.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha2_valid)
      (Rest (Schedule.keyFirst
        (Rounds.Role.length v7P256Sha2.ecdsa.params.nl v7P256Sha2.ecdsa.params.rounds)
        (Rounds.Role.length v7P256Sha2.sha.params.nl v7P256Sha2.sha.params.rounds)).ι₁ → C)
      C Cand₁ F₁ Equations₁ Witness₁ nc₁ nv₁ logw₁ logc₁ Aux₁ Aux₁' tlen n₁ respondFuel₁
      revealFuel₁ dec₁ K₁ challengeOf₁ queryOf₁ dom₁)
    (L₂ : V1Family v7P256Sha2.sha (TwoFieldRowV1.sha_valid v7P256Sha2_valid)
      (Rest (Schedule.keyFirst
        (Rounds.Role.length v7P256Sha2.ecdsa.params.nl v7P256Sha2.ecdsa.params.rounds)
        (Rounds.Role.length v7P256Sha2.sha.params.nl v7P256Sha2.sha.params.rounds)).ι₂ → C)
      C Cand₂ F₂ Equations₂ Witness₂ nc₂ nv₂ logw₂ logc₂ Aux₂ Aux₂' tlen n₂ respondFuel₂
      revealFuel₂ dec₂ K₂ challengeOf₂ queryOf₂ dom₂)
    (decode : C → Fmac) (aP : (Fin tlen → D) → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    {keyB tag : (Fin tlen → D) × (Fin v7P256Sha2.keyFirstLen → C) → Fin nblk → Fmac}
    (common₁ : Witness₁ → Fin nblk → Fmac)
    (hrow₁ : ∀ (ω : (Fin tlen → D) × (Fin v7P256Sha2.keyFirstLen → C)) (cand : Cand₁),
      L₁.accepts (restOf (Schedule.keyFirst _ _).ι₁ ω.2) (ω.1, ω.2 ∘ (Schedule.keyFirst _ _).ι₁) →
      L₁.Sat (restOf (Schedule.keyFirst _ _).ι₁ ω.2) ω.1 cand →
      macTag (aP ω.1 + decode (ω.2 (Schedule.keyFirst _ _).s)) (keyB ω)
        (common₁ ((L₁.field (restOf (Schedule.keyFirst _ _).ι₁ ω.2) ω.1).wOf cand)) = tag ω)
    (common₂ : Witness₂ → Fin nblk → Fmac)
    (hrow₂ : ∀ (ω : (Fin tlen → D) × (Fin v7P256Sha2.keyFirstLen → C)) (cand : Cand₂),
      L₂.accepts (restOf (Schedule.keyFirst _ _).ι₂ ω.2) (ω.1, ω.2 ∘ (Schedule.keyFirst _ _).ι₂) →
      L₂.Sat (restOf (Schedule.keyFirst _ _).ι₂ ω.2) ω.1 cand →
      macTag (aP ω.1 + decode (ω.2 (Schedule.keyFirst _ _).s)) (keyB ω)
        (common₂ ((L₂.field (restOf (Schedule.keyFirst _ _).ι₂ ω.2) ω.1).wOf cand)) = tag ω) :
    ((univ.filter fun ω : (Fin tlen → D) × (Fin v7P256Sha2.keyFirstLen → C) =>
        (L₁.macSide common₁ hrow₁).accepts ω ∧ (L₂.macSide common₂ hrow₂).accepts ω ∧
          composedE (L₁.macSide common₁ hrow₁) (L₂.macSide common₂ hrow₂) ω = none).card : ℚ)
        / (Fintype.card (Fin tlen → D) * (Fintype.card C : ℚ) ^ v7P256Sha2.keyFirstLen)
      ≤ (1 : ℚ) / 2 ^ 115 :=
  TwoFieldRowV1.nizk_ratio_le v7P256Sha2_valid hFmac (Schedule.keyFirst _ _) L₁ L₂ decode aP kmac hbal
    hmac common₁ hrow₁ common₂ hrow₂ (by omega)

/--
**Two-field Longfellow at `v7P256Sha3`, end to end: `2^-115`.**

ECDSA over `P-256`'s base field and SHA-256 over `GF(2^128)`, at the deployed v7 circuits
(`CertifiedV1.v7Sig`, `CertifiedV1.v7Hash3`) proved with Ligero V1 at 132 openings, composed through
the MAC over a field of `2^128` elements, at Protocol 3.8's schedule (`k_v`, then the ECDSA side's
coins, then the SHA side's):

```text
Pr over (pre, tape) [ both compiled verifiers accept  ∧  the composed extractor fails ]  ≤  2^-115
```

The premises are `TwoFieldRowV1.nizk_ratio_le`'s at `v7P256Sha3` and `Schedule.keyFirst`, exactly as
for `p256sha_nizk_ratio_le_keyFirst`; their numeric and type-level parts are jointly satisfiable
(`v7P256Sha3_premises_satisfiable`, `v7P256Sha3_fuel`).
-/
theorem v7P256Sha3_nizk_ratio_le_keyFirst
    (hFmac : Fintype.card Fmac = 2 ^ 128)
    {challengeOf₁ :
      (Fin (Rounds.Role.length v7P256Sha3.ecdsa.params.nl v7P256Sha3.ecdsa.params.rounds) → C) →
        Challenge₁}
    {queryOf₁ :
      (Fin (Rounds.Role.length v7P256Sha3.ecdsa.params.nl v7P256Sha3.ecdsa.params.rounds) → C) → Query₁}
    {dom₁ : LigeroFamily.ReedSolomon.Domain F₁ v7P256Sha3.ecdsa.params.row.openings
      v7P256Sha3.ecdsa.params.q v7P256Sha3.ecdsa.params.row.n}
    {challengeOf₂ :
      (Fin (Rounds.Role.length v7P256Sha3.sha.params.nl v7P256Sha3.sha.params.rounds) → C) → Challenge₂}
    {queryOf₂ :
      (Fin (Rounds.Role.length v7P256Sha3.sha.params.nl v7P256Sha3.sha.params.rounds) → C) → Query₂}
    {dom₂ : LigeroFamily.ReedSolomon.Domain F₂ v7P256Sha3.sha.params.row.openings
      v7P256Sha3.sha.params.q v7P256Sha3.sha.params.row.n}
    (L₁ : V1Family v7P256Sha3.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha3_valid)
      (Rest (Schedule.keyFirst
        (Rounds.Role.length v7P256Sha3.ecdsa.params.nl v7P256Sha3.ecdsa.params.rounds)
        (Rounds.Role.length v7P256Sha3.sha.params.nl v7P256Sha3.sha.params.rounds)).ι₁ → C)
      C Cand₁ F₁ Equations₁ Witness₁ nc₁ nv₁ logw₁ logc₁ Aux₁ Aux₁' tlen n₁ respondFuel₁
      revealFuel₁ dec₁ K₁ challengeOf₁ queryOf₁ dom₁)
    (L₂ : V1Family v7P256Sha3.sha (TwoFieldRowV1.sha_valid v7P256Sha3_valid)
      (Rest (Schedule.keyFirst
        (Rounds.Role.length v7P256Sha3.ecdsa.params.nl v7P256Sha3.ecdsa.params.rounds)
        (Rounds.Role.length v7P256Sha3.sha.params.nl v7P256Sha3.sha.params.rounds)).ι₂ → C)
      C Cand₂ F₂ Equations₂ Witness₂ nc₂ nv₂ logw₂ logc₂ Aux₂ Aux₂' tlen n₂ respondFuel₂
      revealFuel₂ dec₂ K₂ challengeOf₂ queryOf₂ dom₂)
    (decode : C → Fmac) (aP : (Fin tlen → D) → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    {keyB tag : (Fin tlen → D) × (Fin v7P256Sha3.keyFirstLen → C) → Fin nblk → Fmac}
    (common₁ : Witness₁ → Fin nblk → Fmac)
    (hrow₁ : ∀ (ω : (Fin tlen → D) × (Fin v7P256Sha3.keyFirstLen → C)) (cand : Cand₁),
      L₁.accepts (restOf (Schedule.keyFirst _ _).ι₁ ω.2) (ω.1, ω.2 ∘ (Schedule.keyFirst _ _).ι₁) →
      L₁.Sat (restOf (Schedule.keyFirst _ _).ι₁ ω.2) ω.1 cand →
      macTag (aP ω.1 + decode (ω.2 (Schedule.keyFirst _ _).s)) (keyB ω)
        (common₁ ((L₁.field (restOf (Schedule.keyFirst _ _).ι₁ ω.2) ω.1).wOf cand)) = tag ω)
    (common₂ : Witness₂ → Fin nblk → Fmac)
    (hrow₂ : ∀ (ω : (Fin tlen → D) × (Fin v7P256Sha3.keyFirstLen → C)) (cand : Cand₂),
      L₂.accepts (restOf (Schedule.keyFirst _ _).ι₂ ω.2) (ω.1, ω.2 ∘ (Schedule.keyFirst _ _).ι₂) →
      L₂.Sat (restOf (Schedule.keyFirst _ _).ι₂ ω.2) ω.1 cand →
      macTag (aP ω.1 + decode (ω.2 (Schedule.keyFirst _ _).s)) (keyB ω)
        (common₂ ((L₂.field (restOf (Schedule.keyFirst _ _).ι₂ ω.2) ω.1).wOf cand)) = tag ω) :
    ((univ.filter fun ω : (Fin tlen → D) × (Fin v7P256Sha3.keyFirstLen → C) =>
        (L₁.macSide common₁ hrow₁).accepts ω ∧ (L₂.macSide common₂ hrow₂).accepts ω ∧
          composedE (L₁.macSide common₁ hrow₁) (L₂.macSide common₂ hrow₂) ω = none).card : ℚ)
        / (Fintype.card (Fin tlen → D) * (Fintype.card C : ℚ) ^ v7P256Sha3.keyFirstLen)
      ≤ (1 : ℚ) / 2 ^ 115 :=
  TwoFieldRowV1.nizk_ratio_le v7P256Sha3_valid hFmac (Schedule.keyFirst _ _) L₁ L₂ decode aP kmac hbal
    hmac common₁ hrow₁ common₂ hrow₂ (by omega)

/--
**Two-field Longfellow at `v7P256Sha4`, end to end: `2^-115`.**

ECDSA over `P-256`'s base field and SHA-256 over `GF(2^128)`, at the deployed v7 circuits
(`CertifiedV1.v7Sig`, `CertifiedV1.v7Hash4`) proved with Ligero V1 at 132 openings, composed through
the MAC over a field of `2^128` elements, at Protocol 3.8's schedule (`k_v`, then the ECDSA side's
coins, then the SHA side's):

```text
Pr over (pre, tape) [ both compiled verifiers accept  ∧  the composed extractor fails ]  ≤  2^-115
```

The premises are `TwoFieldRowV1.nizk_ratio_le`'s at `v7P256Sha4` and `Schedule.keyFirst`, exactly as
for `p256sha_nizk_ratio_le_keyFirst`; their numeric and type-level parts are jointly satisfiable
(`v7P256Sha4_premises_satisfiable`, `v7P256Sha4_fuel`).
-/
theorem v7P256Sha4_nizk_ratio_le_keyFirst
    (hFmac : Fintype.card Fmac = 2 ^ 128)
    {challengeOf₁ :
      (Fin (Rounds.Role.length v7P256Sha4.ecdsa.params.nl v7P256Sha4.ecdsa.params.rounds) → C) →
        Challenge₁}
    {queryOf₁ :
      (Fin (Rounds.Role.length v7P256Sha4.ecdsa.params.nl v7P256Sha4.ecdsa.params.rounds) → C) → Query₁}
    {dom₁ : LigeroFamily.ReedSolomon.Domain F₁ v7P256Sha4.ecdsa.params.row.openings
      v7P256Sha4.ecdsa.params.q v7P256Sha4.ecdsa.params.row.n}
    {challengeOf₂ :
      (Fin (Rounds.Role.length v7P256Sha4.sha.params.nl v7P256Sha4.sha.params.rounds) → C) → Challenge₂}
    {queryOf₂ :
      (Fin (Rounds.Role.length v7P256Sha4.sha.params.nl v7P256Sha4.sha.params.rounds) → C) → Query₂}
    {dom₂ : LigeroFamily.ReedSolomon.Domain F₂ v7P256Sha4.sha.params.row.openings
      v7P256Sha4.sha.params.q v7P256Sha4.sha.params.row.n}
    (L₁ : V1Family v7P256Sha4.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha4_valid)
      (Rest (Schedule.keyFirst
        (Rounds.Role.length v7P256Sha4.ecdsa.params.nl v7P256Sha4.ecdsa.params.rounds)
        (Rounds.Role.length v7P256Sha4.sha.params.nl v7P256Sha4.sha.params.rounds)).ι₁ → C)
      C Cand₁ F₁ Equations₁ Witness₁ nc₁ nv₁ logw₁ logc₁ Aux₁ Aux₁' tlen n₁ respondFuel₁
      revealFuel₁ dec₁ K₁ challengeOf₁ queryOf₁ dom₁)
    (L₂ : V1Family v7P256Sha4.sha (TwoFieldRowV1.sha_valid v7P256Sha4_valid)
      (Rest (Schedule.keyFirst
        (Rounds.Role.length v7P256Sha4.ecdsa.params.nl v7P256Sha4.ecdsa.params.rounds)
        (Rounds.Role.length v7P256Sha4.sha.params.nl v7P256Sha4.sha.params.rounds)).ι₂ → C)
      C Cand₂ F₂ Equations₂ Witness₂ nc₂ nv₂ logw₂ logc₂ Aux₂ Aux₂' tlen n₂ respondFuel₂
      revealFuel₂ dec₂ K₂ challengeOf₂ queryOf₂ dom₂)
    (decode : C → Fmac) (aP : (Fin tlen → D) → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    {keyB tag : (Fin tlen → D) × (Fin v7P256Sha4.keyFirstLen → C) → Fin nblk → Fmac}
    (common₁ : Witness₁ → Fin nblk → Fmac)
    (hrow₁ : ∀ (ω : (Fin tlen → D) × (Fin v7P256Sha4.keyFirstLen → C)) (cand : Cand₁),
      L₁.accepts (restOf (Schedule.keyFirst _ _).ι₁ ω.2) (ω.1, ω.2 ∘ (Schedule.keyFirst _ _).ι₁) →
      L₁.Sat (restOf (Schedule.keyFirst _ _).ι₁ ω.2) ω.1 cand →
      macTag (aP ω.1 + decode (ω.2 (Schedule.keyFirst _ _).s)) (keyB ω)
        (common₁ ((L₁.field (restOf (Schedule.keyFirst _ _).ι₁ ω.2) ω.1).wOf cand)) = tag ω)
    (common₂ : Witness₂ → Fin nblk → Fmac)
    (hrow₂ : ∀ (ω : (Fin tlen → D) × (Fin v7P256Sha4.keyFirstLen → C)) (cand : Cand₂),
      L₂.accepts (restOf (Schedule.keyFirst _ _).ι₂ ω.2) (ω.1, ω.2 ∘ (Schedule.keyFirst _ _).ι₂) →
      L₂.Sat (restOf (Schedule.keyFirst _ _).ι₂ ω.2) ω.1 cand →
      macTag (aP ω.1 + decode (ω.2 (Schedule.keyFirst _ _).s)) (keyB ω)
        (common₂ ((L₂.field (restOf (Schedule.keyFirst _ _).ι₂ ω.2) ω.1).wOf cand)) = tag ω) :
    ((univ.filter fun ω : (Fin tlen → D) × (Fin v7P256Sha4.keyFirstLen → C) =>
        (L₁.macSide common₁ hrow₁).accepts ω ∧ (L₂.macSide common₂ hrow₂).accepts ω ∧
          composedE (L₁.macSide common₁ hrow₁) (L₂.macSide common₂ hrow₂) ω = none).card : ℚ)
        / (Fintype.card (Fin tlen → D) * (Fintype.card C : ℚ) ^ v7P256Sha4.keyFirstLen)
      ≤ (1 : ℚ) / 2 ^ 115 :=
  TwoFieldRowV1.nizk_ratio_le v7P256Sha4_valid hFmac (Schedule.keyFirst _ _) L₁ L₂ decode aP kmac hbal
    hmac common₁ hrow₁ common₂ hrow₂ (by omega)


end Headline

end Lfzk.TwoFieldV1Rows
