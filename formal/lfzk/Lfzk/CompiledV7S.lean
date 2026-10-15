import Lfzk.CompiledLongfellowAdaptiveS
import Lfzk.CertifiedV7
import Lfzk.TwoFieldV7Rows

/-!
# The clear-verifier headlines at the deployed v7 parameters, at the mixed accounting

`Lfzk.CompiledV7`'s re-committing compiled headlines with the list factor dropped at the two
Ligero slots (`Lfzk.RbrLayerStepS`, `Lfzk.CompiledLongfellowAdaptiveS`): each is
`row_adaptive_ratio_le_v1S` / `twofield_adaptive_compiled_ratio_leS` at the v7 row, followed by the
row's mixed-accounting numerals, certified here by `native_decide`.  The statements are
`CompiledV7`'s with the lemma names and the numerals replaced (generated from that file's text), so
the premises are exactly `CompiledV7`'s.

| row | `CompiledV7` (per-candidate) | here (mixed) |
|---|---|---|
| `v7Sig` | `2^-122 + N · 2^-122` | `2^-123 + N · 2^-123` |
| `v7Hash1` … `v7Hash4` | `2^-115 + N · 2^-116` | `2^-115 + N · 2^-117` |
| `v7P256Sha1` … `v7P256Sha4` (two-field) | `2^-115 + N · 2^-116` | `2^-115 + N · 2^-117` |

The hash rows' `boundS` is `2^-115.7`, so the sequential term stays at `115`; the work-normalized
coefficient gains a bit.  This is still the clear-verifier model (`hfalse` among the premises);
`Lfzk.CompiledZk` is the deployed zero-knowledge verifier.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.CertifiedV1

/-- **A re-committing right-hand side from two slack numerals**, for any bound `B` and coefficient
`K`: `B + N·K + T·(L + N)/2^d ≤ 2^-a + N·2^-b` from the `N = 0` and per-query slacks. -/
theorem rhs_le_of_slack {B K : ℚ} {T L d a b : ℕ}
    (hsb : B + ((T * L : ℕ) : ℚ) / 2 ^ d ≤ (1 : ℚ) / 2 ^ a)
    (hsc : K + (T : ℚ) / 2 ^ d ≤ (1 : ℚ) / 2 ^ b) (N : ℕ) :
    B + N * K + ((T * (L + N) : ℕ) : ℚ) / 2 ^ d ≤ (1 : ℚ) / 2 ^ a + N * ((1 : ℚ) / 2 ^ b) := by
  have hsplit : ((T * (L + N) : ℕ) : ℚ) / 2 ^ d
      = ((T * L : ℕ) : ℚ) / 2 ^ d + N * ((T : ℚ) / 2 ^ d) := by
    push_cast
    ring
  rw [hsplit]
  have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg N
  have := mul_le_mul_of_nonneg_left hsc hN
  nlinarith

/-- `v7Sig` at the mixed accounting, at `N = 0`: `boundS` plus the re-commitment term is at most
`2^-123`. -/
theorem v7Sig_adaptive_slack_boundS :
    v7Sig.boundS
        + ((v7Sig.tape * Rounds.Role.length v7Sig.params.nl v7Sig.params.rounds : ℕ) : ℚ)
          / 2 ^ v7Sig.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 123 := by
  native_decide

/-- `v7Sig`'s mixed coefficient plus the per-query re-commitment term: at most `2^-123`. -/
theorem v7Sig_adaptive_slack_coeffS :
    v7Sig.fsCoefficientS + (v7Sig.tape : ℚ) / 2 ^ v7Sig.params.digestBits ≤ (1 : ℚ) / 2 ^ 123 := by
  native_decide

/-- **`v7Sig`'s numerals at the mixed accounting**: within `2^-123 + N · 2^-123`. -/
theorem v7Sig_adaptive_rhs_leS (N : ℕ) :
    v7Sig.boundS + N * v7Sig.fsCoefficientS
        + ((v7Sig.tape * (Rounds.Role.length v7Sig.params.nl v7Sig.params.rounds + N) : ℕ) : ℚ)
          / 2 ^ v7Sig.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 123 + N * ((1 : ℚ) / 2 ^ 123) :=
  rhs_le_of_slack v7Sig_adaptive_slack_boundS v7Sig_adaptive_slack_coeffS N

/-- `v7Hash1` at the mixed accounting, at `N = 0`: `boundS` plus the re-commitment term is at most
`2^-115`. -/
theorem v7Hash1_adaptive_slack_boundS :
    v7Hash1.boundS
        + ((v7Hash1.tape * Rounds.Role.length v7Hash1.params.nl v7Hash1.params.rounds : ℕ) : ℚ)
          / 2 ^ v7Hash1.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 115 := by
  native_decide

/-- `v7Hash1`'s mixed coefficient plus the per-query re-commitment term: at most `2^-117`. -/
theorem v7Hash1_adaptive_slack_coeffS :
    v7Hash1.fsCoefficientS + (v7Hash1.tape : ℚ) / 2 ^ v7Hash1.params.digestBits ≤ (1 : ℚ) / 2 ^ 117 := by
  native_decide

/-- **`v7Hash1`'s numerals at the mixed accounting**: within `2^-115 + N · 2^-117`. -/
theorem v7Hash1_adaptive_rhs_leS (N : ℕ) :
    v7Hash1.boundS + N * v7Hash1.fsCoefficientS
        + ((v7Hash1.tape * (Rounds.Role.length v7Hash1.params.nl v7Hash1.params.rounds + N) : ℕ) : ℚ)
          / 2 ^ v7Hash1.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) :=
  rhs_le_of_slack v7Hash1_adaptive_slack_boundS v7Hash1_adaptive_slack_coeffS N

/-- `v7Hash2` at the mixed accounting, at `N = 0`: `boundS` plus the re-commitment term is at most
`2^-115`. -/
theorem v7Hash2_adaptive_slack_boundS :
    v7Hash2.boundS
        + ((v7Hash2.tape * Rounds.Role.length v7Hash2.params.nl v7Hash2.params.rounds : ℕ) : ℚ)
          / 2 ^ v7Hash2.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 115 := by
  native_decide

/-- `v7Hash2`'s mixed coefficient plus the per-query re-commitment term: at most `2^-117`. -/
theorem v7Hash2_adaptive_slack_coeffS :
    v7Hash2.fsCoefficientS + (v7Hash2.tape : ℚ) / 2 ^ v7Hash2.params.digestBits ≤ (1 : ℚ) / 2 ^ 117 := by
  native_decide

/-- **`v7Hash2`'s numerals at the mixed accounting**: within `2^-115 + N · 2^-117`. -/
theorem v7Hash2_adaptive_rhs_leS (N : ℕ) :
    v7Hash2.boundS + N * v7Hash2.fsCoefficientS
        + ((v7Hash2.tape * (Rounds.Role.length v7Hash2.params.nl v7Hash2.params.rounds + N) : ℕ) : ℚ)
          / 2 ^ v7Hash2.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) :=
  rhs_le_of_slack v7Hash2_adaptive_slack_boundS v7Hash2_adaptive_slack_coeffS N

/-- `v7Hash3` at the mixed accounting, at `N = 0`: `boundS` plus the re-commitment term is at most
`2^-115`. -/
theorem v7Hash3_adaptive_slack_boundS :
    v7Hash3.boundS
        + ((v7Hash3.tape * Rounds.Role.length v7Hash3.params.nl v7Hash3.params.rounds : ℕ) : ℚ)
          / 2 ^ v7Hash3.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 115 := by
  native_decide

/-- `v7Hash3`'s mixed coefficient plus the per-query re-commitment term: at most `2^-117`. -/
theorem v7Hash3_adaptive_slack_coeffS :
    v7Hash3.fsCoefficientS + (v7Hash3.tape : ℚ) / 2 ^ v7Hash3.params.digestBits ≤ (1 : ℚ) / 2 ^ 117 := by
  native_decide

/-- **`v7Hash3`'s numerals at the mixed accounting**: within `2^-115 + N · 2^-117`. -/
theorem v7Hash3_adaptive_rhs_leS (N : ℕ) :
    v7Hash3.boundS + N * v7Hash3.fsCoefficientS
        + ((v7Hash3.tape * (Rounds.Role.length v7Hash3.params.nl v7Hash3.params.rounds + N) : ℕ) : ℚ)
          / 2 ^ v7Hash3.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) :=
  rhs_le_of_slack v7Hash3_adaptive_slack_boundS v7Hash3_adaptive_slack_coeffS N

/-- `v7Hash4` at the mixed accounting, at `N = 0`: `boundS` plus the re-commitment term is at most
`2^-115`. -/
theorem v7Hash4_adaptive_slack_boundS :
    v7Hash4.boundS
        + ((v7Hash4.tape * Rounds.Role.length v7Hash4.params.nl v7Hash4.params.rounds : ℕ) : ℚ)
          / 2 ^ v7Hash4.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 115 := by
  native_decide

/-- `v7Hash4`'s mixed coefficient plus the per-query re-commitment term: at most `2^-117`. -/
theorem v7Hash4_adaptive_slack_coeffS :
    v7Hash4.fsCoefficientS + (v7Hash4.tape : ℚ) / 2 ^ v7Hash4.params.digestBits ≤ (1 : ℚ) / 2 ^ 117 := by
  native_decide

/-- **`v7Hash4`'s numerals at the mixed accounting**: within `2^-115 + N · 2^-117`. -/
theorem v7Hash4_adaptive_rhs_leS (N : ℕ) :
    v7Hash4.boundS + N * v7Hash4.fsCoefficientS
        + ((v7Hash4.tape * (Rounds.Role.length v7Hash4.params.nl v7Hash4.params.rounds + N) : ℕ) : ℚ)
          / 2 ^ v7Hash4.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) :=
  rhs_le_of_slack v7Hash4_adaptive_slack_boundS v7Hash4_adaptive_slack_coeffS N

end Lfzk.CertifiedV1

namespace Lfzk.TwoFieldV1Rows

open Lfzk.NizkAdaptiveTwoField Lfzk.CertifiedV1

/-- **The two-field re-committing right-hand side at the mixed accounting, from two slack
numerals.** -/
theorem TwoFieldRowV1.adaptive_rhs_leS_of_slack {R : TwoFieldRowV1} {a b : ℕ}
    {Fmac : Type} [Fintype Fmac] (hFmac : Fintype.card Fmac = R.macFieldSize)
    (hsb : R.ecdsa.boundS + R.sha.boundS + 1 / (R.macFieldSize : ℚ)
        + 2 * (((R.ecdsa.tape * len2 R.ecdsa R.sha : ℕ) : ℚ) / 2 ^ R.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ a)
    (hsc : max (max R.ecdsa.fsCoefficientS R.sha.fsCoefficientS) (1 / (R.macFieldSize : ℚ))
        + 2 * ((R.ecdsa.tape : ℚ) / 2 ^ R.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ b)
    (N : ℕ) :
    R.ecdsa.boundS + R.sha.boundS + 1 / (Fintype.card Fmac : ℚ)
        + N * max (max R.ecdsa.fsCoefficientS R.sha.fsCoefficientS) (1 / (Fintype.card Fmac : ℚ))
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

/-- `v7P256Sha1` at the mixed accounting, at `N = 0`: at most `2^-115`. -/
theorem v7P256Sha1_adaptive_slack_boundS :
    v7P256Sha1.ecdsa.boundS + v7P256Sha1.sha.boundS + 1 / (v7P256Sha1.macFieldSize : ℚ)
        + 2 * (((v7P256Sha1.ecdsa.tape * len2 v7P256Sha1.ecdsa v7P256Sha1.sha : ℕ) : ℚ)
          / 2 ^ v7P256Sha1.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 115 := by
  native_decide

/-- `v7P256Sha1`'s worst mixed coefficient plus the per-query term: at most `2^-117`. -/
theorem v7P256Sha1_adaptive_slack_coeffS :
    max (max v7P256Sha1.ecdsa.fsCoefficientS v7P256Sha1.sha.fsCoefficientS) (1 / (v7P256Sha1.macFieldSize : ℚ))
      + 2 * ((v7P256Sha1.ecdsa.tape : ℚ) / 2 ^ v7P256Sha1.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 117 := by
  native_decide

/-- **`v7P256Sha1`'s numerals at the mixed accounting**: within `2^-115 + N · 2^-117`. -/
theorem v7P256Sha1_adaptive_rhs_leS (N : ℕ) {Fmac : Type} [Fintype Fmac]
    (hFmac : Fintype.card Fmac = 2 ^ 128) :
    v7P256Sha1.ecdsa.boundS + v7P256Sha1.sha.boundS + 1 / (Fintype.card Fmac : ℚ)
        + N * max (max v7P256Sha1.ecdsa.fsCoefficientS v7P256Sha1.sha.fsCoefficientS)
            (1 / (Fintype.card Fmac : ℚ))
        + 2 * (((v7P256Sha1.ecdsa.tape * (len2 v7P256Sha1.ecdsa v7P256Sha1.sha + N) : ℕ) : ℚ)
          / 2 ^ v7P256Sha1.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) :=
  TwoFieldRowV1.adaptive_rhs_leS_of_slack hFmac v7P256Sha1_adaptive_slack_boundS
    v7P256Sha1_adaptive_slack_coeffS N

/-- `v7P256Sha2` at the mixed accounting, at `N = 0`: at most `2^-115`. -/
theorem v7P256Sha2_adaptive_slack_boundS :
    v7P256Sha2.ecdsa.boundS + v7P256Sha2.sha.boundS + 1 / (v7P256Sha2.macFieldSize : ℚ)
        + 2 * (((v7P256Sha2.ecdsa.tape * len2 v7P256Sha2.ecdsa v7P256Sha2.sha : ℕ) : ℚ)
          / 2 ^ v7P256Sha2.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 115 := by
  native_decide

/-- `v7P256Sha2`'s worst mixed coefficient plus the per-query term: at most `2^-117`. -/
theorem v7P256Sha2_adaptive_slack_coeffS :
    max (max v7P256Sha2.ecdsa.fsCoefficientS v7P256Sha2.sha.fsCoefficientS) (1 / (v7P256Sha2.macFieldSize : ℚ))
      + 2 * ((v7P256Sha2.ecdsa.tape : ℚ) / 2 ^ v7P256Sha2.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 117 := by
  native_decide

/-- **`v7P256Sha2`'s numerals at the mixed accounting**: within `2^-115 + N · 2^-117`. -/
theorem v7P256Sha2_adaptive_rhs_leS (N : ℕ) {Fmac : Type} [Fintype Fmac]
    (hFmac : Fintype.card Fmac = 2 ^ 128) :
    v7P256Sha2.ecdsa.boundS + v7P256Sha2.sha.boundS + 1 / (Fintype.card Fmac : ℚ)
        + N * max (max v7P256Sha2.ecdsa.fsCoefficientS v7P256Sha2.sha.fsCoefficientS)
            (1 / (Fintype.card Fmac : ℚ))
        + 2 * (((v7P256Sha2.ecdsa.tape * (len2 v7P256Sha2.ecdsa v7P256Sha2.sha + N) : ℕ) : ℚ)
          / 2 ^ v7P256Sha2.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) :=
  TwoFieldRowV1.adaptive_rhs_leS_of_slack hFmac v7P256Sha2_adaptive_slack_boundS
    v7P256Sha2_adaptive_slack_coeffS N

/-- `v7P256Sha3` at the mixed accounting, at `N = 0`: at most `2^-115`. -/
theorem v7P256Sha3_adaptive_slack_boundS :
    v7P256Sha3.ecdsa.boundS + v7P256Sha3.sha.boundS + 1 / (v7P256Sha3.macFieldSize : ℚ)
        + 2 * (((v7P256Sha3.ecdsa.tape * len2 v7P256Sha3.ecdsa v7P256Sha3.sha : ℕ) : ℚ)
          / 2 ^ v7P256Sha3.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 115 := by
  native_decide

/-- `v7P256Sha3`'s worst mixed coefficient plus the per-query term: at most `2^-117`. -/
theorem v7P256Sha3_adaptive_slack_coeffS :
    max (max v7P256Sha3.ecdsa.fsCoefficientS v7P256Sha3.sha.fsCoefficientS) (1 / (v7P256Sha3.macFieldSize : ℚ))
      + 2 * ((v7P256Sha3.ecdsa.tape : ℚ) / 2 ^ v7P256Sha3.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 117 := by
  native_decide

/-- **`v7P256Sha3`'s numerals at the mixed accounting**: within `2^-115 + N · 2^-117`. -/
theorem v7P256Sha3_adaptive_rhs_leS (N : ℕ) {Fmac : Type} [Fintype Fmac]
    (hFmac : Fintype.card Fmac = 2 ^ 128) :
    v7P256Sha3.ecdsa.boundS + v7P256Sha3.sha.boundS + 1 / (Fintype.card Fmac : ℚ)
        + N * max (max v7P256Sha3.ecdsa.fsCoefficientS v7P256Sha3.sha.fsCoefficientS)
            (1 / (Fintype.card Fmac : ℚ))
        + 2 * (((v7P256Sha3.ecdsa.tape * (len2 v7P256Sha3.ecdsa v7P256Sha3.sha + N) : ℕ) : ℚ)
          / 2 ^ v7P256Sha3.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) :=
  TwoFieldRowV1.adaptive_rhs_leS_of_slack hFmac v7P256Sha3_adaptive_slack_boundS
    v7P256Sha3_adaptive_slack_coeffS N

/-- `v7P256Sha4` at the mixed accounting, at `N = 0`: at most `2^-115`. -/
theorem v7P256Sha4_adaptive_slack_boundS :
    v7P256Sha4.ecdsa.boundS + v7P256Sha4.sha.boundS + 1 / (v7P256Sha4.macFieldSize : ℚ)
        + 2 * (((v7P256Sha4.ecdsa.tape * len2 v7P256Sha4.ecdsa v7P256Sha4.sha : ℕ) : ℚ)
          / 2 ^ v7P256Sha4.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 115 := by
  native_decide

/-- `v7P256Sha4`'s worst mixed coefficient plus the per-query term: at most `2^-117`. -/
theorem v7P256Sha4_adaptive_slack_coeffS :
    max (max v7P256Sha4.ecdsa.fsCoefficientS v7P256Sha4.sha.fsCoefficientS) (1 / (v7P256Sha4.macFieldSize : ℚ))
      + 2 * ((v7P256Sha4.ecdsa.tape : ℚ) / 2 ^ v7P256Sha4.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 117 := by
  native_decide

/-- **`v7P256Sha4`'s numerals at the mixed accounting**: within `2^-115 + N · 2^-117`. -/
theorem v7P256Sha4_adaptive_rhs_leS (N : ℕ) {Fmac : Type} [Fintype Fmac]
    (hFmac : Fintype.card Fmac = 2 ^ 128) :
    v7P256Sha4.ecdsa.boundS + v7P256Sha4.sha.boundS + 1 / (Fintype.card Fmac : ℚ)
        + N * max (max v7P256Sha4.ecdsa.fsCoefficientS v7P256Sha4.sha.fsCoefficientS)
            (1 / (Fintype.card Fmac : ℚ))
        + 2 * (((v7P256Sha4.ecdsa.tape * (len2 v7P256Sha4.ecdsa v7P256Sha4.sha + N) : ℕ) : ℚ)
          / 2 ^ v7P256Sha4.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) :=
  TwoFieldRowV1.adaptive_rhs_leS_of_slack hFmac v7P256Sha4_adaptive_slack_boundS
    v7P256Sha4_adaptive_slack_coeffS N

end Lfzk.TwoFieldV1Rows

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

`row_adaptive_ratio_le_v1S` at `CertifiedV1.v7Sig` — the v7 signature row (21 layers, 542 sumcheck
slots, over P-256's base field, Ligero V1 at `n = 3187`, `k = 455` with 132 opened columns) — with
the numerals `CertifiedV1.v7Sig_adaptive_rhs_leS`: against one adaptive program making at most
`tA ≤ 2^60` Merkle-oracle and `N` challenge-oracle queries, interleaved as it likes,

```text
Pr[ AcceptsAt (v1K …) …  ∧  Fails(context of the proof's root) ]  ≤  2^-123  +  N · 2^-123
```

over the Merkle tape (`2^62` slots) and a challenge tape of `566 + N` slots. The premises are
`row_adaptive_ratio_le_v1S`'s; `hr` is discharged.
-/
theorem v7Sig_adaptive_compiled_ratio_leS
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
      ≤ (1 : ℚ) / 2 ^ 123 + N * ((1 : ℚ) / 2 ^ 123) :=
  le_trans
    (row_adaptive_ratio_le_v1S v7Sig_valid v7Sig_openings_pos dec V dom stmt respOf body dflt
      rootOf msgOf claimOf hF hfalse H Sat Ffam hexact MD hmatch hfail htA htape hcand hD)
    (v7Sig_adaptive_rhs_leS N)

/--
**v7Hash1 at the compiled Longfellow verifier, against a re-committing Fiat–Shamir prover.**

`row_adaptive_ratio_le_v1S` at `CertifiedV1.v7Hash1` — the v7 1-attribute hash row (17 layers, 566
sumcheck slots, over `GF(2^128)`, Ligero V1 at `n = 3230`, `k = 461` with 132 opened columns) — with
the numerals `CertifiedV1.v7Hash1_adaptive_rhs_leS`: against one adaptive program making at most
`tA ≤ 2^60` Merkle-oracle and `N` challenge-oracle queries, interleaved as it likes,

```text
Pr[ AcceptsAt (v1K …) …  ∧  Fails(context of the proof's root) ]  ≤  2^-115  +  N · 2^-117
```

over the Merkle tape (`2^62` slots) and a challenge tape of `586 + N` slots. The premises are
`row_adaptive_ratio_le_v1S`'s; `hr` is discharged.
-/
theorem v7Hash1_adaptive_compiled_ratio_leS
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
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) :=
  le_trans
    (row_adaptive_ratio_le_v1S v7Hash1_valid v7Hash1_openings_pos dec V dom stmt respOf body dflt
      rootOf msgOf claimOf hF hfalse H Sat Ffam hexact MD hmatch hfail htA htape hcand hD)
    (v7Hash1_adaptive_rhs_leS N)

/--
**v7Hash2 at the compiled Longfellow verifier, against a re-committing Fiat–Shamir prover.**

`row_adaptive_ratio_le_v1S` at `CertifiedV1.v7Hash2` — the v7 2-attribute hash row (17 layers, 570
sumcheck slots, over `GF(2^128)`, Ligero V1 at `n = 3318`, `k = 474` with 132 opened columns) — with
the numerals `CertifiedV1.v7Hash2_adaptive_rhs_leS`: against one adaptive program making at most
`tA ≤ 2^60` Merkle-oracle and `N` challenge-oracle queries, interleaved as it likes,

```text
Pr[ AcceptsAt (v1K …) …  ∧  Fails(context of the proof's root) ]  ≤  2^-115  +  N · 2^-117
```

over the Merkle tape (`2^62` slots) and a challenge tape of `590 + N` slots. The premises are
`row_adaptive_ratio_le_v1S`'s; `hr` is discharged.
-/
theorem v7Hash2_adaptive_compiled_ratio_leS
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
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) :=
  le_trans
    (row_adaptive_ratio_le_v1S v7Hash2_valid v7Hash2_openings_pos dec V dom stmt respOf body dflt
      rootOf msgOf claimOf hF hfalse H Sat Ffam hexact MD hmatch hfail htA htape hcand hD)
    (v7Hash2_adaptive_rhs_leS N)

/--
**v7Hash3 at the compiled Longfellow verifier, against a re-committing Fiat–Shamir prover.**

`row_adaptive_ratio_le_v1S` at `CertifiedV1.v7Hash3` — the v7 3-attribute hash row (17 layers, 574
sumcheck slots, over `GF(2^128)`, Ligero V1 at `n = 3352`, `k = 478` with 132 opened columns) — with
the numerals `CertifiedV1.v7Hash3_adaptive_rhs_leS`: against one adaptive program making at most
`tA ≤ 2^60` Merkle-oracle and `N` challenge-oracle queries, interleaved as it likes,

```text
Pr[ AcceptsAt (v1K …) …  ∧  Fails(context of the proof's root) ]  ≤  2^-115  +  N · 2^-117
```

over the Merkle tape (`2^62` slots) and a challenge tape of `594 + N` slots. The premises are
`row_adaptive_ratio_le_v1S`'s; `hr` is discharged.
-/
theorem v7Hash3_adaptive_compiled_ratio_leS
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
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) :=
  le_trans
    (row_adaptive_ratio_le_v1S v7Hash3_valid v7Hash3_openings_pos dec V dom stmt respOf body dflt
      rootOf msgOf claimOf hF hfalse H Sat Ffam hexact MD hmatch hfail htA htape hcand hD)
    (v7Hash3_adaptive_rhs_leS N)

/--
**v7Hash4 at the compiled Longfellow verifier, against a re-committing Fiat–Shamir prover.**

`row_adaptive_ratio_le_v1S` at `CertifiedV1.v7Hash4` — the v7 4-attribute hash row (17 layers, 574
sumcheck slots, over `GF(2^128)`, Ligero V1 at `n = 3436`, `k = 490` with 132 opened columns) — with
the numerals `CertifiedV1.v7Hash4_adaptive_rhs_leS`: against one adaptive program making at most
`tA ≤ 2^60` Merkle-oracle and `N` challenge-oracle queries, interleaved as it likes,

```text
Pr[ AcceptsAt (v1K …) …  ∧  Fails(context of the proof's root) ]  ≤  2^-115  +  N · 2^-117
```

over the Merkle tape (`2^62` slots) and a challenge tape of `594 + N` slots. The premises are
`row_adaptive_ratio_le_v1S`'s; `hr` is discharged.
-/
theorem v7Hash4_adaptive_compiled_ratio_leS
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
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) :=
  le_trans
    (row_adaptive_ratio_le_v1S v7Hash4_valid v7Hash4_openings_pos dec V dom stmt respOf body dflt
      rootOf msgOf claimOf hF hfalse H Sat Ffam hexact MD hmatch hfail htA htape hcand hD)
    (v7Hash4_adaptive_rhs_leS N)

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

`twofield_adaptive_compiled_ratio_leS` at `TwoFieldV1Rows.v7P256Sha1` — ECDSA over `P-256`'s base
field (`CertifiedV1.v7Sig`) and SHA-256 over `GF(2^128)` (`CertifiedV1.v7Hash1`), the deployed v7
circuits proved with Ligero V1 at 132 openings, composed through the MAC over a field of `2^128`
elements — with the numerals `TwoFieldV1Rows.v7P256Sha1_adaptive_rhs_leS`: against one adaptive
program making at most `tA ≤ 2^60` Merkle-oracle and `N` challenge-oracle queries, over all roles,

```text
Pr [ both compiled verifiers accept  ∧  no two good witnesses agree on the common value ]
    ≤  2^-115  +  N · 2^-117
```

over one Merkle tape of `2^62` slots and one challenge tape of `1153 + N` slots. The premises are
`twofield_adaptive_compiled_ratio_leS`'s; `hr₁`, `hr₂` are discharged.
-/
theorem v7P256Sha1_adaptive_compiled_ratio_leS {tA N : ℕ} (hFmac : Fintype.card Fmac = 2 ^ 128)
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
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) :=
  le_trans
    (twofield_adaptive_compiled_ratio_leS (TwoFieldRowV1.ecdsa_valid v7P256Sha1_valid)
      (TwoFieldRowV1.sha_valid v7P256Sha1_valid) v7P256Sha1_ecdsa_openings_pos v7P256Sha1_sha_openings_pos
      L₁ L₂ body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂ hcand₁ hcand₂ hD hD
      aP decode kmac hbal hmac keyB tagOf common₁ common₂ hrow₁ hrow₂ htA htA htape rfl)
    (v7P256Sha1_adaptive_rhs_leS N hFmac)

/--
**Two-field Longfellow at `v7P256Sha2`, at the compiled verifiers, against one re-committing
Fiat–Shamir prover with a hashed MAC key.**

`twofield_adaptive_compiled_ratio_leS` at `TwoFieldV1Rows.v7P256Sha2` — ECDSA over `P-256`'s base
field (`CertifiedV1.v7Sig`) and SHA-256 over `GF(2^128)` (`CertifiedV1.v7Hash2`), the deployed v7
circuits proved with Ligero V1 at 132 openings, composed through the MAC over a field of `2^128`
elements — with the numerals `TwoFieldV1Rows.v7P256Sha2_adaptive_rhs_leS`: against one adaptive
program making at most `tA ≤ 2^60` Merkle-oracle and `N` challenge-oracle queries, over all roles,

```text
Pr [ both compiled verifiers accept  ∧  no two good witnesses agree on the common value ]
    ≤  2^-115  +  N · 2^-117
```

over one Merkle tape of `2^62` slots and one challenge tape of `1157 + N` slots. The premises are
`twofield_adaptive_compiled_ratio_leS`'s; `hr₁`, `hr₂` are discharged.
-/
theorem v7P256Sha2_adaptive_compiled_ratio_leS {tA N : ℕ} (hFmac : Fintype.card Fmac = 2 ^ 128)
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
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) :=
  le_trans
    (twofield_adaptive_compiled_ratio_leS (TwoFieldRowV1.ecdsa_valid v7P256Sha2_valid)
      (TwoFieldRowV1.sha_valid v7P256Sha2_valid) v7P256Sha2_ecdsa_openings_pos v7P256Sha2_sha_openings_pos
      L₁ L₂ body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂ hcand₁ hcand₂ hD hD
      aP decode kmac hbal hmac keyB tagOf common₁ common₂ hrow₁ hrow₂ htA htA htape rfl)
    (v7P256Sha2_adaptive_rhs_leS N hFmac)

/--
**Two-field Longfellow at `v7P256Sha3`, at the compiled verifiers, against one re-committing
Fiat–Shamir prover with a hashed MAC key.**

`twofield_adaptive_compiled_ratio_leS` at `TwoFieldV1Rows.v7P256Sha3` — ECDSA over `P-256`'s base
field (`CertifiedV1.v7Sig`) and SHA-256 over `GF(2^128)` (`CertifiedV1.v7Hash3`), the deployed v7
circuits proved with Ligero V1 at 132 openings, composed through the MAC over a field of `2^128`
elements — with the numerals `TwoFieldV1Rows.v7P256Sha3_adaptive_rhs_leS`: against one adaptive
program making at most `tA ≤ 2^60` Merkle-oracle and `N` challenge-oracle queries, over all roles,

```text
Pr [ both compiled verifiers accept  ∧  no two good witnesses agree on the common value ]
    ≤  2^-115  +  N · 2^-117
```

over one Merkle tape of `2^62` slots and one challenge tape of `1161 + N` slots. The premises are
`twofield_adaptive_compiled_ratio_leS`'s; `hr₁`, `hr₂` are discharged.
-/
theorem v7P256Sha3_adaptive_compiled_ratio_leS {tA N : ℕ} (hFmac : Fintype.card Fmac = 2 ^ 128)
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
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) :=
  le_trans
    (twofield_adaptive_compiled_ratio_leS (TwoFieldRowV1.ecdsa_valid v7P256Sha3_valid)
      (TwoFieldRowV1.sha_valid v7P256Sha3_valid) v7P256Sha3_ecdsa_openings_pos v7P256Sha3_sha_openings_pos
      L₁ L₂ body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂ hcand₁ hcand₂ hD hD
      aP decode kmac hbal hmac keyB tagOf common₁ common₂ hrow₁ hrow₂ htA htA htape rfl)
    (v7P256Sha3_adaptive_rhs_leS N hFmac)

/--
**Two-field Longfellow at `v7P256Sha4`, at the compiled verifiers, against one re-committing
Fiat–Shamir prover with a hashed MAC key.**

`twofield_adaptive_compiled_ratio_leS` at `TwoFieldV1Rows.v7P256Sha4` — ECDSA over `P-256`'s base
field (`CertifiedV1.v7Sig`) and SHA-256 over `GF(2^128)` (`CertifiedV1.v7Hash4`), the deployed v7
circuits proved with Ligero V1 at 132 openings, composed through the MAC over a field of `2^128`
elements — with the numerals `TwoFieldV1Rows.v7P256Sha4_adaptive_rhs_leS`: against one adaptive
program making at most `tA ≤ 2^60` Merkle-oracle and `N` challenge-oracle queries, over all roles,

```text
Pr [ both compiled verifiers accept  ∧  no two good witnesses agree on the common value ]
    ≤  2^-115  +  N · 2^-117
```

over one Merkle tape of `2^62` slots and one challenge tape of `1161 + N` slots. The premises are
`twofield_adaptive_compiled_ratio_leS`'s; `hr₁`, `hr₂` are discharged.
-/
theorem v7P256Sha4_adaptive_compiled_ratio_leS {tA N : ℕ} (hFmac : Fintype.card Fmac = 2 ^ 128)
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
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) :=
  le_trans
    (twofield_adaptive_compiled_ratio_leS (TwoFieldRowV1.ecdsa_valid v7P256Sha4_valid)
      (TwoFieldRowV1.sha_valid v7P256Sha4_valid) v7P256Sha4_ecdsa_openings_pos v7P256Sha4_sha_openings_pos
      L₁ L₂ body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂ hcand₁ hcand₂ hD hD
      aP decode kmac hbal hmac keyB tagOf common₁ common₂ hrow₁ hrow₂ htA htA htape rfl)
    (v7P256Sha4_adaptive_rhs_leS N hFmac)

end TwoField

end Lfzk.CompiledLongfellowAdaptive
