import examples.Ligero.Longfellow.OptimizedIOPCertificates
import Ligero.V1.AdaptiveLocal
import Ligero.V2.AdaptiveLocal
import Ligero.V3.AdaptiveLocal

/-! Exact per-round arithmetic certificates for the Ligero profile bounds. -/

namespace Ligero.Examples.Grid.LongfellowProfiledExtraction

open LigeroFamily

def Result.adaptiveEscapeRate (s : Result) (failureThreshold arithmeticThreshold : ℕ) : ℚ :=
  let c := s.certificate
  (s.failureProfile.labelsAtLeast (failureThreshold + 1) : ℚ) /
      c.optimizedFailureDenominator +
    (s.arithmeticProfile.labelsAtLeast (arithmeticThreshold + 1) : ℚ) / c.fieldSize

def Result.adaptiveCoverSize (s : Result) (failureThreshold arithmeticThreshold : ℕ) : ℕ :=
  let c := s.certificate
  (max failureThreshold (max (c.n - c.e - 1)
    (min c.n (c.g + arithmeticThreshold)))).choose c.openings

def Result.adaptiveCoverRate (s : Result) (failureThreshold arithmeticThreshold : ℕ) : ℚ :=
  (s.adaptiveCoverSize failureThreshold arithmeticThreshold : ℚ) /
    s.certificate.n.choose s.certificate.openings

structure CountCertificate (s : Result) where
  failureThreshold : ℕ
  arithmeticThreshold : ℕ
  bits : ℕ
  failure_fits : failureThreshold + 1 ≤ s.certificate.n
  arithmetic_fits : arithmeticThreshold + 1 ≤ s.certificate.n
  escape_le : s.adaptiveEscapeRate failureThreshold arithmeticThreshold ≤
    (1 : ℚ) / 2 ^ bits
  cover_le : s.adaptiveCoverRate failureThreshold arithmeticThreshold ≤
    (1 : ℚ) / 2 ^ bits

/-- Exact integer count for each variant's local escape budget, for any
concrete challenge type. -/
def CountCertificate.escapeCount {s : Result} (x : CountCertificate s)
    (challengeCard : ℕ) : ℕ :=
  Nat.ceil (s.adaptiveEscapeRate x.failureThreshold x.arithmeticThreshold *
    challengeCard)

def CountCertificate.coverCount {s : Result} (x : CountCertificate s) : ℕ :=
  s.adaptiveCoverSize x.failureThreshold x.arithmeticThreshold

theorem CountCertificate.escape_budget {s : Result} (x : CountCertificate s)
    (challengeCard : ℕ) :
    s.adaptiveEscapeRate x.failureThreshold x.arithmeticThreshold *
      challengeCard ≤ x.escapeCount challengeCard := by
  exact_mod_cast Nat.le_ceil
    (s.adaptiveEscapeRate x.failureThreshold x.arithmeticThreshold * challengeCard)

/-- The sole numerical rounding cost is less than one challenge point. -/
theorem CountCertificate.escape_ratio_lt {s : Result} (x : CountCertificate s)
    (challengeCard : ℕ) (hcard : 0 < challengeCard) :
    (x.escapeCount challengeCard : ℚ) / challengeCard <
      s.adaptiveEscapeRate x.failureThreshold x.arithmeticThreshold +
        1 / (challengeCard : ℚ) := by
  have hnonneg : 0 ≤ s.adaptiveEscapeRate x.failureThreshold
      x.arithmeticThreshold * (challengeCard : ℚ) := by
    unfold Result.adaptiveEscapeRate
    positivity
  have hceil := Nat.ceil_lt_add_one hnonneg
  have hpositive : (0 : ℚ) < challengeCard := by exact_mod_cast hcard
  apply (div_lt_iff₀ hpositive).2
  dsimp [CountCertificate.escapeCount] at hceil ⊢
  field_simp
  nlinarith

theorem CountCertificate.cover_budget {s : Result} (x : CountCertificate s)
    (hopen : s.certificate.openings ≤ s.certificate.n) :
    hypergeometricRatio
      (max x.failureThreshold
        (max (s.certificate.n - s.certificate.e - 1)
          (min s.certificate.n (s.certificate.g + x.arithmeticThreshold))))
      s.certificate.n s.certificate.openings *
        s.certificate.n.choose s.certificate.openings ≤ x.coverCount := by
  have hn : (s.certificate.n.choose s.certificate.openings : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hopen).ne'
  simp [CountCertificate.coverCount, Result.adaptiveCoverSize,
    hypergeometricRatio, hn]

/-- The checked V1 numeric record supplies its exact escape-count budget. -/
theorem CountCertificate.v1_escape_budget {s : Result} (x : CountCertificate s)
    (hv : s.variant = .v1)
    {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations] {nw nq : ℕ}
    (hf : Fintype.card F = s.certificate.fieldSize) :
    (((SchemeSelectedMCA.selectedMCAOptimizedIntegratedFailureProfile
        (Fintype.card F) s.certificate.n s.certificate.e s.certificate.g
        s.certificate.d s.certificate.lineBound s.localBound).labelsAtLeast
          (x.failureThreshold + 1) : ℚ) /
        SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator
          (Fintype.card F) s.certificate.g +
      ((maskAgreementProfile (Fintype.card F) s.certificate.n
        s.certificate.listSize s.certificate.maskStart s.certificate.maskBound).labelsAtLeast
          (x.arithmeticThreshold + 1) : ℚ) / Fintype.card F) *
      Fintype.card (Ligero.V1.Challenge F nw nq 1 Equations) ≤
      x.escapeCount (Fintype.card (Ligero.V1.Challenge F nw nq 1 Equations)) := by
  simpa [Result.adaptiveEscapeRate, Result.failureProfile,
    Result.arithmeticProfile, hv, hf, Certificate.optimizedFailureDenominator]
    using x.escape_budget (Fintype.card (Ligero.V1.Challenge F nw nq 1 Equations))

/-- The checked V2 numeric record supplies its exact escape-count budget. -/
theorem CountCertificate.v2_escape_budget {s : Result} (x : CountCertificate s)
    (hv : s.variant = .v2)
    {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations] {nw nq : ℕ}
    (hf : Fintype.card F = s.certificate.fieldSize) :
    (((SchemeSelectedMCA.selectedMCAOptimizedIntegratedFailureProfile
        (Fintype.card F) s.certificate.n s.certificate.e s.certificate.g
        s.certificate.d s.certificate.lineBound s.localBound).labelsAtLeast
          (x.failureThreshold + 1) : ℚ) /
        SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator
          (Fintype.card F) s.certificate.g +
      ((checkedAgreementProfile (Fintype.card F) s.certificate.listSize
        s.certificate.n (2 * s.certificate.k - 1)).labelsAtLeast
          (x.arithmeticThreshold + 1) : ℚ) / Fintype.card F) *
      Fintype.card (Ligero.V2.Challenge F nw nq 1 Equations) ≤
      x.escapeCount (Fintype.card (Ligero.V2.Challenge F nw nq 1 Equations)) := by
  simpa [Result.adaptiveEscapeRate, Result.failureProfile,
    Result.arithmeticProfile, hv, hf, Certificate.optimizedFailureDenominator]
    using x.escape_budget (Fintype.card (Ligero.V2.Challenge F nw nq 1 Equations))

/-- V3 has the same checked-mask count profile as V2, with its direct
challenge type in the integer ceiling. -/
theorem CountCertificate.v3_escape_budget {s : Result} (x : CountCertificate s)
    (hv : s.variant = .v3)
    {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations] {nw nq : ℕ}
    (hf : Fintype.card F = s.certificate.fieldSize) :
    (((SchemeSelectedMCA.selectedMCAOptimizedIntegratedFailureProfile
        (Fintype.card F) s.certificate.n s.certificate.e s.certificate.g
        s.certificate.d s.certificate.lineBound s.localBound).labelsAtLeast
          (x.failureThreshold + 1) : ℚ) /
        SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator
          (Fintype.card F) s.certificate.g +
      ((checkedAgreementProfile (Fintype.card F) s.certificate.listSize
        s.certificate.n (2 * s.certificate.k - 1)).labelsAtLeast
          (x.arithmeticThreshold + 1) : ℚ) / Fintype.card F) *
      Fintype.card (DirectChallenge F Equations nw nq 1) ≤
      x.escapeCount (Fintype.card (DirectChallenge F Equations nw nq 1)) := by
  simpa [Result.adaptiveEscapeRate, Result.failureProfile,
    Result.arithmeticProfile, hv, hf, Certificate.optimizedFailureDenominator]
    using x.escape_budget (Fintype.card (DirectChallenge F Equations nw nq 1))

set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

namespace Optimized

/-- Signature count certificates on the IOP-optimized geometries. -/
def v7Sig_v1_adaptiveCounts : CountCertificate v7Sig_v1 :=
  ⟨0, 1664, 127, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

def v7Sig_v2_adaptiveCounts : CountCertificate v7Sig_v2 :=
  ⟨0, 909, 191, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

def v7Sig_v3_adaptiveCounts : CountCertificate v7Sig_v3 :=
  ⟨0, 909, 191, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

def v8Sig_v1_adaptiveCounts : CountCertificate v8Sig_v1 :=
  ⟨0, 1807, 127, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

def v8Sig_v2_adaptiveCounts : CountCertificate v8Sig_v2 :=
  ⟨0, 987, 191, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

def v8Sig_v3_adaptiveCounts : CountCertificate v8Sig_v3 :=
  ⟨0, 987, 191, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

end Optimized
end Ligero.Examples.Grid.LongfellowProfiledExtraction
