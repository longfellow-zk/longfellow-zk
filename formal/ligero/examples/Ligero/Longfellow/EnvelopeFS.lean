import examples.Ligero.Longfellow.ProfiledExtraction
import LigeroFamily.Soundness.EnvelopeCompiler

/-! Concrete RS bridges for the response-uniform typed FS compiler. Every
local numerical premise comes from a complete certified IOP instance. -/
namespace Ligero.Examples.Grid.LongfellowProfiledExtraction
open LigeroFamily Bcs.EnvelopeFiatShamir Bcs.TypedFiatShamir
open scoped Classical BigOperators
set_option maxHeartbeats 10000000
variable {AlphaKey Salt Digest Encoding Output PrefixOut RunOut : Type*}
variable [DecidableEq AlphaKey] [Inhabited Salt] [Inhabited Digest]
variable [Fintype Digest] [DecidableEq Digest] [DecidableEq Encoding]
variable {N merkleT prefixFuel runFuel : ℕ}

theorem CertifiedResult.v1_fs_localBound
    (s : CertifiedResult) (hv : s.result.variant = .v1)
    {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations] {w nw nq : ℕ}
    (hf : Fintype.card F = s.result.certificate.fieldSize)
    (hdim : s.result.certificate.openings + w = s.result.certificate.k)
    (D : ReedSolomon.Domain F s.result.certificate.openings w s.result.certificate.n)
    (hkn : s.result.certificate.openings + w ≤ s.result.certificate.n)
    (hrows : CoreRowsNonempty nw nq)
    (statement : ConstraintSystem F nw nq w Equations)
    (oracle : SchemeOracle F NoMask Ligero.V1.Mask nw nq s.result.certificate.n 1) :
    Nonempty (ResponseUniformBound (fun alpha response query => (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.result.code D hkn) Ligero.V1.scheme).accepts statement alpha response query
        (openSchemeOracle oracle query) ∧
        ScalarGapExtraction.extract (oracle := oracle) (e := s.result.certificate.e) (g := s.result.certificate.g)
          (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.result.code D hkn) Ligero.V1.scheme) (fun candidate => candidate.decodedMessages) statement alpha response = none) ((1 : ℚ) / 2 ^ s.result.certificate.targetBits)) := by
  letI : Nonempty (Response F s.result.certificate.openings w s.result.certificate.n 1) := ⟨⟨fun _ => 0, fun _ => 0, fun _ => 0⟩⟩
  exact EnvelopeFS.localBound_of_mean (e := s.result.certificate.e) (g := s.result.certificate.g) (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.result.code D hkn) Ligero.V1.scheme) (fun _ candidate => candidate.decodedMessages)
    statement oracle ((1 : ℚ) / 2 ^ s.result.certificate.targetBits) (CertifiedResult.v1_uniform_envelope s hv hf hdim D hkn hrows statement oracle)

theorem CertifiedResult.v1_fs_extraction
    (s : CertifiedResult) (hv : s.result.variant = .v1)
    {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations] {w nw nq : ℕ}
    (hf : Fintype.card F = s.result.certificate.fieldSize)
    (hdim : s.result.certificate.openings + w = s.result.certificate.k)
    (D : ReedSolomon.Domain F s.result.certificate.openings w s.result.certificate.n)
    (hkn : s.result.certificate.openings + w ≤ s.result.certificate.n)
    (hrows : CoreRowsNonempty nw nq)
    (statement : ConstraintSystem F nw nq w Equations)
    (experiment : EnvelopeFS.Experiment (SchemeColumn F NoMask Ligero.V1.Mask nw nq 1)
      (Ligero.V1.Challenge F nw nq 1 Equations) (Response F s.result.certificate.openings w s.result.certificate.n 1) AlphaKey Salt Digest Encoding Output PrefixOut RunOut
      s.result.certificate.n s.result.certificate.openings N merkleT prefixFuel runFuel) :
    ((Finset.univ.filter fun value : (Fin merkleT → Digest) × (Fin (N + 2) → Answer (Ligero.V1.Challenge F nw nq 1 Equations) (QuerySet s.result.certificate.n s.result.certificate.openings)) =>
      EnvelopeFS.compiledAccepts (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.result.code D hkn) Ligero.V1.scheme) statement experiment value.1 value.2 ∧
        EnvelopeFS.extract (e := s.result.certificate.e) (g := s.result.certificate.g) (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.result.code D hkn) Ligero.V1.scheme) (fun _ candidate => candidate.decodedMessages) statement experiment value.1 value.2 = none).card : ℚ) /
      Fintype.card ((Fin merkleT → Digest) × (Fin (N + 2) → Answer (Ligero.V1.Challenge F nw nq 1 Equations) (QuerySet s.result.certificate.n s.result.certificate.openings))) ≤ experiment.compiledBound ((1 : ℚ) / 2 ^ s.result.certificate.targetBits) := by
  exact EnvelopeFS.extraction_ratio_le (e := s.result.certificate.e) (g := s.result.certificate.g) (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.result.code D hkn) Ligero.V1.scheme) (fun _ candidate => candidate.decodedMessages)
    statement experiment ((1 : ℚ) / 2 ^ s.result.certificate.targetBits)
    (fun oracle => CertifiedResult.v1_fs_localBound s hv hf hdim D hkn hrows statement oracle)

theorem CertifiedResult.v1_fs_soundness
    (s : CertifiedResult) (hv : s.result.variant = .v1)
    {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations] {w nw nq : ℕ}
    (hf : Fintype.card F = s.result.certificate.fieldSize)
    (hdim : s.result.certificate.openings + w = s.result.certificate.k)
    (D : ReedSolomon.Domain F s.result.certificate.openings w s.result.certificate.n)
    (hkn : s.result.certificate.openings + w ≤ s.result.certificate.n)
    (hrows : CoreRowsNonempty nw nq)
    (statement : ConstraintSystem F nw nq w Equations)
    (experiment : EnvelopeFS.Experiment (SchemeColumn F NoMask Ligero.V1.Mask nw nq 1)
      (Ligero.V1.Challenge F nw nq 1 Equations) (Response F s.result.certificate.openings w s.result.certificate.n 1) AlphaKey Salt Digest Encoding Output PrefixOut RunOut
      s.result.certificate.n s.result.certificate.openings N merkleT prefixFuel runFuel)
    (hfalse : ¬statement.Language) :
    ((Finset.univ.filter fun value : (Fin merkleT → Digest) × (Fin (N + 2) → Answer (Ligero.V1.Challenge F nw nq 1 Equations) (QuerySet s.result.certificate.n s.result.certificate.openings)) =>
      EnvelopeFS.compiledAccepts (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.result.code D hkn) Ligero.V1.scheme) statement experiment value.1 value.2).card : ℚ) /
      Fintype.card ((Fin merkleT → Digest) × (Fin (N + 2) → Answer (Ligero.V1.Challenge F nw nq 1 Equations) (QuerySet s.result.certificate.n s.result.certificate.openings))) ≤ experiment.compiledBound ((1 : ℚ) / 2 ^ s.result.certificate.targetBits) := by
  exact EnvelopeFS.soundness_ratio_le (e := s.result.certificate.e) (g := s.result.certificate.g) (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.result.code D hkn) Ligero.V1.scheme) (fun _ candidate => candidate.decodedMessages)
    statement experiment ((1 : ℚ) / 2 ^ s.result.certificate.targetBits)
    (fun oracle => CertifiedResult.v1_fs_localBound s hv hf hdim D hkn hrows statement oracle) hfalse

theorem CertifiedResult.v2_fs_localBound
    (s : CertifiedResult) (hv : s.result.variant = .v2)
    {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations] {w nw nq : ℕ}
    (hf : Fintype.card F = s.result.certificate.fieldSize)
    (hdim : s.result.certificate.openings + w = s.result.certificate.k)
    (D : ReedSolomon.Domain F s.result.certificate.openings w s.result.certificate.n)
    (hkn : s.result.certificate.openings + w ≤ s.result.certificate.n)
    (M : (s.result.code D hkn).MaskingBasis)
    (statement : ConstraintSystem F nw nq w Equations)
    (oracle : SchemeOracle F Ligero.V2.Mask NoMask nw nq s.result.certificate.n 1) :
    Nonempty (ResponseUniformBound (fun alpha response query => (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.result.code D hkn) (Ligero.V2.scheme (s.result.code D hkn) M)).accepts statement alpha response query
        (openSchemeOracle oracle query) ∧
        ScalarGapExtraction.extract (oracle := oracle) (e := s.result.certificate.e) (g := s.result.certificate.g)
          (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.result.code D hkn) (Ligero.V2.scheme (s.result.code D hkn) M)) (fun candidate => candidate.decodedMessages) statement alpha response = none) ((1 : ℚ) / 2 ^ s.result.certificate.targetBits)) := by
  letI : Nonempty (Response F s.result.certificate.openings w s.result.certificate.n 1) := ⟨⟨fun _ => 0, fun _ => 0, fun _ => 0⟩⟩
  exact EnvelopeFS.localBound_of_mean (e := s.result.certificate.e) (g := s.result.certificate.g) (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.result.code D hkn) (Ligero.V2.scheme (s.result.code D hkn) M)) (fun _ candidate => candidate.decodedMessages)
    statement oracle ((1 : ℚ) / 2 ^ s.result.certificate.targetBits) (CertifiedResult.v2_uniform_envelope s hv hf hdim D hkn M statement oracle)

theorem CertifiedResult.v2_fs_extraction
    (s : CertifiedResult) (hv : s.result.variant = .v2)
    {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations] {w nw nq : ℕ}
    (hf : Fintype.card F = s.result.certificate.fieldSize)
    (hdim : s.result.certificate.openings + w = s.result.certificate.k)
    (D : ReedSolomon.Domain F s.result.certificate.openings w s.result.certificate.n)
    (hkn : s.result.certificate.openings + w ≤ s.result.certificate.n)
    (M : (s.result.code D hkn).MaskingBasis)
    (statement : ConstraintSystem F nw nq w Equations)
    (experiment : EnvelopeFS.Experiment (SchemeColumn F Ligero.V2.Mask NoMask nw nq 1)
      (Ligero.V2.Challenge F nw nq 1 Equations) (Response F s.result.certificate.openings w s.result.certificate.n 1) AlphaKey Salt Digest Encoding Output PrefixOut RunOut
      s.result.certificate.n s.result.certificate.openings N merkleT prefixFuel runFuel) :
    ((Finset.univ.filter fun value : (Fin merkleT → Digest) × (Fin (N + 2) → Answer (Ligero.V2.Challenge F nw nq 1 Equations) (QuerySet s.result.certificate.n s.result.certificate.openings)) =>
      EnvelopeFS.compiledAccepts (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.result.code D hkn) (Ligero.V2.scheme (s.result.code D hkn) M)) statement experiment value.1 value.2 ∧
        EnvelopeFS.extract (e := s.result.certificate.e) (g := s.result.certificate.g) (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.result.code D hkn) (Ligero.V2.scheme (s.result.code D hkn) M)) (fun _ candidate => candidate.decodedMessages) statement experiment value.1 value.2 = none).card : ℚ) /
      Fintype.card ((Fin merkleT → Digest) × (Fin (N + 2) → Answer (Ligero.V2.Challenge F nw nq 1 Equations) (QuerySet s.result.certificate.n s.result.certificate.openings))) ≤ experiment.compiledBound ((1 : ℚ) / 2 ^ s.result.certificate.targetBits) := by
  exact EnvelopeFS.extraction_ratio_le (e := s.result.certificate.e) (g := s.result.certificate.g) (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.result.code D hkn) (Ligero.V2.scheme (s.result.code D hkn) M)) (fun _ candidate => candidate.decodedMessages)
    statement experiment ((1 : ℚ) / 2 ^ s.result.certificate.targetBits)
    (fun oracle => CertifiedResult.v2_fs_localBound s hv hf hdim D hkn M statement oracle)

theorem CertifiedResult.v2_fs_soundness
    (s : CertifiedResult) (hv : s.result.variant = .v2)
    {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations] {w nw nq : ℕ}
    (hf : Fintype.card F = s.result.certificate.fieldSize)
    (hdim : s.result.certificate.openings + w = s.result.certificate.k)
    (D : ReedSolomon.Domain F s.result.certificate.openings w s.result.certificate.n)
    (hkn : s.result.certificate.openings + w ≤ s.result.certificate.n)
    (M : (s.result.code D hkn).MaskingBasis)
    (statement : ConstraintSystem F nw nq w Equations)
    (experiment : EnvelopeFS.Experiment (SchemeColumn F Ligero.V2.Mask NoMask nw nq 1)
      (Ligero.V2.Challenge F nw nq 1 Equations) (Response F s.result.certificate.openings w s.result.certificate.n 1) AlphaKey Salt Digest Encoding Output PrefixOut RunOut
      s.result.certificate.n s.result.certificate.openings N merkleT prefixFuel runFuel)
    (hfalse : ¬statement.Language) :
    ((Finset.univ.filter fun value : (Fin merkleT → Digest) × (Fin (N + 2) → Answer (Ligero.V2.Challenge F nw nq 1 Equations) (QuerySet s.result.certificate.n s.result.certificate.openings)) =>
      EnvelopeFS.compiledAccepts (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.result.code D hkn) (Ligero.V2.scheme (s.result.code D hkn) M)) statement experiment value.1 value.2).card : ℚ) /
      Fintype.card ((Fin merkleT → Digest) × (Fin (N + 2) → Answer (Ligero.V2.Challenge F nw nq 1 Equations) (QuerySet s.result.certificate.n s.result.certificate.openings))) ≤ experiment.compiledBound ((1 : ℚ) / 2 ^ s.result.certificate.targetBits) := by
  exact EnvelopeFS.soundness_ratio_le (e := s.result.certificate.e) (g := s.result.certificate.g) (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.result.code D hkn) (Ligero.V2.scheme (s.result.code D hkn) M)) (fun _ candidate => candidate.decodedMessages)
    statement experiment ((1 : ℚ) / 2 ^ s.result.certificate.targetBits)
    (fun oracle => CertifiedResult.v2_fs_localBound s hv hf hdim D hkn M statement oracle) hfalse

theorem CertifiedResult.v3_fs_localBound
    (s : CertifiedResult) (hv : s.result.variant = .v3)
    {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations] {w nw nq : ℕ}
    (hf : Fintype.card F = s.result.certificate.fieldSize)
    (hdim : s.result.certificate.openings + w = s.result.certificate.k)
    (D : ReedSolomon.Domain F s.result.certificate.openings w s.result.certificate.n)
    (hkn : s.result.certificate.openings + w ≤ s.result.certificate.n)
    (M : (s.result.code D hkn).MaskingBasis)
    (statement : ConstraintSystem F nw nq w Equations)
    (oracle : SchemeOracle F LinearConstraintMask NoMask nw nq s.result.certificate.n 1) :
    Nonempty (ResponseUniformBound (fun alpha response query => (DirectVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.result.code D hkn) M (ConstraintLayout.identity (F := F) w)).accepts statement alpha response query
        (openSchemeOracle oracle query) ∧
        ScalarGapExtraction.extract (oracle := oracle) (e := s.result.certificate.e) (g := s.result.certificate.g)
          (DirectVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.result.code D hkn) M (ConstraintLayout.identity (F := F) w)) (fun candidate => candidate.directMessages (layout := ConstraintLayout.identity (F := F) w)) statement alpha response = none) ((1 : ℚ) / 2 ^ s.result.certificate.targetBits)) := by
  letI : Nonempty (DirectResponse F s.result.certificate.openings w s.result.certificate.n 1) := ⟨⟨fun _ => 0, fun _ => 0⟩⟩
  exact EnvelopeFS.localBound_of_mean (e := s.result.certificate.e) (g := s.result.certificate.g) (DirectVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.result.code D hkn) M (ConstraintLayout.identity (F := F) w)) (fun _ candidate => candidate.directMessages (layout := ConstraintLayout.identity (F := F) w))
    statement oracle ((1 : ℚ) / 2 ^ s.result.certificate.targetBits) (CertifiedResult.v3_uniform_envelope s hv hf hdim D hkn M statement oracle)

theorem CertifiedResult.v3_fs_extraction
    (s : CertifiedResult) (hv : s.result.variant = .v3)
    {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations] {w nw nq : ℕ}
    (hf : Fintype.card F = s.result.certificate.fieldSize)
    (hdim : s.result.certificate.openings + w = s.result.certificate.k)
    (D : ReedSolomon.Domain F s.result.certificate.openings w s.result.certificate.n)
    (hkn : s.result.certificate.openings + w ≤ s.result.certificate.n)
    (M : (s.result.code D hkn).MaskingBasis)
    (statement : ConstraintSystem F nw nq w Equations)
    (experiment : EnvelopeFS.Experiment (SchemeColumn F LinearConstraintMask NoMask nw nq 1)
      (DirectChallenge F Equations nw nq 1) (DirectResponse F s.result.certificate.openings w s.result.certificate.n 1) AlphaKey Salt Digest Encoding Output PrefixOut RunOut
      s.result.certificate.n s.result.certificate.openings N merkleT prefixFuel runFuel) :
    ((Finset.univ.filter fun value : (Fin merkleT → Digest) × (Fin (N + 2) → Answer (DirectChallenge F Equations nw nq 1) (QuerySet s.result.certificate.n s.result.certificate.openings)) =>
      EnvelopeFS.compiledAccepts (DirectVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.result.code D hkn) M (ConstraintLayout.identity (F := F) w)) statement experiment value.1 value.2 ∧
        EnvelopeFS.extract (e := s.result.certificate.e) (g := s.result.certificate.g) (DirectVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.result.code D hkn) M (ConstraintLayout.identity (F := F) w)) (fun _ candidate => candidate.directMessages (layout := ConstraintLayout.identity (F := F) w)) statement experiment value.1 value.2 = none).card : ℚ) /
      Fintype.card ((Fin merkleT → Digest) × (Fin (N + 2) → Answer (DirectChallenge F Equations nw nq 1) (QuerySet s.result.certificate.n s.result.certificate.openings))) ≤ experiment.compiledBound ((1 : ℚ) / 2 ^ s.result.certificate.targetBits) := by
  exact EnvelopeFS.extraction_ratio_le (e := s.result.certificate.e) (g := s.result.certificate.g) (DirectVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.result.code D hkn) M (ConstraintLayout.identity (F := F) w)) (fun _ candidate => candidate.directMessages (layout := ConstraintLayout.identity (F := F) w))
    statement experiment ((1 : ℚ) / 2 ^ s.result.certificate.targetBits)
    (fun oracle => CertifiedResult.v3_fs_localBound s hv hf hdim D hkn M statement oracle)

theorem CertifiedResult.v3_fs_soundness
    (s : CertifiedResult) (hv : s.result.variant = .v3)
    {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations] {w nw nq : ℕ}
    (hf : Fintype.card F = s.result.certificate.fieldSize)
    (hdim : s.result.certificate.openings + w = s.result.certificate.k)
    (D : ReedSolomon.Domain F s.result.certificate.openings w s.result.certificate.n)
    (hkn : s.result.certificate.openings + w ≤ s.result.certificate.n)
    (M : (s.result.code D hkn).MaskingBasis)
    (statement : ConstraintSystem F nw nq w Equations)
    (experiment : EnvelopeFS.Experiment (SchemeColumn F LinearConstraintMask NoMask nw nq 1)
      (DirectChallenge F Equations nw nq 1) (DirectResponse F s.result.certificate.openings w s.result.certificate.n 1) AlphaKey Salt Digest Encoding Output PrefixOut RunOut
      s.result.certificate.n s.result.certificate.openings N merkleT prefixFuel runFuel)
    (hfalse : ¬statement.Language) :
    ((Finset.univ.filter fun value : (Fin merkleT → Digest) × (Fin (N + 2) → Answer (DirectChallenge F Equations nw nq 1) (QuerySet s.result.certificate.n s.result.certificate.openings)) =>
      EnvelopeFS.compiledAccepts (DirectVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.result.code D hkn) M (ConstraintLayout.identity (F := F) w)) statement experiment value.1 value.2).card : ℚ) /
      Fintype.card ((Fin merkleT → Digest) × (Fin (N + 2) → Answer (DirectChallenge F Equations nw nq 1) (QuerySet s.result.certificate.n s.result.certificate.openings))) ≤ experiment.compiledBound ((1 : ℚ) / 2 ^ s.result.certificate.targetBits) := by
  exact EnvelopeFS.soundness_ratio_le (e := s.result.certificate.e) (g := s.result.certificate.g) (DirectVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.result.code D hkn) M (ConstraintLayout.identity (F := F) w)) (fun _ candidate => candidate.directMessages (layout := ConstraintLayout.identity (F := F) w))
    statement experiment ((1 : ℚ) / 2 ^ s.result.certificate.targetBits)
    (fun oracle => CertifiedResult.v3_fs_localBound s hv hf hdim D hkn M statement oracle) hfalse

end Ligero.Examples.Grid.LongfellowProfiledExtraction
