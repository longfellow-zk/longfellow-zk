import polygero.Recursion.Extractor

/-! Successful extraction produces a witness satisfying the original constraints. -/

namespace RecursivePolygero.Protocol.ProfileProof
open Finset Counting ProfileAnalysis
attribute [local instance] Classical.propDecidable
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {I : Instance F} {protocol : Protocol I} {p : ProfileCertificate I}

theorem extract_eq_run_of_accept (r : protocol.ProfileProof p) (σ : I.layer.Statement)
    (W : I.layer.Oracle) (messages : Strategy protocol.chain) (coins : protocol.chain.Coins)
    (h : executionVerify protocol.chain σ W messages coins = true) :
    r.extract σ W messages coins = r.run σ W messages coins := by
  simp [extract,extractTranscript,run,h]

theorem extract_eq_none_of_reject (r : protocol.ProfileProof p) (σ : I.layer.Statement)
    (W : I.layer.Oracle) (messages : Strategy protocol.chain) (coins : protocol.chain.Coins)
    (h : executionVerify protocol.chain σ W messages coins = false) :
    r.extract σ W messages coins = none := by
  simp [extract,extractTranscript,h]

theorem runTranscript_valid (r : protocol.ProfileProof p) (σ : I.layer.Statement) (W : I.layer.Oracle)
    (transcript : protocol.chain.Transcript) (g)
    (h : r.runTranscript σ W transcript = some g) :
    I.layer.satisfies σ ((r.family W).witness g) := by
  cases r with
  | terminal p => exact scanRecoverAt_valid I σ W _ _ g h
  | step p rest =>
    simp only [runTranscript] at h
    split at h
    · contradiction
    · exact scanRecoverAt_valid I σ W _ _ g h

theorem extractTranscript_valid (r : protocol.ProfileProof p) (σ : I.layer.Statement)
    (W : I.layer.Oracle) (transcript : Option protocol.chain.Transcript) (g)
    (h : r.extractTranscript σ W transcript = some g) :
    I.layer.satisfies σ ((r.family W).witness g) := by
  cases transcript with
  | none => simp [extractTranscript] at h
  | some transcript => exact r.runTranscript_valid σ W transcript g h

theorem run_valid (r : protocol.ProfileProof p) (σ : I.layer.Statement) (W : I.layer.Oracle)
    (messages : Strategy protocol.chain) (coins : protocol.chain.Coins) (g)
    (h : r.run σ W messages coins = some g) :
    I.layer.satisfies σ ((r.family W).witness g) :=
  r.runTranscript_valid σ W (protocol.chain.record messages coins) g h

end RecursivePolygero.Protocol.ProfileProof

namespace RecursivePolygero.Protocol.HahnProfileProof
open Finset Counting ProfileAnalysis
attribute [local instance] Classical.propDecidable
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {I : Instance F} {protocol : Protocol I} {p : HahnSystemCertificate I}

theorem extract_eq_run_of_accept (r : protocol.HahnProfileProof p) (σ : I.layer.Statement)
    (W : I.layer.Oracle) (messages : Strategy protocol.chain) (coins : protocol.chain.Coins)
    (h : executionVerify protocol.chain σ W messages coins = true) :
    r.extract σ W messages coins = r.run σ W messages coins := by
  simp [extract, extractTranscript, run, h]

theorem extract_eq_none_of_reject (r : protocol.HahnProfileProof p) (σ : I.layer.Statement)
    (W : I.layer.Oracle) (messages : Strategy protocol.chain) (coins : protocol.chain.Coins)
    (h : executionVerify protocol.chain σ W messages coins = false) :
    r.extract σ W messages coins = none := by
  simp [extract, extractTranscript, h]

theorem runTranscript_valid (r : protocol.HahnProfileProof p) (σ : I.layer.Statement) (W : I.layer.Oracle)
    (transcript : protocol.chain.Transcript) (g)
    (h : r.runTranscript σ W transcript = some g) :
    I.layer.satisfies σ ((r.family W).witness g) := by
  cases r with
  | terminal p => exact scanRecoverAt_valid I σ W _ _ g h
  | step p rest =>
    simp only [runTranscript] at h
    split at h
    · contradiction
    · exact scanRecoverAt_valid I σ W _ _ g h

theorem extractTranscript_valid (r : protocol.HahnProfileProof p) (σ : I.layer.Statement)
    (W : I.layer.Oracle) (transcript : Option protocol.chain.Transcript) (g)
    (h : r.extractTranscript σ W transcript = some g) :
    I.layer.satisfies σ ((r.family W).witness g) := by
  cases transcript with
  | none => simp [extractTranscript] at h
  | some transcript => exact r.runTranscript_valid σ W transcript g h

theorem run_valid (r : protocol.HahnProfileProof p) (σ : I.layer.Statement) (W : I.layer.Oracle)
    (messages : Strategy protocol.chain) (coins : protocol.chain.Coins) (g)
    (h : r.run σ W messages coins = some g) :
    I.layer.satisfies σ ((r.family W).witness g) :=
  r.runTranscript_valid σ W (protocol.chain.record messages coins) g h

end RecursivePolygero.Protocol.HahnProfileProof
