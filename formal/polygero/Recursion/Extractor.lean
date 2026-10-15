import polygero.Recursion.Certificate
import polygero.Recursion.Transcript
import polygero.Local.Decoder

/-! The transcript-assisted recursive extractor; this module contains no probability bound. -/

namespace RecursivePolygero.Protocol.ProfileProof
open Finset Counting ProfileAnalysis
attribute [local instance] Classical.propDecidable
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {I : Instance F} {protocol : Protocol I} {p : ProfileCertificate I}

noncomputable def family (_r : protocol.ProfileProof p) (_W : I.layer.Oracle) :=
  tupleCounts I

/-- The extractor reads one transcript and invokes only the concrete local decoder. -/
noncomputable def runTranscript {I : Instance F} {protocol : Protocol I} {p : ProfileCertificate I} (r : protocol.ProfileProof p) :
    ∀ (_σ : I.layer.Statement) (W : I.layer.Oracle), protocol.chain.Transcript →
      Option (r.family W).Index :=
  match r with
  | .terminal p => fun σ W transcript =>
      scanRecoverAt I σ W transcript.1 transcript.2.2
  | @step _ _ _ child tail p _ rest => fun σ W transcript =>
      match rest.runTranscript (child.link.statement σ W transcript.1 transcript.2.1)
          transcript.2.2.1 transcript.2.2.2 with
      | none => none
      | some g => scanRecoverAt I σ W transcript.1
          (child.link.decode ((rest.family transcript.2.2.1).witness g))

noncomputable def run (r : protocol.ProfileProof p) (σ : I.layer.Statement) (W : I.layer.Oracle)
    (messages : Strategy protocol.chain) (coins : protocol.chain.Coins) :
    Option (r.family W).Index :=
  r.runTranscript σ W (protocol.chain.record messages coins)

/-- Rejected executions supply `none`; an accepted execution supplies its complete transcript.
No padded child oracle or response is needed to return failure on rejection. -/
noncomputable def extractTranscript (r : protocol.ProfileProof p) (σ : I.layer.Statement)
    (W : I.layer.Oracle) (transcript : Option protocol.chain.Transcript) :
    Option (r.family W).Index := transcript.bind (r.runTranscript σ W)

/-- The actual extractor rejects first and otherwise scans the recorded transcript. -/
noncomputable def extract (r : protocol.ProfileProof p) (σ : I.layer.Statement)
    (W : I.layer.Oracle) (messages : Strategy protocol.chain) (coins : protocol.chain.Coins) :
    Option (r.family W).Index :=
  r.extractTranscript σ W (if executionVerify protocol.chain σ W messages coins then
    some (protocol.chain.record messages coins) else none)

end RecursivePolygero.Protocol.ProfileProof

namespace RecursivePolygero.Protocol.HahnProfileProof
open Finset Counting ProfileAnalysis
attribute [local instance] Classical.propDecidable
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {I : Instance F} {protocol : Protocol I} {p : HahnSystemCertificate I}

noncomputable def family (_r : protocol.HahnProfileProof p) (_W : I.layer.Oracle) :=
  tupleCounts I

/-- The extractor reads one transcript and invokes only the concrete local decoder. -/
noncomputable def runTranscript {I : Instance F} {protocol : Protocol I}
    {p : HahnSystemCertificate I} (r : protocol.HahnProfileProof p) :
    ∀ (_σ : I.layer.Statement) (W : I.layer.Oracle), protocol.chain.Transcript →
      Option (r.family W).Index :=
  match r with
  | .terminal _ => fun σ W transcript =>
      scanRecoverAt I σ W transcript.1 transcript.2.2
  | @step _ _ _ child _ _ _ rest => fun σ W transcript =>
      match rest.runTranscript (child.link.statement σ W transcript.1 transcript.2.1)
          transcript.2.2.1 transcript.2.2.2 with
      | none => none
      | some g => scanRecoverAt I σ W transcript.1
          (child.link.decode ((rest.family transcript.2.2.1).witness g))

noncomputable def run (r : protocol.HahnProfileProof p) (σ : I.layer.Statement) (W : I.layer.Oracle)
    (messages : Strategy protocol.chain) (coins : protocol.chain.Coins) :
    Option (r.family W).Index :=
  r.runTranscript σ W (protocol.chain.record messages coins)

noncomputable def extractTranscript (r : protocol.HahnProfileProof p) (σ : I.layer.Statement)
    (W : I.layer.Oracle) (transcript : Option protocol.chain.Transcript) :
    Option (r.family W).Index := transcript.bind (r.runTranscript σ W)

noncomputable def extract (r : protocol.HahnProfileProof p) (σ : I.layer.Statement)
    (W : I.layer.Oracle) (messages : Strategy protocol.chain) (coins : protocol.chain.Coins) :
    Option (r.family W).Index :=
  r.extractTranscript σ W (if executionVerify protocol.chain σ W messages coins then
    some (protocol.chain.record messages coins) else none)

end RecursivePolygero.Protocol.HahnProfileProof

namespace RecursivePolygero.Protocol.ProfileProof
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {I : Instance F} {protocol : Protocol I} {p : ProfileCertificate I}

/-- Converting the numerical certificate preserves the transcript extractor. -/
theorem toHahnProfileProof_runTranscript (r : protocol.ProfileProof p) :
    ∀ (σ : I.layer.Statement) (W : I.layer.Oracle) (transcript : protocol.chain.Transcript),
      r.toHahnProfileProof.runTranscript σ W transcript = r.runTranscript σ W transcript := by
  induction r with
  | terminal p => intros; rfl
  | step p rest ih =>
    intro σ W transcript
    simp only [toHahnProfileProof, HahnProfileProof.runTranscript, runTranscript,
      HahnProfileProof.family, family]
    rw [ih]
    split <;> simp_all

theorem toHahnProfileProof_run (r : protocol.ProfileProof p)
    (σ : I.layer.Statement) (W : I.layer.Oracle)
    (messages : Strategy protocol.chain) (coins : protocol.chain.Coins) :
    r.toHahnProfileProof.run σ W messages coins = r.run σ W messages coins :=
  r.toHahnProfileProof_runTranscript σ W _

theorem toHahnProfileProof_extractTranscript (r : protocol.ProfileProof p)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (transcript : Option protocol.chain.Transcript) :
    r.toHahnProfileProof.extractTranscript σ W transcript = r.extractTranscript σ W transcript := by
  cases transcript with
  | none => rfl
  | some t => exact r.toHahnProfileProof_runTranscript σ W t

theorem toHahnProfileProof_extract (r : protocol.ProfileProof p)
    (σ : I.layer.Statement) (W : I.layer.Oracle)
    (messages : Strategy protocol.chain) (coins : protocol.chain.Coins) :
    r.toHahnProfileProof.extract σ W messages coins = r.extract σ W messages coins :=
  r.toHahnProfileProof_extractTranscript σ W _

end RecursivePolygero.Protocol.ProfileProof
