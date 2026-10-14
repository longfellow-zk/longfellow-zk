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
