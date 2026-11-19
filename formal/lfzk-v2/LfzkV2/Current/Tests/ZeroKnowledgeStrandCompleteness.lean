import LfzkV2.Current.ZeroKnowledge.StrandHonestCompletion
import LfzkV2.Current.ZeroKnowledge.StrandSamplerNonvacuity

/-! Current indexed completeness and a nondegenerate physical-reader
instance. Importing this file also places the complete new theorem graph
under the aggregate test's standard-axiom audit. -/
noncomputable section
namespace LfzkV2.Current.Tests.ZeroKnowledgeStrandCompleteness
open TranscriptV2 Merkle.RandomOracle
open ZeroKnowledge.StrandSamplerNonvacuity

#check ZeroKnowledge.StrandCanonicalBackend.respondHonest_accepts
#check ZeroKnowledge.StrandCanonicalBackend.finish_accepts

example (value : Strand.Digest) :
    ∃ stream, (readDigest.run stream).1 = some value := every_value_succeeds value

example (value : Strand.Digest) :
    (Finset.univ.filter fun stream => (readDigest.run stream).1 = some value).card =
      Fintype.card residual := balanced value

example : 0 < Fintype.card residual := positive_fiber

example : ∃ first second : Strand.Word → Strand.Digest,
    (readDigest.run first).1 ≠ (readDigest.run second).1 := two_different_successes

example (stream : Strand.Word → Strand.Digest) :
    (readDigest.run stream).2 = [(0,stream 0)] := rfl

example {Point : Type} (history : Point → Strand.History) (SHA : Strand.Oracle) (point : Point) :
    TranscriptV2.StrandVerifier.sampled history (fun _ => readDigest) SHA point :=
  sampled history SHA point

end LfzkV2.Current.Tests.ZeroKnowledgeStrandCompleteness
