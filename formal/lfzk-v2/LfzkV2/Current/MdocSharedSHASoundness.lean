import LfzkV2.Current.MdocSHAExperiment

/-! Average the conditioned rate-1/7 theorem for the actual single-SHA
execution. The auxiliary SHA marginal and the transcript marginal are fixed
before sampling; the Merkle restriction uses a fresh uniform lazy tape.
The proof introduces neither an oracle-consistency hypothesis nor a new
query or soundness error. -/
noncomputable section
namespace LfzkV2.Current.MdocSharedSHASoundness
open Application ApplicationSetup Finset Merkle.RandomOracle ZeroKnowledge
open scoped Classical
set_option maxRecDepth 8192
set_option maxHeartbeats 600000

variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable (binary : ConcreteSetup.BinaryCircuit B) (prime : ConcreteSetup.PrimeCircuit)
variable (cantor : Module.Basis (Fin 128) (ZMod 2) B) (scalars : MdocRuntime.Scalars B)
variable (ids : MdocIdentifiers.Identifiers) (bounds : MdocIdentifiers.Bounds binary prime)
variable {tA calls Q : ℕ}
variable (body : MdocSetupFamily.Values → TwoOracleTree Bytes Digest Bytes
  (Digest × MdocSharedSHA.Answer binary prime cantor) (MdocSharedSHA.RawOutput binary prime bounds) tA calls)
variable (fits : (MdocRuntime.geometry binary.description prime.description binary.plan prime.plan).roles.length < 2^64)

local instance answerFintype : Fintype (MdocSharedSHA.Answer binary prime cantor) := by
  dsimp only [MdocSharedSHA.Answer,MdocRuntime.Answer,IdealRuntime.Answer,IdealSamples.Answer]
  infer_instance

local instance answerNonempty : Nonempty (MdocSharedSHA.Answer binary prime cantor) :=
  ⟨(MdocProofRate7.defaultAnswer binary prime cantor).2⟩

abbrev Experiment (auxiliary : Finset Bytes) :=
  ({raw // raw ∈ auxiliary} → Digest) ×
    ((Fin (4886+tA) → Digest) ×
      ({raw // raw ∈ MdocSharedSHA.transcriptWindow binary prime cantor scalars ids bounds body fits} →
        Digest × MdocSharedSHA.Answer binary prime cantor))

/-- `auxiliary` may contain any finite collection of SHA inputs. Only its
non-Merkle restriction is read through the complement; redundant coordinates
are harmless. Every call in the original run uses the one assembled SHA. -/
def event (auxiliary : Finset Bytes) (fallback : Bytes → Digest)
    (coin : Experiment binary prime cantor scalars ids bounds body fits auxiliary) : Prop :=
  MdocSHAExperiment.event binary prime cantor scalars ids bounds body fits
    (OracleWindow.extend auxiliary coin.1 fallback) coin.2.1
    (OracleWindow.extend (MdocSharedSHA.transcriptWindow binary prime cantor scalars ids bounds body fits)
      coin.2.2 (fun _ => MdocProofRate7.defaultAnswer binary prime cantor))

variable (bodyFits : ProofBodyBounds.bodyBound (MdocRuntime.representations scalars)
  (MdocRuntime.geometry binary.description prime.description binary.plan prime.plan) ≤ CanonicalPrefix.maxLength)

include bodyFits in
/-- For every Q>=0, the original raw prover's distinct transcript queries
pay the same leading 2Q/2^128 term. This experiment verifies through one SHA
function and uses the unchanged first-context paired extractor. Arbitrary
finite repetitions and adaptive public requests are permitted. -/
theorem ratio_le (auxiliary : Finset Bytes) (fallback : Bytes → Digest)
    (support : ∀ (SHA : Bytes → Digest)
      (HT : Bytes → Digest × MdocSharedSHA.Answer binary prime cantor),
      ((Observer.transcriptTrace (Observer.run SHA HT (body (MdocSetupFamily.values binary prime cantor scalars ids bounds SHA))).2).map Prod.fst).toFinset.card ≤ Q) :
    ((univ.filter (event binary prime cantor scalars ids bounds body fits auxiliary fallback)).card : ℚ) /
      Fintype.card (Experiment binary prime cantor scalars ids bounds body fits auxiliary) ≤
      MdocSharedSHA.bound binary prime Q tA := by
  let Aux := {raw // raw ∈ auxiliary} → Digest
  let Core := (Fin (4886+tA) → Digest) ×
    ({raw // raw ∈ MdocSharedSHA.transcriptWindow binary prime cantor scalars ids bounds body fits} →
      Digest × MdocSharedSHA.Answer binary prime cantor)
  rw [← ByteOracleTransport.ratio_equiv (Equiv.prodComm Core Aux)
    (event binary prime cantor scalars ids bounds body fits auxiliary fallback)]
  apply ByteOracleTransport.product_ratio_le
  intro table
  have law := MdocSharedSHA.conditioned_ratio_le binary prime cantor scalars ids bounds body fits bodyFits
    support (OracleWindow.extend auxiliary table fallback) (fun _ => MdocProofRate7.defaultAnswer binary prime cantor)
  change ((univ.filter fun coin : Core =>
    MdocSHAExperiment.event binary prime cantor scalars ids bounds body fits
      (OracleWindow.extend auxiliary table fallback) coin.1
      (OracleWindow.extend (MdocSharedSHA.transcriptWindow binary prime cantor scalars ids bounds body fits)
        coin.2 (fun _ => MdocProofRate7.defaultAnswer binary prime cantor))).card : ℚ) / _ ≤ _
  simp_rw [MdocSHAExperiment.event_iff]
  exact SHAProbability.changeFintype law

end LfzkV2.Current.MdocSharedSHASoundness
