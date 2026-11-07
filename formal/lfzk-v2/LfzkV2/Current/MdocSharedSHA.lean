import LfzkV2.Current.SHALazy
import LfzkV2.Current.SHAProbability
import LfzkV2.Current.ZeroKnowledge.MdocSetupFamily

/-! The rate-1/7 soundness experiment with one SHA function. Its Merkle
restriction is sampled lazily; all other SHA coordinates are an independently
sampled finite marginal. Setup and causal identifiers use that very same
function. The complement is fixed only inside the proof, then averaged.
No independence of an observed adaptive trace is assumed. -/
noncomputable section
namespace LfzkV2.Current.MdocSharedSHA
open Application ApplicationSetup Finset Merkle.RandomOracle
open Merkle.RandomOracle.TwoOracleTree ZeroKnowledge
open scoped Classical
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable (binary : ConcreteSetup.BinaryCircuit B) (prime : ConcreteSetup.PrimeCircuit)
variable (cantor : Module.Basis (Fin 128) (ZMod 2) B) (scalars : MdocRuntime.Scalars B)
variable (ids : MdocIdentifiers.Identifiers) (bounds : MdocIdentifiers.Bounds binary prime)

abbrev Answer := MdocRuntime.Answer binary.description prime.description binary.plan prime.plan
  (ConcreteSetup.binaryNodes cantor)

abbrev RawOutput := MdocProofRate7.RawOutput binary prime bounds

variable {tA calls Q : ℕ}
variable (body : MdocSetupFamily.Values → TwoOracleTree Bytes Digest Bytes
  (Digest × MdocRuntime.Answer binary.description prime.description binary.plan prime.plan
    (ConcreteSetup.binaryNodes cantor)) (MdocProofRate7.RawOutput binary prime bounds) tA calls)
variable (fits : (MdocRuntime.geometry binary.description prime.description binary.plan prime.plan).roles.length < 2^64)

def routed (outside : Bytes → Digest) :=
  SHAOracle.route SHAOracle.merkleDomain outside
    (body (MdocSetupFamily.values binary prime cantor scalars ids bounds outside))

/-- Chosen from all public digest values and all program branches before
either oracle is sampled. Extra coordinates carry no query charge. -/
def transcriptWindow : Finset Bytes :=
  univ.biUnion fun visible =>
    (MdocSetupFamily.codec binary prime cantor scalars ids bounds fits visible).window (body visible)

theorem window_subset (outside : Bytes → Digest) :
    MdocProofRate7.window binary prime cantor scalars (MdocPublicSetup.identifiers ids outside) bounds
      (routed binary prime cantor scalars ids bounds body outside) fits ⊆
      transcriptWindow binary prime cantor scalars ids bounds body fits := by
  let visible := MdocSetupFamily.values binary prime cantor scalars ids bounds outside
  change (MdocSetupFamily.codec binary prime cantor scalars ids bounds fits visible).window
    (SHAOracle.route SHAOracle.merkleDomain outside (body visible)) ⊆ _
  intro raw member
  apply mem_biUnion.mpr
  refine ⟨visible,mem_univ _,?_⟩
  rcases mem_union.mp member with member | member
  · exact mem_union_left _ (SHARouting.queries_subset SHAOracle.merkleDomain outside (body visible) member)
  · exact mem_union_right _ member

omit [Fintype B] [DecidableEq B] in
/-- The hypothesis bounds the ORIGINAL program on total SHA/transcript
functions. Routing never gives the reduction a new transcript-query budget. -/
theorem query_budget
    (support : ∀ (SHA : Bytes → Digest) (HT : Bytes → Digest × Answer binary prime cantor),
      ((Observer.transcriptTrace (Observer.run SHA HT (body (MdocSetupFamily.values binary prime cantor scalars ids bounds SHA))).2).map Prod.fst).toFinset.card ≤ Q)
    (outside : Bytes → Digest) (tape : Fin (4886+tA) → Digest)
    (HT : Bytes → Digest × Answer binary prime cantor) :
    (TranscriptV2.seen
      (fixLeft tape default (routed binary prime cantor scalars ids bounds body outside) []) HT).card ≤ Q := by
  have same := SHALazy.transcript_run HT tape
    (routed binary prime cantor scalars ids bounds body outside)
  unfold routed at same
  rw [SHARouting.transcript_run] at same
  change (((fixLeft tape default (routed binary prime cantor scalars ids bounds body outside) []).run HT).2.map Prod.fst).toFinset.card ≤ Q
  unfold routed
  rw [← same]
  have actual := support (SHAOracle.merge SHAOracle.merkleDomain outside
    (SHALazy.oracle HT tape (routed binary prime cantor scalars ids bounds body outside))) HT
  simpa only [MdocSetupFamily.values_merge,routed] using actual

def bound (Q tA : ℕ) : ℚ :=
  2*Q/(Adapter.Mdoc.binaryOrder : ℚ) +
    ((4*Q+1+tA*(tA-1)/2+
      (4886+tA)*(2*tA+(MdocRuntime.geometry binary.description prime.description binary.plan prime.plan).roles.length+Q+2) : ℕ) : ℚ) /
      (Adapter.Mdoc.binaryOrder : ℚ)^2

variable (bodyFits : ProofBodyBounds.bodyBound (MdocRuntime.representations scalars)
  (MdocRuntime.geometry binary.description prime.description binary.plan prime.plan) ≤ CanonicalPrefix.maxLength)

include bodyFits in
theorem conditioned_ratio_le
    (support : ∀ (SHA : Bytes → Digest) (HT : Bytes → Digest × Answer binary prime cantor),
      ((Observer.transcriptTrace (Observer.run SHA HT (body (MdocSetupFamily.values binary prime cantor scalars ids bounds SHA))).2).map Prod.fst).toFinset.card ≤ Q)
    (outside : Bytes → Digest) (fallback : Bytes → Digest × Answer binary prime cantor) :
    ((univ.filter fun coin : (Fin (4886+tA) → Digest) ×
        ({raw // raw ∈ transcriptWindow binary prime cantor scalars ids bounds body fits} → Digest × Answer binary prime cantor) =>
      MdocProofRate7.rawEvent binary prime cantor scalars (MdocPublicSetup.identifiers ids outside) bounds
        (routed binary prime cantor scalars ids bounds body outside) fits coin.1
        (OracleWindow.extend (transcriptWindow binary prime cantor scalars ids bounds body fits) coin.2 fallback)).card : ℚ) /
      Fintype.card ((Fin (4886+tA) → Digest) ×
        ({raw // raw ∈ transcriptWindow binary prime cantor scalars ids bounds body fits} → Digest × Answer binary prime cantor)) ≤
      bound binary prime Q tA := by
  apply SHAProbability.window_ratio_le
    (MdocProofRate7.window binary prime cantor scalars (MdocPublicSetup.identifiers ids outside) bounds
      (routed binary prime cantor scalars ids bounds body outside) fits)
    _ (window_subset binary prime cantor scalars ids bounds body fits outside) fallback
  intro complement
  exact MdocProofRate7.window_ratio_le binary prime cantor scalars (MdocPublicSetup.identifiers ids outside) bounds
    (routed binary prime cantor scalars ids bounds body outside) fits bodyFits complement
    (query_budget binary prime cantor scalars ids bounds body support outside)

end LfzkV2.Current.MdocSharedSHA
