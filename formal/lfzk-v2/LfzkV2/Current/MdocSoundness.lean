import LfzkV2.Current.Mdoc.Setup
import LfzkV2.Current.MdocStrandOracle
import LfzkV2.Current.MdocWitnessRequest

/-! Application soundness for the numbered-strand verifier: extraction at the
original commitment cut yields the ordinary hash witness and signature-circuit
witness at the actual request. Sampling, scalar representations and trusted
circuit semantics retain their explicit interfaces.

The original query budget `Q` counts distinct byte queries in the worst case,
for every adversarial coin and total oracle. Averaging uses a finite coin that
may jointly determine the complementary setup slice and adversarial choices;
only the remaining fresh protocol-domain oracle is independent of that coin.
See `MdocStrandOracle` for the conditioning and filtered-trace identities. -/
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
namespace LfzkV2.Current.MdocSoundness
open Application ApplicationSetup RuntimeAdaptive Bcs.FiniteProbability Merkle.RandomOracle TranscriptV2
open scoped Classical

variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable (binary : ConcreteSetup.BinaryCircuit B) (prime : ConcreteSetup.PrimeCircuit)
variable (cantor : Module.Basis (Fin 128) (ZMod 2) B) (scalars : MdocRuntime.Scalars B)
variable (ids : MdocIdentifiers.Identifiers) (bounds : MdocIdentifiers.Bounds binary prime)
variable (outside : Bytes → Digest)
local notation "currentIds" => MdocStrandOracle.identifiers ids outside
local notation "E" => Mdoc.Setup.protocol binary prime cantor scalars currentIds bounds
local notation "c" => FixedRate.Rate7.certificate
local notation "bp" => binary.description
local notation "pp" => prime.description
local notation "nodes" => ConcreteSetup.binaryNodes cantor
local notation "P" => MdocRuntime.binaryBackend bp nodes
local notation "R" => MdocRuntime.primeBackend pp
local notation "g" => MdocRuntime.geometry bp pp binary.plan prime.plan
local notation "repr" => MdocRuntime.representations scalars
local notation "shape" => MdocRuntime.shape bp pp binary.plan prime.plan bounds.inputFits bounds.privateFits (by change 128 < 2^64; decide)
local notation "setup" => MdocIdentifiers.setup binary prime cantor scalars currentIds bounds
local notation "cfg" => MdocRuntime.configuration bp pp binary.plan prime.plan nodes scalars
  bounds.inputFits bounds.privateFits (by change 128 < 2^64; decide) setup (MdocRuntime.field_card binary.basis)
  (MdocRuntime.polynomialX binary.basis)
local notation "Answer" => MdocRuntime.Answer bp pp binary.plan prime.plan nodes
local notation "cb" => Geometry.affineRows g Side.binary
local notation "cp" => Geometry.affineRows g Side.prime
local notation "bc" => MdocRuntime.binaryCapacity bp binary.plan
local notation "pc" => MdocRuntime.primeCapacity pp prime.plan
local notation "params" => MdocIdentifiers.parameters binary prime cantor scalars currentIds bounds
local notation "metadata" => ConcreteMetadata.metadata (Advice := MdocAdvice.Value) (C := Answer)
  bp pp shape params setup
local notation "bf" => Nat.le_max_right (BinaryPublic.degree bp) binary.plan.capacity
local notation "primeFits" => Nat.le_max_right ((Layered.Circuit.layers (PrimePublic.circuit pp))+1) prime.plan.capacity
local notation "df" => Nat.le_max_left (BinaryPublic.degree bp) binary.plan.capacity
local notation "rf" => Nat.le_max_left ((Layered.Circuit.layers (PrimePublic.circuit pp))+1) prime.plan.capacity
local notation "Point" => QueryRuntime.Runtime.Point repr shape setup (BinaryPublic.nPublic bp)
local notation "Values" => Protocol.Sampling.values c bp pp P R cb cp bc pc repr shape setup
local notation "First" => FieldBackend.participant (FieldBackend.indexed P cb)
local notation "Second" => FieldBackend.participant (FieldBackend.indexed R cp)

local instance : Algebra (ZMod 2) (FieldBackend.participant
    (FieldBackend.indexed (MdocRuntime.binaryBackend binary.description (ConcreteSetup.binaryNodes cantor))
      ((MdocRuntime.geometry binary.description prime.description binary.plan prime.plan).affineRows .binary))).Carrier :=
  inferInstanceAs (Algebra (ZMod 2) B)

private instance saltInhabited : Inhabited (Fin (c).n × MerkleNonce) :=
  ⟨⟨⟨0,by decide⟩,fun _ => 0⟩⟩

private instance familyLeafInhabited {k s n t : ℕ} (family : Joint.Family k s n t) : Inhabited family.Leaf :=
  ⟨fun _ => ⟨⟨fun _ _ => 0,fun _ => 0⟩,0⟩⟩


local notation "I" => IdealRuntime.challengePublic bp pp P R cb cp bc pc cfg
local notation "W" => CanonicalRuntime.wirePublic bp pp P R repr shape setup I
local notation "earlier" => CanonicalRuntime.earlier bp pp P R repr shape setup I rfl metadata
local notation "decodePublic" => CanonicalRuntime.decodePrimePublic bp pp P R repr shape setup I rfl
local notation "draw" => IdealRuntime.draw bp pp P R cb cp bc pc cfg
local notation "codec" => MerkleWireCodec.codec First Second repr
  (RuntimeVerifier.Public.binaryField cfg) (RuntimeVerifier.Public.primeField cfg)
  (FingerprintPrefix.Setup.jointContext setup) (by decide)
local notation "Output" => CanonicalRuntime.Output (Advice := MdocAdvice.Value) bp shape
local notation "Witness" => Selection.Pair B (ZMod Adapter.Mdoc.primeOrder)
  (BinaryPublic.Original bp) (PrimePublic.Original pp)

/-- Both circuits use the request's public values and the same selected
private witness; ordinary hash truth is independent of adapter challenges. -/
def Valid (request : MdocStrandSoundness.Request binary prime bounds) (w : Witness) : Prop :=
  MdocWitness.Valid binary prime request.publicBits request.primeInputs w

theorem decoded_valid (separated : MdocWitness.ReadDisjoint binary)
    (output : Output) (H : Point → Digest × Answer)
    (decoded : RuntimeVerifier.Decoded bp pp P R W)
    (found : RuntimeAdaptiveVerifier.decode bp pp P R W earlier
      (CanonicalRequest.hashPublic (BinaryPublic.nPublic bp)) decodePublic draw output H = some decoded)
    (w : Witness) (truth : decoded.application.True w) : Valid binary prime bounds output.request w := by
  exact MdocWitness.valid_at_request binary prime P R repr shape setup I rfl rfl metadata draw
    separated output H decoded found w truth

variable {fuel blocks Q : ℕ}
variable (body : Tree Bytes Digest (MdocStrandSoundness.Request binary prime bounds × Bytes) fuel)
variable (fits : (MdocRuntime.geometry binary.description prime.description binary.plan prime.plan).roles.length < 2^64)
variable (sample : (point : MdocStrandSoundness.RoundPoint binary prime cantor scalars
    (MdocStrandOracle.identifiers ids outside) bounds) →
  Tree Strand.Word Digest (Option (MdocStrandSoundness.RoundValue binary prime cantor scalars
    (MdocStrandOracle.identifiers ids outside) bounds point)) blocks)
local notation "physical" => Protocol.Sampling.sampler c bp pp P R cb cp bc pc repr shape setup
  binary.plan prime.plan rfl rfl bf primeFits df rf cfg sample
local notation "Raw" => MdocStrandOracle.Raw binary prime cantor scalars ids bounds body outside fits sample
local notation "view" G => MdocStrandOracle.observation binary prime cantor scalars ids bounds body outside fits sample G
local notation "SHA" G => MdocStrandOracle.sha binary prime cantor scalars ids bounds body outside fits sample G
local notation "decodedView" => StrandExecution.decoded bp pp P R W earlier (ProofBodyCodec.codec repr g)
  physical (CanonicalRequest.hashPublic (BinaryPublic.nPublic bp)) decodePublic draw
local notation "authentication" => StrandProtocol.viewAuthentication E

/-- The existing first-commitment-cut extractor, with the decoded system
used only to recover its authenticated statement and challenges. -/
def extract (G : Raw → Digest) : Option Witness :=
  (decodedView (view G)).bind fun decoded => (authentication (view G) decoded).context.extract

/-- Actual verifier acceptance, including parsing, tuple openings, and the
final seal, with extraction failing to produce an application-valid witness. -/
def event (G : Raw → Digest) : Prop :=
  (ProofOutput.read («g» := g) repr (body.run (SHA G)).1.2).isSome ∧
  MdocStrandSoundness.verify binary prime cantor scalars currentIds bounds sample
    (SHA G) (view G).original.1 = true ∧
  ¬ ∃ w, extract binary prime cantor scalars ids bounds outside body fits sample G = some w ∧
    Valid binary prime bounds (view G).original.1.request w

theorem event_implies_extraction_failure (separated : MdocWitness.ReadDisjoint binary)
    (G : Raw → Digest) (bad : event binary prime cantor scalars ids bounds outside body fits sample G) :
    MdocStrandOracle.event binary prime cantor scalars ids bounds body outside fits sample G := by
  have replayed := MdocStrandOracle.verifier_actual binary prime cantor scalars ids bounds body outside fits sample G
  have decoding := StrandExecution.decoded_of_trace bp pp P R W earlier (ProofBodyCodec.codec repr g)
    physical codec id (CanonicalRequest.hashPublic (BinaryPublic.nPublic bp)) decodePublic draw
    (view G) (SHA G) (congrArg Prod.snd replayed)
  obtain ⟨decoded,found,_⟩ := (StrandVerifier.verify_true_iff bp pp P R W earlier (ProofBodyCodec.codec repr g)
    physical (CanonicalRequest.hashPublic (BinaryPublic.nPublic bp)) decodePublic draw codec
    (SHA G) id (view G).original.1).mp bad.2.1
  have foundView : decodedView (view G) = some decoded := decoding.trans found
  have decision := StrandExecution.decision_of_trace bp pp P R W earlier (ProofBodyCodec.codec repr g)
    physical codec id (CanonicalRequest.hashPublic (BinaryPublic.nPublic bp)) decodePublic draw
    (view G) (SHA G) (congrArg Prod.snd replayed)
  refine ⟨bad.1,decision.trans bad.2.1,decoded,foundView,?_⟩
  rintro ⟨w,extracted,truth⟩
  apply bad.2.2
  refine ⟨w,?_,decoded_valid binary prime cantor scalars ids bounds outside separated
    (view G).original.1 _ decoded found w truth⟩
  simp only [extract,foundView,Option.bind_some]
  exact extracted

variable (bodyFits : ProofBodyBounds.bodyBound (MdocRuntime.representations scalars)
  (MdocRuntime.geometry binary.description prime.description binary.plan prime.plan) ≤ CanonicalPrefix.maxLength)
variable (fiber : MdocStrandSoundness.RoundPoint binary prime cantor scalars
  (MdocStrandOracle.identifiers ids outside) bounds → ℕ)
variable (uniform : ∀ point value,
  (Finset.univ.filter fun stream => ((sample point).run stream).1 = some value).card = fiber point)
variable (queries : ∀ oracle : Bytes → Digest, (seen body oracle).card ≤ Q)

include bodyFits uniform queries in
theorem ratio_le (separated : MdocWitness.ReadDisjoint binary) (budget : Q < 2^127) :
    density (event binary prime cantor scalars ids bounds outside body fits sample) ≤
      LfzkV2.Current.Soundness.Rate7.failureBound Q (g).roles.length :=
  (density_mono (fun G bad => event_implies_extraction_failure binary prime cantor scalars ids bounds outside
    body fits sample separated G bad)).trans
    (MdocStrandOracle.ratio_le binary prime cantor scalars ids bounds body outside queries fits sample
      fiber uniform bodyFits budget)

include bodyFits uniform queries in
theorem linear_ratio_le (separated : MdocWitness.ReadDisjoint binary) :
    density (event binary prime cantor scalars ids bounds outside body fits sample) ≤
      LfzkV2.Current.Soundness.Rate7.rate*Q + LfzkV2.Current.Soundness.Rate7.correction Q (g).roles.length :=
  (density_mono (fun G bad => event_implies_extraction_failure binary prime cantor scalars ids bounds outside
    body fits sample separated G bad)).trans
    (MdocStrandOracle.linear_ratio_le binary prime cantor scalars ids bounds body outside queries fits sample
      fiber uniform bodyFits)



private theorem averaged_event_le {Omega : Type} [Fintype Omega] [Nonempty Omega]
    (separated : MdocWitness.ReadDisjoint binary)
    (external : Omega → Bytes → Digest)
    (adversary : Omega → Tree Bytes Digest (MdocStrandSoundness.Request binary prime bounds × Bytes) fuel)
    (sampler : (coin : Omega) →
      (point : MdocStrandSoundness.RoundPoint binary prime cantor scalars (MdocStrandOracle.identifiers ids (external coin)) bounds) →
      Tree Strand.Word Digest
        (Option (MdocStrandSoundness.RoundValue binary prime cantor scalars (MdocStrandOracle.identifiers ids (external coin)) bounds point)) blocks)
 :
      (∑ coin, density (event binary prime cantor scalars ids bounds (external coin) (adversary coin) fits (sampler coin))) /
        Fintype.card Omega ≤
      (∑ coin, density (MdocStrandOracle.event binary prime cantor scalars ids bounds (adversary coin) (external coin) fits (sampler coin))) /
        Fintype.card Omega := by
  apply div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro coin _
  exact density_mono (fun G bad => event_implies_extraction_failure binary prime cantor scalars ids bounds
    (external coin) (adversary coin) fits (sampler coin) separated G bad)

include bodyFits in
theorem averaged_linear_ratio_le {Omega : Type} [Fintype Omega] [Nonempty Omega]
    (separated : MdocWitness.ReadDisjoint binary)
    (external : Omega → Bytes → Digest)
    (adversary : Omega → Tree Bytes Digest (MdocStrandSoundness.Request binary prime bounds × Bytes) fuel)
    (sampler : (coin : Omega) →
      (point : MdocStrandSoundness.RoundPoint binary prime cantor scalars (MdocStrandOracle.identifiers ids (external coin)) bounds) →
      Tree Strand.Word Digest
        (Option (MdocStrandSoundness.RoundValue binary prime cantor scalars (MdocStrandOracle.identifiers ids (external coin)) bounds point)) blocks)
    (sampleFiber : (coin : Omega) →
      MdocStrandSoundness.RoundPoint binary prime cantor scalars (MdocStrandOracle.identifiers ids (external coin)) bounds → ℕ)
    (balanced : ∀ coin point value,
      (Finset.univ.filter fun stream => ((sampler coin point).run stream).1 = some value).card = sampleFiber coin point)
    (queryBound : ∀ coin oracle, (seen (adversary coin) oracle).card ≤ Q) :
    (∑ coin, density (event binary prime cantor scalars ids bounds (external coin) (adversary coin) fits (sampler coin))) /
        Fintype.card Omega ≤
      LfzkV2.Current.Soundness.Rate7.rate*Q + LfzkV2.Current.Soundness.Rate7.correction Q
        (MdocRuntime.geometry binary.description prime.description binary.plan prime.plan).roles.length := by
  have comparison := averaged_event_le binary prime cantor scalars ids bounds
    (fits := fits) separated external adversary sampler
  exact comparison.trans (MdocStrandOracle.averaged_linear_ratio_le binary prime cantor scalars ids bounds
    (fits := fits) (bodyFits := bodyFits) external adversary sampler sampleFiber balanced queryBound)

include bodyFits in
theorem averaged_ratio_le {Omega : Type} [Fintype Omega] [Nonempty Omega]
    (separated : MdocWitness.ReadDisjoint binary)
    (external : Omega → Bytes → Digest)
    (adversary : Omega → Tree Bytes Digest (MdocStrandSoundness.Request binary prime bounds × Bytes) fuel)
    (sampler : (coin : Omega) →
      (point : MdocStrandSoundness.RoundPoint binary prime cantor scalars (MdocStrandOracle.identifiers ids (external coin)) bounds) →
      Tree Strand.Word Digest
        (Option (MdocStrandSoundness.RoundValue binary prime cantor scalars (MdocStrandOracle.identifiers ids (external coin)) bounds point)) blocks)
    (sampleFiber : (coin : Omega) →
      MdocStrandSoundness.RoundPoint binary prime cantor scalars (MdocStrandOracle.identifiers ids (external coin)) bounds → ℕ)
    (balanced : ∀ coin point value,
      (Finset.univ.filter fun stream => ((sampler coin point).run stream).1 = some value).card = sampleFiber coin point)
    (queryBound : ∀ coin oracle, (seen (adversary coin) oracle).card ≤ Q) (budget : Q < 2^127) :
    (∑ coin, density (event binary prime cantor scalars ids bounds (external coin) (adversary coin) fits (sampler coin))) /
        Fintype.card Omega ≤
      LfzkV2.Current.Soundness.Rate7.failureBound Q
        (MdocRuntime.geometry binary.description prime.description binary.plan prime.plan).roles.length := by
  have comparison := averaged_event_le binary prime cantor scalars ids bounds
    (fits := fits) separated external adversary sampler
  exact comparison.trans (MdocStrandOracle.averaged_ratio_le binary prime cantor scalars ids bounds
    (fits := fits) (bodyFits := bodyFits) external adversary sampler sampleFiber balanced queryBound budget)

include bodyFits in
theorem averaged_nonvacuous {Omega : Type} [Fintype Omega] [Nonempty Omega]
    (separated : MdocWitness.ReadDisjoint binary)
    (external : Omega → Bytes → Digest)
    (adversary : Omega → Tree Bytes Digest (MdocStrandSoundness.Request binary prime bounds × Bytes) fuel)
    (sampler : (coin : Omega) →
      (point : MdocStrandSoundness.RoundPoint binary prime cantor scalars (MdocStrandOracle.identifiers ids (external coin)) bounds) →
      Tree Strand.Word Digest
        (Option (MdocStrandSoundness.RoundValue binary prime cantor scalars (MdocStrandOracle.identifiers ids (external coin)) bounds point)) blocks)
    (sampleFiber : (coin : Omega) →
      MdocStrandSoundness.RoundPoint binary prime cantor scalars (MdocStrandOracle.identifiers ids (external coin)) bounds → ℕ)
    (balanced : ∀ coin point value,
      (Finset.univ.filter fun stream => ((sampler coin point).run stream).1 = some value).card = sampleFiber coin point)
    (queryBound : ∀ coin oracle, (seen (adversary coin) oracle).card ≤ Q) (budget : Q < 2^127) :
    (∑ coin, density (event binary prime cantor scalars ids bounds (external coin) (adversary coin) fits (sampler coin))) /
        Fintype.card Omega < 97/100 := by
  have comparison := averaged_event_le binary prime cantor scalars ids bounds
    (fits := fits) separated external adversary sampler
  exact comparison.trans_lt (MdocStrandOracle.averaged_nonvacuous binary prime cantor scalars ids bounds
    (fits := fits) (bodyFits := bodyFits) external adversary sampler sampleFiber balanced queryBound budget)

include bodyFits in
theorem averaged_polynomial_ratio_le {Omega : Type} [Fintype Omega] [Nonempty Omega]
    (separated : MdocWitness.ReadDisjoint binary)
    (external : Omega → Bytes → Digest)
    (adversary : Omega → Tree Bytes Digest (MdocStrandSoundness.Request binary prime bounds × Bytes) fuel)
    (sampler : (coin : Omega) →
      (point : MdocStrandSoundness.RoundPoint binary prime cantor scalars (MdocStrandOracle.identifiers ids (external coin)) bounds) →
      Tree Strand.Word Digest
        (Option (MdocStrandSoundness.RoundValue binary prime cantor scalars (MdocStrandOracle.identifiers ids (external coin)) bounds point)) blocks)
    (sampleFiber : (coin : Omega) →
      MdocStrandSoundness.RoundPoint binary prime cantor scalars (MdocStrandOracle.identifiers ids (external coin)) bounds → ℕ)
    (balanced : ∀ coin point value,
      (Finset.univ.filter fun stream => ((sampler coin point).run stream).1 = some value).card = sampleFiber coin point)
    (queryBound : ∀ coin oracle, (seen (adversary coin) oracle).card ≤ Q) :
    (∑ coin, density (event binary prime cantor scalars ids bounds (external coin) (adversary coin) fits (sampler coin))) /
        Fintype.card Omega ≤
      2*Q*(2 : ℚ)^(-128 : ℤ) +
        (2*(Q : ℚ)^2/(1-(2 : ℚ)^(-128 : ℤ)) +
          (MdocRuntime.geometry binary.description prime.description binary.plan prime.plan).roles.length + 15) *
            (2 : ℚ)^(-256 : ℤ) := by
  have comparison := averaged_event_le binary prime cantor scalars ids bounds
    (fits := fits) separated external adversary sampler
  exact comparison.trans (MdocStrandOracle.averaged_polynomial_ratio_le binary prime cantor scalars ids bounds
    (fits := fits) (bodyFits := bodyFits) external adversary sampler sampleFiber balanced queryBound)

include bodyFits in
theorem averaged_mdoc_approximation {Omega : Type} [Fintype Omega] [Nonempty Omega]
    (separated : MdocWitness.ReadDisjoint binary)
    (external : Omega → Bytes → Digest)
    (adversary : Omega → Tree Bytes Digest (MdocStrandSoundness.Request binary prime bounds × Bytes) fuel)
    (sampler : (coin : Omega) →
      (point : MdocStrandSoundness.RoundPoint binary prime cantor scalars (MdocStrandOracle.identifiers ids (external coin)) bounds) →
      Tree Strand.Word Digest
        (Option (MdocStrandSoundness.RoundValue binary prime cantor scalars (MdocStrandOracle.identifiers ids (external coin)) bounds point)) blocks)
    (sampleFiber : (coin : Omega) →
      MdocStrandSoundness.RoundPoint binary prime cantor scalars (MdocStrandOracle.identifiers ids (external coin)) bounds → ℕ)
    (balanced : ∀ coin point value,
      (Finset.univ.filter fun stream => ((sampler coin point).run stream).1 = some value).card = sampleFiber coin point)
    (queryBound : ∀ coin oracle, (seen (adversary coin) oracle).card ≤ Q)
    (supported : MdocRoundShape.Supported (MdocRuntime.geometry binary.description prime.description binary.plan prime.plan)) :
    (∑ coin, density (event binary prime cantor scalars ids bounds (external coin) (adversary coin) fits (sampler coin))) /
        Fintype.card Omega ≤
      (Q : ℚ)/2^127 + (Q : ℚ)^2/2^257 + 1/2^246 := by
  have comparison := averaged_event_le binary prime cantor scalars ids bounds
    (fits := fits) separated external adversary sampler
  exact comparison.trans (MdocStrandOracle.averaged_mdoc_approximation binary prime cantor scalars ids bounds
    (fits := fits) (bodyFits := bodyFits) external adversary sampler sampleFiber balanced queryBound supported)

end LfzkV2.Current.MdocSoundness
