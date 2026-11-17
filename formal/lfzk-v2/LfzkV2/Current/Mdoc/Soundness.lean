import LfzkV2.Current.Mdoc.Setup
import LfzkV2.Current.Mdoc.OracleSoundness
import LfzkV2.Current.MdocWitnessRequest
import LfzkV2.Current.Protocol.Sampling

/-! Application soundness for the numbered-strand verifier: extraction at the
original commitment cut yields the ordinary hash witness and signature-circuit
witness at the actual request. Sampling, scalar representations and trusted
circuit semantics retain their explicit interfaces.

The extractor `extract` is straight-line. It is a function of the public
statement setup, the request and proof bytes the adversary submits, and the
adversary's own query log; it takes no oracle. From the protocol-domain
entries of the log, in query order, it reads the commitment cut of the
submitted context: each node at its first occurrence, up to the context's own
node (`StrandCutObservation.logCut`), exactly the cut the observation
records (`Soundness.OracleTransport.viewMap_cuts`). It returns a pair valid at
the submitted request among the selected cells the committed tuple
list-decodes to. It reads no challenge: the adversary may query a round's
node without its PRF words, so Round 0's fingerprint coins need not be in the
log. The list contains the pair that fingerprint selection with the
verifier's coins picks (`selected_listed`), so whenever that pair is valid the
extractor succeeds (`extract_of_selected`).

The original query budget `Q` counts distinct byte queries in the worst case,
for every adversarial coin and total oracle. Averaging uses a finite coin that
may jointly determine the complementary setup slice and adversarial choices;
only the remaining fresh protocol-domain oracle is independent of that coin.
See `Mdoc.OracleSoundness` for the conditioning and filtered-trace identities. -/
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
namespace LfzkV2.Current.Mdoc.Soundness
open Application ApplicationSetup RuntimeAdaptive Bcs.FiniteProbability Merkle.RandomOracle TranscriptV2
open scoped Classical

-- The frontend role lists are irrelevant here; unfolding them only slows unification.
attribute [local irreducible] LfzkV2.Current.Frontend.roles

variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable (binary : ConcreteSetup.BinaryCircuit B) (prime : ConcreteSetup.PrimeCircuit)
variable (cantor : Module.Basis (Fin 128) (ZMod 2) B) (scalars : MdocRuntime.Scalars B)
variable (ids : MdocIdentifiers.Identifiers) (bounds : MdocIdentifiers.Bounds binary prime)
variable (outside : Bytes → Digest)
local notation "currentIds" => Mdoc.OracleSoundness.identifiers ids outside
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
local notation "Fmt" => MdocRuntime.format bp pp binary.plan prime.plan scalars bounds.inputFits bounds.privateFits (by change 128 < 2^64; decide) setup
local notation "metadata" => MdocRuntime.metadata bp pp binary.plan prime.plan scalars bounds.inputFits bounds.privateFits
  (by change 128 < 2^64; decide) setup (C := Answer)
local notation "bf" => Nat.le_max_right (BinaryPublic.degree bp) binary.plan.capacity
local notation "primeFits" => Nat.le_max_right ((Layered.Circuit.layers (PrimePublic.circuit pp))+1) prime.plan.capacity
local notation "df" => Nat.le_max_left (BinaryPublic.degree bp) binary.plan.capacity
local notation "rf" => Nat.le_max_left ((Layered.Circuit.layers (PrimePublic.circuit pp))+1) prime.plan.capacity
local notation "Point" => Format.Point (Fmt)
local notation "Values" => Protocol.Sampling.values c bp pp P R cb cp bc pc (MdocRuntime.format bp pp binary.plan prime.plan scalars bounds.inputFits bounds.privateFits (by change 128 < 2^64; decide) setup)
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
local notation "W" => CanonicalRuntime.wirePublic bp pp P R (MdocRuntime.format bp pp binary.plan prime.plan scalars bounds.inputFits bounds.privateFits (by change 128 < 2^64; decide) setup) I
local notation "earlier" => CanonicalRuntime.earlier bp pp P R (MdocRuntime.format bp pp binary.plan prime.plan scalars bounds.inputFits bounds.privateFits (by change 128 < 2^64; decide) setup) I rfl metadata
local notation "decodePublic" => CanonicalRuntime.decodePrimePublic bp pp P R (MdocRuntime.format bp pp binary.plan prime.plan scalars bounds.inputFits bounds.privateFits (by change 128 < 2^64; decide) setup) I rfl
local notation "draw" => IdealRuntime.draw bp pp P R cb cp bc pc cfg
local notation "codec" => MerkleWireCodec.codec First Second repr
  (RuntimeVerifier.Public.binaryField cfg) (RuntimeVerifier.Public.primeField cfg)
  (Format.jointContext (MdocRuntime.format bp pp binary.plan prime.plan scalars bounds.inputFits bounds.privateFits (by change 128 < 2^64; decide) setup)) (by decide)
local notation "Output" => CanonicalRuntime.Output (Advice := MdocAdvice.Value) bp shape
local notation "Witness" => Selection.Pair B (ZMod Adapter.Mdoc.primeOrder)
  (BinaryPublic.Original bp) (PrimePublic.Original pp)

/-- Both circuits use the request's public values and the same selected
private witness; hash truth reads only the hash circuit's own input prefix. -/
def Valid (request : Mdoc.RuntimeSoundness.Request binary prime bounds) (w : Witness) : Prop :=
  MdocWitness.Valid binary prime request.publicBits request.primeInputs w

theorem decoded_valid (output : Output) (H : Point → Digest × Answer)
    (decoded : RuntimeVerifier.Decoded bp pp P R W)
    (found : RuntimeAdaptiveVerifier.decode bp pp P R W earlier
      (Format.hashPublic (Fmt)) decodePublic draw output H = some decoded)
    (w : Witness) (truth : decoded.application.True w) : Valid binary prime bounds output.request w := by
  exact MdocWitness.valid_at_request binary prime P R (MdocRuntime.format bp pp binary.plan prime.plan scalars bounds.inputFits bounds.privateFits (by change 128 < 2^64; decide) setup) I rfl rfl metadata draw
    output H decoded found w truth

variable {fuel blocks Q : ℕ}
variable (body : Tree Bytes Digest (Mdoc.RuntimeSoundness.Request binary prime bounds × Bytes) fuel)
variable (fits : (MdocRuntime.geometry binary.description prime.description binary.plan prime.plan).roles.length < 2^64)
variable (sample : (point : Mdoc.RuntimeSoundness.RoundPoint binary prime cantor scalars
    (Mdoc.OracleSoundness.identifiers ids outside) bounds) →
  Tree Strand.Word Digest (Option (Mdoc.RuntimeSoundness.RoundValue binary prime cantor scalars
    (Mdoc.OracleSoundness.identifiers ids outside) bounds point)) blocks)
local notation "physical" => Protocol.Sampling.sampler c bp pp P R cb cp bc pc (MdocRuntime.format bp pp binary.plan prime.plan scalars bounds.inputFits bounds.privateFits (by change 128 < 2^64; decide) setup)
  binary.plan prime.plan rfl rfl bf primeFits df rf cfg sample
local notation "Raw" => Mdoc.OracleSoundness.Raw binary prime cantor scalars ids bounds body outside fits sample
local notation "view" G => Mdoc.OracleSoundness.observation binary prime cantor scalars ids bounds body outside fits sample G
local notation "SHA" G => Mdoc.OracleSoundness.sha binary prime cantor scalars ids bounds body outside fits sample G
local notation "decodedView" => Protocol.Observation.decoded bp pp P R W earlier (Format.wire (Protocol.Setup.fmt (E))) (Protocol.Setup.bodyCodec (E))
  physical (Format.hashPublic (Fmt)) decodePublic draw
local notation "authentication" => Soundness.Runtime.viewAuthentication E

/-- The public protocol whose statement node absorbs `formatSetup`; every
other field is the fixed mdoc setup. At the actual statement setup it is
`Mdoc.Setup.protocol` (`publicProtocol_setup`). -/
abbrev publicProtocol (formatSetup : MdocRuntime.FormatSetup) :=
  (Mdoc.Runtime.mk binary prime.description prime.plan (ConcreteSetup.binaryNodes cantor) scalars
    bounds.inputFits bounds.privateFits formatSetup).protocol

theorem publicProtocol_setup :
    publicProtocol binary prime cantor scalars bounds setup = E := rfl

/-- The adversary's submitted proof output: its request and proof bytes,
parsed by the complete-proof reader. -/
def submitted (submission : Mdoc.RuntimeSoundness.Request binary prime bounds × Bytes) : Output :=
  ProofOutput.decode (TaggedFormat.complete repr g) (MdocDefaults.proof g B) submission

/-- The selected-cell pairs that the tuple committed at the submitted
context list-decodes to. The commitment cut is read from the protocol-domain
entries of the adversary's own query log, in query order
(`StrandCutObservation.logCut`). -/
def listed (formatSetup : MdocRuntime.FormatSetup)
    (submission : (Mdoc.RuntimeSoundness.Request binary prime bounds × Bytes) × List (Bytes × Digest)) :
    Finset Witness :=
  let protocol := publicProtocol binary prime cantor scalars bounds formatSetup
  let output := submitted binary prime scalars bounds submission.1
  let key := Replay.Encoding.context (RuntimeAdaptiveVerifier.encodings protocol.binary protocol.prime protocol.P
    protocol.R protocol.wire protocol.earlier output.request) output.proof
  Soundness.Runtime.candidates protocol key (StrandCutObservation.logCut protocol.fmt.schema protocol.fmt.key key
    (submission.2.filter fun qa => decide (StrandDomains.protocol qa.1)))

/-- The straight-line extractor: it reads only the adversary's submitted
request and proof bytes and its own query log. It returns a listed pair valid
for the submitted request. It takes no oracle, reads no challenge, and
depends on neither the adversary's program nor the challenge reader. -/
def extract (formatSetup : MdocRuntime.FormatSetup)
    (submission : (Mdoc.RuntimeSoundness.Request binary prime bounds × Bytes) × List (Bytes × Digest)) :
    Option Witness :=
  if found : ∃ w ∈ listed binary prime cantor scalars bounds formatSetup submission,
      Valid binary prime bounds (submitted binary prime scalars bounds submission.1).request w then
    some found.choose
  else none

/-- Whenever a listed pair is valid for the submitted request, the
extractor returns a valid pair. -/
theorem extract_valid (formatSetup : MdocRuntime.FormatSetup)
    (submission : (Mdoc.RuntimeSoundness.Request binary prime bounds × Bytes) × List (Bytes × Digest))
    (w : Witness) (member : w ∈ listed binary prime cantor scalars bounds formatSetup submission)
    (valid : Valid binary prime bounds (submitted binary prime scalars bounds submission.1).request w) :
    ∃ v, extract binary prime cantor scalars bounds formatSetup submission = some v ∧
      Valid binary prime bounds (submitted binary prime scalars bounds submission.1).request v := by
  have found : ∃ w ∈ listed binary prime cantor scalars bounds formatSetup submission,
      Valid binary prime bounds (submitted binary prime scalars bounds submission.1).request w := ⟨w,member,valid⟩
  exact ⟨found.choose,dif_pos found,found.choose_spec.2⟩

/-- The pair that fingerprint selection picks at the original cut, with the
coins and responses the verifier decodes, is listed. The listed pairs are
read from the adversary's own submission and query log: they equal the
candidates of the observation's cut at its submitted output. -/
theorem selected_listed (G : Raw → Digest) (decoded : RuntimeVerifier.Decoded bp pp P R W)
    (found : decodedView (view G) = some decoded) (w : Witness)
    (selected : (authentication (view G) decoded).context.extract = some w) :
    w ∈ listed binary prime cantor scalars bounds setup (body.run (SHA G)) := by
  have output := Mdoc.OracleSoundness.submitted_output binary prime cantor scalars ids bounds body outside fits sample G
  have trace := Mdoc.OracleSoundness.original_trace binary prime cantor scalars ids bounds body outside fits sample G
  have cuts : ∀ key, (view G).cuts key =
      StrandCutObservation.logCut (E).fmt.schema (E).fmt.key key (view G).original.2 := fun key =>
    Soundness.OracleTransport.viewMap_cuts _ _ _ _ _ _ _ _ _ _ _ _ _ _ key
  have member := Soundness.Runtime.selected_mem_candidates (E) (Protocol.SamplerData.mk (S := E) sample)
    (view G) decoded found w selected
  rw [cuts,trace,output] at member
  exact member

/-- Whenever the selection the verifier's decoding would make is a valid
witness, the straight-line extractor returns a valid witness too. -/
theorem extract_of_selected (G : Raw → Digest) (decoded : RuntimeVerifier.Decoded bp pp P R W)
    (found : decodedView (view G) = some decoded) (w : Witness)
    (selected : (authentication (view G) decoded).context.extract = some w)
    (truth : decoded.application.True w) :
    ∃ v, extract binary prime cantor scalars bounds setup (body.run (SHA G)) = some v ∧
      Valid binary prime bounds (view G).original.1.request v := by
  have output := Mdoc.OracleSoundness.submitted_output binary prime cantor scalars ids bounds body outside fits sample G
  have valid := decoded_valid binary prime cantor scalars ids bounds outside (view G).original.1 _ decoded found w truth
  rw [output] at valid
  obtain ⟨v,extracted,checked⟩ := extract_valid binary prime cantor scalars bounds setup (body.run (SHA G)) w
    (selected_listed binary prime cantor scalars ids bounds outside body fits sample G decoded found w selected) valid
  exact ⟨v,extracted,output ▸ checked⟩

/-- Actual verifier acceptance, including parsing, tuple openings, and the
final seal, with the straight-line extractor, run on the adversary's
submission and query log, failing to produce an application-valid witness. -/
def event (G : Raw → Digest) : Prop :=
  (ProofOutput.read (TaggedFormat.complete repr g) (body.run (SHA G)).1.2).isSome ∧
  Mdoc.RuntimeSoundness.verify binary prime cantor scalars currentIds bounds sample
    (SHA G) (view G).original.1 = true ∧
  ¬ ∃ w, extract binary prime cantor scalars bounds setup (body.run (SHA G)) = some w ∧
    Valid binary prime bounds (view G).original.1.request w

-- The decoded split-claim system makes this unfolding slightly larger.
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 400000 in
theorem event_implies_extraction_failure (G : Raw → Digest) (bad : event binary prime cantor scalars ids bounds outside body fits sample G) :
    Mdoc.OracleSoundness.event binary prime cantor scalars ids bounds body outside fits sample G := by
  have replayed := Mdoc.OracleSoundness.verifier_actual binary prime cantor scalars ids bounds body outside fits sample G
  have decoding := Protocol.Observation.decoded_of_trace bp pp P R W earlier (Format.wire (Protocol.Setup.fmt (E))) (Protocol.Setup.bodyCodec (E))
    physical codec id (Format.hashPublic (Fmt)) decodePublic draw
    (view G) (SHA G) (congrArg Prod.snd replayed)
  obtain ⟨decoded,found,_⟩ := (StrandVerifier.verify_true_iff bp pp P R W earlier (Format.wire (Protocol.Setup.fmt (E))) (Protocol.Setup.bodyCodec (E))
    physical (Format.hashPublic (Fmt)) decodePublic draw codec
    (SHA G) id (view G).original.1).mp bad.2.1
  have foundView : decodedView (view G) = some decoded := decoding.trans found
  have decision := Protocol.Observation.decision_of_trace bp pp P R W earlier (Format.wire (Protocol.Setup.fmt (E))) (Protocol.Setup.bodyCodec (E))
    physical codec id (Format.hashPublic (Fmt)) decodePublic draw
    (view G) (SHA G) (congrArg Prod.snd replayed)
  refine ⟨bad.1,decision.trans bad.2.1,decoded,foundView,?_⟩
  rintro ⟨w,extracted,truth⟩
  exact bad.2.2 (extract_of_selected binary prime cantor scalars ids bounds outside body fits sample G
    decoded foundView w extracted truth)

variable (bodyFits : ProofBodyBounds.bodyBound (MdocRuntime.representations scalars)
  (MdocRuntime.geometry binary.description prime.description binary.plan prime.plan) ≤ CanonicalPrefix.maxLength)
variable (queries : ∀ oracle : Bytes → Digest, (seen body oracle).card ≤ Q)

include bodyFits queries in
/-- Soundness at one setup slice, for every challenge reader with the
balanced-fiber law (`Protocol.Sampler`); `Mdoc.Soundness.averaged_ratio_le_rust`
fixes the Rust reader. -/
theorem ratio_le (sampler : Protocol.Sampler E blocks) (budget : Q < 2^127) :
    density (event binary prime cantor scalars ids bounds outside body fits sampler.data.sample) ≤
      LfzkV2.Current.Soundness.Rate7.failureBound Q (g).roles.length :=
  (density_mono (fun G bad => event_implies_extraction_failure binary prime cantor scalars ids bounds outside
    body fits sampler.data.sample G bad)).trans
    (Mdoc.OracleSoundness.ratio_le binary prime cantor scalars ids bounds body outside queries fits
      sampler.data.sample sampler.laws.fiber sampler.laws.uniform bodyFits budget)

include bodyFits queries in
theorem linear_ratio_le (sampler : Protocol.Sampler E blocks) :
    density (event binary prime cantor scalars ids bounds outside body fits sampler.data.sample) ≤
      LfzkV2.Current.Soundness.Rate7.rate*Q + LfzkV2.Current.Soundness.Rate7.correction Q (g).roles.length :=
  (density_mono (fun G bad => event_implies_extraction_failure binary prime cantor scalars ids bounds outside
    body fits sampler.data.sample G bad)).trans
    (Mdoc.OracleSoundness.linear_ratio_le binary prime cantor scalars ids bounds body outside queries fits
      sampler.data.sample sampler.laws.fiber sampler.laws.uniform bodyFits)

private theorem averaged_event_le {Omega : Type} [Fintype Omega] [Nonempty Omega]
    (external : Omega → Bytes → Digest)
    (adversary : Omega → Tree Bytes Digest (Mdoc.RuntimeSoundness.Request binary prime bounds × Bytes) fuel)
    (sampler : (coin : Omega) →
      (point : Mdoc.RuntimeSoundness.RoundPoint binary prime cantor scalars (Mdoc.OracleSoundness.identifiers ids (external coin)) bounds) →
      Tree Strand.Word Digest
        (Option (Mdoc.RuntimeSoundness.RoundValue binary prime cantor scalars (Mdoc.OracleSoundness.identifiers ids (external coin)) bounds point)) blocks) :
      (∑ coin, density (event binary prime cantor scalars ids bounds (external coin) (adversary coin) fits (sampler coin))) /
        Fintype.card Omega ≤
      (∑ coin, density (Mdoc.OracleSoundness.event binary prime cantor scalars ids bounds (adversary coin) (external coin) fits (sampler coin))) /
        Fintype.card Omega := by
  apply div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro coin _
  exact density_mono (fun G bad => event_implies_extraction_failure binary prime cantor scalars ids bounds
    (external coin) (adversary coin) fits (sampler coin) G bad)

include bodyFits in
theorem averaged_linear_ratio_le {Omega : Type} [Fintype Omega] [Nonempty Omega]
    (external : Omega → Bytes → Digest)
    (adversary : Omega → Tree Bytes Digest (Mdoc.RuntimeSoundness.Request binary prime bounds × Bytes) fuel)
    (sampler : (coin : Omega) → Protocol.Sampler
      (Mdoc.Setup.protocol binary prime cantor scalars (Mdoc.OracleSoundness.identifiers ids (external coin)) bounds)
      blocks)
    (queryBound : ∀ coin oracle, (seen (adversary coin) oracle).card ≤ Q) :
    (∑ coin, density (event binary prime cantor scalars ids bounds (external coin) (adversary coin) fits
        (sampler coin).data.sample)) / Fintype.card Omega ≤
      LfzkV2.Current.Soundness.Rate7.rate*Q + LfzkV2.Current.Soundness.Rate7.correction Q
        (MdocRuntime.geometry binary.description prime.description binary.plan prime.plan).roles.length := by
  have comparison := averaged_event_le binary prime cantor scalars ids bounds
    (fits := fits) external adversary (fun coin => (sampler coin).data.sample)
  exact comparison.trans (Mdoc.OracleSoundness.averaged_linear_ratio_le binary prime cantor scalars ids bounds
    (fits := fits) (bodyFits := bodyFits) external adversary (fun coin => (sampler coin).data.sample)
    (fun coin => (sampler coin).laws.fiber) (fun coin => (sampler coin).laws.uniform) queryBound)

include bodyFits in
/-- The soundness endpoint: one balanced challenge reader per coin
(`Protocol.Sampler`); `Mdoc.Soundness.averaged_ratio_le_rust` fixes the Rust
reader. -/
theorem averaged_ratio_le {Omega : Type} [Fintype Omega] [Nonempty Omega]
    (external : Omega → Bytes → Digest)
    (adversary : Omega → Tree Bytes Digest (Mdoc.RuntimeSoundness.Request binary prime bounds × Bytes) fuel)
    (sampler : (coin : Omega) → Protocol.Sampler
      (Mdoc.Setup.protocol binary prime cantor scalars (Mdoc.OracleSoundness.identifiers ids (external coin)) bounds)
      blocks)
    (queryBound : ∀ coin oracle, (seen (adversary coin) oracle).card ≤ Q) (budget : Q < 2^127) :
    (∑ coin, density (event binary prime cantor scalars ids bounds (external coin) (adversary coin) fits
        (sampler coin).data.sample)) / Fintype.card Omega ≤
      LfzkV2.Current.Soundness.Rate7.failureBound Q
        (MdocRuntime.geometry binary.description prime.description binary.plan prime.plan).roles.length := by
  have comparison := averaged_event_le binary prime cantor scalars ids bounds
    (fits := fits) external adversary (fun coin => (sampler coin).data.sample)
  exact comparison.trans (Mdoc.OracleSoundness.averaged_ratio_le binary prime cantor scalars ids bounds
    (fits := fits) (bodyFits := bodyFits) external adversary (fun coin => (sampler coin).data.sample)
    (fun coin => (sampler coin).laws.fiber) (fun coin => (sampler coin).laws.uniform) queryBound budget)

include bodyFits in
theorem averaged_nonvacuous {Omega : Type} [Fintype Omega] [Nonempty Omega]
    (external : Omega → Bytes → Digest)
    (adversary : Omega → Tree Bytes Digest (Mdoc.RuntimeSoundness.Request binary prime bounds × Bytes) fuel)
    (sampler : (coin : Omega) → Protocol.Sampler
      (Mdoc.Setup.protocol binary prime cantor scalars (Mdoc.OracleSoundness.identifiers ids (external coin)) bounds)
      blocks)
    (queryBound : ∀ coin oracle, (seen (adversary coin) oracle).card ≤ Q) (budget : Q < 2^127) :
    (∑ coin, density (event binary prime cantor scalars ids bounds (external coin) (adversary coin) fits
        (sampler coin).data.sample)) / Fintype.card Omega < 97/100 := by
  have comparison := averaged_event_le binary prime cantor scalars ids bounds
    (fits := fits) external adversary (fun coin => (sampler coin).data.sample)
  exact comparison.trans_lt (Mdoc.OracleSoundness.averaged_nonvacuous binary prime cantor scalars ids bounds
    (fits := fits) (bodyFits := bodyFits) external adversary (fun coin => (sampler coin).data.sample)
    (fun coin => (sampler coin).laws.fiber) (fun coin => (sampler coin).laws.uniform) queryBound budget)

include bodyFits in
theorem averaged_polynomial_ratio_le {Omega : Type} [Fintype Omega] [Nonempty Omega]
    (external : Omega → Bytes → Digest)
    (adversary : Omega → Tree Bytes Digest (Mdoc.RuntimeSoundness.Request binary prime bounds × Bytes) fuel)
    (sampler : (coin : Omega) → Protocol.Sampler
      (Mdoc.Setup.protocol binary prime cantor scalars (Mdoc.OracleSoundness.identifiers ids (external coin)) bounds)
      blocks)
    (queryBound : ∀ coin oracle, (seen (adversary coin) oracle).card ≤ Q) :
    (∑ coin, density (event binary prime cantor scalars ids bounds (external coin) (adversary coin) fits
        (sampler coin).data.sample)) / Fintype.card Omega ≤
      2*Q*(2 : ℚ)^(-128 : ℤ) +
        (2*(Q : ℚ)^2/(1-(2 : ℚ)^(-128 : ℤ)) +
          (MdocRuntime.geometry binary.description prime.description binary.plan prime.plan).roles.length + 15) *
            (2 : ℚ)^(-256 : ℤ) := by
  have comparison := averaged_event_le binary prime cantor scalars ids bounds
    (fits := fits) external adversary (fun coin => (sampler coin).data.sample)
  exact comparison.trans (Mdoc.OracleSoundness.averaged_polynomial_ratio_le binary prime cantor scalars ids bounds
    (fits := fits) (bodyFits := bodyFits) external adversary (fun coin => (sampler coin).data.sample)
    (fun coin => (sampler coin).laws.fiber) (fun coin => (sampler coin).laws.uniform) queryBound)

include bodyFits in
theorem averaged_mdoc_approximation {Omega : Type} [Fintype Omega] [Nonempty Omega]
    (external : Omega → Bytes → Digest)
    (adversary : Omega → Tree Bytes Digest (Mdoc.RuntimeSoundness.Request binary prime bounds × Bytes) fuel)
    (sampler : (coin : Omega) → Protocol.Sampler
      (Mdoc.Setup.protocol binary prime cantor scalars (Mdoc.OracleSoundness.identifiers ids (external coin)) bounds)
      blocks)
    (queryBound : ∀ coin oracle, (seen (adversary coin) oracle).card ≤ Q)
    (supported : MdocRoundShape.Supported (MdocRuntime.geometry binary.description prime.description binary.plan prime.plan)) :
    (∑ coin, density (event binary prime cantor scalars ids bounds (external coin) (adversary coin) fits
        (sampler coin).data.sample)) / Fintype.card Omega ≤
      (Q : ℚ)/2^127 + (Q : ℚ)^2/2^257 + 1/2^246 := by
  have comparison := averaged_event_le binary prime cantor scalars ids bounds
    (fits := fits) external adversary (fun coin => (sampler coin).data.sample)
  exact comparison.trans (Mdoc.OracleSoundness.averaged_mdoc_approximation binary prime cantor scalars ids bounds
    (fits := fits) (bodyFits := bodyFits) external adversary (fun coin => (sampler coin).data.sample)
    (fun coin => (sampler coin).laws.fiber) (fun coin => (sampler coin).laws.uniform) queryBound supported)

end LfzkV2.Current.Mdoc.Soundness
