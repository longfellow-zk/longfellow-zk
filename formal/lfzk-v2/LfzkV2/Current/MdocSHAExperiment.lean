import LfzkV2.Current.MdocSharedSHA
import LfzkV2.Current.SHAPrefix
import LfzkV2.Current.SHATransport
import LfzkV2.Current.SHAAuthentication

/-! Execute the original raw prover and the verifier with one SHA function.
The function is assembled from an independently fixed auxiliary restriction
and the COMPLETE lazy Merkle run. This is an operational random oracle: new
Merkle inputs receive fresh tape cells, repeated inputs retain their answer.
Unqueried defaults are never exposed as fresh answers in the execution. -/
noncomputable section
namespace LfzkV2.Current.MdocSHAExperiment
open Application ApplicationSetup Finset Merkle.RandomOracle
open Merkle.RandomOracle.TwoOracleTree ZeroKnowledge
open scoped Classical
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable (binary : ConcreteSetup.BinaryCircuit B) (prime : ConcreteSetup.PrimeCircuit)
variable (cantor : Module.Basis (Fin 128) (ZMod 2) B) (scalars : MdocRuntime.Scalars B)
variable (ids : MdocIdentifiers.Identifiers) (bounds : MdocIdentifiers.Bounds binary prime)

omit [Fintype B] [DecidableEq B] in
private theorem degreeFits : binary.description.degree < 2^64 := by
  change 128 < 2^64
  decide

local notation "bp" => binary.description
local notation "pp" => prime.description
local notation "nodes" => ConcreteSetup.binaryNodes cantor
local notation "P" => MdocRuntime.binaryBackend bp nodes
local notation "R" => MdocRuntime.primeBackend pp
local notation "Geom" => MdocRuntime.geometry bp pp binary.plan prime.plan
local notation "Repr" => MdocRuntime.representations scalars
local notation "Shape" => MdocRuntime.shape bp pp binary.plan prime.plan bounds.inputFits bounds.privateFits (degreeFits binary)
local notation "Answer" => MdocSharedSHA.Answer binary prime cantor
local notation "Setup" SHA:max => MdocPublicSetup.setup binary prime cantor scalars ids bounds SHA
local notation "Cfg" SHA:max => MdocPublicSetup.configuration binary prime cantor scalars ids bounds SHA
local notation "Meta" SHA:max => MdocPublicSetup.metadata binary prime cantor scalars ids bounds SHA
local notation "Public" SHA:max => CanonicalRate7.wirePublic bp pp P R Repr Shape (Setup SHA) (Cfg SHA)
local notation "Earlier" SHA:max => CanonicalRate7.earlier bp pp P R Repr Shape (Setup SHA) (Cfg SHA) rfl (Meta SHA)
local notation "Codec" SHA:max => CanonicalRate7.merkleCodec bp pp P R Repr Shape (Setup SHA) (Cfg SHA)

variable {tA calls : ℕ}
variable (body : MdocSetupFamily.Values → TwoOracleTree Bytes Digest Bytes
  (Digest × MdocSharedSHA.Answer binary prime cantor) (MdocSharedSHA.RawOutput binary prime bounds) tA calls)
variable (fits : (MdocRuntime.geometry binary.description prime.description binary.plan prime.plan).roles.length < 2^64)

def normalized (outside : Bytes → Digest) :=
  ProofOutput.normalize Repr (MdocDefaults.proof Geom B)
    (MdocSharedSHA.routed binary prime cantor scalars ids bounds body outside)

def typedOracle (outside : Bytes → Digest) (HT : Bytes → Digest × Answer) :=
  CanonicalRate7.restricted bp Repr Shape (Setup outside) fits
    (MdocProofRate7.defaultAnswer binary prime cantor) HT

def program (outside : Bytes → Digest) (HT : Bytes → Digest × Answer) :=
  CanonicalRate7.typedBody bp Repr Shape (Setup outside) fits
    (normalized binary prime cantor scalars ids bounds body outside) HT

def commitment (outside : Bytes → Digest) (HT : Bytes → Digest × Answer) :=
  CanonicalRate7.commitmentSetup bp pp P R Repr Shape (Setup outside) (Cfg outside) rfl (Meta outside) fits
    (normalized binary prime cantor scalars ids bounds body outside)
    (MdocProofRate7.defaultAnswer binary prime cantor) HT

def originalProgram (outside : Bytes → Digest) (HT : Bytes → Digest × Answer) :=
  CanonicalRate7.typedBody bp Repr Shape (Setup outside) fits
    (ProofOutput.normalize Repr (MdocDefaults.proof Geom B)
      (body (MdocSetupFamily.values binary prime cantor scalars ids bounds outside))) HT

omit [DecidableEq B] in
theorem program_routing (outside : Bytes → Digest) (HT : Bytes → Digest × Answer) :
    SHAOracle.route SHAOracle.merkleDomain outside
      (originalProgram binary prime cantor scalars ids bounds body fits outside HT) =
      program binary prime cantor scalars ids bounds body fits outside HT := by
  unfold originalProgram program CanonicalRate7.typedBody normalized ProofOutput.normalize
  rw [SHATransport.program,SHATransport.map]
  rfl

def originalBody (outside : Bytes → Digest) (HT : Bytes → Digest × Answer) :=
  (originalProgram binary prime cantor scalars ids bounds body fits outside HT).bindRight
    (RuntimeAdaptiveVerifier.chain bp pp P R (Public outside) (Earlier outside)).recompute

theorem body_routing (outside : Bytes → Digest) (HT : Bytes → Digest × Answer) :
    SHAOracle.route SHAOracle.merkleDomain outside
      (originalBody binary prime cantor scalars ids bounds body fits outside HT) =
      (commitment binary prime cantor scalars ids bounds body fits outside HT).body := by
  unfold originalBody
  rw [SHATransport.bind,program_routing]
  rfl

def merkleOracle (outside : Bytes → Digest) (tape : Fin (4886+tA) → Digest) (HT : Bytes → Digest × Answer) : Bytes → Digest :=
  RuntimeAdaptiveMerkle.merkleOracle bp pp P R (Public outside) (Earlier outside) (Codec outside)
    (MdocProofRate7.defaultAnswer binary prime cantor)
    (program binary prime cantor scalars ids bounds body fits outside HT) tape
    (typedOracle binary prime cantor scalars ids bounds fits outside HT)

def SHA (outside : Bytes → Digest) (tape : Fin (4886+tA) → Digest) (HT : Bytes → Digest × Answer) : Bytes → Digest :=
  SHAOracle.merge SHAOracle.merkleDomain outside
    (merkleOracle binary prime cantor scalars ids bounds body fits outside tape HT)

/-- The auxiliary restriction determines setup and all causal identifier
computations even though the input being identified depends on challenges. -/
theorem setup_same (outside : Bytes → Digest) (tape : Fin (4886+tA) → Digest) (HT : Bytes → Digest × Answer) :
    Setup (SHA binary prime cantor scalars ids bounds body fits outside tape HT) = Setup outside :=
  MdocPublicSetup.setup_merge binary prime cantor scalars ids bounds outside _

theorem metadata_same (outside : Bytes → Digest) (tape : Fin (4886+tA) → Digest) (HT : Bytes → Digest × Answer) :
    Meta (SHA binary prime cantor scalars ids bounds body fits outside tape HT) = Meta outside :=
  MdocPublicSetup.metadata_merge binary prime cantor scalars ids bounds outside _

theorem original_output (outside : Bytes → Digest) (tape : Fin (4886+tA) → Digest) (HT : Bytes → Digest × Answer) :
    (Observer.run (SHA binary prime cantor scalars ids bounds body fits outside tape HT) HT
      (body (MdocSetupFamily.values binary prime cantor scalars ids bounds
        (SHA binary prime cantor scalars ids bounds body fits outside tape HT)))).1 =
      ((fixLeft tape default (MdocSharedSHA.routed binary prime cantor scalars ids bounds body outside) []).run HT).1 := by
  rw [SHA,MdocSetupFamily.values_merge,← SHAOracle.route_output]
  let S := commitment binary prime cantor scalars ids bounds body fits outside HT
  let H := typedOracle binary prime cantor scalars ids bounds fits outside HT
  let A := S.atOracle H
  let check := RuntimeAdaptiveMerkle.check (Request := CanonicalRuntime.Request bp Shape) bp pp P R (Public outside) (Codec outside)
  have slots : (lazyRun tape default
      (fixRight Bcs.TotalOracleCommit.Setup.emptyTape A.dflt A.joint []) []).2.1 =
      (lazyRun tape default (TranscriptV2.Memoize.left HT
        (MdocSharedSHA.routed binary prime cantor scalars ids bounds body outside)) []).2.1 := by
    change (lazyRun tape default (fixRight (Fin.elim0 : Fin 0 → Digest × Answer) S.dflt
      ((Bcs.TotalOracleCommit.answerRight H S.body).bindRight S.recompute) []) []).2.1 = _
    rw [TranscriptV2.Memoize.actual_bind,lazyRun_map]
    change (lazyRun tape default (TranscriptV2.Memoize.left H
      ((program binary prime cantor scalars ids bounds body fits outside HT).bindRight
        (RuntimeAdaptiveVerifier.chain bp pp P R (Public outside) (Earlier outside)).recompute)) []).2.1 = _
    rw [SHAPrefix.left_bind,lazyRun_map]
    unfold program CanonicalRate7.typedBody
    rw [SHAPrefix.left_program]
    unfold H typedOracle CanonicalRate7.restricted
    rw [ByteOracleTransport.Codec.oracle_restrict]
    unfold normalized ProofOutput.normalize
    rw [SHAPrefix.left_map,lazyRun_map]
  have contains : (lazyRun tape default (TranscriptV2.Memoize.left HT
      (MdocSharedSHA.routed binary prime cantor scalars ids bounds body outside)) []).2.1 <+:
      Merkle.MH.runSlots (4886+tA) (A.merkleRun check Bcs.TotalOracleCommit.Setup.emptyTape) tape := by
    rw [← slots]
    exact lazyRun_seen_prefix_bind tape default _ _ []
  exact SHAPrefix.run_of_prefix HT tape
    (MdocSharedSHA.routed binary prime cantor scalars ids bounds body outside)
    (A.merkleRun check Bcs.TotalOracleCommit.Setup.emptyTape) contains

/-- The extractor reads the Merkle-domain projection of the original
execution prefix. It neither reads later queries nor treats identifier
answers as Merkle preimages. The cut index comes from the unchanged
first-context construction; routing preserves every transcript boundary. -/
def cutTrace (outside : Bytes → Digest) (tape : Fin (4886+tA) → Digest) (HT : Bytes → Digest × Answer)
    (key : FingerprintPrefix.Key binary.nPublic) : List (Bytes × Digest) :=
  let S := commitment binary prime cantor scalars ids bounds body fits outside HT
  let H := typedOracle binary prime cantor scalars ids bounds fits outside HT
  let index := (S.atOracle H).cutIdx tape Bcs.TotalOracleCommit.Setup.emptyTape key
  let original := (originalBody binary prime cantor scalars ids bounds body fits outside HT).bindRight
    fun out => Bcs.TotalOracleCommit.answerWith (fun _ => S.dflt) (S.recompute out)
  Observer.merkleTrace ((Observer.run (SHA binary prime cantor scalars ids bounds body fits outside tape HT) H
    (Bcs.AdaptiveCommit.stopAt index original [])).2.filter (SHARouting.keep SHAOracle.merkleDomain))

theorem cut_preserved (outside : Bytes → Digest) (tape : Fin (4886+tA) → Digest) (HT : Bytes → Digest × Answer)
    (key : FingerprintPrefix.Key binary.nPublic) :
    cutTrace binary prime cantor scalars ids bounds body fits outside tape HT key =
      ((commitment binary prime cantor scalars ids bounds body fits outside HT).atOracle
        (typedOracle binary prime cantor scalars ids bounds fits outside HT)).cutTrace
          tape Bcs.TotalOracleCommit.Setup.emptyTape key := by
  let S := commitment binary prime cantor scalars ids bounds body fits outside HT
  let H := typedOracle binary prime cantor scalars ids bounds fits outside HT
  let original := (originalBody binary prime cantor scalars ids bounds body fits outside HT).bindRight
    fun out => Bcs.TotalOracleCommit.answerWith (fun _ => S.dflt) (S.recompute out)
  have routing : SHAOracle.route SHAOracle.merkleDomain outside original =
      S.body.bindRight (fun out => Bcs.TotalOracleCommit.answerWith (fun _ => S.dflt) (S.recompute out)) := by
    dsimp only [original]
    rw [SHATransport.bind,body_routing]
    rfl
  have same := SHARouting.cut_run SHAOracle.merkleDomain outside
    ((S.atOracle H).cutIdx tape Bcs.TotalOracleCommit.Setup.emptyTape key) original []
    (merkleOracle binary prime cantor scalars ids bounds body fits outside tape HT) H
  rw [routing] at same
  have trace := congrArg (fun result => Observer.merkleTrace result.2) same
  exact trace.symm.trans (SHALazy.setup_cut_run H S
    (RuntimeAdaptiveMerkle.check (Request := CanonicalRuntime.Request bp Shape) bp pp P R (Public outside) (Codec outside)) tape key)

def output (outside : Bytes → Digest) (tape : Fin (4886+tA) → Digest) (HT : Bytes → Digest × Answer) :=
  (Observer.run (SHA binary prime cantor scalars ids bounds body fits outside tape HT) HT
    (body (MdocSetupFamily.values binary prime cantor scalars ids bounds
      (SHA binary prime cantor scalars ids bounds body fits outside tape HT)))).1

def decodedOutput (outside : Bytes → Digest) (tape : Fin (4886+tA) → Digest) (HT : Bytes → Digest × Answer) :=
  ProofOutput.decode Repr (MdocDefaults.proof Geom B)
    (output binary prime cantor scalars ids bounds body fits outside tape HT)

theorem decoded_output (outside : Bytes → Digest) (tape : Fin (4886+tA) → Digest) (HT : Bytes → Digest × Answer) :
    decodedOutput binary prime cantor scalars ids bounds body fits outside tape HT =
      RuntimeAdaptiveMerkle.originalOutput
        (program binary prime cantor scalars ids bounds body fits outside HT) tape
        (typedOracle binary prime cantor scalars ids bounds fits outside HT) := by
  unfold decodedOutput output
  rw [original_output]
  unfold program typedOracle
  rw [CanonicalRate7.raw_output]
  unfold normalized ProofOutput.normalize
  rw [ProofOutput.run_map]

/-- One canonical verifier construction is shared by the real and routed
experiments. Only the SHA function changes between their two views. -/
def verify (outside : Bytes → Digest) (HM : Bytes → Digest)
    (proof : CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description Shape)
    (HT : Bytes → Digest × Answer) : Bool :=
  RuntimeAdaptiveVerifier.verify bp pp P R (Public outside) (Earlier outside)
    (CanonicalRequest.hashPublic binary.nPublic)
    (CanonicalRate7.decodePublic bp pp P R Repr Shape (Setup outside) (Cfg outside) rfl)
    (MdocPublicSetup.draw binary prime cantor scalars ids bounds outside) (Codec outside)
    HM proof (typedOracle binary prime cantor scalars ids bounds fits outside HT)

/-- Full verification uses the single SHA function. The setup and causal
metadata in its constructor equal those computed through that function by
`setup_same` and `metadata_same`; only notation is normalized here. -/
def accepted (outside : Bytes → Digest) (tape : Fin (4886+tA) → Digest) (HT : Bytes → Digest × Answer) : Prop :=
  (ProofOutput.read (g := Geom) Repr (output binary prime cantor scalars ids bounds body fits outside tape HT).2).isSome ∧
    verify binary prime cantor scalars ids bounds fits outside
      (SHA binary prime cantor scalars ids bounds body fits outside tape HT)
      (decodedOutput binary prime cantor scalars ids bounds body fits outside tape HT) HT = true

/-- This is the retained paired extractor. Its whole first-context trace
equals the Merkle projection of the original single-SHA prefix, for every
key (`cut_preserved`), so all subsequent decoding/search is unchanged. -/
def failure (outside : Bytes → Digest) (tape : Fin (4886+tA) → Digest) (HT : Bytes → Digest × Answer) : Prop :=
  CanonicalRate7.extractionFailure bp pp P R Repr Shape (Setup outside) (Cfg outside) rfl rfl (Meta outside) fits
    (normalized binary prime cantor scalars ids bounds body outside)
    (MdocProofRate7.defaultAnswer binary prime cantor)
    (MdocPublicSetup.draw binary prime cantor scalars ids bounds outside) HT tape
    (typedOracle binary prime cantor scalars ids bounds fits outside HT)

def event (outside : Bytes → Digest) (tape : Fin (4886+tA) → Digest) (HT : Bytes → Digest × Answer) : Prop :=
  accepted binary prime cantor scalars ids bounds body fits outside tape HT ∧
    failure binary prime cantor scalars ids bounds body fits outside tape HT

/-- The canonical verifier is insensitive to the auxiliary SHA restriction.
This holds for every decoded proof and Merkle function, independently of
the prover's behavior. -/
theorem verify_merge (outside inside : Bytes → Digest)
    (proof : CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description Shape) (HT : Bytes → Digest × Answer) :
    verify binary prime cantor scalars ids bounds fits outside
        (SHAOracle.merge SHAOracle.merkleDomain outside inside) proof HT =
      verify binary prime cantor scalars ids bounds fits outside inside proof HT := by
  have leafDomain : ∀ value, SHAOracle.merkleDomain ((Codec outside).leafEnc value) :=
    SHAOracle.leaf_in_domain
      (RuntimeVerifier.first bp pp P R (Public outside)).participant
      (RuntimeVerifier.second bp pp P R (Public outside)).participant
      Repr (Cfg outside).binaryField (Cfg outside).primeField
      (Setup outside).jointContext (by decide)
  have nodeDomain : ∀ value, SHAOracle.merkleDomain ((Codec outside).nodeEnc value) :=
    SHAOracle.node_in_domain
      (RuntimeVerifier.first bp pp P R (Public outside)).participant
      (RuntimeVerifier.second bp pp P R (Public outside)).participant
      Repr (Cfg outside).binaryField (Cfg outside).primeField
      (Setup outside).jointContext (by decide)
  unfold verify RuntimeAdaptiveVerifier.verify
  split
  · rfl
  · apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    unfold RuntimeAdaptiveVerifier.Checks Bcs.Compiler.Accepts
    refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr ?_ Iff.rfl))
    refine and_congr Iff.rfl (and_congr ?_ Iff.rfl)
    exact SHAAuthentication.accepts SHAOracle.merkleDomain outside
      inside (Codec outside) leafDomain nodeDomain _ _ _ _ _

/-- The serialized proof, verifier decision and exact paired extraction
event coincide with the conditioned theorem. This is an equality of events,
not a supplied execution/correspondence certificate. -/
theorem event_iff (outside : Bytes → Digest) (tape : Fin (4886+tA) → Digest) (HT : Bytes → Digest × Answer) :
    event binary prime cantor scalars ids bounds body fits outside tape HT ↔
      MdocProofRate7.rawEvent binary prime cantor scalars (MdocPublicSetup.identifiers ids outside) bounds
        (MdocSharedSHA.routed binary prime cantor scalars ids bounds body outside) fits tape HT := by
  unfold event accepted
  rw [SHA,verify_merge]
  unfold output
  rw [original_output]
  rw [decoded_output]
  change (_ ∧ _) ∧ _ ↔ _ ∧ (_ ∧ _)
  exact and_assoc

end LfzkV2.Current.MdocSHAExperiment
