import LfzkV2.Current.Mdoc.Soundness
import LfzkV2.Current.Mdoc.ZeroKnowledge
import LfzkV2.Current.Mdoc.VerifierPrivacy
import LfzkV2.Current.Mdoc.Completeness
import LfzkV2.Current.Mdoc.Rust

/-! Pin the exact statements of the public endpoints. Each fingerprint hashes
an endpoint's type together with the type and body of every project
definition it depends on, transitively; proofs and external libraries are
excluded. Any change to what an endpoint states, including a change to a
definition it mentions, fails this module until the pinned value is updated
after review. The pins cover the four endpoints (soundness, zero knowledge,
simulator acceptance and completeness) and their corollaries at the Rust
challenge reader (`Mdoc.Rust`), and each of them must reach the definitions
that carry its meaning (`required`). The soundness extractor must decode
uniquely from the transcript: it reaches Polygero's unique decoder and no
list-decoding definition (`uniqueDecoder`, `listDecoding`). It must also take
no oracle: it reaches no oracle of the soundness experiment, no raw SHA table
and no verifier replay (`straightLine`). Axiom and
connectivity checks live in `Tests.MdocSoundness`. -/
namespace LfzkV2.Current.Tests.EndpointStatements
open Lean Elab Command

/-- Modules outside this repository; their definitions are not pinned here. -/
def external (module : Name) : Bool :=
  [`Init, `Lean, `Std, `Mathlib, `Batteries, `Aesop, `Qq, `ProofWidgets, `Plausible,
    `LeanSearchClient, `ImportGraph].any (·.isPrefixOf module)

/-- Statement fingerprint: the endpoint's type plus the types and bodies of
the repository definitions, structures and constructors it reaches. -/
def fingerprint (env : Environment) (root : Name) : UInt64 × NameSet := Id.run do
  let mut pending := [root]
  let mut visited : NameSet := {}
  let mut acc : UInt64 := 7
  while let name :: rest := pending do
    pending := rest
    if visited.contains name then continue
    visited := visited.insert name
    let some info := env.find? name | continue
    let module := (env.getModuleIdxFor? name).bind (env.header.moduleNames[·]?)
    if name != root && module.any external then continue
    acc := mixHash acc (mixHash (hash name) info.type.hash)
    pending := info.type.getUsedConstants.toList ++ pending
    match info with
    | .thmInfo _ => pure ()
    | .inductInfo induct => pending := induct.ctors ++ pending
    | _ =>
      if let some value := info.value? true then
        acc := mixHash acc value.hash
        pending := value.getUsedConstants.toList ++ pending
  return (acc, visited)

/-- Reviewed statement fingerprints. Update a value only after reviewing the
statement change it reflects. -/
def pinned : List (Name × UInt64) := [
  (``Current.Mdoc.Soundness.ratio_le, 8582023105427532507),
  (``Current.Mdoc.Soundness.linear_ratio_le, 2256592093110131377),
  (``Current.Mdoc.Soundness.averaged_ratio_le, 16532026915781597033),
  (``Current.Mdoc.Soundness.averaged_linear_ratio_le, 4865304750125696021),
  (``Current.Mdoc.Soundness.averaged_nonvacuous, 82060277669800425),
  (``Current.Mdoc.Soundness.averaged_polynomial_ratio_le, 12966774689929099418),
  (``Current.Mdoc.Soundness.averaged_mdoc_approximation, 9439100636994569996),
  (``Current.Mdoc.ZeroKnowledge.statClose, 11089277535653201106),
  (``Current.Mdoc.ZeroKnowledge.statClose_at_query_budget, 3608117319759410495),
  (``Current.Mdoc.VerifierPrivacy.acceptance_probability, 17334613443263901531),
  (``Current.Mdoc.Completeness.some_accepts, 4494509276498619142),
  (``Current.Mdoc.Completeness.accepts, 14703360873936376765),
  (``Current.Mdoc.Completeness.accepts_rust, 7576761460556919049),
  (``Current.Mdoc.Soundness.averaged_ratio_le_rust, 2288941145299443603),
  (``Current.Mdoc.ZeroKnowledge.statClose_rust, 9355581669937741965),
  (``Current.Mdoc.VerifierPrivacy.acceptance_probability_rust, 11679471597644133134)]

/-- Definitions each endpoint must reach: its event or experiment, its
witness premises, the setup it is stated for and, for a deployed corollary,
the Rust reader. -/
def required : List (Name × List Name) := [
  (``Current.Mdoc.Soundness.averaged_ratio_le,
    [``Soundness.Rate7.failureBound, ``Soundness.Rate7.polygeroConstant,
      ``Current.Mdoc.Soundness.event, ``Current.Mdoc.Soundness.Valid,
      ``Current.Mdoc.Soundness.extract, ``Current.Mdoc.Soundness.rowTrace,
      ``Soundness.Runtime.traceRecover, ``StrandRowTrace.oracle, ``StrandRowTrace.ofLog,
      ``StrandCutObservation.logCut, ``Application.StatementData.recover,
      ``RecursivePolygero.scanRecoverAt,
      ``MdocWitness.HashValid, ``MdocWitness.HashChecks,
      ``ConcreteAdapterTopology.Others, ``MdocIdentifiers.setup, ``MdocIdentifiers.fragmentId,
      ``Protocol.Sampler, ``Protocol.SamplerLaws]),
  (``Current.Mdoc.ZeroKnowledge.statClose,
    [``Current.Mdoc.ZeroKnowledge.honest, ``Current.Mdoc.ZeroKnowledge.simulate,
      ``Current.Mdoc.ZeroKnowledge.window, ``Current.Mdoc.ZeroKnowledge.Reachable,
      ``ZeroKnowledge.StrandCanonicalExecution.rawReal,
      ``ZeroKnowledge.StrandCanonicalExperiments.rawSimulate, ``MdocWitness.HashValid,
      ``Current.Mdoc.SetupFamily.values, ``Current.Mdoc.SetupFamily.setup,
      ``MdocIdentifiers.fragmentId]),
  (``Current.Mdoc.VerifierPrivacy.acceptance_probability,
    [``Current.Mdoc.VerifierPrivacy.afterVerifier,
      ``ZeroKnowledge.StrandVerifierObserver.optional, ``Current.Mdoc.ZeroKnowledge.honest,
      ``Current.Mdoc.ZeroKnowledge.simulate, ``Current.Mdoc.ZeroKnowledge.window,
      ``MdocWitness.HashValid, ``MdocIdentifiers.fragmentId]),
  (``Current.Mdoc.Completeness.some_accepts,
    [``Current.Mdoc.Completeness.prove, ``Current.Mdoc.Completeness.verify, ``StrandVerifier.verify,
      ``ZeroKnowledge.StrandCanonicalExecution.rawReal,
      ``MdocWitness.HashValid, ``ZeroKnowledge.Frontend.CompleteHonest.primeInputs]),
  (``Current.Mdoc.Completeness.accepts,
    [``Current.Mdoc.Completeness.prove, ``Current.Mdoc.Completeness.verify, ``StrandVerifier.verify,
      ``Current.Mdoc.Completeness.Sampled, ``TranscriptV2.StrandVerifier.sampled,
      ``MdocWitness.HashValid, ``ZeroKnowledge.Frontend.CompleteHonest.primeInputs]),
  -- The deployed corollaries must reach the Rust reader itself: its lazy
  -- block reading, its role programs and the exact draws.
  (``Current.Mdoc.Soundness.averaged_ratio_le_rust,
    [``Current.Mdoc.Soundness.event, ``Current.Mdoc.Soundness.extract, ``Soundness.Rate7.failureBound,
      ``Protocol.RustSampler.sampler, ``Protocol.RustSampler.lazySampler,
      ``Protocol.RustSampler.kindProg, ``Protocol.RustSampler.gfBits, ``Protocol.RustSampler.fp,
      ``Protocol.RustSampler.fpNonzero, ``Protocol.RustSampler.natDec,
      ``Protocol.RustSampler.Prog.choices, ``OpeningFisherYates.ordered,
      ``Protocol.RustSampler.rustBlocks]),
  (``Current.Mdoc.ZeroKnowledge.statClose_rust,
    [``Current.Mdoc.ZeroKnowledge.honest, ``Current.Mdoc.ZeroKnowledge.simulate,
      ``Protocol.RustSampler.lazySampler, ``Protocol.RustSampler.kindProg,
      ``Protocol.RustSampler.rustBlocks]),
  (``Current.Mdoc.VerifierPrivacy.acceptance_probability_rust,
    [``Current.Mdoc.VerifierPrivacy.afterVerifier, ``Protocol.RustSampler.lazySampler,
      ``Protocol.RustSampler.kindProg, ``Protocol.RustSampler.rustBlocks]),
  (``Current.Mdoc.Completeness.accepts_rust,
    [``Current.Mdoc.Completeness.prove, ``Current.Mdoc.Completeness.verify,
      ``Protocol.RustSampler.prfWindow, ``Protocol.RustSampler.lazySampler,
      ``Protocol.RustSampler.kindProg, ``Protocol.RustSampler.rustBlocks])]

/-- The unique decoder that the soundness extractor `Mdoc.Soundness.extract`
must reach: Polygero's transcript-assisted scan and its row-wise decoding on
the good columns. -/
def uniqueDecoder : List Name := [
  ``RecursivePolygero.scanRecoverAt, ``RecursivePolygero.recoverOnAt,
  ``Application.StatementData.recover]

/-- What the extractor must not reach: the commitment-only candidate list and
its fixed-size enumeration, the outside-list event, fingerprint selection from
the list, and the list cutoffs and list-size caps of the certificate. The
extractor reaches the certificate's structure for the code geometry
(`n`, `k`, `s`, `t`), but reads none of these fields. -/
def listDecoding : List Name := [
  ``RecursivePolygero.Counting.committedCandidates, ``RecursivePolygero.Counting.committedCandidate,
  ``RecursivePolygero.NonrecursiveFS.decodedOutsideList,
  ``Selection.Context.extract, ``WitnessSelection.select,
  ``Application.Authentication.context, ``Application.Authentication.BackendBad,
  ``CertifiedProfile.cutoff, ``CertifiedProfile.binaryCutoff, ``CertifiedProfile.primeCutoff,
  ``CertifiedProfile.binaryList, ``CertifiedProfile.primeList,
  ``CertifiedProfile.activeCutoff, ``CertifiedProfile.activeList,
  ``RecursivePolygero.HahnSystemCertificate.listBound,
  -- Removed list-search extractor; kept so that it cannot return.
  `LfzkV2.Current.Soundness.Runtime.candidates]

/-- What the extractor must not reach, since it takes no oracle: the oracle
and observation of the soundness experiment, the setup slice it hashes, the
raw SHA table, the verifier's replay, decoding and decision on an observation,
and the experiment's row trace. -/
def straightLine : List Name := [
  ``Current.Mdoc.OracleSoundness.sha, ``Current.Mdoc.OracleSoundness.observation,
  ``Current.Mdoc.OracleSoundness.inside, ``Current.Mdoc.OracleSoundness.identifiers,
  ``Current.Mdoc.RuntimeSoundness.Raw, ``Current.Mdoc.RuntimeSoundness.observation,
  ``Soundness.OracleTransport.rawSHA, ``Soundness.OracleTransport.rawView,
  ``Soundness.OracleTransport.other, ``StrandAuthentication.replay,
  ``Protocol.Observation.decoded, ``Protocol.Observation.decision,
  ``Soundness.Runtime.viewAuthentication, ``Soundness.Runtime.viewRecover,
  ``Current.Mdoc.Soundness.rowTrace]

run_cmd do
  let env ← getEnv
  let mut changed : Array MessageData := #[]
  for (name, expected) in pinned do
    unless env.contains name do
      throwError "Pinned endpoint {name} no longer exists"
    let (actual, _) := fingerprint env name
    unless actual == expected do
      changed := changed.push m!"{name}: {actual} (pinned {expected})"
  unless changed.isEmpty do
    throwError "Endpoint statements changed; review, then update the pins:\n{MessageData.joinSep changed.toList "\n"}"
  -- Each endpoint's fingerprint must cover the definitions that carry its meaning.
  for (endpoint, requiredList) in required do
    let (_, reached) := fingerprint env endpoint
    for name in requiredList do
      unless reached.contains name do
        throwError "Endpoint fingerprint of {endpoint} does not cover {name}"
  -- Hash separation is a consequence of the circuit types, never a premise.
  for (name, _) in pinned do
    let (_, reached) := fingerprint env name
    if reached.contains ``HashCircuit.ReadDisjoint then
      throwError "Endpoint {name} depends on a read-separation premise"
  -- The soundness extractor decodes uniquely from the transcript, never from a list.
  let (_, reached) := fingerprint env ``Current.Mdoc.Soundness.extract
  for name in uniqueDecoder do
    unless reached.contains name do
      throwError "The soundness extractor does not reach the unique decoder {name}"
  for name in listDecoding do
    if reached.contains name then
      throwError "The soundness extractor reaches the list-decoding definition {name}"
  -- The soundness extractor takes no oracle.
  for name in straightLine do
    if reached.contains name then
      throwError "The soundness extractor reaches {name}"

end LfzkV2.Current.Tests.EndpointStatements
