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
that carry its meaning (`required`). Axiom and connectivity
checks live in `Tests.MdocSoundness`. -/
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
  (``Current.Mdoc.Soundness.ratio_le, 12513049308035022),
  (``Current.Mdoc.Soundness.linear_ratio_le, 8149359971269711468),
  (``Current.Mdoc.Soundness.averaged_ratio_le, 1343762886749493020),
  (``Current.Mdoc.Soundness.averaged_linear_ratio_le, 2199048693965618856),
  (``Current.Mdoc.Soundness.averaged_nonvacuous, 15240982601471283804),
  (``Current.Mdoc.Soundness.averaged_polynomial_ratio_le, 327645463245882727),
  (``Current.Mdoc.Soundness.averaged_mdoc_approximation, 5162694118443197585),
  (``Current.Mdoc.ZeroKnowledge.statClose, 11089277535653201106),
  (``Current.Mdoc.ZeroKnowledge.statClose_at_query_budget, 3608117319759410495),
  (``Current.Mdoc.VerifierPrivacy.acceptance_probability, 17334613443263901531),
  (``Current.Mdoc.Completeness.some_accepts, 4494509276498619142),
  (``Current.Mdoc.Completeness.accepts, 14703360873936376765),
  (``Current.Mdoc.Completeness.accepts_rust, 7576761460556919049),
  (``Current.Mdoc.Soundness.averaged_ratio_le_rust, 10790887318093611518),
  (``Current.Mdoc.ZeroKnowledge.statClose_rust, 9355581669937741965),
  (``Current.Mdoc.VerifierPrivacy.acceptance_probability_rust, 11679471597644133134)]

/-- Definitions each endpoint must reach: its event or experiment, its
witness premises, the setup it is stated for and, for a deployed corollary,
the Rust reader. -/
def required : List (Name × List Name) := [
  (``Current.Mdoc.Soundness.averaged_ratio_le,
    [``Soundness.Rate7.failureBound, ``Soundness.Rate7.polygeroConstant,
      ``Current.Mdoc.Soundness.event, ``Current.Mdoc.Soundness.Valid,
      ``Current.Mdoc.Soundness.extract, ``MdocWitness.HashValid, ``MdocWitness.HashChecks,
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
    [``Current.Mdoc.Soundness.event, ``Soundness.Rate7.failureBound,
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

end LfzkV2.Current.Tests.EndpointStatements
