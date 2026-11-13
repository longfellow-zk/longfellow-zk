import LfzkV2.Current.Mdoc.Soundness
import LfzkV2.Current.Mdoc.ZeroKnowledge

/-! Pin the exact statements of the public endpoints. Each fingerprint hashes
an endpoint's type together with the type and body of every project
definition it depends on, transitively; proofs and external libraries are
excluded. Any change to what an endpoint states, including a change to a
definition it mentions, fails this module until the pinned value is updated
after review. Axiom and connectivity checks live in `Tests.MdocSoundness`. -/
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
  (``Current.Mdoc.Soundness.ratio_le, 2320960330717783613),
  (``Current.Mdoc.Soundness.linear_ratio_le, 4794053449157163209),
  (``Current.Mdoc.Soundness.averaged_ratio_le, 8171944902145713937),
  (``Current.Mdoc.Soundness.averaged_linear_ratio_le, 13806769135036279007),
  (``Current.Mdoc.Soundness.averaged_nonvacuous, 15946407965016625641),
  (``Current.Mdoc.Soundness.averaged_polynomial_ratio_le, 9926718859704130105),
  (``Current.Mdoc.Soundness.averaged_mdoc_approximation, 4182175844650144754),
  (``Current.Mdoc.ZeroKnowledge.statClose, 5356686738951577342),
  (``Current.Mdoc.ZeroKnowledge.statClose_at_query_budget, 6755905065642033840)]

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
  -- The fingerprint must cover the definitions that carry the meaning.
  let (_, reached) := fingerprint env ``Current.Mdoc.Soundness.averaged_ratio_le
  for required in [``Soundness.Rate7.failureBound, ``Soundness.Rate7.polygeroConstant,
      ``Current.Mdoc.Soundness.event, ``Current.Mdoc.Soundness.Valid,
      ``Current.Mdoc.Soundness.extract, ``MdocWitness.HashValid, ``MdocWitness.ReadDisjoint] do
    unless reached.contains required do
      throwError "Endpoint fingerprint does not cover {required}"

end LfzkV2.Current.Tests.EndpointStatements
