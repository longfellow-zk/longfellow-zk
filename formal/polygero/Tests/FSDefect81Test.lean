import polygero.Instances.FSDefect81
import polygero.Tests.FSWholeBlock81Test
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-! Audit the complete clean126 theorem and its actual algebra/compiler
path, including every private declaration owned by the benchmark module. -/
open Lean Elab Command

run_cmd do
  let env ← getEnv
  for (name,deps) in #[
      (``RecursivePolygero.Instances.FSDefect81.actual_iop_error, #[
        ``RecursivePolygero.HahnSystemCertificate.error]),
      (``RecursivePolygero.Instances.FSDefect81.certifiedAffineFS, #[
        ``RecursivePolygero.Instances.FSWholeBlock81.certificate_with_cutoff,
        ``RecursivePolygero.Instances.FSDefectSpectrum.query_oracle_sound,
        ``RecursivePolygero.FiatShamir.TwoLevel.child_block_oracle_sound_fixed,
        ``RecursivePolygero.FiatShamir.TwoLevel.whole_block_affine_bound]),
      (``RecursivePolygero.Instances.FSDefect81.certifiedFS, #[
        ``RecursivePolygero.Instances.FSDefect81.certifiedAffineFS]),
      (``RecursivePolygero.Instances.FSDefect81.certifiedSoundness, #[
        ``RecursivePolygero.Instances.FSDefect81.certifiedFS,
        ``RecursivePolygero.FiatShamir.TwoLevel.failure_empty_iff]),
      (``RecursivePolygero.Instances.FSDefect81.certifiedAffineSoundness, #[
        ``RecursivePolygero.Instances.FSDefect81.certifiedAffineFS,
        ``RecursivePolygero.FiatShamir.TwoLevel.failure_empty_iff]),
      (``RecursivePolygero.Instances.FSDefect81.certifiedSoundness_iop, #[
        ``RecursivePolygero.Instances.FSDefect81.certifiedAffineSoundness,
        ``RecursivePolygero.Instances.FSDefect81.checked_iop_comparison])] do
    let some info := env.find? name | throwError "Missing theorem {name}"
    for dep in deps do
      unless info.getUsedConstantsAsSet.contains dep do
        throwError "{name} omits actual dependency {dep}"
  for (name,info) in env.constants.toList do
    let owner := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => env.mainModule
    unless owner == `polygero.Instances.FSDefect81 do continue
    if info.isAxiom then throwError "Unexpected axiom declaration {name}"
    for ax in ← collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {name}"
