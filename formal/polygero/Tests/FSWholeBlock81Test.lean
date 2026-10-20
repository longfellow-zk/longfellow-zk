import polygero.Instances.FSWholeBlock81
import polygero.Tests.FSBaselinePriceTest
import polygero.Tests.FSTerminalBlockTest
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-! Complete 81/80 refinement: actual parent spectra, actual whole-child
unit coverage, disjoint-domain composition, and false-statement transfer. -/
open Lean Elab Command

run_cmd do
  let env ← getEnv
  for (name, deps) in #[
      (``RecursivePolygero.FiatShamir.TwoLevel.whole_block_oracle_sound, #[
        ``Bcs.AffineBlock.oracle_parallel_certificate]),
      (``RecursivePolygero.FiatShamir.TwoLevel.whole_block_affine_bound, #[
        ``RecursivePolygero.FiatShamir.TwoLevel.whole_block_oracle_sound]),
      (``RecursivePolygero.FiatShamir.TwoLevel.whole_block_soundness_bound, #[
        ``RecursivePolygero.FiatShamir.TwoLevel.whole_block_affine_bound,
        ``RecursivePolygero.FiatShamir.TwoLevel.failure_empty_iff]),
      (``RecursivePolygero.Instances.FSWholeBlock81.certificate_with_cutoff, #[
        ``CodingTheory.IntegerOccupancy.uniformFamilyBound,
        ``RecursivePolygero.HahnSystemCertificate.ofUniformFamilyBound]),
      (``RecursivePolygero.Instances.FSWholeBlock81.certifiedAffineFS, #[
        ``RecursivePolygero.Instances.FSWholeBlock81.certificate_with_cutoff,
        ``RecursivePolygero.Instances.FSBaselinePrice.query_oracle_sound,
        ``RecursivePolygero.Instances.FSNonuniformSpectrum.query_oracle_sound,
        ``RecursivePolygero.FiatShamir.TwoLevel.child_block_oracle_sound_fixed,
        ``RecursivePolygero.FiatShamir.TwoLevel.whole_block_affine_bound]),
      (``RecursivePolygero.Instances.FSWholeBlock81.certifiedFS, #[
        ``RecursivePolygero.Instances.FSWholeBlock81.certifiedAffineFS]),
      (``RecursivePolygero.Instances.FSWholeBlock81.certifiedSoundness, #[
        ``RecursivePolygero.Instances.FSWholeBlock81.certifiedFS,
        ``RecursivePolygero.FiatShamir.TwoLevel.failure_empty_iff])] do
    let some info := env.find? name | throwError "Missing theorem {name}"
    for dep in deps do
      unless info.getUsedConstantsAsSet.contains dep do
        throwError "{name} omits actual dependency {dep}"
  for (name, info) in env.constants.toList do
    let owner := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => env.mainModule
    unless #[`polygero.Recursion.FSWholeBlock,
      `polygero.Instances.FSBaselinePrice,
      `polygero.Instances.FSWholeBlock81].contains owner do continue
    if info.isAxiom then throwError "Unexpected axiom declaration {name}"
    for ax in ← collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {name}"
