import Lfzk.AffineBlockInstances
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-! The adapters must use the existing endpoints and introduce no new
axioms beyond their numerical trust base and ordinary kernel axioms. -/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  for (adapter, original) in #[
      (``Lfzk.AffineBlockInstances.ligero_affine_certificate,
       ``Lfzk.V1StrongV7TranscriptOutsideFinal.v7_v1_transcript_outside_final_le),
      (``Lfzk.CompiledZk.AffineBlockInstances.lfzk_affine_certificate,
       ``Lfzk.CompiledZk.FlatV7Headline.v7Hash1_deployed_fs_extraction_116_circuit)] do
    let some info := env.find? adapter | throwError "Missing adapter {adapter}"
    unless info.getUsedConstantsAsSet.contains original do
      throwError "Adapter {adapter} does not call {original}"
    let inherited ← collectAxioms original
    for ax in ← collectAxioms adapter do
      if ax == ``sorryAx then throwError "Unfinished proof in {adapter}"
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound ||
          inherited.contains ax do
        throwError "New axiom {ax} in adapter {adapter}"
