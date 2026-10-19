import Lfzk.V1StrongV7Hash1HybridFS
import Lfzk.Fork.HybridPath

/-! Schedule-dependent bridge for the forked verifier. Generic local
counts, cut-context lemmas, and numerical certificates are reused. -/

/-! The direct V1 terminal bound and the field-only hybrid potential apply
to the same forked v7 hash1 extraction-failure event. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 500000

namespace Lfzk.Fork.HybridFS

open Lfzk.V1StrongV7Hash1HybridFS

open Finset LigeroFamily Lfzk.CertifiedV1 Lfzk.V1StrongV7Numeric
  Lfzk.CompiledZk Lfzk.CompiledZk.FlatV7Deployed
  Lfzk.CompiledZk.FlatV7Radius
  Lfzk.NizkDeployedHashTwoField Lfzk.NizkZkDeployedHash
open Merkle.MH Merkle.RandomOracle
open Lfzk.CompiledLongfellow (Col)
open scoped Classical

private abbrev HashPoint (D Coin X Other F Msg₂ : Type) :=
  Lfzk.V1StrongV7TwoSideFinal.Point 0 D Coin X Other F Msg₂
    v7Hash1.params.nl v7SigHahn.params.nl
    v7Hash1.params.rounds v7SigHahn.params.rounds

/-- Extraction-first bound for the actual forked v7 hash1 flat event.
The hash-side V1 terminal probability is the direct two-coordinate count;
only field-prefix escapes remain in the graded FS potential. -/
theorem flatEvent_hybrid_fs_ratio_le
    {Coin F Other Enc D Salt₁ Salt₂ X Msg₂ Witness₂ Out Fmac : Type}
    [Fintype Coin] [DecidableEq Coin] [Inhabited Coin] [Nonempty Coin]
    [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype D] [DecidableEq D] [Inhabited D]
    [Fintype X] [DecidableEq X]
    [Fintype Other] [DecidableEq Other] [Inhabited Other]
    [Fintype Msg₂] [DecidableEq Msg₂] [Inhabited Msg₂]
    [DecidableEq Enc] [Inhabited Salt₁] [Inhabited Salt₂]
    [Field Fmac] [Fintype Fmac] [DecidableEq Fmac]
    {F₂ : Type} [Field F₂] [Fintype F₂] [DecidableEq F₂]
    [SumcheckInterp F₂]
    {M nt nlin M₂ ninp₂ nt₂ nlin₂ logw₂ logc₂ nblk tA N TM fc : ℕ}
    {codec₁ : Codec Salt₁ (Col F v7Hash1.params.nw v7Hash1.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7SigHahn.params.nw v7SigHahn.params.nq)
      D Enc}
    {dec₂ : RoleDecoders codec₂}
    (Hside : CircuitSide v7Hash1 v7Hash1_valid v7Hash1_openings_pos
      3 Coin F
      (Lfzk.LigeroTranscriptInputs.Message
        (Other := Other) (F := F)
        (block := (row (0 : Fin 4)).k)
        (dblock := 2 * (row (0 : Fin 4)).k - 1)
        (r := (row (0 : Fin 4)).openings))
      M nt nlin X dec₁ Prod.fst)
    (L₂ : CompiledZkSide v7SigHahn v7SigHahn_valid
      v7SigHahn_openings_pos 8 Coin F₂ Msg₂ Witness₂
      M₂ ninp₂ nt₂ nlin₂ logw₂ logc₂ X dec₂ Prod.snd)
    (baseNodes : Fin (row (0 : Fin 4)).k ↪
      Position (row (0 : Fin 4)).openings v7Hash1.params.q
        (row (0 : Fin 4)).n)
    (responseNodes : Fin (2 * (row (0 : Fin 4)).k - 1) ↪
      Position (row (0 : Fin 4)).openings v7Hash1.params.q
        (row (0 : Fin 4)).n)
    (body : TwoOracleTree Enc D (HashPoint D Coin X Other F Msg₂)
      Coin Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → Coin) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Lfzk.LigeroTranscriptInputs.Message
      (Other := Other) (F := F)
      (block := (row (0 : Fin 4)).k)
      (dblock := 2 * (row (0 : Fin 4)).k - 1)
      (r := (row (0 : Fin 4)).openings))
    (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7Hash1.params.row.n Salt₁
      (Col F v7Hash1.params.nw v7Hash1.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7SigHahn.params.row.n Salt₂
      (Col F₂ v7SigHahn.params.nw v7SigHahn.params.nq) D)
    (common₁ : (Fin Hside.c.ninp → F) → Fin nblk → Fmac)
    (common₂ : Witness₂ → Fin nblk → Fmac)
    (check : Out → Merkle.RandomOracle.Tree Enc D Unit fc)
    (hcheck₁ : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec₁ v7Hash1.params.row.n
          (claimOf₁ out).I (claimOf₁ out).a
          (claimOf₁ out).pf (2 * v7Hash1.params.row.n)
          fun _ => default).run H).2,
        qa ∈ ((check out).run H).2)
    (hcheck₂ : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec₂ v7SigHahn.params.row.n
          (claimOf₂ out).I (claimOf₂ out).a
          (claimOf₂ out).pf (2 * v7SigHahn.params.row.n)
          fun _ => default).run H).2,
        qa ∈ ((check out).run H).2)
    (responseOf : Out → Lfzk.V1StrongV7Terminal.Payload 0 F)
    (wellFormed : Out → Prop)
    (hresponse : ∀ out, wellFormed out →
      msgOf₁ out (Rounds.Role.layerBase v7Hash1.params.rounds
        v7Hash1.params.nl + 2) = Sum.inr (responseOf out))
    (hdecode : ∀ out, wellFormed out →
      Hside.respOf (Sum.inr (responseOf out)) =
        Lfzk.V1StrongV7Terminal.decodePayload 0 Hside.dom
          baseNodes responseNodes (responseOf out))
    (P₁ : ∀ σ, Lfzk.RbrZkFlat.TerminalPotential
      ((v7Hash1_flatSide Hside).LD σ))
    (P₂ : ∀ σ, Lfzk.RbrZkFlat.TerminalPotential
      (L₂.toZkSide.LD σ))
    (keyBad : ((D × D) × List (Enc × D)) → Coin → Prop)
    (dflt : Coin)
    (budget : HashPoint D Coin X Other F Msg₂ → ℚ)
    (hbudget : ∀ p, 0 ≤ budget p)
    (hlocal : ∀ κ p pref,
      (∑ c : Coin, twoFieldHybridCharge
        (v7Hash1_flatSide Hside) L₂.toZkSide P₁ P₂
        keyBad dflt κ p pref c) ≤ budget p)
    (betaMax : ℚ) (hbetaMax : 0 ≤ betaMax)
    (hmax : ∀ p, budget p ≤ betaMax)
    (slotBeta : Fin (1 + Rounds.Role.length v7Hash1.params.nl
      v7Hash1.params.rounds +
      Rounds.Role.length v7SigHahn.params.nl v7SigHahn.params.rounds) → ℚ)
    (hslot : ∀ out i,
      budget (Lfzk.Fork.Transcript.hash2 rootOf₁ rootOf₂ avOf pubOf
        msgOf₁ msgOf₂ out i.val) ≤ slotBeta i)
    (ht : tA ≤ TM) (hF : fc + tA ≤ TM) (hTM : 1 ≤ TM)
    (hwell : ∀ (mt : Fin TM → D)
      (ro : HashPoint D Coin X Other F Msg₂ → Coin),
      let Ssetup := Lfzk.Fork.Transcript.setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      v7Hash1_flatEvent Hside L₂ rootOf₁ rootOf₂ avOf pubOf
        msgOf₁ msgOf₂ claimOf₁ claimOf₂ common₁ common₂
        (Ssetup.context mt ro) (Ssetup.merkleOracle check mt ro)
        (Ssetup.proof mt ro) (Ssetup.challenges mt ro) →
      wellFormed (Ssetup.proof mt ro))
    (hkey : ∀ (mt : Fin TM → D)
      (ro : HashPoint D Coin X Other F Msg₂ → Coin),
      let Ssetup := Lfzk.Fork.Transcript.setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      let out := Ssetup.proof mt ro
      let σ := (Ssetup.context mt ro, avOf out, pubOf out)
      v7Hash1_flatEvent Hside L₂ rootOf₁ rootOf₂ avOf pubOf
        msgOf₁ msgOf₂ claimOf₁ claimOf₂ common₁ common₂
        (Ssetup.context mt ro) (Ssetup.merkleOracle check mt ro)
        out (Ssetup.challenges mt ro) →
      ¬ Lfzk.NizkZk.ZkFails (v7Hash1_flatSide Hside).Sat σ →
      ¬ Lfzk.NizkZk.ZkFails L₂.toZkSide.Sat σ →
      keyBad (Ssetup.context mt ro)
        (ro (Sum.inl (rootOf₁ out, rootOf₂ out)))) :
    let Ssetup := Lfzk.Fork.Transcript.setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
    let Acc := fun (mt : Fin TM → D)
        (ro : HashPoint D Coin X Other F Msg₂ → Coin) =>
      v7Hash1_flatEvent Hside L₂ rootOf₁ rootOf₂ avOf pubOf
        msgOf₁ msgOf₂ claimOf₁ claimOf₂ common₁ common₂
        (Ssetup.context mt ro) (Ssetup.merkleOracle check mt ro)
        (Ssetup.proof mt ro) (Ssetup.challenges mt ro)
    ((univ.filter fun ω : (Fin TM → D) ×
        (HashPoint D Coin X Other F Msg₂ → Coin) =>
          Acc ω.1 ω.2).card : ℚ) /
      ((Fintype.card D : ℚ) ^ TM *
        (Fintype.card Coin : ℚ) ^
          Fintype.card (HashPoint D Coin X Other F Msg₂)) ≤
      (N * betaMax + ∑ i, slotBeta i) / Fintype.card Coin +
        2 * (Bcs.AdaptiveCommit.adaptiveNumerator fc tA
          (1 + Rounds.Role.length v7Hash1.params.nl
            v7Hash1.params.rounds +
            Rounds.Role.length v7SigHahn.params.nl
              v7SigHahn.params.rounds + N) : ℚ) / Fintype.card D +
        (N + 1 : ℕ) * density 0 := by
  let Ssetup := Lfzk.Fork.Transcript.setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
  let Acc := fun (mt : Fin TM → D)
      (ro : HashPoint D Coin X Other F Msg₂ → Coin) =>
    v7Hash1_flatEvent Hside L₂ rootOf₁ rootOf₂ avOf pubOf
      msgOf₁ msgOf₂ claimOf₁ claimOf₂ common₁ common₂
      (Ssetup.context mt ro) (Ssetup.merkleOracle check mt ro)
      (Ssetup.proof mt ro) (Ssetup.challenges mt ro)
  let selected := Lfzk.LigeroPairGeometry.selectedFromOutput
    (nl := v7Hash1.params.nl) (w := v7Hash1.params.rounds)
    (ctxOf rootOf₁ rootOf₂ avOf pubOf) msgOf₁ responseOf
  let terminal := fun (mt : Fin TM → D)
      (ro : HashPoint D Coin X Other F Msg₂ → Coin) =>
    let out := Ssetup.proof mt ro
    let pr := selected out
    let st := Lfzk.V1StrongV7TwoSideCutContext.cutState Ssetup mt pr.1 ro
    Lfzk.V1StrongV7Hash1Local.terminalFailureAt
      Hside baseNodes responseNodes st pr.1 (wellFormed out)
      (ro (Lfzk.Fork.Transcript.hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out
        (1 + (Rounds.Role.layerBase v7Hash1.params.rounds
          v7Hash1.params.nl + 1))))
      pr.2
      (ro (Lfzk.Fork.Transcript.hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out
        (1 + (Rounds.Role.layerBase v7Hash1.params.rounds
          v7Hash1.params.nl + 2))))
  have hterminal :
      ((univ.filter fun ω : (Fin TM → D) ×
          (HashPoint D Coin X Other F Msg₂ → Coin) =>
        terminal ω.1 ω.2).card : ℚ) /
        ((Fintype.card D : ℚ) ^ TM *
          (Fintype.card Coin : ℚ) ^
            Fintype.card (HashPoint D Coin X Other F Msg₂)) ≤
        (N + 1 : ℕ) * density 0 := by
    simpa only [terminal, selected, Ssetup] using
      Lfzk.Fork.JointBound.hash1_cut_failure_joint_le
        Hside baseNodes responseNodes body rootOf₁ rootOf₂ avOf pubOf
        msgOf₁ msgOf₂ responseOf wellFormed hresponse
  have hroot₁ : ∀ out, (Ssetup.keyOut out).1 = rootOf₁ out := fun _ => rfl
  have hroot₂ : ∀ out, (Ssetup.keyOut out).2 = rootOf₂ out := fun _ => rfl
  have hm₁ : ∀ mt ro, Acc mt ro →
      Ssetup.MerkleAccepts codec₁ check Prod.fst claimOf₁ mt ro := by
    intro mt ro ha
    have hh := (v7Hash1_flatEvent_actual_iff Hside L₂ Ssetup
      rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂
      common₁ common₂ check mt ro).mp ha
    exact Hside.toSide.acceptsDH_merkle Ssetup check rootOf₁ hroot₁
      msgOf₁ claimOf₁ avOf pubOf (Lfzk.CompiledLongfellowAdaptive.slice1
        v7Hash1 v7SigHahn) mt ro hh.1
  have hm₂ : ∀ mt ro, Acc mt ro →
      Ssetup.MerkleAccepts codec₂ check Prod.snd claimOf₂ mt ro := by
    intro mt ro ha
    have hh := (v7Hash1_flatEvent_actual_iff Hside L₂ Ssetup
      rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂
      common₁ common₂ check mt ro).mp ha
    exact L₂.acceptsDH_merkle Ssetup check rootOf₂ hroot₂
      msgOf₂ claimOf₂ avOf pubOf (Lfzk.CompiledLongfellowAdaptive.slice2
        v7Hash1 v7SigHahn) mt ro hh.2.1
  have hpath : ∀ mt ro, Acc mt ro → ¬ terminal mt ro →
      Ssetup.Explains dec₁ Prod.fst claimOf₁ mt ro →
      Ssetup.Explains dec₂ Prod.snd claimOf₂ mt ro →
      (none : Option Unit) = none →
      let out := Ssetup.proof mt ro
      1 ≤ ∑ i : Fin (1 + Rounds.Role.length v7Hash1.params.nl
          v7Hash1.params.rounds +
          Rounds.Role.length v7SigHahn.params.nl v7SigHahn.params.rounds),
        twoFieldHybridCharge (v7Hash1_flatSide Hside) L₂.toZkSide
          P₁ P₂ keyBad dflt (Ssetup.context mt ro)
          (Ssetup.hashInput out i.val)
          (pts2.chal ro (Ssetup.hashInput out i.val))
          (ro (Ssetup.hashInput out i.val)) := by
    intro mt ro ha hn he₁ he₂ _
    exact Lfzk.Fork.HybridPath.flatEvent_pays_outside_terminal
      Hside L₂ baseNodes responseNodes body rootOf₁ rootOf₂ avOf pubOf
      msgOf₁ msgOf₂ claimOf₁ claimOf₂ common₁ common₂ check
      responseOf wellFormed hresponse hdecode P₁ P₂ keyBad dflt
      mt ro ha he₁ he₂ (hwell mt ro ha) (hkey mt ro ha) hn
  have houtside := Lfzk.Fork.PotentialFS.twoFieldHybrid_fs_extraction_outside
    body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
    (v7Hash1_flatSide Hside) L₂.toZkSide P₁ P₂ keyBad dflt
    codec₁ dec₁ codec₂ dec₂ check claimOf₁ claimOf₂ hcheck₁ hcheck₂
    budget hbudget hlocal betaMax hbetaMax hmax slotBeta hslot
    ht hF hTM Acc terminal (fun _ _ => (none : Option Unit))
    hm₁ hm₂ hpath
  have hden : (0 : ℚ) <
      (Fintype.card D : ℚ) ^ TM *
        (Fintype.card Coin : ℚ) ^
          Fintype.card (HashPoint D Coin X Other F Msg₂) := by
    have hd : (0 : ℚ) < Fintype.card D := by exact_mod_cast Fintype.card_pos
    have hc : (0 : ℚ) < Fintype.card Coin := by exact_mod_cast Fintype.card_pos
    exact mul_pos (pow_pos hd _) (pow_pos hc _)
  have hcover : ∀ ω : (Fin TM → D) ×
      (HashPoint D Coin X Other F Msg₂ → Coin),
      Acc ω.1 ω.2 →
        (Acc ω.1 ω.2 ∧ ¬ terminal ω.1 ω.2) ∨
          terminal ω.1 ω.2 := by
    intro ω ha
    by_cases ht' : terminal ω.1 ω.2
    · exact Or.inr ht'
    · exact Or.inl ⟨ha, ht'⟩
  have h := Lfzk.V1StrongV7Hash1JointBound.ratio_le_of_cover
    (fun ω : (Fin TM → D) ×
      (HashPoint D Coin X Other F Msg₂ → Coin) => Acc ω.1 ω.2)
    (fun ω => Acc ω.1 ω.2 ∧ ¬ terminal ω.1 ω.2)
    (fun ω => terminal ω.1 ω.2)
    ((Fintype.card D : ℚ) ^ TM *
      (Fintype.card Coin : ℚ) ^
        Fintype.card (HashPoint D Coin X Other F Msg₂))
    ((N * betaMax + ∑ i, slotBeta i) / Fintype.card Coin +
      2 * (Bcs.AdaptiveCommit.adaptiveNumerator fc tA
        (1 + Rounds.Role.length v7Hash1.params.nl
          v7Hash1.params.rounds +
          Rounds.Role.length v7SigHahn.params.nl
            v7SigHahn.params.rounds + N) : ℚ) / Fintype.card D)
    ((N + 1 : ℕ) * density 0)
    hden hcover (by
      simpa only [and_true, HashPoint,
        Lfzk.V1StrongV7TwoSideFinal.Point,
        Lfzk.LigeroPairGeometryTwoSide.Point] using houtside) hterminal
  simpa only [Acc, Ssetup] using h

end Lfzk.Fork.HybridFS
