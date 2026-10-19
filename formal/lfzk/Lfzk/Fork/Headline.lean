import Lfzk.V1StrongV7Hash1HybridHeadline
import Lfzk.Fork.HybridFS

/-! Schedule-dependent bridge for the forked verifier. Generic local
counts, cut-context lemmas, and numerical certificates are reused. -/

/-! Concrete 116-bit T-security for the forked v7 hash1 V1 hybrid FS event. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

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

theorem flatEvent_hybrid_fs_ratio_le_116
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
    (keyBad : ((D × D) × List (Enc × D)) → Coin → Prop)
    (dflt : Coin)
    (hkeyLocal : ∀ κ : ((D × D) × List (Enc × D)),
      (∑ c : Coin, if keyBad κ c then (1 : ℚ) else 0) ≤
        (4 * 2 ^ 128 : ℚ))
    (hC : Fintype.card Coin = 2 ^ 256)
    (hD : Fintype.card D = 2 ^ 256)
    (htA : tA ≤ 2 ^ 116)
    (hfc : fc = 2 * v7Hash1.params.row.n +
      2 * v7SigHahn.params.row.n)
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
      (1 + N + tA : ℚ) / 2 ^ 116 := by
  let P₁ : ∀ σ, Lfzk.RbrZkFlat.TerminalPotential
      ((v7Hash1_flatSide Hside).LD σ) :=
    fun σ => Lfzk.RbrZkFlat.TerminalPotential.coarse
      ((v7Hash1_flatSide Hside).LD σ)
  let P₂ : ∀ σ, Lfzk.RbrZkFlat.TerminalPotential
      (L₂.toZkSide.LD σ) :=
    fun σ => L₂.terminalPotential σ (Lfzk.GradedSignature.curve false)
  let keyBudget : ℚ := 4 * 2 ^ 128
  let β₂c : ℚ := max 0 ((Fintype.card Coin : ℚ) *
    Lfzk.V1StrongV7Hash1HybridNumeric.sigChallenge)
  let β₂q : ℚ := max 0 ((Fintype.card Coin : ℚ) *
    Lfzk.V1StrongV7Hash1HybridNumeric.sigQuery)
  let budget : HashPoint D Coin X Other F Msg₂ → ℚ :=
    twoFieldPotentialBudget keyBudget
      (Lfzk.RbrZkFlat.sideUniformPotentialBudget
        (R := v7Hash1) (logv := 3) (C := Coin) 0 0)
      (Lfzk.RbrZkFlat.sideUniformPotentialBudget
        (R := v7SigHahn) (logv := 8) (C := Coin) β₂c β₂q)
  let betaMax : ℚ := twoFieldPotentialMaxBudget
    v7Hash1 v7SigHahn 3 8 (Fintype.card Coin)
    keyBudget 0 0 β₂c β₂q
  let slotBeta : Fin (1 + Rounds.Role.length v7Hash1.params.nl
      v7Hash1.params.rounds +
      Rounds.Role.length v7SigHahn.params.nl
        v7SigHahn.params.rounds) → ℚ :=
    fun i => twoFieldPotentialSlotBudgetAt
      (R₁ := v7Hash1) (R₂ := v7SigHahn)
      (logv₁ := 3) (logv₂ := 8) (C := Coin)
      keyBudget 0 0 β₂c β₂q i.val
  have hP₂c : ∀ σ, (P₂ σ).challengeBudget ≤ β₂c := by
    intro σ
    exact L₂.terminalPotential_challengeBudget_le_bound σ
      (Lfzk.GradedSignature.curve false)
      Lfzk.V1StrongV7Hash1HybridNumeric.sigChallenge
      (by change Lfzk.GradedSignature.challengeCost false ≤
          v7SigHahn.params.row.fail + v7SigHahn.params.row.arith
          exact Lfzk.GradedSignature.challengeCost_le false)
  have hP₂q : ∀ σ, (P₂ σ).queryBudget ≤ β₂q := by
    intro σ
    exact L₂.terminalPotential_queryBudget_le_bound σ
      (Lfzk.GradedSignature.curve false)
      Lfzk.V1StrongV7Hash1HybridNumeric.sigQuery
      (by change Lfzk.GradedSignature.queryCost false ≤
          v7SigHahn.params.row.cover
          exact Lfzk.GradedSignature.queryCost_le false)
  have hb : ∀ p, 0 ≤ budget p := by
    intro p
    rcases p with p | p | p
    · dsimp [budget, twoFieldPotentialBudget, keyBudget]
      positivity
    · exact Lfzk.RbrZkFlat.sideUniformPotentialBudget_nonneg
        (R := v7Hash1) (logv := 3) (C := Coin) 0 0
        (le_refl _) (le_refl _) p
    · exact Lfzk.RbrZkFlat.sideUniformPotentialBudget_nonneg
        (R := v7SigHahn) (logv := 8) (C := Coin) β₂c β₂q
        (le_max_left _ _) (le_max_left _ _) p
  have hloc : ∀ κ p pref,
      (∑ c : Coin, twoFieldHybridCharge
        (v7Hash1_flatSide Hside) L₂.toZkSide P₁ P₂
        keyBad dflt κ p pref c) ≤ budget p := by
    intro κ p pref
    exact twoFieldHybridCharge_local_coarse_first
      (v7Hash1_flatSide Hside) L₂.toZkSide
      Hside.hF L₂.hF P₂ keyBad dflt keyBudget hkeyLocal
      β₂c β₂q (le_max_left _ _) (le_max_left _ _)
      hP₂c hP₂q κ p pref
  have hm : 0 ≤ betaMax := by
    dsimp [betaMax, twoFieldPotentialMaxBudget]
    exact le_trans (by positivity : (0 : ℚ) ≤ keyBudget)
      (le_max_left _ _)
  have hmax : ∀ p, budget p ≤ betaMax := by
    intro p
    exact twoFieldPotentialBudget_le_max
      (R₁ := v7Hash1) (R₂ := v7SigHahn)
      (logv₁ := 3) (logv₂ := 8) (C := Coin)
      keyBudget 0 0 β₂c β₂q p
  have hslot : ∀ out i,
      budget (Lfzk.Fork.Transcript.hash2 rootOf₁ rootOf₂ avOf pubOf
        msgOf₁ msgOf₂ out i.val) ≤ slotBeta i := by
    intro out i
    apply le_of_eq
    dsimp only [budget, slotBeta]
    unfold Lfzk.Fork.Transcript.hash2 twoFieldPotentialSlotBudgetAt
    split_ifs <;>
      simp only [twoFieldPotentialBudget, Lfzk.RbrZkFlat.sideUniformPotentialBudget_eq_role,
        Lfzk.NizkDeployedHash.msgPoint]

  have h := Lfzk.Fork.HybridFS.flatEvent_hybrid_fs_ratio_le
    Hside L₂ baseNodes responseNodes body rootOf₁ rootOf₂ avOf pubOf
    msgOf₁ msgOf₂ claimOf₁ claimOf₂ common₁ common₂ check
    hcheck₁ hcheck₂ responseOf wellFormed hresponse hdecode
    P₁ P₂ keyBad dflt budget hb hloc betaMax hm hmax
    slotBeta hslot ht hF hTM hwell hkey
  have hsum : (∑ i, slotBeta i) =
      twoFieldPotentialTotalBudget v7Hash1 v7SigHahn 3 8
        (Fintype.card Coin) keyBudget 0 0 β₂c β₂q := by
    exact twoFieldPotentialSlotBudgetAt_sum
      (R₁ := v7Hash1) (R₂ := v7SigHahn)
      (logv₁ := 3) (logv₂ := 8) (C := Coin)
      keyBudget 0 0 β₂c β₂q
  have hn := Lfzk.V1StrongV7Hash1HybridNumeric.hybridBudget_rhs_le_116
    N tA htA
  rw [← Lfzk.V1StrongV7Hash1HybridNumeric.hybridBudget_eq_role N] at hn
  have hc : 0 ≤ (2 ^ 256 : ℚ) *
      Lfzk.V1StrongV7Hash1HybridNumeric.sigChallenge :=
    mul_nonneg (by positivity) (add_nonneg
      (Lfzk.LigeroV1LayerStep.fail_nonneg _) (Lfzk.LigeroV1LayerStep.arith_nonneg _))
  have hq : 0 ≤ (2 ^ 256 : ℚ) *
      Lfzk.V1StrongV7Hash1HybridNumeric.sigQuery :=
    mul_nonneg (by positivity) (Lfzk.LigeroV1LayerStep.cover_nonneg _)
  have hcost :
      (N * betaMax + ∑ i, slotBeta i) / Fintype.card Coin +
        2 * (Bcs.AdaptiveCommit.adaptiveNumerator fc tA
          (1 + Rounds.Role.length v7Hash1.params.nl
            v7Hash1.params.rounds +
            Rounds.Role.length v7SigHahn.params.nl
              v7SigHahn.params.rounds + N) : ℚ) / Fintype.card D +
        (N + 1 : ℕ) * density 0 ≤
          (1 + N + tA : ℚ) / 2 ^ 116 := by
    have hfc' : fc =
        Lfzk.V1StrongV7Hash1HybridNumeric.fc := by
      simpa only [Lfzk.V1StrongV7Hash1HybridNumeric.fc] using hfc
    rw [hsum]
    dsimp only [betaMax, keyBudget, β₂c, β₂q]
    rw [hC, hD, hfc']
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    rw [max_eq_right hc, max_eq_right hq]
    convert hn using 1
    simp only [Lfzk.V1StrongV7Hash1HybridNumeric.L,
      Lfzk.NizkAdaptiveTwoField.len2]
    ring
  dsimp only at h ⊢
  exact h.trans hcost

end Lfzk.Fork.HybridFS
