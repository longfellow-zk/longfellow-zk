import Lfzk.V1StrongV7Hash1HybridTypedHeadline
import Lfzk.CompiledZkProfileSepMac

/-! The v7 hash1 hybrid FS bound with both circuit sides and the
merged Merkle checker instantiated. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000

namespace Lfzk.V1StrongV7Hash1HybridFS

open Finset LigeroFamily Lfzk.CertifiedV1 Lfzk.V1StrongV7Numeric
  Lfzk.CompiledZk Lfzk.CompiledZk.FlatV7Deployed
  Lfzk.CompiledZk.FlatV7Radius
  Lfzk.NizkDeployedHashTwoField Lfzk.NizkZkDeployedHash
open Merkle.MH Merkle.RandomOracle
open Lfzk.CompiledLongfellow (Col)
open Lfzk.CompiledLongfellowAdaptive (slice1 slice2)
open Lfzk.NizkAdaptiveTwoField (check2)
open Ligero.Examples.Grid.LongfellowProfiledExtraction
open Lfzk.V1StrongV7Hash1Adapter (withTypedRespOf withTypedRespOf_response)
open Lfzk.LigeroTranscriptInputs (withResponse withResponse_querySlot)
open scoped Classical

private abbrev HashPoint (D Coin X Other F Msg₂ : Type) :=
  Lfzk.V1StrongV7TwoSideFinal.Point 0 D Coin X Other F Msg₂
    v7Hash1.params.nl v7SigHahn.params.nl
    v7Hash1.params.rounds v7SigHahn.params.rounds

private abbrev typedMsg {Other F Out : Type}
    (raw : Out → ℕ → Lfzk.LigeroTranscriptInputs.Message
      (Other := Other) (F := F)
      (block := (row (0 : Fin 4)).k)
      (dblock := 2 * (row (0 : Fin 4)).k - 1)
      (r := (row (0 : Fin 4)).openings))
    (response : Out → Lfzk.V1StrongV7Terminal.Payload 0 F) :
    Out → ℕ → Lfzk.LigeroTranscriptInputs.Message
      (Other := Other) (F := F)
      (block := (row (0 : Fin 4)).k)
      (dblock := 2 * (row (0 : Fin 4)).k - 1)
      (r := (row (0 : Fin 4)).openings) :=
  fun out => withResponse
    (nl := v7Hash1.params.nl) (w := v7Hash1.params.rounds)
    (raw out) (response out)

/-- The all-budget 116-bit bound with the response message and decoder
fixed by the four-slice V1 payload. The remaining hypotheses describe the two
circuits, their MAC rows, and the Merkle tape. -/
theorem flatEvent_hybrid_fs_ratio_le_116_circuit_typed
    {Coin F Other Enc D Salt₁ Salt₂ X Msg₂ Out Fmac : Type}
    [Fintype Coin] [DecidableEq Coin] [Inhabited Coin] [Nonempty Coin]
    [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype D] [DecidableEq D] [Inhabited D]
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Other] [DecidableEq Other] [Inhabited Other]
    [Fintype Msg₂] [DecidableEq Msg₂] [Inhabited Msg₂]
    [DecidableEq Enc] [Inhabited Salt₁] [Inhabited Salt₂]
    [Field Fmac] [Fintype Fmac] [DecidableEq Fmac]
    {F₂ : Type} [Field F₂] [Fintype F₂] [DecidableEq F₂]
    [SumcheckInterp F₂]
    {M nt nlin M₂ nt₂ nlin₂ nblk tA N TM fc : ℕ}
    {codec₁ : Codec Salt₁ (Col F v7Hash1.params.nw v7Hash1.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7SigHahn.params.nw v7SigHahn.params.nq)
      D Enc}
    {dec₂ : RoleDecoders codec₂}
    (Hraw : CircuitSide v7Hash1 v7Hash1_valid v7Hash1_openings_pos
      3 Coin F
      (Lfzk.LigeroTranscriptInputs.Message
        (Other := Other) (F := F)
        (block := (row (0 : Fin 4)).k)
        (dblock := 2 * (row (0 : Fin 4)).k - 1)
        (r := (row (0 : Fin 4)).openings))
      M nt nlin X dec₁ Prod.fst)
    (S₂ : CircuitSide v7SigHahn v7SigHahn_valid
      v7SigHahn_openings_pos 8 Coin F₂ Msg₂
      M₂ nt₂ nlin₂ X dec₂ Prod.snd)
    (baseNodes : Fin (row (0 : Fin 4)).k ↪
      Position (row (0 : Fin 4)).openings v7Hash1.params.q
        (row (0 : Fin 4)).n)
    (responseNodes : Fin (2 * (row (0 : Fin 4)).k - 1) ↪
      Position (row (0 : Fin 4)).openings v7Hash1.params.q
        (row (0 : Fin 4)).n)
    (body : TwoOracleTree Enc D (HashPoint D Coin X Other F Msg₂)
      Coin Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → Coin) (pubOf : Out → X)
    (rawMsgOf₁ : Out → ℕ → Lfzk.LigeroTranscriptInputs.Message
      (Other := Other) (F := F)
      (block := (row (0 : Fin 4)).k)
      (dblock := 2 * (row (0 : Fin 4)).k - 1)
      (r := (row (0 : Fin 4)).openings))
    (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7Hash1.params.row.n Salt₁
      (Col F v7Hash1.params.nw v7Hash1.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7SigHahn.params.row.n Salt₂
      (Col F₂ v7SigHahn.params.nw v7SigHahn.params.nq) D)
    (common₁ : (Fin Hraw.c.ninp → F) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (responseOf : Out → Lfzk.V1StrongV7Terminal.Payload 0 F)
    (aP : ((D × D) × List (Enc × D)) → Fmac)
    (decode : Coin → Fmac) (tagOf : Out → Fin nblk → Fmac)
    (mac₁ : (Fin Hraw.c.ninp → F) → Fmac → Fin nblk → Fmac)
    (mac₂ : (Fin S₂.c.ninp → F₂) → Fmac → Fin nblk → Fmac)
    (hbal : ∀ x : Fmac,
      (univ.filter fun c : Coin => decode c = x).card ≤ 2 ^ 128)
    (hcoll : ∀ a₁ a₂, common₁ a₁ ≠ common₂ a₂ →
      (univ.filter fun x => mac₁ a₁ x = mac₂ a₂ x).card ≤ 1)
    (dflt : Coin)
    (hC : Fintype.card Coin = 2 ^ 256)
    (hD : Fintype.card D = 2 ^ 256)
    (hfc : fc = 2 * v7Hash1.params.row.n +
      2 * v7SigHahn.params.row.n)
    (ht : tA ≤ TM) (hF : fc + tA ≤ TM) (hTM : 1 ≤ TM)
    (hrowSat₁ : ∀ (mt : Fin TM → D)
      (ro : HashPoint D Coin X Other F Msg₂ → Coin)
      (a : Fin Hraw.c.ninp → F),
      let Ssetup := setup2 body rootOf₁ rootOf₂ avOf pubOf
        (typedMsg rawMsgOf₁ responseOf) msgOf₂
      let out := Ssetup.proof mt ro
      Hraw.c.Satisfied (Hraw.pubIn (avOf out) (pubOf out)) a →
        mac₁ a (aP (Ssetup.context mt ro) + decode (avOf out)) =
          tagOf out)
    (hrowSat₂ : ∀ (mt : Fin TM → D)
      (ro : HashPoint D Coin X Other F Msg₂ → Coin)
      (a : Fin S₂.c.ninp → F₂),
      let Ssetup := setup2 body rootOf₁ rootOf₂ avOf pubOf
        (typedMsg rawMsgOf₁ responseOf) msgOf₂
      let out := Ssetup.proof mt ro
      S₂.c.Satisfied (S₂.pubIn (avOf out) (pubOf out)) a →
        mac₂ a (aP (Ssetup.context mt ro) + decode (avOf out)) =
          tagOf out) :
    let Ssetup := setup2 body rootOf₁ rootOf₂ avOf pubOf (typedMsg rawMsgOf₁ responseOf) msgOf₂
    let check := check2 codec₁ claimOf₁ codec₂ claimOf₂
    let Acc := fun (mt : Fin TM → D)
        (ro : HashPoint D Coin X Other F Msg₂ → Coin) =>
      v7Hash1_flatEvent (withTypedRespOf Hraw baseNodes responseNodes) S₂.toSide rootOf₁ rootOf₂ avOf pubOf
        (typedMsg rawMsgOf₁ responseOf) msgOf₂ claimOf₁ claimOf₂ common₁ common₂
        (Ssetup.context mt ro) (Ssetup.merkleOracle check mt ro)
        (Ssetup.proof mt ro) (Ssetup.challenges mt ro)
    ((univ.filter fun ω : (Fin TM → D) ×
        (HashPoint D Coin X Other F Msg₂ → Coin) =>
          Acc ω.1 ω.2).card : ℚ) /
      ((Fintype.card D : ℚ) ^ TM *
        (Fintype.card Coin : ℚ) ^
          Fintype.card (HashPoint D Coin X Other F Msg₂)) ≤
      (1 + N + tA : ℚ) / 2 ^ 116 := by
  by_cases htA : tA ≤ 2 ^ 116
  ·
    let Htyped := withTypedRespOf Hraw baseNodes responseNodes
    let msgTyped := typedMsg rawMsgOf₁ responseOf
    let check := check2 codec₁ claimOf₁ codec₂ claimOf₂
    have hcheck₁ : ∀ (H : Enc → D) (out : Out),
        ∀ qa ∈ ((checkPass codec₁ v7Hash1.params.row.n
            (claimOf₁ out).I (claimOf₁ out).a
            (claimOf₁ out).pf (2 * v7Hash1.params.row.n)
            fun _ => default).run H).2,
          qa ∈ ((check out).run H).2 := by
      intro H out qa hqa
      change qa ∈ ((check2 codec₁ claimOf₁ codec₂ claimOf₂ out).run H).2
      rw [check2, Tree.run_bind]
      exact List.mem_append_left _
        (NizkAdaptive.lfCheck_trace codec₁ claimOf₁ H out qa hqa)
    have hcheck₂ : ∀ (H : Enc → D) (out : Out),
        ∀ qa ∈ ((checkPass codec₂ v7SigHahn.params.row.n
            (claimOf₂ out).I (claimOf₂ out).a
            (claimOf₂ out).pf (2 * v7SigHahn.params.row.n)
            fun _ => default).run H).2,
          qa ∈ ((check out).run H).2 := by
      intro H out qa hqa
      change qa ∈ ((check2 codec₁ claimOf₁ codec₂ claimOf₂ out).run H).2
      rw [check2, Tree.run_bind]
      exact List.mem_append_right _
        (NizkAdaptive.lfCheck_trace codec₂ claimOf₂ H out qa hqa)
    have hrow₁ : ∀ (mt : Fin TM → D)
        (ro : HashPoint D Coin X Other F Msg₂ → Coin)
        (a : Fin Htyped.c.ninp → F),
        let Ssetup := setup2 body rootOf₁ rootOf₂ avOf pubOf msgTyped msgOf₂
        let out := Ssetup.proof mt ro
        let σ := (Ssetup.context mt ro, avOf out, pubOf out)
        (v7Hash1_flatSide Htyped).Good σ a →
          mac₁ a (aP (Ssetup.context mt ro) + decode (avOf out)) =
            tagOf out := by
      intro mt ro a
      dsimp only
      intro hgood
      apply hrowSat₁ mt ro a
      exact Htyped.toZkSideAt_good_property
        (Optimized.v7Hash1_v1.certificate.e +
          Optimized.v7Hash1_v1.certificate.g)
        (by decide) (v7Hash1_flat_lift_card Htyped)
        (fun σ a => Htyped.c.Satisfied (Htyped.pubIn σ.2.1 σ.2.2) a)
        (by intro σ a hs; exact hs) _ a hgood
    have hrow₂ : ∀ (mt : Fin TM → D)
        (ro : HashPoint D Coin X Other F Msg₂ → Coin)
        (a : Fin S₂.c.ninp → F₂),
        let Ssetup := setup2 body rootOf₁ rootOf₂ avOf pubOf msgTyped msgOf₂
        let out := Ssetup.proof mt ro
        let σ := (Ssetup.context mt ro, avOf out, pubOf out)
        S₂.toSide.toZkSide.Good σ a →
          mac₂ a (aP (Ssetup.context mt ro) + decode (avOf out)) =
            tagOf out := by
      intro mt ro a
      dsimp only
      intro hgood
      apply hrowSat₂ mt ro a
      exact S₂.toSide_good_property
        (fun σ a => S₂.c.Satisfied (S₂.pubIn σ.2.1 σ.2.2) a)
        (by intro σ a hs; exact hs) _ a hgood
    exact flatEvent_hybrid_fs_ratio_le_116_mac_typed
      Hraw S₂.toSide baseNodes responseNodes body
      rootOf₁ rootOf₂ avOf pubOf rawMsgOf₁ msgOf₂
      claimOf₁ claimOf₂ common₁ common₂ check hcheck₁ hcheck₂
      responseOf aP decode tagOf S₂.cands S₂.cands_card_le
      S₂.good_mem_cands mac₁ mac₂ hbal hcoll dflt
      hC hD htA (by omega) ht (by omega) hTM hrow₁ hrow₂
  · calc
      _ ≤ (1 : ℚ) := Lfzk.TSec.ratio_le_one _
      _ ≤ (1 + N + tA : ℚ) / 2 ^ 116 := by
        have hn : 2 ^ 116 ≤ tA := by omega
        have hq : (2 ^ 116 : ℚ) ≤ (tA : ℚ) := by exact_mod_cast hn
        apply (le_div_iff₀ (by positivity)).mpr
        nlinarith [show (0 : ℚ) ≤ N by positivity]

/-- False-statement soundness follows from the direct four-slice
response-assisted extraction theorem. -/
theorem falseStatement_hybrid_fs_ratio_le_116_circuit_typed
    {Coin F Other Enc D Salt₁ Salt₂ X Msg₂ Out Fmac : Type}
    [Fintype Coin] [DecidableEq Coin] [Inhabited Coin] [Nonempty Coin]
    [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype D] [DecidableEq D] [Inhabited D]
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Other] [DecidableEq Other] [Inhabited Other]
    [Fintype Msg₂] [DecidableEq Msg₂] [Inhabited Msg₂]
    [DecidableEq Enc] [Inhabited Salt₁] [Inhabited Salt₂]
    [Field Fmac] [Fintype Fmac] [DecidableEq Fmac]
    {F₂ : Type} [Field F₂] [Fintype F₂] [DecidableEq F₂]
    [SumcheckInterp F₂]
    {M nt nlin M₂ nt₂ nlin₂ nblk tA N TM fc : ℕ}
    {codec₁ : Codec Salt₁ (Col F v7Hash1.params.nw v7Hash1.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7SigHahn.params.nw v7SigHahn.params.nq)
      D Enc}
    {dec₂ : RoleDecoders codec₂}
    (Hraw : CircuitSide v7Hash1 v7Hash1_valid v7Hash1_openings_pos
      3 Coin F
      (Lfzk.LigeroTranscriptInputs.Message
        (Other := Other) (F := F)
        (block := (row (0 : Fin 4)).k)
        (dblock := 2 * (row (0 : Fin 4)).k - 1)
        (r := (row (0 : Fin 4)).openings))
      M nt nlin X dec₁ Prod.fst)
    (S₂ : CircuitSide v7SigHahn v7SigHahn_valid
      v7SigHahn_openings_pos 8 Coin F₂ Msg₂
      M₂ nt₂ nlin₂ X dec₂ Prod.snd)
    (baseNodes : Fin (row (0 : Fin 4)).k ↪
      Position (row (0 : Fin 4)).openings v7Hash1.params.q
        (row (0 : Fin 4)).n)
    (responseNodes : Fin (2 * (row (0 : Fin 4)).k - 1) ↪
      Position (row (0 : Fin 4)).openings v7Hash1.params.q
        (row (0 : Fin 4)).n)
    (body : TwoOracleTree Enc D (HashPoint D Coin X Other F Msg₂)
      Coin Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → Coin) (pubOf : Out → X)
    (rawMsgOf₁ : Out → ℕ → Lfzk.LigeroTranscriptInputs.Message
      (Other := Other) (F := F)
      (block := (row (0 : Fin 4)).k)
      (dblock := 2 * (row (0 : Fin 4)).k - 1)
      (r := (row (0 : Fin 4)).openings))
    (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7Hash1.params.row.n Salt₁
      (Col F v7Hash1.params.nw v7Hash1.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7SigHahn.params.row.n Salt₂
      (Col F₂ v7SigHahn.params.nw v7SigHahn.params.nq) D)
    (common₁ : (Fin Hraw.c.ninp → F) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (responseOf : Out → Lfzk.V1StrongV7Terminal.Payload 0 F)
    (aP : ((D × D) × List (Enc × D)) → Fmac)
    (decode : Coin → Fmac) (tagOf : Out → Fin nblk → Fmac)
    (mac₁ : (Fin Hraw.c.ninp → F) → Fmac → Fin nblk → Fmac)
    (mac₂ : (Fin S₂.c.ninp → F₂) → Fmac → Fin nblk → Fmac)
    (hbal : ∀ x : Fmac,
      (univ.filter fun c : Coin => decode c = x).card ≤ 2 ^ 128)
    (hcoll : ∀ a₁ a₂, common₁ a₁ ≠ common₂ a₂ →
      (univ.filter fun x => mac₁ a₁ x = mac₂ a₂ x).card ≤ 1)
    (dflt : Coin)
    (hC : Fintype.card Coin = 2 ^ 256)
    (hD : Fintype.card D = 2 ^ 256)
    (hfc : fc = 2 * v7Hash1.params.row.n +
      2 * v7SigHahn.params.row.n)
    (ht : tA ≤ TM) (hF : fc + tA ≤ TM) (hTM : 1 ≤ TM)
    (hrowSat₁ : ∀ (mt : Fin TM → D)
      (ro : HashPoint D Coin X Other F Msg₂ → Coin)
      (a : Fin Hraw.c.ninp → F),
      let Ssetup := setup2 body rootOf₁ rootOf₂ avOf pubOf
        (typedMsg rawMsgOf₁ responseOf) msgOf₂
      let out := Ssetup.proof mt ro
      Hraw.c.Satisfied (Hraw.pubIn (avOf out) (pubOf out)) a →
        mac₁ a (aP (Ssetup.context mt ro) + decode (avOf out)) =
          tagOf out)
    (hrowSat₂ : ∀ (mt : Fin TM → D)
      (ro : HashPoint D Coin X Other F Msg₂ → Coin)
      (a : Fin S₂.c.ninp → F₂),
      let Ssetup := setup2 body rootOf₁ rootOf₂ avOf pubOf
        (typedMsg rawMsgOf₁ responseOf) msgOf₂
      let out := Ssetup.proof mt ro
      S₂.c.Satisfied (S₂.pubIn (avOf out) (pubOf out)) a →
        mac₂ a (aP (Ssetup.context mt ro) + decode (avOf out)) =
          tagOf out) :
    let Htyped := withTypedRespOf Hraw baseNodes responseNodes
    let msgTyped := typedMsg rawMsgOf₁ responseOf
    let Ssetup := setup2 body rootOf₁ rootOf₂ avOf pubOf msgTyped msgOf₂
    let check := check2 codec₁ claimOf₁ codec₂ claimOf₂
    ((univ.filter fun ω : (Fin TM → D) ×
        (HashPoint D Coin X Other F Msg₂ → Coin) =>
      Htyped.toSide.acceptsTape rootOf₁ msgTyped claimOf₁ avOf pubOf
        (slice1 v7Hash1 v7SigHahn) (Ssetup.merkleOracle check ω.1 ω.2)
        (Ssetup.proof ω.1 ω.2) (Ssetup.challenges ω.1 ω.2) ∧
      S₂.toSide.acceptsTape rootOf₂ msgOf₂ claimOf₂ avOf pubOf
        (slice2 v7Hash1 v7SigHahn) (Ssetup.merkleOracle check ω.1 ω.2)
        (Ssetup.proof ω.1 ω.2) (Ssetup.challenges ω.1 ω.2) ∧
      Ssetup.challenges ω.1 ω.2 ⟨0, by omega⟩ =
        avOf (Ssetup.proof ω.1 ω.2) ∧
      ¬ ∃ a₁ a₂,
        Htyped.c.Satisfied (Htyped.pubIn
          (avOf (Ssetup.proof ω.1 ω.2))
          (pubOf (Ssetup.proof ω.1 ω.2))) a₁ ∧
        S₂.c.Satisfied (S₂.pubIn
          (avOf (Ssetup.proof ω.1 ω.2))
          (pubOf (Ssetup.proof ω.1 ω.2))) a₂ ∧
        common₁ a₁ = common₂ a₂).card : ℚ) /
      ((Fintype.card D : ℚ) ^ TM *
        (Fintype.card Coin : ℚ) ^
          Fintype.card (HashPoint D Coin X Other F Msg₂)) ≤
      (1 + N + tA : ℚ) / 2 ^ 116 := by
  let Htyped := withTypedRespOf Hraw baseNodes responseNodes
  let msgTyped := typedMsg rawMsgOf₁ responseOf
  let Ssetup := setup2 body rootOf₁ rootOf₂ avOf pubOf msgTyped msgOf₂
  let check := check2 codec₁ claimOf₁ codec₂ claimOf₂
  have hcore := flatEvent_hybrid_fs_ratio_le_116_circuit_typed
    Hraw S₂ baseNodes responseNodes body
    rootOf₁ rootOf₂ avOf pubOf rawMsgOf₁ msgOf₂
    claimOf₁ claimOf₂ common₁ common₂ responseOf
    aP decode tagOf mac₁ mac₂ hbal hcoll dflt
    hC hD hfc ht hF hTM hrowSat₁ hrowSat₂
  let P : (Fin TM → D) × (HashPoint D Coin X Other F Msg₂ → Coin) → Prop :=
    fun ω =>
      Htyped.toSide.acceptsTape rootOf₁ msgTyped claimOf₁ avOf pubOf
        (slice1 v7Hash1 v7SigHahn) (Ssetup.merkleOracle check ω.1 ω.2)
        (Ssetup.proof ω.1 ω.2) (Ssetup.challenges ω.1 ω.2) ∧
      S₂.toSide.acceptsTape rootOf₂ msgOf₂ claimOf₂ avOf pubOf
        (slice2 v7Hash1 v7SigHahn) (Ssetup.merkleOracle check ω.1 ω.2)
        (Ssetup.proof ω.1 ω.2) (Ssetup.challenges ω.1 ω.2) ∧
      Ssetup.challenges ω.1 ω.2 ⟨0, by omega⟩ =
        avOf (Ssetup.proof ω.1 ω.2) ∧
      ¬ ∃ a₁ a₂,
        Htyped.c.Satisfied (Htyped.pubIn
          (avOf (Ssetup.proof ω.1 ω.2))
          (pubOf (Ssetup.proof ω.1 ω.2))) a₁ ∧
        S₂.c.Satisfied (S₂.pubIn
          (avOf (Ssetup.proof ω.1 ω.2))
          (pubOf (Ssetup.proof ω.1 ω.2))) a₂ ∧
        common₁ a₁ = common₂ a₂
  let Q : (Fin TM → D) × (HashPoint D Coin X Other F Msg₂ → Coin) → Prop :=
    fun ω => v7Hash1_flatEvent Htyped S₂.toSide
      rootOf₁ rootOf₂ avOf pubOf msgTyped msgOf₂
      claimOf₁ claimOf₂ common₁ common₂
      (Ssetup.context ω.1 ω.2) (Ssetup.merkleOracle check ω.1 ω.2)
      (Ssetup.proof ω.1 ω.2) (Ssetup.challenges ω.1 ω.2)
  have hsub : univ.filter P ⊆ univ.filter Q := by
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    dsimp only [P] at hω
    dsimp only [Q, v7Hash1_flatEvent]
    rcases hω with ⟨hacc₁, hacc₂, hkey, hfalse⟩
    refine ⟨hacc₁, hacc₂, hkey, ?_⟩
    intro ⟨a₁, a₂, hg₁, hg₂, heq⟩
    apply hfalse
    refine ⟨a₁, a₂, ?_, ?_, heq⟩
    · exact Htyped.toZkSideAt_good_property
        (Optimized.v7Hash1_v1.certificate.e +
          Optimized.v7Hash1_v1.certificate.g)
        (by decide) (v7Hash1_flat_lift_card Htyped)
        (fun σ a => Htyped.c.Satisfied (Htyped.pubIn σ.2.1 σ.2.2) a)
        (by intro σ a hs; exact hs) _ a₁ hg₁
    · exact S₂.toSide_good_property
        (fun σ a => S₂.c.Satisfied (S₂.pubIn σ.2.1 σ.2.2) a)
        (by intro σ a hs; exact hs) _ a₂ hg₂
  have hcard : ((univ.filter P).card : ℚ) ≤ ((univ.filter Q).card : ℚ) := by
    exact_mod_cast Finset.card_le_card hsub
  apply le_trans ?_ hcore
  exact div_le_div_of_nonneg_right hcard (by positivity)

end Lfzk.V1StrongV7Hash1HybridFS
