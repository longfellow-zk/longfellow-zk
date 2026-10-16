import Lfzk.V1StrongV7Terminal
import Lfzk.FlatV7Radius
import Lfzk.RbrZkFlatBuilt

/-! Identify the strong V1 hash1 certificate with the shipped circuit's code. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.V1StrongV7Hash1Adapter

open LigeroFamily Lfzk.V1StrongV7Numeric Lfzk.CertifiedV1
open Lfzk.LigeroV1Rows
open Ligero.Examples.Grid.LongfellowProfiledExtraction
open scoped Classical

/-- The typed response decoder for the transmitted four-slice V1 message.
Other transcript rounds have an arbitrary zero response because the verifier
reads `respOf` only at the response round. -/
noncomputable def typedRespOf
    {F Other : Type} [Field F] [Fintype F] [DecidableEq F]
    (D : ReedSolomon.Domain F (row (0 : Fin 4)).openings
      v7Hash1.params.q (row (0 : Fin 4)).n)
    (baseNodes : Fin (row (0 : Fin 4)).k ↪
      Position (row (0 : Fin 4)).openings v7Hash1.params.q
        (row (0 : Fin 4)).n)
    (responseNodes : Fin (2 * (row (0 : Fin 4)).k - 1) ↪
      Position (row (0 : Fin 4)).openings v7Hash1.params.q
        (row (0 : Fin 4)).n)
    (msg : Lfzk.LigeroTranscriptInputs.Message
      (Other := Other) (F := F)
      (block := (row (0 : Fin 4)).k)
      (dblock := 2 * (row (0 : Fin 4)).k - 1)
      (r := (row (0 : Fin 4)).openings)) :
    Response F (row (0 : Fin 4)).openings v7Hash1.params.q
      (row (0 : Fin 4)).n 1 :=
  match msg with
  | Sum.inl _ => ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0⟩
  | Sum.inr payload =>
      Lfzk.V1StrongV7Terminal.decodePayload 0 D baseNodes responseNodes payload

theorem typedRespOf_response
    {F Other : Type} [Field F] [Fintype F] [DecidableEq F]
    (D : ReedSolomon.Domain F (row (0 : Fin 4)).openings
      v7Hash1.params.q (row (0 : Fin 4)).n)
    (baseNodes : Fin (row (0 : Fin 4)).k ↪
      Position (row (0 : Fin 4)).openings v7Hash1.params.q
        (row (0 : Fin 4)).n)
    (responseNodes : Fin (2 * (row (0 : Fin 4)).k - 1) ↪
      Position (row (0 : Fin 4)).openings v7Hash1.params.q
        (row (0 : Fin 4)).n)
    (payload : Lfzk.V1StrongV7Terminal.Payload 0 F) :
    typedRespOf (Other := Other) D baseNodes responseNodes (Sum.inr payload) =
      Lfzk.V1StrongV7Terminal.decodePayload 0 D baseNodes responseNodes payload := by
  rfl

/-- Fix the circuit-side response decoder to the transmitted V1 four-slice
layout.  The remaining circuit, code, and challenge decoders are unchanged. -/
noncomputable def withTypedRespOf
    {Coin F Other Enc D Salt X : Type}
    [Fintype Coin] [Field F] [Fintype F] [DecidableEq F]
    [SumcheckInterp F] [Inhabited Other]
    [Inhabited D] [DecidableEq D] [DecidableEq Enc] [Inhabited Salt]
    {M nt nlin : ℕ}
    {codec : Merkle.MH.Codec Salt
      (Lfzk.CompiledLongfellow.Col F v7Hash1.params.nw v7Hash1.params.nq)
      D Enc}
    {dec : Merkle.MH.RoleDecoders codec}
    {rootOfKey : D × D → D}
    (S : Lfzk.CompiledZk.CircuitSide v7Hash1 v7Hash1_valid
      v7Hash1_openings_pos 3 Coin F
      (Lfzk.LigeroTranscriptInputs.Message
        (Other := Other) (F := F)
        (block := (row (0 : Fin 4)).k)
        (dblock := 2 * (row (0 : Fin 4)).k - 1)
        (r := (row (0 : Fin 4)).openings))
      M nt nlin X dec rootOfKey)
    (baseNodes : Fin (row (0 : Fin 4)).k ↪
      Position (row (0 : Fin 4)).openings v7Hash1.params.q
        (row (0 : Fin 4)).n)
    (responseNodes : Fin (2 * (row (0 : Fin 4)).k - 1) ↪
      Position (row (0 : Fin 4)).openings v7Hash1.params.q
        (row (0 : Fin 4)).n) :
    Lfzk.CompiledZk.CircuitSide v7Hash1 v7Hash1_valid
      v7Hash1_openings_pos 3 Coin F
      (Lfzk.LigeroTranscriptInputs.Message
        (Other := Other) (F := F)
        (block := (row (0 : Fin 4)).k)
        (dblock := 2 * (row (0 : Fin 4)).k - 1)
        (r := (row (0 : Fin 4)).openings))
      M nt nlin X dec rootOfKey :=
  { S with respOf := typedRespOf S.dom baseNodes responseNodes }

theorem withTypedRespOf_response
    {Coin F Other Enc D Salt X : Type}
    [Fintype Coin] [Field F] [Fintype F] [DecidableEq F]
    [SumcheckInterp F] [Inhabited Other]
    [Inhabited D] [DecidableEq D] [DecidableEq Enc] [Inhabited Salt]
    {M nt nlin : ℕ}
    {codec : Merkle.MH.Codec Salt
      (Lfzk.CompiledLongfellow.Col F v7Hash1.params.nw v7Hash1.params.nq)
      D Enc}
    {dec : Merkle.MH.RoleDecoders codec}
    {rootOfKey : D × D → D}
    (S : Lfzk.CompiledZk.CircuitSide v7Hash1 v7Hash1_valid
      v7Hash1_openings_pos 3 Coin F
      (Lfzk.LigeroTranscriptInputs.Message
        (Other := Other) (F := F)
        (block := (row (0 : Fin 4)).k)
        (dblock := 2 * (row (0 : Fin 4)).k - 1)
        (r := (row (0 : Fin 4)).openings))
      M nt nlin X dec rootOfKey)
    (baseNodes : Fin (row (0 : Fin 4)).k ↪
      Position (row (0 : Fin 4)).openings v7Hash1.params.q
        (row (0 : Fin 4)).n)
    (responseNodes : Fin (2 * (row (0 : Fin 4)).k - 1) ↪
      Position (row (0 : Fin 4)).openings v7Hash1.params.q
        (row (0 : Fin 4)).n)
    (payload : Lfzk.V1StrongV7Terminal.Payload 0 F) :
    (withTypedRespOf S baseNodes responseNodes).respOf (Sum.inr payload) =
      Lfzk.V1StrongV7Terminal.decodePayload 0 S.dom
        baseNodes responseNodes payload := by
  rfl

theorem hash1_dimensions :
    (row (0 : Fin 4)).n = v7Hash1.params.row.n ∧
    (row (0 : Fin 4)).openings = v7Hash1.params.row.openings ∧
    (row (0 : Fin 4)).k = v7Hash1.params.row.k ∧
    (row (0 : Fin 4)).e + (row (0 : Fin 4)).g =
      Optimized.v7Hash1_v1.certificate.e +
        Optimized.v7Hash1_v1.certificate.g := by
  decide

theorem hash1_code_eq
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (D : ReedSolomon.Domain F v7Hash1.params.row.openings
      v7Hash1.params.q v7Hash1.params.row.n) :
    (row (0 : Fin 4)).code
      (Lfzk.V1StrongV7Mass.row_valid 0) D
      (by decide : (row (0 : Fin 4)).openings +
        v7Hash1.params.q = (row (0 : Fin 4)).k) =
    v7Hash1.params.row.code (Row.rowValid v7Hash1_valid) D
      (Row.hkrow v7Hash1_valid) := by
  rfl

/-- A built hash1 system with no satisfying committed lift contributes to
the certified V1 extraction-failure event whenever its actual query check
accepts the transmitted response. -/
theorem hash1_accepts_of_noSat
    {Coin F Other Enc D Salt X : Type}
    [Fintype Coin] [Inhabited Other]
    [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Inhabited D] [DecidableEq D] [DecidableEq Enc] [Inhabited Salt]
    {M nt nlin : ℕ}
    {codec : Merkle.MH.Codec Salt
      (Lfzk.CompiledLongfellow.Col F v7Hash1.params.nw v7Hash1.params.nq)
      D Enc}
    {dec : Merkle.MH.RoleDecoders codec}
    {rootOfKey : D × D → D}
    (S : Lfzk.CompiledZk.CircuitSide v7Hash1 v7Hash1_valid
      v7Hash1_openings_pos 3 Coin F
      (Lfzk.LigeroTranscriptInputs.Message
        (Other := Other) (F := F)
        (block := (row (0 : Fin 4)).k)
        (dblock := 2 * (row (0 : Fin 4)).k - 1)
        (r := (row (0 : Fin 4)).openings))
      M nt nlin X dec rootOfKey)
    (σ : Lfzk.CompiledLongfellowAdaptive.Sig D Coin X Enc)
    (sys : LigeroSystem S.c.ninp M F)
    (hlin : sys.linear.length ≤ nlin)
    (hquad : sys.quad.length ≤ nt)
    (baseNodes : Fin (row (0 : Fin 4)).k ↪
      Position (row (0 : Fin 4)).openings v7Hash1.params.q
        (row (0 : Fin 4)).n)
    (responseNodes : Fin (2 * (row (0 : Fin 4)).k - 1) ↪
      Position (row (0 : Fin 4)).openings v7Hash1.params.q
        (row (0 : Fin 4)).n)
    (payload : Lfzk.V1StrongV7Terminal.Payload 0 F)
    (challenge : Ligero.V1.Challenge F v7Hash1.params.nw
      v7Hash1.params.nq 1 (Fin nlin ⊕ (Fin nt × Encode.QSide)))
    (query : QuerySet (row (0 : Fin 4)).n
      (row (0 : Fin 4)).openings)
    (hresponse : S.respOf (Sum.inr payload) =
      Lfzk.V1StrongV7Terminal.decodePayload 0 S.dom
        baseNodes responseNodes payload)
    (hn : Lfzk.RbrZkLongfellow.NoSat (fun ℓ : Lfzk.CompiledZk.sideLiftAt S
      ((row (0 : Fin 4)).e + (row (0 : Fin 4)).g) σ =>
        Lfzk.ZkLigeroV1.asgAt S.pl
          ((row (0 : Fin 4)).e + (row (0 : Fin 4)).g) ℓ) sys)
    (hacc : query ∈ Lfzk.CompiledLongfellowAdaptive.acceptingR
      (Row.rowValid v7Hash1_valid) S.dom (Row.hkrow v7Hash1_valid)
      ⟨Lfzk.ZkLigeroV1.stmtOf S.pl nlin sys,
        Lfzk.CompiledZk.extOracle (row := v7Hash1.params.row) nlin nt
          (Row.rowValid v7Hash1_valid) S.dom
          (Row.hkrow v7Hash1_valid) v7Hash1_openings_pos dec
          (rootOfKey σ.1.1, σ.1.2)⟩
      (S.respOf (Sum.inr payload)) challenge) :
    Lfzk.V1StrongV7Terminal.accepts 0 S.dom
      (by decide : (row (0 : Fin 4)).openings + v7Hash1.params.q =
        (row (0 : Fin 4)).k)
      baseNodes responseNodes
      (Lfzk.CompiledZk.extOracle (row := v7Hash1.params.row) nlin nt
        (Row.rowValid v7Hash1_valid) S.dom
        (Row.hkrow v7Hash1_valid) v7Hash1_openings_pos dec
        (rootOfKey σ.1.1, σ.1.2))
      (Lfzk.ZkLigeroV1.stmtOf S.pl nlin sys)
      challenge payload query := by
  let O := Lfzk.CompiledZk.extOracle (row := v7Hash1.params.row) nlin nt
    (Row.rowValid v7Hash1_valid) S.dom
    (Row.hkrow v7Hash1_valid) v7Hash1_openings_pos dec
    (rootOfKey σ.1.1, σ.1.2)
  have hnd₀ := Lfzk.ZkLigeroV1.noDecoded_of_noSatAt S.pl nlin
    ((row (0 : Fin 4)).e + (row (0 : Fin 4)).g)
    (Row.rowValid v7Hash1_valid) S.dom (Row.hkrow v7Hash1_valid)
    O sys hlin hquad hn
  have hnd : NoDecodedSolution
      ((row (0 : Fin 4)).code
        (Lfzk.V1StrongV7Mass.row_valid 0) S.dom
        (by decide : (row (0 : Fin 4)).openings + v7Hash1.params.q =
          (row (0 : Fin 4)).k))
      O ((row (0 : Fin 4)).e + (row (0 : Fin 4)).g)
      (Lfzk.ZkLigeroV1.stmtOf S.pl nlin sys) := by
    exact hnd₀
  apply (Lfzk.V1StrongV7Terminal.accepts_iff_of_noDecoded 0 S.dom
    (by decide) baseNodes responseNodes O
    (Lfzk.ZkLigeroV1.stmtOf S.pl nlin sys)
    challenge payload query hnd).2
  have hp := (Finset.mem_filter.mp hacc).2
  rw [hresponse] at hp
  exact hp

/-- The terminal branch of the already-proved flat LayerStep split is the
same strong V1 extraction-failure event. -/
theorem hash1_terminalPairAccept_strong
    {Coin F Other Enc D Salt X : Type}
    [Fintype Coin] [Inhabited Other]
    [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Inhabited D] [DecidableEq D] [DecidableEq Enc] [Inhabited Salt]
    {M nt nlin : ℕ}
    {codec : Merkle.MH.Codec Salt
      (Lfzk.CompiledLongfellow.Col F v7Hash1.params.nw v7Hash1.params.nq)
      D Enc}
    {dec : Merkle.MH.RoleDecoders codec}
    {rootOfKey : D × D → D}
    (S : Lfzk.CompiledZk.CircuitSide v7Hash1 v7Hash1_valid
      v7Hash1_openings_pos 3 Coin F
      (Lfzk.LigeroTranscriptInputs.Message
        (Other := Other) (F := F)
        (block := (row (0 : Fin 4)).k)
        (dblock := 2 * (row (0 : Fin 4)).k - 1)
        (r := (row (0 : Fin 4)).openings))
      M nt nlin X dec rootOfKey)
    (σ : Lfzk.CompiledLongfellowAdaptive.Sig D Coin X Enc)
    (baseNodes : Fin (row (0 : Fin 4)).k ↪
      Position (row (0 : Fin 4)).openings v7Hash1.params.q
        (row (0 : Fin 4)).n)
    (responseNodes : Fin (2 * (row (0 : Fin 4)).k - 1) ↪
      Position (row (0 : Fin 4)).openings v7Hash1.params.q
        (row (0 : Fin 4)).n)
    (payload : Lfzk.V1StrongV7Terminal.Payload 0 F)
    (hresponse : S.respOf (Sum.inr payload) =
      Lfzk.V1StrongV7Terminal.decodePayload 0 S.dom
        baseNodes responseNodes payload)
    (ms : ℕ → Lfzk.LigeroTranscriptInputs.Message
      (Other := Other) (F := F)
      (block := (row (0 : Fin 4)).k)
      (dblock := 2 * (row (0 : Fin 4)).k - 1)
      (r := (row (0 : Fin 4)).openings))
    (hmsg : ms (Rounds.Role.layerBase v7Hash1.params.rounds
      v7Hash1.params.nl + 2) = Sum.inr payload)
    (pref : Fin (Rounds.Role.layerBase v7Hash1.params.rounds
      v7Hash1.params.nl + 1) → Coin)
    (c d : Coin)
    (tape : Fin (Rounds.Role.length v7Hash1.params.nl
      v7Hash1.params.rounds) → Coin)
    (hprefix : Bcs.trunc tape
      (Rounds.Role.layerBase v7Hash1.params.rounds
        v7Hash1.params.nl + 1)
      Lfzk.CompiledLongfellow.fieldLen_le = pref)
    (hterm : Lfzk.RbrZkFlat.terminalPairAccept
      (H := (Lfzk.CompiledZk.FlatV7Radius.v7Hash1_flatSide S).H σ)
      (Sat := (Lfzk.CompiledZk.FlatV7Radius.v7Hash1_flatSide S).Sat σ)
      ((Lfzk.CompiledZk.FlatV7Radius.v7Hash1_flatSide S).LD σ)
      ms pref c d) :
    ∃ sys : LigeroSystem S.c.ninp M F,
      Lfzk.CompiledZk.zkBuilt (nl := v7Hash1.params.nl)
        (w := v7Hash1.params.rounds)
        ((Lfzk.CompiledZk.FlatV7Radius.v7Hash1_flatSide S).V σ)
        ms tape = some sys ∧
      Lfzk.RbrZkLongfellow.Fits (S.Vc σ.2.1 σ.2.2) sys ∧
      Lfzk.V1StrongV7Terminal.accepts 0 S.dom
        (by decide : (row (0 : Fin 4)).openings + v7Hash1.params.q =
          (row (0 : Fin 4)).k)
        baseNodes responseNodes
        (Lfzk.CompiledZk.extOracle (row := v7Hash1.params.row) nlin nt
          (Row.rowValid v7Hash1_valid) S.dom
          (Row.hkrow v7Hash1_valid) v7Hash1_openings_pos dec
          (rootOfKey σ.1.1, σ.1.2))
        (Lfzk.ZkLigeroV1.stmtOf S.pl nlin sys)
        ((S.Vc σ.2.1 σ.2.2).decodeChal c) payload
        ((S.Vc σ.2.1 σ.2.2).decodeQuery d) := by
  obtain ⟨sys, hs, hf, hn, hq⟩ := hterm
  have hf' : Lfzk.RbrZkLongfellow.Fits
      (S.Vc σ.2.1 σ.2.2) sys := hf
  have hbuilt := Lfzk.RbrZkFlat.built_state_eq_zkBuilt
    ((Lfzk.CompiledZk.FlatV7Radius.v7Hash1_flatSide S).LD σ)
    ms pref tape hprefix sys hs
  refine ⟨sys, hbuilt, hf', ?_⟩
  have hlin : sys.linear.length ≤ nlin := by
    simpa only [S.hnlin] using hf'.1
  have hquad : sys.quad.length ≤ nt := by
    simpa only [S.hnt] using hf'.2
  have hn' : Lfzk.RbrZkLongfellow.NoSat
      (fun ℓ : Lfzk.CompiledZk.sideLiftAt S
        ((row (0 : Fin 4)).e + (row (0 : Fin 4)).g) σ =>
        Lfzk.ZkLigeroV1.asgAt S.pl
          ((row (0 : Fin 4)).e + (row (0 : Fin 4)).g) ℓ) sys := by
    have hradius : (row (0 : Fin 4)).e + (row (0 : Fin 4)).g =
        Optimized.v7Hash1_v1.certificate.e +
          Optimized.v7Hash1_v1.certificate.g := by decide
    change Lfzk.RbrZkLongfellow.NoSat
      (fun ℓ : Lfzk.CompiledZk.sideLiftAt S
        (Optimized.v7Hash1_v1.certificate.e +
          Optimized.v7Hash1_v1.certificate.g) σ =>
        Lfzk.ZkLigeroV1.asgAt S.pl
          (Optimized.v7Hash1_v1.certificate.e +
            Optimized.v7Hash1_v1.certificate.g) ℓ) sys at hn
    rw [hradius]
    exact hn
  have hacc := hq
  rw [Lfzk.CompiledZk.FlatV7Radius.v7Hash1_flatSide_accepting S σ] at hacc
  rw [hmsg] at hacc
  change (S.Vc σ.2.1 σ.2.2).decodeQuery d ∈
    Lfzk.CompiledLongfellowAdaptive.acceptingR
      (Row.rowValid v7Hash1_valid) S.dom
      (Row.hkrow v7Hash1_valid)
      ⟨Lfzk.ZkLigeroV1.stmtOf S.pl nlin sys,
        Lfzk.CompiledZk.extOracle (row := v7Hash1.params.row) nlin nt
          (Row.rowValid v7Hash1_valid) S.dom
          (Row.hkrow v7Hash1_valid) v7Hash1_openings_pos dec
          (rootOfKey σ.1.1, σ.1.2)⟩
      (S.respOf (Sum.inr payload))
      ((S.Vc σ.2.1 σ.2.2).decodeChal c) at hacc
  exact hash1_accepts_of_noSat S σ sys hlin hquad baseNodes
    responseNodes payload _ _ hresponse hn' hacc

/-- An accepted hash1 LayerStep with no satisfying committed lift either
escapes during the earlier field rounds or enters the strong V1 terminal
event at exactly the system built by the compiled verifier. -/
theorem hash1_accepted_field_or_strong_terminal
    {Coin F Other Enc D Salt X : Type}
    [Fintype Coin] [Inhabited Other]
    [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Inhabited D] [DecidableEq D] [DecidableEq Enc] [Inhabited Salt]
    {M nt nlin : ℕ}
    {codec : Merkle.MH.Codec Salt
      (Lfzk.CompiledLongfellow.Col F v7Hash1.params.nw v7Hash1.params.nq)
      D Enc}
    {dec : Merkle.MH.RoleDecoders codec}
    {rootOfKey : D × D → D}
    (S : Lfzk.CompiledZk.CircuitSide v7Hash1 v7Hash1_valid
      v7Hash1_openings_pos 3 Coin F
      (Lfzk.LigeroTranscriptInputs.Message
        (Other := Other) (F := F)
        (block := (row (0 : Fin 4)).k)
        (dblock := 2 * (row (0 : Fin 4)).k - 1)
        (r := (row (0 : Fin 4)).openings))
      M nt nlin X dec rootOfKey)
    (σ : Lfzk.CompiledLongfellowAdaptive.Sig D Coin X Enc)
    (baseNodes : Fin (row (0 : Fin 4)).k ↪
      Position (row (0 : Fin 4)).openings v7Hash1.params.q
        (row (0 : Fin 4)).n)
    (responseNodes : Fin (2 * (row (0 : Fin 4)).k - 1) ↪
      Position (row (0 : Fin 4)).openings v7Hash1.params.q
        (row (0 : Fin 4)).n)
    (payload : Lfzk.V1StrongV7Terminal.Payload 0 F)
    (hresponse : S.respOf (Sum.inr payload) =
      Lfzk.V1StrongV7Terminal.decodePayload 0 S.dom
        baseNodes responseNodes payload)
    (ms : ℕ → Lfzk.LigeroTranscriptInputs.Message
      (Other := Other) (F := F)
      (block := (row (0 : Fin 4)).k)
      (dblock := 2 * (row (0 : Fin 4)).k - 1)
      (r := (row (0 : Fin 4)).openings))
    (hmsg : ms (Rounds.Role.layerBase v7Hash1.params.rounds
      v7Hash1.params.nl + 2) = Sum.inr payload)
    (tape : Fin (Rounds.Role.length v7Hash1.params.nl
      v7Hash1.params.rounds) → Coin)
    (hfalse : ∀ ℓ,
      ¬ (Lfzk.CompiledZk.FlatV7Radius.v7Hash1_flatSide S).Sat σ ℓ)
    (hacc : Lfzk.RbrZkSplit.ZkLayerStepAccepts .accepted .start
      (Lfzk.RbrZkSplit.steps (nl := v7Hash1.params.nl)
        (w := v7Hash1.params.rounds)
        ((Lfzk.CompiledZk.FlatV7Radius.v7Hash1_flatSide S).V σ)
        ((Lfzk.CompiledZk.FlatV7Radius.v7Hash1_flatSide S).LD σ)
        ms) tape) :
    let u := Rounds.Role.layerBase v7Hash1.params.rounds
      v7Hash1.params.nl + 1
    let p := Bcs.terminalPairEquiv u tape
    Lfzk.RbrZkFlat.fieldPrefixEscape
      (H := (Lfzk.CompiledZk.FlatV7Radius.v7Hash1_flatSide S).H σ)
      (Sat := (Lfzk.CompiledZk.FlatV7Radius.v7Hash1_flatSide S).Sat σ)
      ((Lfzk.CompiledZk.FlatV7Radius.v7Hash1_flatSide S).LD σ)
      ms p.1 ∨
    ∃ sys : LigeroSystem S.c.ninp M F,
      Lfzk.CompiledZk.zkBuilt (nl := v7Hash1.params.nl)
        (w := v7Hash1.params.rounds)
        ((Lfzk.CompiledZk.FlatV7Radius.v7Hash1_flatSide S).V σ)
        ms tape = some sys ∧
      Lfzk.RbrZkLongfellow.Fits (S.Vc σ.2.1 σ.2.2) sys ∧
      Lfzk.V1StrongV7Terminal.accepts 0 S.dom
        (by decide : (row (0 : Fin 4)).openings + v7Hash1.params.q =
          (row (0 : Fin 4)).k)
        baseNodes responseNodes
        (Lfzk.CompiledZk.extOracle (row := v7Hash1.params.row) nlin nt
          (Row.rowValid v7Hash1_valid) S.dom
          (Row.hkrow v7Hash1_valid) v7Hash1_openings_pos dec
          (rootOfKey σ.1.1, σ.1.2))
        (Lfzk.ZkLigeroV1.stmtOf S.pl nlin sys)
        ((S.Vc σ.2.1 σ.2.2).decodeChal p.2.1) payload
        ((S.Vc σ.2.1 σ.2.2).decodeQuery p.2.2) := by
  have h := Lfzk.RbrZkFlat.accepted_field_or_terminal_pair
    (H := (Lfzk.CompiledZk.FlatV7Radius.v7Hash1_flatSide S).H σ)
    (Sat := (Lfzk.CompiledZk.FlatV7Radius.v7Hash1_flatSide S).Sat σ)
    ((Lfzk.CompiledZk.FlatV7Radius.v7Hash1_flatSide S).LD σ)
    ms tape hfalse hacc
  dsimp only at h ⊢
  rcases h with hfield | hterminal
  · exact Or.inl hfield
  · right
    let u := Rounds.Role.layerBase v7Hash1.params.rounds
      v7Hash1.params.nl + 1
    let p := Bcs.terminalPairEquiv u tape
    have hpref : Bcs.trunc tape u
        Lfzk.CompiledLongfellow.fieldLen_le = p.1 := rfl
    have ht : Lfzk.RbrZkFlat.terminalPairAccept
        (H := (Lfzk.CompiledZk.FlatV7Radius.v7Hash1_flatSide S).H σ)
        (Sat := (Lfzk.CompiledZk.FlatV7Radius.v7Hash1_flatSide S).Sat σ)
        ((Lfzk.CompiledZk.FlatV7Radius.v7Hash1_flatSide S).LD σ)
        ms p.1 p.2.1 p.2.2 := hterminal
    exact hash1_terminalPairAccept_strong S σ baseNodes responseNodes
      payload hresponse ms hmsg p.1 p.2.1 p.2.2 tape hpref ht

end Lfzk.V1StrongV7Hash1Adapter
