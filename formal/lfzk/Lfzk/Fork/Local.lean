import Lfzk.V1StrongV7Hash1Local
import Lfzk.Fork.CutContext

/-! Schedule-dependent bridge for the forked verifier. Generic local
counts, cut-context lemmas, and numerical certificates are reused. -/

/-! The strong V1 event's oracle and statement at a selected two-field cut. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.Fork.Local

open Lfzk.V1StrongV7Hash1Local

open LigeroFamily Lfzk.CertifiedV1 Lfzk.V1StrongV7Numeric
open scoped Classical

variable {Coin F Other Enc D Salt X Msg₂ : Type}
  [Fintype Coin] [Inhabited Coin] [Inhabited Other]
  [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
  [Inhabited D] [DecidableEq D] [DecidableEq Enc] [Inhabited Salt]
variable {M nt nlin nl₂ : ℕ} {rounds₂ : ℕ → ℕ}
variable {codec : Merkle.MH.Codec Salt
  (Lfzk.CompiledLongfellow.Col F v7Hash1.params.nw v7Hash1.params.nq)
  D Enc}
variable {dec : Merkle.MH.RoleDecoders codec}
variable {rootOfKey : D × D → D}

private abbrev LocalState := Lfzk.V1StrongV7TwoSideCutContext.State
  (Enc := Enc) (D := D) (Coin := Coin) (X := X)
  (Other := Other) (F := F) (Msg₂ := Msg₂)
  (nl := v7Hash1.params.nl) (nl₂ := nl₂)
  (block := (row (0 : Fin 4)).k)
  (dblock := 2 * (row (0 : Fin 4)).k - 1)
  (r := (row (0 : Fin 4)).openings)
  (rounds := v7Hash1.params.rounds) (rounds₂ := rounds₂)

private abbrev LocalPrefix := Lfzk.V1StrongV7TwoSideFinal.Prefix 0
  D Coin X Other F v7Hash1.params.nl v7Hash1.params.rounds

/-- The cut trace and selected hash-prefix context determine the circuit
side's public parameters. -/
theorem builtAt_ofMessages
    [Inhabited Msg₂]
    (S : Lfzk.CompiledZk.CircuitSide v7Hash1 v7Hash1_valid
      v7Hash1_openings_pos 3 Coin F
      (Lfzk.LigeroTranscriptInputs.Message
        (Other := Other) (F := F)
        (block := (row (0 : Fin 4)).k)
        (dblock := 2 * (row (0 : Fin 4)).k - 1)
        (r := (row (0 : Fin 4)).openings))
      M nt nlin X dec rootOfKey)
    (κ : (D × D) × List (Enc × D))
    {Out : Type}
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → Coin) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Lfzk.LigeroTranscriptInputs.Message
      (Other := Other) (F := F)
      (block := (row (0 : Fin 4)).k)
      (dblock := 2 * (row (0 : Fin 4)).k - 1)
      (r := (row (0 : Fin 4)).openings))
    (msgOf₂ : Out → ℕ → Msg₂)
    (H : Lfzk.V1StrongV7TwoSideFinal.Point 0 D Coin X Other F Msg₂
      v7Hash1.params.nl nl₂ v7Hash1.params.rounds rounds₂ → Coin)
    (out : Out) :
    let p := Lfzk.LigeroPairGeometry.ofMessages
      (nl := v7Hash1.params.nl) (w := v7Hash1.params.rounds)
      (Lfzk.NizkDeployedHashTwoField.ctxOf
        rootOf₁ rootOf₂ avOf pubOf out) (msgOf₁ out)
    builtAt S (κ, Lfzk.LigeroPairGeometryTwoSide.outsideTerminal H) p =
      Lfzk.CompiledZk.zkBuilt (nl := v7Hash1.params.nl)
        (w := v7Hash1.params.rounds)
        (S.Vc (avOf out) (pubOf out)) (msgOf₁ out)
        (fun j => H (Lfzk.Fork.Transcript.hash2
          (nl₁ := v7Hash1.params.nl) (nl₂ := nl₂)
          (w₁ := v7Hash1.params.rounds) (w₂ := rounds₂)
          rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out
          (1 + j.val))) := by
  let p := Lfzk.LigeroPairGeometry.ofMessages
    (nl := v7Hash1.params.nl) (w := v7Hash1.params.rounds)
    (Lfzk.NizkDeployedHashTwoField.ctxOf
      rootOf₁ rootOf₂ avOf pubOf out) (msgOf₁ out)
  let actualTape : Fin (Rounds.Role.length v7Hash1.params.nl
      v7Hash1.params.rounds) → Coin :=
    fun j => H (Lfzk.Fork.Transcript.hash2
      (nl₁ := v7Hash1.params.nl) (nl₂ := nl₂)
      (w₁ := v7Hash1.params.rounds) (w₂ := rounds₂)
      rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out (1 + j.val))
  have hm : ∀ j, j < Rounds.Role.layerBase v7Hash1.params.rounds
      v7Hash1.params.nl + 1 → messagesAt p j = msgOf₁ out j := by
    intro j hj
    exact messagesAt_ofMessages
      (Lfzk.NizkDeployedHashTwoField.ctxOf
        rootOf₁ rootOf₂ avOf pubOf out) (msgOf₁ out) j (by omega)
  have ht : Bcs.trunc actualTape
      (Rounds.Role.layerBase v7Hash1.params.rounds
        v7Hash1.params.nl + 1)
      Lfzk.CompiledLongfellow.fieldLen_le =
      Lfzk.LigeroPairGeometryTwoSide.fieldTape
        (Lfzk.LigeroPairGeometryTwoSide.outsideTerminal H) p := by
    funext j
    exact (Lfzk.Fork.Geometry.fieldTape_ofMessages_eq_hash2
      rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ H out j).symm
  unfold builtAt
  have hmsg := Lfzk.CompiledZkDeployedHash.zkBuilt_congr
    (nl := v7Hash1.params.nl) (w := v7Hash1.params.rounds)
    (S.Vc (avOf out) (pubOf out)) hm
    (Lfzk.RbrZkFlat.fillFieldPrefix
      (Lfzk.LigeroPairGeometryTwoSide.fieldTape
        (Lfzk.LigeroPairGeometryTwoSide.outsideTerminal H) p))
  change Lfzk.CompiledZk.zkBuilt
    (S.Vc (avOf out) (pubOf out)) (messagesAt p) _ = _
  rw [hmsg]
  exact Lfzk.RbrZkFlat.zkBuilt_fillFieldPrefix_eq
    (S.Vc (avOf out) (pubOf out)) (msgOf₁ out)
    actualTape _ ht

/-- `cutState` supplies exactly the outside answers used by `builtAt`.
Its adaptive Merkle trace may depend on other terminal-role queries. -/
theorem builtAt_cutState_eq_compiled
    [Inhabited Msg₂]
    {Out : Type} {tA N Lsch TM : ℕ}
    (S : Lfzk.CompiledZk.CircuitSide v7Hash1 v7Hash1_valid
      v7Hash1_openings_pos 3 Coin F
      (Lfzk.LigeroTranscriptInputs.Message
        (Other := Other) (F := F)
        (block := (row (0 : Fin 4)).k)
        (dblock := 2 * (row (0 : Fin 4)).k - 1)
        (r := (row (0 : Fin 4)).openings))
      M nt nlin X dec rootOfKey)
    (Ssetup : Bcs.TotalOracleCommit.Setup Enc D
      (Lfzk.V1StrongV7TwoSideFinal.Point 0 D Coin X Other F Msg₂
        v7Hash1.params.nl nl₂ v7Hash1.params.rounds rounds₂)
      Coin Out (D × D) tA N Lsch)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → Coin)
    (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Lfzk.LigeroTranscriptInputs.Message
      (Other := Other) (F := F)
      (block := (row (0 : Fin 4)).k)
      (dblock := 2 * (row (0 : Fin 4)).k - 1)
      (r := (row (0 : Fin 4)).openings))
    (msgOf₂ : Out → ℕ → Msg₂)
    (mt : Fin TM → D)
    (H : Lfzk.V1StrongV7TwoSideFinal.Point 0 D Coin X Other F Msg₂
      v7Hash1.params.nl nl₂ v7Hash1.params.rounds rounds₂ → Coin)
    (out : Out) :
    let p := Lfzk.LigeroPairGeometry.ofMessages
      (nl := v7Hash1.params.nl) (w := v7Hash1.params.rounds)
      (Lfzk.NizkDeployedHashTwoField.ctxOf
        rootOf₁ rootOf₂ avOf pubOf out) (msgOf₁ out)
    builtAt S (Lfzk.V1StrongV7TwoSideCutContext.cutState
      Ssetup mt p H) p =
      Lfzk.CompiledZk.zkBuilt (nl := v7Hash1.params.nl)
        (w := v7Hash1.params.rounds)
        (S.Vc (avOf out) (pubOf out)) (msgOf₁ out)
        (fun j => H (Lfzk.Fork.Transcript.hash2
          (nl₁ := v7Hash1.params.nl) (nl₂ := nl₂)
          (w₁ := v7Hash1.params.rounds) (w₂ := rounds₂)
          rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out
          (1 + j.val))) := by
  let p := Lfzk.LigeroPairGeometry.ofMessages
    (nl := v7Hash1.params.nl) (w := v7Hash1.params.rounds)
    (Lfzk.NizkDeployedHashTwoField.ctxOf
      rootOf₁ rootOf₂ avOf pubOf out) (msgOf₁ out)
  have h := Lfzk.Fork.Local.builtAt_ofMessages S
    (Lfzk.V1StrongV7TwoSideCutContext.cutState Ssetup mt p H).1
    rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ H out
  change builtAt S (Lfzk.V1StrongV7TwoSideCutContext.cutState
    Ssetup mt p H) p = _ at h
  exact h

omit [Inhabited Coin] in
/-- The selected local V1 oracle uses precisely the forked verifier's
Merkle extraction context, including its adaptive cut trace. -/
theorem oracleAt_setup2_eq_compiled
    [Nonempty Coin] [Inhabited Msg₂]
    {Out : Type} {tA N TM : ℕ}
    (S : Lfzk.CompiledZk.CircuitSide v7Hash1 v7Hash1_valid
      v7Hash1_openings_pos 3 Coin F
      (Lfzk.LigeroTranscriptInputs.Message
        (Other := Other) (F := F)
        (block := (row (0 : Fin 4)).k)
        (dblock := 2 * (row (0 : Fin 4)).k - 1)
        (r := (row (0 : Fin 4)).openings))
      M nt nlin X dec rootOfKey)
    (body : Merkle.RandomOracle.TwoOracleTree Enc D
      (Lfzk.V1StrongV7TwoSideFinal.Point 0 D Coin X Other F Msg₂
        v7Hash1.params.nl nl₂ v7Hash1.params.rounds rounds₂)
      Coin Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → Coin)
    (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Lfzk.LigeroTranscriptInputs.Message
      (Other := Other) (F := F)
      (block := (row (0 : Fin 4)).k)
      (dblock := 2 * (row (0 : Fin 4)).k - 1)
      (r := (row (0 : Fin 4)).openings))
    (msgOf₂ : Out → ℕ → Msg₂)
    (mt : Fin TM → D)
    (H : Lfzk.V1StrongV7TwoSideFinal.Point 0 D Coin X Other F Msg₂
      v7Hash1.params.nl nl₂ v7Hash1.params.rounds rounds₂ → Coin) :
    let Ssetup := Lfzk.Fork.Transcript.setup2 body
      rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
    let out := Ssetup.proof mt H
    let p := Lfzk.LigeroPairGeometry.ofMessages
      (nl := v7Hash1.params.nl) (w := v7Hash1.params.rounds)
      (Lfzk.NizkDeployedHashTwoField.ctxOf
        rootOf₁ rootOf₂ avOf pubOf out) (msgOf₁ out)
    let st := Lfzk.V1StrongV7TwoSideCutContext.cutState
      Ssetup mt p H
    oracleAt S st p =
      Lfzk.CompiledZk.extOracle (row := v7Hash1.params.row) nlin nt
        (Row.rowValid v7Hash1_valid) S.dom
        (Row.hkrow v7Hash1_valid) v7Hash1_openings_pos dec
        (rootOfKey (Ssetup.context mt H).1,
          (Ssetup.context mt H).2) := by
  let Ssetup := Lfzk.Fork.Transcript.setup2 body
    rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
  let out := Ssetup.proof mt H
  let p := Lfzk.LigeroPairGeometry.ofMessages
    (nl := v7Hash1.params.nl) (w := v7Hash1.params.rounds)
    (Lfzk.NizkDeployedHashTwoField.ctxOf
      rootOf₁ rootOf₂ avOf pubOf out) (msgOf₁ out)
  let st := Lfzk.V1StrongV7TwoSideCutContext.cutState Ssetup mt p H
  have hctx := Lfzk.Fork.CutContext.setup2_context_eq_output_cutState_fst
    body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ mt H
  have hroot : p.1.1 = (Ssetup.context mt H).1 := by
    rfl
  have hcut : st.1.2 = (Ssetup.context mt H).2 :=
    congrArg Prod.snd hctx.symm
  exact oracleAt_eq_of_context S st p
    ((Ssetup.context mt H), avOf out, pubOf out) hroot hcut

/-- The actual compiled terminal event is the local event charged by the
strong V1 two-coordinate FS theorem. -/
theorem forked_accepts_at_cut
    [Nonempty Coin] [Inhabited Msg₂]
    {Out : Type} {tA N TM : ℕ}
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
    (body : Merkle.RandomOracle.TwoOracleTree Enc D
      (Lfzk.V1StrongV7TwoSideFinal.Point 0 D Coin X Other F Msg₂
        v7Hash1.params.nl nl₂ v7Hash1.params.rounds rounds₂)
      Coin Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → Coin)
    (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Lfzk.LigeroTranscriptInputs.Message
      (Other := Other) (F := F)
      (block := (row (0 : Fin 4)).k)
      (dblock := 2 * (row (0 : Fin 4)).k - 1)
      (r := (row (0 : Fin 4)).openings))
    (msgOf₂ : Out → ℕ → Msg₂)
    (mt : Fin TM → D)
    (H : Lfzk.V1StrongV7TwoSideFinal.Point 0 D Coin X Other F Msg₂
      v7Hash1.params.nl nl₂ v7Hash1.params.rounds rounds₂ → Coin)
    (sys : LigeroSystem S.c.ninp M F)
    (challenge : Ligero.V1.Challenge F v7Hash1.params.nw
      v7Hash1.params.nq 1 (Fin nlin ⊕ (Fin nt × Encode.QSide)))
    (payload : Lfzk.V1StrongV7Terminal.Payload 0 F)
    (query : QuerySet (row (0 : Fin 4)).n
      (row (0 : Fin 4)).openings)
    (hbuilt :
      let out := (Lfzk.Fork.Transcript.setup2 body
        rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof mt H
      Lfzk.CompiledZk.zkBuilt (nl := v7Hash1.params.nl)
        (w := v7Hash1.params.rounds)
        (S.Vc (avOf out) (pubOf out)) (msgOf₁ out)
        (fun j => H (Lfzk.Fork.Transcript.hash2
          (nl₁ := v7Hash1.params.nl) (nl₂ := nl₂)
          (w₁ := v7Hash1.params.rounds) (w₂ := rounds₂)
          rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out
          (1 + j.val))) = some sys)
    (haccepts :
      let Ssetup := Lfzk.Fork.Transcript.setup2 body
        rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      Lfzk.V1StrongV7Terminal.accepts 0 S.dom
        (by decide : (row (0 : Fin 4)).openings + v7Hash1.params.q =
          (row (0 : Fin 4)).k)
        baseNodes responseNodes
        (Lfzk.CompiledZk.extOracle (row := v7Hash1.params.row)
          nlin nt (Row.rowValid v7Hash1_valid) S.dom
          (Row.hkrow v7Hash1_valid) v7Hash1_openings_pos dec
          (rootOfKey (Ssetup.context mt H).1,
            (Ssetup.context mt H).2))
        (Lfzk.ZkLigeroV1.stmtOf S.pl nlin sys)
        challenge payload query) :
    let Ssetup := Lfzk.Fork.Transcript.setup2 body
      rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
    let out := Ssetup.proof mt H
    let p := Lfzk.LigeroPairGeometry.ofMessages
      (nl := v7Hash1.params.nl) (w := v7Hash1.params.rounds)
      (Lfzk.NizkDeployedHashTwoField.ctxOf
        rootOf₁ rootOf₂ avOf pubOf out) (msgOf₁ out)
    let st := Lfzk.V1StrongV7TwoSideCutContext.cutState
      Ssetup mt p H
    Lfzk.V1StrongV7Terminal.accepts 0 S.dom
      (by decide : (row (0 : Fin 4)).openings + v7Hash1.params.q =
        (row (0 : Fin 4)).k)
      baseNodes responseNodes
      (oracleAt S st p) (statementAt S st p)
      challenge payload query := by
  let Ssetup := Lfzk.Fork.Transcript.setup2 body
    rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
  let out := Ssetup.proof mt H
  let p := Lfzk.LigeroPairGeometry.ofMessages
    (nl := v7Hash1.params.nl) (w := v7Hash1.params.rounds)
    (Lfzk.NizkDeployedHashTwoField.ctxOf
      rootOf₁ rootOf₂ avOf pubOf out) (msgOf₁ out)
  let st := Lfzk.V1StrongV7TwoSideCutContext.cutState Ssetup mt p H
  have hb : builtAt S st p = some sys := by
    rw [Lfzk.Fork.Local.builtAt_cutState_eq_compiled S Ssetup rootOf₁ rootOf₂
      avOf pubOf msgOf₁ msgOf₂ mt H out]
    exact hbuilt
  have ho := Lfzk.Fork.Local.oracleAt_setup2_eq_compiled S body
    rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ mt H
  have hs := statementAt_eq_of_built S st p sys hb
  dsimp only at ho haccepts ⊢
  rw [ho, hs]
  exact haccepts


end Lfzk.Fork.Local
