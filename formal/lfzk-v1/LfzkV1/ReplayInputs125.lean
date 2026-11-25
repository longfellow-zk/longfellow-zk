import LfzkV1.HashCircuitReplay125
import LfzkV1.MerkleWork125Total
import LfzkV1.TwoFieldCover125

/-! The three analytical lookups and the actual submitted v1 field tape. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LfzkV1.ReplayInputs125

open Bcs.TotalOracleCommit Bcs.TotalOracle Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree
open LfzkV1.CertifiedV1 LfzkV1.CompiledLongfellowAdaptive
open LfzkV1.NizkAdaptiveTwoField (SideCtx)
open LfzkV1.NizkDeployedHash LfzkV1.NizkDeployedHashTwoField
open LfzkV1.HashCircuitReplay125 LfzkV1.TwoFieldCover125
open scoped Classical

variable {C D K Enc Early MsgH MsgS Out : Type}
variable {R : Row} {tA N TM : ℕ}

local notation "Pt" => SignatureBudget125.PairPoint D K Early MsgH MsgS R
local notation "SidePt" => MPoint (SideCtx D K Early) MsgH R.params.nl R.params.rounds
local notation "Role" => Rounds.Role R.params.nl R.params.rounds

/-- Embed the hash side's legacy prefix in the shared transcript space. -/
def sideAddress : SidePt ↪ Pt where
  toFun p := .inr (.inl p)
  inj' _ _ h := Sum.inl.inj (Sum.inr.inj h)

variable [Inhabited MsgH] [Inhabited MsgS]
variable (rootH rootS : Out → D) (avOf : Out → K) (earlyOf : Out → Early)
variable (msgH : Out → ℕ → MsgH) (msgS : Out → ℕ → MsgS)

/-- The submitted point at each scheduled hash-side role. -/
noncomputable def points (out : Out) : Role ↪ Pt :=
  addresses sideAddress (ctxOf rootH rootS avOf earlyOf out) (msgH out)

/-- Freeze the decoded-key source and the two terminal hash-side draws.
The field answers may still vary when they were absent from search. -/
noncomputable def lookups (out : Out) : List Pt :=
  [.inl (rootH out, rootS out), points rootH rootS avOf earlyOf msgH out .ligeroChallenge,
    points rootH rootS avOf earlyOf msgH out .ligeroQuery]

theorem points_eq (out : Out) (role : Role) :
    points rootH rootS avOf earlyOf msgH out role =
      hash2 rootH rootS avOf earlyOf msgH msgS out (1 + role.slot) := by
  rw [hash2_side1 _ _ _ _ _ _ _ role.slot_lt]
  rfl

variable [Nonempty C] [DecidableEq Enc] [Inhabited D] [DecidableEq D] [DecidableEq K]
  [DecidableEq Early] [DecidableEq MsgH] [DecidableEq MsgS]

variable (body : TwoOracleTree Enc D (SignatureBudget125.PairPoint D K Early MsgH MsgS R) C Out tA N)
variable (mt : Fin TM → D)

local notation "S" => setup2 body rootH rootS avOf earlyOf msgH msgS

include msgS body mt

omit [DecidableEq K] [DecidableEq Early] [DecidableEq MsgH] [DecidableEq MsgS] in
theorem tape_eq (H : Pt → C) :
    roleTape (points rootH rootS avOf earlyOf msgH ((S).proof mt H)) H =
      slice1 R v7SigHahn ((S).challenges mt H) := by
  funext j
  change H (points rootH rootS avOf earlyOf msgH ((S).proof mt H) (Rounds.Role.indexEquiv.symm j)) =
    H (hash2 rootH rootS avOf earlyOf msgH msgS ((S).proof mt H) (1 + j.val))
  rw [points_eq rootH rootS avOf earlyOf msgH msgS]
  congr 2
  exact congrArg (fun k => 1 + k.val) (Rounds.Role.indexEquiv.apply_symm_apply j)

omit [DecidableEq K] [DecidableEq Early] [DecidableEq MsgH] [DecidableEq MsgS] in
theorem terminal_revealed (H : Pt → C) :
    let ps := points rootH rootS avOf earlyOf msgH ((S).proof mt H)
    let seen := ReplayView125.revealed ((S).search mt) (lookups rootH rootS avOf earlyOf msgH) H
    ps .ligeroChallenge ∈ seen ∧ ps .ligeroQuery ∈ seen := by
  dsimp only
  rw [(S).proof_eq mt H]
  exact ⟨List.mem_append_right _ (by simp [lookups]), List.mem_append_right _ (by simp [lookups])⟩

omit [DecidableEq K] [DecidableEq Early] [DecidableEq MsgH] [DecidableEq MsgS] in
theorem view_fixes_output_and_cut (H U : Pt → C)
    (hview : ReplayView125.view ((S).search mt) (lookups rootH rootS avOf earlyOf msgH) U =
      ReplayView125.view ((S).search mt) (lookups rootH rootS avOf earlyOf msgH) H) :
    (S).proof mt U = (S).proof mt H ∧ (S).context mt U = (S).context mt H := by
  refine ⟨?_, MerkleWork125.totalContext_eq_of_replay_view S mt _ H U hview⟩
  rw [(S).proof_eq mt U, (S).proof_eq mt H]
  exact congrArg (fun run => run.1.1) hview

omit msgS body mt

omit [Nonempty C] [DecidableEq Enc] [Inhabited D] [DecidableEq D] [DecidableEq K]
  [DecidableEq Early] [DecidableEq MsgH] [DecidableEq MsgS] [Inhabited MsgS] in
theorem role_of_field_slot (out : Out) (j : ℕ) (hj : j < Rounds.Role.layerBase R.params.rounds R.params.nl + 1) :
    queryRole (sideAddress (msgPoint (ctxOf rootH rootS avOf earlyOf out) msgH out j) : Pt) =
      .field := by
  let p : SidePt := msgPoint (ctxOf rootH rootS avOf earlyOf out) msgH out j
  have hlen : j < Rounds.Role.length R.params.nl R.params.rounds := by
    dsimp [Rounds.Role.length]
    omega
  have hslot : p.role.slot = j := slot_msgPoint (ctxOf rootH rootS avOf earlyOf out) msgH out hlen
  have hf : p.role.slot < Rounds.Role.layerBase R.params.rounds R.params.nl + 1 := hslot ▸ hj
  change queryRole (sideAddress p : Pt) = .field
  cases hrole : p.role <;> simp [queryRole, sideAddress, hrole, Rounds.Role.slot] at hf ⊢

omit [Nonempty C] [DecidableEq Enc] [Inhabited D] [DecidableEq D] [DecidableEq K]
  [DecidableEq Early] [DecidableEq MsgH] [DecidableEq MsgS] [Inhabited MsgS] in
theorem role_of_lookup (out : Out) (p : Pt)
    (hp : p ∈ lookups rootH rootS avOf earlyOf msgH out) :
    queryRole p ≠ .field := by
  simp only [lookups, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · simp [queryRole]
  · let role : Role := .ligeroChallenge
    let p : SidePt := msgPoint (ctxOf rootH rootS avOf earlyOf out) msgH out role.slot
    have h : p.role.slot = role.slot := slot_msgPoint _ _ _ role.slot_lt
    have hr : p.role = role := Rounds.Role.index_bijective.1 (Fin.ext h)
    change queryRole (sideAddress p : Pt) ≠ .field
    simp [queryRole, sideAddress, hr, role]
  · let role : Role := .ligeroQuery
    let p : SidePt := msgPoint (ctxOf rootH rootS avOf earlyOf out) msgH out role.slot
    have h : p.role.slot = role.slot := slot_msgPoint _ _ _ role.slot_lt
    have hr : p.role = role := Rounds.Role.index_bijective.1 (Fin.ext h)
    change queryRole (sideAddress p : Pt) ≠ .field
    simp [queryRole, sideAddress, hr, role]

omit [Nonempty C] [DecidableEq Enc] [Inhabited D] [DecidableEq D] [DecidableEq K]
  [DecidableEq Early] [DecidableEq MsgH] [DecidableEq MsgS] [Inhabited MsgS] in
theorem field_not_replayed (out : Out) (j : ℕ) (hj : j < Rounds.Role.layerBase R.params.rounds R.params.nl + 1) :
    sideAddress (msgPoint (ctxOf rootH rootS avOf earlyOf out) msgH out j) ∉
      (lookups rootH rootS avOf earlyOf msgH out : List Pt) := by
  intro hm
  exact role_of_lookup rootH rootS avOf earlyOf msgH out _ hm
    (role_of_field_slot rootH rootS avOf earlyOf msgH out j hj)

end LfzkV1.ReplayInputs125
