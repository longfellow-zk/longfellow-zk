import LfzkV1.V7Soundness125
import LfzkV1.IdealSampler
import ECDSA.Pratt
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Premise inhabitation (non-vacuity) for `V7Soundness125`

Constructs a toy instance discharging every premise of
`V7Soundness125.annotated_fs_knowledge_soundness_125` for all four registered
v7 hash profiles `i : Fin 4`, using empty-gate circuits of the exact layer
counts, `IdealSampler.Coins` for all balanced challenge decoders, tagged
disjoint Merkle codecs, and a canonical message carrier.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

namespace LfzkV1.V7Soundness125Instance

open Finset Bcs.TotalOracleCommit Merkle.MH Merkle.RandomOracle
open LigeroFamily LigeroFamily.ReedSolomon
open LfzkV1.CertifiedV1 LfzkV1.CompiledZk LfzkV1.CompiledZkDeployedHash
open LfzkV1.Arith (QuadCircuit)
open LfzkV1.RbrZkLongfellow (ZkCode)
open LfzkV1.CompiledLongfellow (Col)
open LfzkV1.NizkAdaptiveTwoField (SideCtx check2)
open LfzkV1.SoundnessAudit LfzkV1.TwoFieldV1Rows LfzkV1.MerkleWork125
open LfzkV1.LigeroV1Rows LfzkV1.V7Soundness125 LfzkV1.ZkArithProfile
open scoped Classical

abbrev GF128 := GaloisField 2 128

local instance instFintypeGF128 : Fintype GF128 := Fintype.ofFinite _

instance instFactP256Prime : Fact p256Order.Prime :=
  ⟨ECDSA.prime_115792089210356248762697446949407573530086143415290314195533631308867097853951⟩

abbrev FP256 := GaloisField p256Order 1

local instance instFintypeFP256 : Fintype FP256 := Fintype.ofFinite _

private theorem card_GF128 : Fintype.card GF128 = 2 ^ 128 := by
  rw [← Nat.card_eq_fintype_card]
  exact GaloisField.card 2 128 (by decide)

private theorem card_FP256 : Fintype.card FP256 = p256Order := by
  rw [← Nat.card_eq_fintype_card]
  simpa using GaloisField.card p256Order 1 (by decide)

@[implicit_reducible]
private def sumcheckInterpOfCard {F : Type} [Field F] [Fintype F] (hcard : 2 < Fintype.card F) :
    SumcheckV1Interp F := by
  have hlt : ({0, 1} : Finset F).card < (Finset.univ : Finset F).card := by
    calc ({0, 1} : Finset F).card ≤ 2 := Finset.card_le_two
      _ < Fintype.card F := hcard
      _ = (Finset.univ : Finset F).card := (Finset.card_univ).symm
  have hex := Finset.exists_mem_notMem_of_card_lt_card hlt
  let x : F := Classical.choose hex
  have hx : x ∉ ({0, 1} : Finset F) := (Classical.choose_spec hex).2
  have hx0 : x ≠ 0 := fun h => hx (by simp [h])
  have hx1 : x ≠ 1 := fun h => hx (by simp [h])
  exact {
    pts := ![0, 1, x]
    pts_inj := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [hx0.symm, hx1.symm]
    pts_zero := rfl
    pts_one := rfl
  }

local instance instInterpGF128 : SumcheckV1Interp GF128 :=
  sumcheckInterpOfCard (by rw [card_GF128]; norm_num)

local instance instInterpFP256 : SumcheckV1Interp FP256 :=
  sumcheckInterpOfCard (by rw [card_FP256]; unfold p256Order; norm_num)

private theorem v7HashRow_valid (i : Fin 4) : (v7HashRow i).Valid := by
  fin_cases i
  · exact v7Hash1_valid
  · exact v7Hash2_valid
  · exact v7Hash3_valid
  · exact v7Hash4_valid

private theorem v7HashRow_openings_pos (i : Fin 4) : 0 < (v7HashRow i).params.row.openings := by
  fin_cases i <;> decide

private theorem v7HashRow_fieldSize (i : Fin 4) :
    Fintype.card GF128 = (v7HashRow i).params.row.fieldSize := by
  rw [card_GF128]
  fin_cases i <;> rfl

private theorem v7SigHahn_fieldSize :
    Fintype.card FP256 = v7SigHahn.params.row.fieldSize := by
  rw [card_FP256]
  rfl

private def emptyCircuit (F : Type) (nl : ℕ) : QuadCircuit F where
  layers := List.replicate nl []
  ninp := 0
  npub := 0

private theorem emptyCircuit_nl (F : Type) (nl : ℕ) : (emptyCircuit F nl).nl = nl := by
  simp [emptyCircuit, QuadCircuit.nl]

private theorem emptyCircuit_gates (F : Type) (nl ly : ℕ) :
    (emptyCircuit F nl).gates ly = [] := by
  unfold emptyCircuit QuadCircuit.gates
  by_cases h : ly < nl
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp
  · rw [List.getD_eq_default _ _ (by simpa using h)]

private theorem emptyCircuit_isolated (F : Type) [Field F] (nl : ℕ) :
    (emptyCircuit F nl).Isolated := by
  intro ly _ t
  have hlen : ((emptyCircuit F nl).gates ly).length = 0 := by rw [emptyCircuit_gates]; rfl
  have hlt : t.val < 0 := by simpa [hlen] using t.isLt
  exact (Nat.not_lt_zero _ hlt).elim

private theorem emptyCircuit_deadEnd (F : Type) [Field F] (nl : ℕ) :
    (emptyCircuit F nl).DeadEnd := by
  intro ly _ t ht
  rw [emptyCircuit_gates] at ht
  cases ht

private theorem emptyCircuit_wellFormed {F : Type} [Field F] [DecidableEq F]
    {nl logv L : ℕ} {lw : ℕ → ℕ}
    (hnl : 0 < nl) (hlogv : logv ≤ L) (hlw : ∀ ly < nl, lw ly ≤ L) :
    WellFormedP (emptyCircuit F nl) logv lw L := by
  refine ⟨by rw [emptyCircuit_nl]; exact hnl, hlogv, ?_, ?_, ?_⟩
  · intro ly hly
    rw [emptyCircuit_nl] at hly
    exact hlw ly hly
  · simp [emptyCircuit]
  · intro ly _ t ht
    rw [emptyCircuit_gates] at ht
    cases ht

private def trivialPlacement {w nw nq : ℕ} (hnw : 0 < nw) (hw : 0 < w) :
    Encode.Placement 0 1 w nw nq 0 where
  cell := fun _ => (⟨0, hnw⟩, ⟨0, hw⟩)
  cell_inj := by
    intro a b _
    rcases a with a | a <;> rcases b with b | b
    · exact a.elim0
    · exact a.elim0
    · exact b.elim0
    · exact congrArg Sum.inr (Subsingleton.elim a b)
  qcell := Fin.elim0
  qcell_inj := fun a => a.elim0

private abbrev ToyMsg (F : Type) (r w n : ℕ) :=
  (F × F) ⊕ (F × F) ⊕ LigeroFamily.Response F r w n 1 ⊕ Unit

local instance instFintypeResponse {F : Type} [Fintype F] {r w n : ℕ} :
    Fintype (LigeroFamily.Response F r w n 1) :=
  letI : Finite (LigeroFamily.Response F r w n 1) := Finite.of_injective
    (fun resp : LigeroFamily.Response F r w n 1 => (resp.proximity, resp.linear, resp.quadratic))
    (fun a b h => by cases a; cases b; simp_all)
  Fintype.ofFinite _

private instance instInhabitedToyMsg {F : Type} {r w n : ℕ} : Inhabited (ToyMsg F r w n) :=
  ⟨Sum.inr (Sum.inr (Sum.inr ()))⟩

private def toyZkCode {C F X Q : Type} [Field F] [DecidableEq F]
    (c : QuadCircuit F) (logv L : ℕ)
    (dInit : C → (Fin logv → F) × F × F) (dPair : C → F × F) (dF : C → F)
    (dChal : C → X) (dQuery : C → Q) {r w n : ℕ} :
    ZkCode C F X Q (ToyMsg F r w n) (Fin logv → F) 1 c.ninp L 0 where
  st0 G := ⟨0, 0, Vector.ofFn Fin.elim0, padG L G, padG L G⟩
  stNext bnd wc0 wc1 :=
    ⟨wc0, wc1, Vector.ofFn Fin.elim0, evenPt L (ZkArithInit.ptOf bnd),
      oddPt L (ZkArithInit.ptOf bnd)⟩
  eqqOf ly st b a bnd :=
    Arith.bindGhAll (c.gates ly) b a st.g0 st.g1 (evenPt L (ZkArithInit.ptOf bnd))
      (oddPt L (ZkArithInit.ptOf bnd))
  npub := c.npub
  inCoeffs bnd a i :=
    eq_mle_basis i.val (evenPt L (ZkArithInit.ptOf bnd)) +
      a * eq_mle_basis i.val (oddPt L (ZkArithInit.ptOf bnd))
  pubBinding _ _ := 0
  nlin := 0
  nt := 0
  roundOf m := match m with
    | Sum.inl (t0, t2) => ⟨t0, t2, ⟨0, by omega⟩, ⟨0, by omega⟩⟩
    | _ => ⟨0, 0, ⟨0, by omega⟩, ⟨0, by omega⟩⟩
  closeOf m := match m with
    | Sum.inr (Sum.inl (w0, w1)) => ⟨w0, w1, ⟨0, by omega⟩, ⟨0, by omega⟩, ⟨0, by omega⟩⟩
    | _ => ⟨0, 0, ⟨0, by omega⟩, ⟨0, by omega⟩, ⟨0, by omega⟩⟩
  decodeInit := dInit
  decodePair := dPair
  decodeF := dF
  decodeChal := dChal
  decodeQuery := dQuery

private theorem toyZkCode_agrees {C F X Q : Type} [Field F] [DecidableEq F]
    {nl logv L r w n : ℕ}
    (dInit : C → (Fin logv → F) × F × F) (dPair : C → F × F) (dF : C → F)
    (dChal : C → X) (dQuery : C → Q) :
    CodeAgreesP (emptyCircuit F nl) Fin.elim0 L
      (toyZkCode (emptyCircuit F nl) logv L dInit dPair dF dChal dQuery (r := r) (w := w) (n := n)) where
  hst _ _ _ := ⟨rfl, rfl⟩
  heqq _ _ _ _ _ _ := rfl
  hnpub := rfl
  hinC _ _ i := i.elim0
  hpubB _ _ := by
    show (0 : F) = _
    exact (Finset.sum_eq_zero fun x _ => x.elim0).symm

private def toyRespOf {F : Type} [Field F] {r w n : ℕ} (m : ToyMsg F r w n) :
    LigeroFamily.Response F r w n 1 :=
  match m with
  | Sum.inr (Sum.inr (Sum.inl resp)) => resp
  | _ => {
      proximity := fun _ _ => 0
      linear := fun _ _ => 0
      quadratic := fun _ _ => 0
    }

private def toyFieldMessages {C F X Q : Type} [Field F] [DecidableEq F]
    {nl logv L r w n : ℕ} {lw : ℕ → ℕ}
    (dInit : C → (Fin logv → F) × F × F) (dPair : C → F × F) (dF : C → F)
    (dChal : C → X) (dQuery : C → Q) :
    CanonicalHashPrefix125.FieldMessages
      (toyZkCode (emptyCircuit F nl) logv L dInit dPair dF dChal dQuery (r := r) (w := w) (n := n))
      nl lw where
  valid role m :=
    match role with
    | .layerPair ly => if ly.val = 0 then m = Sum.inr (Sum.inr (Sum.inr ())) else ∃ p, m = Sum.inr (Sum.inl p)
    | .sumcheck _ _ => ∃ p, m = Sum.inl p
    | .inputBind => ∃ p, m = Sum.inr (Sum.inl p)
    | .ligeroChallenge => m = Sum.inr (Sum.inr (Sum.inr ()))
    | .ligeroQuery => ∃ resp, m = Sum.inr (Sum.inr (Sum.inl resp))
  eq_of_payload_eq := by
    intro role hne a b ha hb hp
    cases role with
    | layerPair ly =>
      dsimp only at ha hb
      split_ifs at ha hb with h0
      · exact ha.trans hb.symm
      · rcases ha with ⟨⟨a0, a1⟩, rfl⟩
        rcases hb with ⟨⟨b0, b1⟩, rfl⟩
        simp only [CanonicalHashPrefix125.payload, h0, ↓reduceIte, toyZkCode,
          Option.some.injEq, Prod.mk.injEq] at hp
        rw [hp.1, hp.2]
    | sumcheck ly j =>
      rcases ha with ⟨⟨a0, a1⟩, rfl⟩
      rcases hb with ⟨⟨b0, b1⟩, rfl⟩
      simp only [CanonicalHashPrefix125.payload, toyZkCode, Option.some.injEq, Prod.mk.injEq] at hp
      rw [hp.1, hp.2]
    | inputBind =>
      rcases ha with ⟨⟨a0, a1⟩, rfl⟩
      rcases hb with ⟨⟨b0, b1⟩, rfl⟩
      simp only [CanonicalHashPrefix125.payload, toyZkCode, Option.some.injEq, Prod.mk.injEq] at hp
      rw [hp.1, hp.2]
    | ligeroChallenge =>
      exact ha.trans hb.symm
    | ligeroQuery => exact (hne rfl).elim
  round_pads := by
    intro ly j a b ha hb
    rcases ha with ⟨_, rfl⟩
    rcases hb with ⟨_, rfl⟩
    exact ⟨rfl, rfl⟩
  close_pads := by
    intro role hrole a b ha hb
    rcases hrole with rfl | ⟨ly, hly, rfl⟩
    · rcases ha with ⟨_, rfl⟩
      rcases hb with ⟨_, rfl⟩
      exact ⟨rfl, rfl⟩
    · dsimp only at ha hb
      rw [if_neg hly] at ha hb
      rcases ha with ⟨_, rfl⟩
      rcases hb with ⟨_, rfl⟩
      exact ⟨rfl, rfl⟩

private theorem v7Hash_row_props (i : Fin 4) :
    0 < (v7HashRow i).params.nl ∧
    v7HashLogv i ≤ 20 ∧
    (∀ ly < (v7HashRow i).params.nl, (v7HashRow i).params.logw ly ≤ 20) ∧
    0 < (v7HashRow i).params.nw ∧
    0 < (v7HashRow i).params.q ∧
    (v7HashRow i).params.row.openings + (v7HashRow i).params.q + (v7HashRow i).params.row.n ≤ 2 ^ 128 := by
  refine ⟨by fin_cases i <;> decide, by fin_cases i <;> decide, by fin_cases i <;> decide,
    by fin_cases i <;> decide, by fin_cases i <;> decide, ?_⟩
  have hle : (v7HashRow i).params.row.openings + (v7HashRow i).params.q + (v7HashRow i).params.row.n ≤ 10000 := by
    fin_cases i <;> decide
  exact hle.trans (by norm_num)

private theorem v7Sig_row_props :
    0 < v7SigHahn.params.nl ∧
    8 ≤ 20 ∧
    (∀ ly < v7SigHahn.params.nl, v7SigHahn.params.logw ly ≤ 20) ∧
    0 < v7SigHahn.params.nw ∧
    0 < v7SigHahn.params.q ∧
    v7SigHahn.params.row.openings + v7SigHahn.params.q + v7SigHahn.params.row.n ≤ p256Order := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_⟩
  have hle : v7SigHahn.params.row.openings + v7SigHahn.params.q + v7SigHahn.params.row.n ≤ 10000 := by decide
  exact hle.trans (by unfold p256Order; norm_num)

private abbrev Digest256 := Fin 256 → Bool

private theorem card_Digest256 : Fintype.card Digest256 = 2 ^ 256 := by
  simp [Digest256]

private def toyQuerySet {n r : ℕ} (hlt : r ≤ n) : QuerySet n r :=
  ⟨Finset.univ.filter (fun j : Fin n => j.val < r), by
    have hbij : (Finset.univ.filter (fun j : Fin n => j.val < r)).card =
        (Finset.univ : Finset (Fin r)).card := by
      refine Finset.card_bij
        (fun (j : Fin n) (hj : j ∈ Finset.univ.filter (fun j : Fin n => j.val < r)) =>
          (⟨j.val, (Finset.mem_filter.mp hj).2⟩ : Fin r)) ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro a _ b _ h; exact Fin.ext (congrArg (Fin.val : Fin r → ℕ) h)
      · intro b _; exact ⟨⟨b.val, lt_of_lt_of_le b.isLt hlt⟩, by simp [b.isLt], by ext; rfl⟩
    simpa using hbij⟩

private abbrev ChalH (i : Fin 4) := ZkLigeroV1.Chal GF128 (v7HashRow i).params.nw (v7HashRow i).params.nq 0 0
private abbrev QryH (i : Fin 4) := LigeroV1LayerStep.Qry (v7HashRow i).params.row
private abbrev ChalS := ZkLigeroV1.Chal FP256 v7SigHahn.params.nw v7SigHahn.params.nq 0 0
private abbrev QryS := LigeroV1LayerStep.Qry v7SigHahn.params.row
private abbrev MsgH (i : Fin 4) :=
  ToyMsg GF128 (v7HashRow i).params.row.openings (v7HashRow i).params.q (v7HashRow i).params.row.n
private abbrev MsgS :=
  ToyMsg FP256 v7SigHahn.params.row.openings v7SigHahn.params.q v7SigHahn.params.row.n
private abbrev ToyEnc (i : Fin 4) :=
  (Unit × Col GF128 (v7HashRow i).params.nw (v7HashRow i).params.nq) ⊕
  (Unit × Col FP256 v7SigHahn.params.nw v7SigHahn.params.nq) ⊕
  (Digest256 × Digest256)
private abbrev ToyInitH (i : Fin 4) := (Fin (v7HashLogv i) → GF128) × GF128 × GF128
private abbrev ToyInitS := (Fin 8 → FP256) × FP256 × FP256
private abbrev ToyCoins (i : Fin 4) :=
  IdealSampler.Coins (ToyInitH i) ToyInitS GF128 (ChalH i) (QryH i) FP256 ChalS QryS GF128

local instance instFintypePairPoint (i : Fin 4) :
    Fintype (SignatureBudget125.PairPoint Digest256 GF128 Unit (MsgH i) MsgS (v7HashRow i)) :=
  Fintype.ofFinite _

local instance instDecidableEqPairPoint (i : Fin 4) :
    DecidableEq (SignatureBudget125.PairPoint Digest256 GF128 Unit (MsgH i) MsgS (v7HashRow i)) :=
  Classical.decEq _

local instance instFintypeSpace (i : Fin 4) :
    Fintype ((Fin 14000 → Digest256) ×
      (SignatureBudget125.PairPoint Digest256 GF128 Unit (MsgH i) MsgS (v7HashRow i) → ToyCoins i)) :=
  Fintype.ofFinite _

local instance (priority := high) instFintypeQryH (i : Fin 4) : Fintype (QryH i) :=
  Fintype.ofFinite _

local instance (priority := high) instFintypeQryS : Fintype QryS :=
  Fintype.ofFinite _

local instance instNonemptyChalH (i : Fin 4) : Nonempty (ChalH i) :=
  ⟨fun _ => {
    proximity := fun _ => 0
    linear := fun e => by rcases e with e | ⟨e, _⟩ <;> exact e.elim0
    quadratic := fun _ => 0
  }⟩

local instance instNonemptyChalS : Nonempty ChalS :=
  ⟨fun _ => {
    proximity := fun _ => 0
    linear := fun e => by rcases e with e | ⟨e, _⟩ <;> exact e.elim0
    quadratic := fun _ => 0
  }⟩

local instance instNonemptyQryH (i : Fin 4) : Nonempty (QryH i) :=
  ⟨toyQuerySet (by fin_cases i <;> decide)⟩

local instance instNonemptyQryS : Nonempty QryS :=
  ⟨toyQuerySet (by decide)⟩

local instance instNonemptyToyCoins (i : Fin 4) : Nonempty (ToyCoins i) := by
  unfold ToyCoins IdealSampler.Coins TwoFieldV1Rows.TwoFieldCoins TwoFieldV1Rows.SideCoins
  infer_instance

private def toyCodecH (i : Fin 4) :
    Codec Unit (Col GF128 (v7HashRow i).params.nw (v7HashRow i).params.nq) Digest256 (ToyEnc i) where
  leafEnc := Sum.inl
  nodeEnc dd := Sum.inr (Sum.inr dd)

private def toyCodecS (i : Fin 4) :
    Codec Unit (Col FP256 v7SigHahn.params.nw v7SigHahn.params.nq) Digest256 (ToyEnc i) where
  leafEnc sm := Sum.inr (Sum.inl sm)
  nodeEnc dd := Sum.inr (Sum.inr dd)

private def toyDecH (i : Fin 4) : RoleDecoders (toyCodecH i) where
  leafDec
    | Sum.inl sm => some sm
    | _ => none
  nodeDec
    | Sum.inr (Sum.inr dd) => some dd
    | _ => none
  leaf_roundTrip _ := rfl
  node_roundTrip _ := rfl
  leaf_sound x sm h := by cases x <;> simp_all [toyCodecH]
  node_sound x dd h := by
    cases x with
    | inl _ => simp at h
    | inr y => cases y <;> simp_all [toyCodecH]

private def toyDecS (i : Fin 4) : RoleDecoders (toyCodecS i) where
  leafDec
    | Sum.inr (Sum.inl sm) => some sm
    | _ => none
  nodeDec
    | Sum.inr (Sum.inr dd) => some dd
    | _ => none
  leaf_roundTrip _ := rfl
  node_roundTrip _ := rfl
  leaf_sound x sm h := by
    cases x with
    | inl _ => simp at h
    | inr y => cases y <;> simp_all [toyCodecS]
  node_sound x dd h := by
    cases x with
    | inl _ => simp at h
    | inr y => cases y <;> simp_all [toyCodecS]

private def toyInputLength (i : Fin 4) : ToyEnc i → ℕ
  | Sum.inl _ => leafInputBytes (v7HashTableauRows i) 16
  | Sum.inr (Sum.inl _) => leafInputBytes 19 32
  | Sum.inr (Sum.inr _) => 64

private def toyHashSide (i : Fin 4) :
    CircuitSide (v7HashRow i) (v7HashRow_valid i) (v7HashRow_openings_pos i) (v7HashLogv i)
      (ToyCoins i) GF128 (MsgH i) 1 0 0 Unit (toyDecH i) Prod.fst where
  c := emptyCircuit GF128 (v7HashRow i).params.nl
  hnl := emptyCircuit_nl GF128 (v7HashRow i).params.nl
  L := 20
  hwf := emptyCircuit_wellFormed (v7Hash_row_props i).1 (v7Hash_row_props i).2.1
    (v7Hash_row_props i).2.2.1
  hiso := emptyCircuit_isolated GF128 (v7HashRow i).params.nl
  hde := emptyCircuit_deadEnd GF128 (v7HashRow i).params.nl
  pubIn _ _ := Fin.elim0
  pl := trivialPlacement (v7Hash_row_props i).2.2.2.1 (v7Hash_row_props i).2.2.2.2.1
  dom := Domain.ofCardLE (by rw [card_GF128]; exact (v7Hash_row_props i).2.2.2.2.2)
  Vc _ _ := toyZkCode (emptyCircuit GF128 (v7HashRow i).params.nl) (v7HashLogv i) 20
    (IdealSampler.initial₁ _ _ _ _ _ _ _ _ _).decode
    (IdealSampler.pair₁ _ _ _ _ _ _ _ _ _).decode
    (IdealSampler.element₁ _ _ _ _ _ _ _ _ _).decode
    (IdealSampler.challenge₁ _ _ _ _ _ _ _ _ _).decode
    (IdealSampler.query₁ _ _ _ _ _ _ _ _ _).decode
  hnlin _ _ := rfl
  hnt _ _ := rfl
  hV _ _ := toyZkCode_agrees _ _ _ _ _
  hst0 _ _ _ := ⟨rfl, rfl⟩
  respOf := toyRespOf
  kinit := (IdealSampler.initial₁ _ _ _ _ _ _ _ _ _).k
  kpair := (IdealSampler.pair₁ _ _ _ _ _ _ _ _ _).k
  k := (IdealSampler.element₁ _ _ _ _ _ _ _ _ _).k
  kchal := (IdealSampler.challenge₁ _ _ _ _ _ _ _ _ _).k
  kq := (IdealSampler.query₁ _ _ _ _ _ _ _ _ _).k
  hbalInit _ _ := (IdealSampler.initial₁ _ _ _ _ _ _ _ _ _).hbal
  hbalPair _ _ := (IdealSampler.pair₁ _ _ _ _ _ _ _ _ _).hbal
  hbalF _ _ := (IdealSampler.element₁ _ _ _ _ _ _ _ _ _).hbal
  hbalChal _ _ := (IdealSampler.challenge₁ _ _ _ _ _ _ _ _ _).hbal
  hbalQuery _ _ := (IdealSampler.query₁ _ _ _ _ _ _ _ _ _).hbal
  hkinit := by
    have h := (IdealSampler.initial₁
      ((Fin (v7HashLogv i) → GF128) × GF128 × GF128)
      ((Fin 8 → FP256) × FP256 × FP256)
      GF128 (ChalH i) (QryH i) FP256 ChalS QryS GF128).hexact
    have hc : Fintype.card ((Fin (v7HashLogv i) → GF128) × GF128 × GF128) =
        Fintype.card GF128 ^ (v7HashLogv i + 2) := by
      rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
        pow_add, pow_two]
    rw [hc] at h
    convert h
  hkpair := by
    have h := (IdealSampler.pair₁
      ((Fin (v7HashLogv i) → GF128) × GF128 × GF128)
      ((Fin 8 → FP256) × FP256 × FP256)
      GF128 (ChalH i) (QryH i) FP256 ChalS QryS GF128).hexact
    rw [Fintype.card_prod] at h
    convert h
  hk := by convert (IdealSampler.element₁ _ _ _ _ _ _ _ _ _).hexact
  hkchal := by convert (IdealSampler.challenge₁ _ _ _ _ _ _ _ _ _).hexact
  hkq := by convert (IdealSampler.query₁ _ _ _ _ _ _ _ _ _).hexact
  hF := v7HashRow_fieldSize i

private def toySigSide (i : Fin 4) :
    CircuitSide v7SigHahn v7SigHahn_valid v7SigHahn_openings_pos 8
      (ToyCoins i) FP256 MsgS 1 0 0 Unit (toyDecS i) Prod.snd where
  c := emptyCircuit FP256 v7SigHahn.params.nl
  hnl := emptyCircuit_nl FP256 v7SigHahn.params.nl
  L := 20
  hwf := emptyCircuit_wellFormed v7Sig_row_props.1 v7Sig_row_props.2.1 v7Sig_row_props.2.2.1
  hiso := emptyCircuit_isolated FP256 v7SigHahn.params.nl
  hde := emptyCircuit_deadEnd FP256 v7SigHahn.params.nl
  pubIn _ _ := Fin.elim0
  pl := trivialPlacement v7Sig_row_props.2.2.2.1 v7Sig_row_props.2.2.2.2.1
  dom := Domain.ofCardLE (by rw [card_FP256]; exact v7Sig_row_props.2.2.2.2.2)
  Vc _ _ := toyZkCode (emptyCircuit FP256 v7SigHahn.params.nl) 8 20
    (IdealSampler.initial₂ (ToyInitH i) ToyInitS GF128 (ChalH i) (QryH i) FP256 ChalS QryS GF128).decode
    (IdealSampler.pair₂ (ToyInitH i) ToyInitS GF128 (ChalH i) (QryH i) FP256 ChalS QryS GF128).decode
    (IdealSampler.element₂ (ToyInitH i) ToyInitS GF128 (ChalH i) (QryH i) FP256 ChalS QryS GF128).decode
    (IdealSampler.challenge₂ (ToyInitH i) ToyInitS GF128 (ChalH i) (QryH i) FP256 ChalS QryS GF128).decode
    (IdealSampler.query₂ (ToyInitH i) ToyInitS GF128 (ChalH i) (QryH i) FP256 ChalS QryS GF128).decode
  hnlin _ _ := rfl
  hnt _ _ := rfl
  hV _ _ := toyZkCode_agrees _ _ _ _ _
  hst0 _ _ _ := ⟨rfl, rfl⟩
  respOf := toyRespOf
  kinit := (IdealSampler.initial₂ (ToyInitH i) ToyInitS GF128 (ChalH i) (QryH i) FP256 ChalS QryS GF128).k
  kpair := (IdealSampler.pair₂ (ToyInitH i) ToyInitS GF128 (ChalH i) (QryH i) FP256 ChalS QryS GF128).k
  k := (IdealSampler.element₂ (ToyInitH i) ToyInitS GF128 (ChalH i) (QryH i) FP256 ChalS QryS GF128).k
  kchal := (IdealSampler.challenge₂ (ToyInitH i) ToyInitS GF128 (ChalH i) (QryH i) FP256 ChalS QryS GF128).k
  kq := (IdealSampler.query₂ (ToyInitH i) ToyInitS GF128 (ChalH i) (QryH i) FP256 ChalS QryS GF128).k
  hbalInit _ _ := (IdealSampler.initial₂ (ToyInitH i) ToyInitS GF128 (ChalH i) (QryH i) FP256 ChalS QryS GF128).hbal
  hbalPair _ _ := (IdealSampler.pair₂ (ToyInitH i) ToyInitS GF128 (ChalH i) (QryH i) FP256 ChalS QryS GF128).hbal
  hbalF _ _ := (IdealSampler.element₂ (ToyInitH i) ToyInitS GF128 (ChalH i) (QryH i) FP256 ChalS QryS GF128).hbal
  hbalChal _ _ := (IdealSampler.challenge₂ (ToyInitH i) ToyInitS GF128 (ChalH i) (QryH i) FP256 ChalS QryS GF128).hbal
  hbalQuery _ _ := (IdealSampler.query₂ (ToyInitH i) ToyInitS GF128 (ChalH i) (QryH i) FP256 ChalS QryS GF128).hbal
  hkinit := by
    have h := (IdealSampler.initial₂ (ToyInitH i) ToyInitS GF128 (ChalH i) (QryH i) FP256 ChalS QryS GF128).hexact
    have hc : Fintype.card ToyInitS = Fintype.card FP256 ^ (8 + 2) := by
      rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
        pow_add, pow_two]
    rw [hc] at h
    convert h
  hkpair := by
    have h := (IdealSampler.pair₂ (ToyInitH i) ToyInitS GF128 (ChalH i) (QryH i) FP256 ChalS QryS GF128).hexact
    rw [Fintype.card_prod] at h
    convert h
  hk := by convert (IdealSampler.element₂ (ToyInitH i) ToyInitS GF128 (ChalH i) (QryH i) FP256 ChalS QryS GF128).hexact
  hkchal := by convert (IdealSampler.challenge₂ (ToyInitH i) ToyInitS GF128 (ChalH i) (QryH i) FP256 ChalS QryS GF128).hexact
  hkq := by convert (IdealSampler.query₂ (ToyInitH i) ToyInitS GF128 (ChalH i) (QryH i) FP256 ChalS QryS GF128).hexact
  hF := v7SigHahn_fieldSize

private def toyMsgOfRole (i : Fin 4) (role : V7FixedTape125.HashRoleAt i) : MsgH i :=
  match role with
  | .layerPair ly => if ly.val = 0 then Sum.inr (Sum.inr (Sum.inr ())) else Sum.inr (Sum.inl (0, 0))
  | .sumcheck _ _ => Sum.inl (0, 0)
  | .inputBind => Sum.inr (Sum.inl (0, 0))
  | .ligeroChallenge => Sum.inr (Sum.inr (Sum.inr ()))
  | .ligeroQuery => Sum.inr (Sum.inr (Sum.inl (toyRespOf (Sum.inr (Sum.inr (Sum.inr ()))))))

private def toyHashMsg (i : Fin 4) (k : ℕ) : MsgH i :=
  if h : ∃ r : V7FixedTape125.HashRoleAt i, r.slot = k then
    toyMsgOfRole i (Classical.choose h)
  else
    default

private theorem toyHashMsg_slot (i : Fin 4) (role : V7FixedTape125.HashRoleAt i) :
    toyHashMsg i role.slot = toyMsgOfRole i role := by
  unfold toyHashMsg
  have hex : ∃ r : V7FixedTape125.HashRoleAt i, r.slot = role.slot := ⟨role, rfl⟩
  rw [dif_pos hex]
  have heq : Classical.choose hex = role := Rounds.Role.slot_inj (Classical.choose_spec hex)
  rw [heq]

private def toyClaimH (i : Fin 4) :
    OpeningClaim (v7HashRow i).params.row.n Unit
      (Col GF128 (v7HashRow i).params.nw (v7HashRow i).params.nq) Digest256 where
  I := Finset.empty
  a := fun _ => default
  pf := { nonce := fun _ => (), frontierValue := fun _ => default }

private def toyClaimS :
    OpeningClaim v7SigHahn.params.row.n Unit
      (Col FP256 v7SigHahn.params.nw v7SigHahn.params.nq) Digest256 where
  I := Finset.empty
  a := fun _ => default
  pf := { nonce := fun _ => (), frontierValue := fun _ => default }

private theorem toyTape_le (i : Fin 4) :
    2 * v7SigHahn.params.row.n + 2 * (v7HashRow i).params.row.n + 0 ≤ 14000 := by
  fin_cases i <;> decide

/-- Direct instantiation of `V7Soundness125.annotated_fs_knowledge_soundness_125`
at all four registered v7 hash profiles `i : Fin 4`, proving its hypotheses are
jointly satisfiable (non-vacuous). -/
theorem v7_soundness_125_inhabited (i : Fin 4) :
    let body : TwoOracleTree (ToyEnc i) Digest256
      (SignatureBudget125.PairPoint Digest256 GF128 Unit (MsgH i) MsgS (v7HashRow i))
      (ToyCoins i) Unit 0 0 := .done ()
    ((univ.filter fun ω : (Fin 14000 → Digest256) ×
        (SignatureBudget125.PairPoint Digest256 GF128 Unit (MsgH i) MsgS (v7HashRow i) → ToyCoins i) =>
      extractionFailure (toyHashSide i) (toySigSide i) body
        (fun _ => default) (fun _ => default)
        (fun _ => (0 : GF128)) (fun _ => ())
        (fun _ => toyHashMsg i) (fun _ _ => default)
        (fun _ => toyClaimH i) (fun _ => toyClaimS)
        (fun _ => Classical.arbitrary (ToyCoins i)) (fun _ => ()) (fun _ => ())
        (IdealSampler.mac _ _ _ _ _ _ _ _ _)
        (fun _ (_ : Fin 6) => (0 : GF128)) (fun _ (_ : Fin 6) => (0 : GF128))
        ω.1 ω.2).card : ℚ) /
      ((Fintype.card Digest256 : ℚ) ^ 14000 *
        (Fintype.card (ToyCoins i) : ℚ) ^
          Fintype.card (SignatureBudget125.PairPoint Digest256 GF128 Unit (MsgH i) MsgS (v7HashRow i))) ≤
      33628000 / 2 ^ 256 := by
  intro body
  let resp0 : V7FixedTape125.HashResponseAt i GF128 :=
    toyRespOf (Sum.inr (Sum.inr (Sum.inr ())))
  have hbound := annotated_fs_knowledge_soundness_125
    (i := i) (TM := 14000) (nblk := 6)
    (Hash := toyHashSide i) (Signature := toySigSide i)
    (body := body)
    (rootH := fun _ => default)
    (rootS := fun _ => default)
    (avOf := fun _ => (0 : GF128))
    (earlyOf := fun _ => ())
    (msgH := fun _ => toyHashMsg i)
    (msgS := fun _ _ => default)
    (claimH := fun _ => toyClaimH i)
    (claimS := fun _ => toyClaimS)
    (represent := fun _ => Classical.arbitrary (ToyCoins i))
    (hashPublic := fun _ => ())
    (sigPublic := fun _ => ())
    (d := IdealSampler.mac _ _ _ _ _ _ _ _ _)
    (commonH := fun _ _ => (0 : GF128))
    (shareH := fun _ _ => (0 : GF128))
    (commonS := fun _ _ => (0 : GF128))
    (shareS := fun _ _ => (0 : GF128))
    (shift := fun _ => (0 : GF128))
    (tagOf := fun _ _ => (0 : GF128))
    (Wire := V7FixedTape125.HashResponseAt i GF128)
    (hD := card_Digest256)
    (hmacCard := card_GF128)
    (htape := toyTape_le i)
    (hTM := by norm_num)
    (inputLength := toyInputLength i)
    (hleafH := fun _ => rfl)
    (hnodeH := fun _ => rfl)
    (hleafS := fun _ => rfl)
    (sigPubAt := fun _ => ())
    (hsigPub := fun _ _ => rfl)
    (wire := fun _ => toyFieldMessages _ _ _ _ _)
    (toResponse := Function.Embedding.refl _)
    (wireResponse := fun _ => resp0)
    (encode := fun _ u => Sum.inr (Sum.inr (Sum.inl u)))
    (decode := fun _ m => match m with | Sum.inr (Sum.inr (Sum.inl u)) => some u | _ => none)
    (valid := fun _ m => ∃ u, m = Sum.inr (Sum.inr (Sum.inl u)))
    (hdecode := fun _ _ => rfl)
    (hvalid := fun _ m u _ hd => by
      cases m with
      | inl _ => simp at hd
      | inr m1 =>
        cases m1 with
        | inl _ => simp at hd
        | inr m2 =>
          cases m2 with
          | inl v => cases Option.some.inj hd; rfl
          | inr _ => simp at hd)
    (hwire := fun _ => by
      dsimp only [TerminalPrefix125.openingOfMessages, NizkDeployedHash.msgPoint,
        NizkDeployedHash.padMsgs, TerminalPrefix125.openingIndex, Rounds.Role.index]
      rw [if_pos le_rfl, toyHashMsg_slot i .ligeroQuery]
      exact ⟨⟨resp0, rfl⟩, rfl, rfl⟩)
    (hwmsgs := fun _ _ role => by
      rw [toyHashMsg_slot]
      cases role with
      | layerPair ly =>
        dsimp only [toyFieldMessages, toyMsgOfRole]
        split_ifs <;> simp
      | sumcheck _ _ => exact ⟨(0, 0), rfl⟩
      | inputBind => exact ⟨(0, 0), rfl⟩
      | ligeroChallenge => rfl
      | ligeroQuery => exact ⟨resp0, rfl⟩)
    (hwresp := fun _ a b ha hb hr => by
      rcases ha with ⟨ra, rfl⟩
      rcases hb with ⟨rb, rfl⟩
      simp only [toyHashSide, toyRespOf] at hr
      rw [hr])
    (hrowSatH := fun _ _ _ _ => by funext j; simp [MacSep.shiftTag])
    (hrowSatS := fun _ _ _ _ => by funext j; simp [MacSep.shiftTag])
  rw [if_pos rfl] at hbound
  refine le_trans (le_of_eq ?_) hbound
  refine congrArg₂ (· / ·) ?_ ?_
  · refine congrArg Nat.cast (congrArg Finset.card ?_)
    ext ω
    simp
  · refine congrArg₂ (· * ·) rfl (congrArg₂ HPow.hPow ?_ ?_)
    · exact congrArg Nat.cast (by
        have h : ∀ (a b : Fintype (ToyCoins i)),
            @Fintype.card _ a = @Fintype.card _ b := fun a b => by rw [Subsingleton.elim a b]
        exact h _ _)
    · exact by
        have h : ∀ (a b : Fintype (SignatureBudget125.PairPoint Digest256 GF128 Unit (MsgH i) MsgS (v7HashRow i))),
            @Fintype.card _ a = @Fintype.card _ b := fun a b => by rw [Subsingleton.elim a b]
        exact h _ _

end LfzkV1.V7Soundness125Instance
