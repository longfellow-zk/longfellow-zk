import LfzkV1.V7ZkProfile
import ECDSA.Pratt
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Premise inhabitation (non-vacuity) for `V7ZkProfile`

Constructs a toy instance discharging every premise of
`V7ZkProfile.v7mac_twofield_zk_deployed_padding` for all four registered
v7 hash profiles `attr : Fin 4`, using a `GaloisField 2 16 →+* GaloisField 2 128`
embedding and a Reed-Solomon domain inside `GF(2^16)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

namespace LfzkV1.V7ZkProfileInstance

open Finset Merkle.MH LigeroFamily LigeroFamily.ReedSolomon
open LfzkV1.CompiledLongfellowZk LfzkV1.CompiledLongfellowZkTwoField
open LfzkV1.ZkGhostTwoField (HonestTape)
open LfzkV1.ZkGhostSampled (realSampledV7)
open LfzkV1.CompiledLongfellowZkV7Joint LfzkV1.V7ZkProfile
open LfzkV1.MerkleWork125 LfzkV1.CertifiedV1 LfzkV1.LigeroV1Rows
open scoped Classical

abbrev GF128 := GaloisField 2 128
abbrev GF16 := GaloisField 2 16

local instance instFintypeGF128 : Fintype GF128 := Fintype.ofFinite _
local instance instFintypeGF16 : Fintype GF16 := Fintype.ofFinite _

local instance instFintypeCol {F : Type} [Fintype F] : Fintype (Col F 0 0 1) :=
  letI : Finite (Col F 0 0 1) := Finite.of_injective
    (fun c : Col F 0 0 1 => (c.directMask, c.proximityBlind))
    (fun a b h => by
      obtain ⟨hd, hp⟩ := Prod.mk.inj h
      exact SchemeColumn.ext (by funext block j; cases block <;> exact j.elim0)
        (by funext _ m; exact m.elim) hd hp)
  Fintype.ofFinite _

local instance instDecidableEqCol {F : Type} : DecidableEq (Col F 0 0 1) :=
  Classical.decEq _

instance instFactP256Prime : Fact p256Order.Prime :=
  ⟨ECDSA.prime_115792089210356248762697446949407573530086143415290314195533631308867097853951⟩

abbrev FP256 := ZMod p256Order

private theorem card_GF128 : Fintype.card GF128 = 2 ^ 128 := by
  rw [← Nat.card_eq_fintype_card]
  exact GaloisField.card 2 128 (by decide)

private theorem card_GF16 : Fintype.card GF16 = 2 ^ 16 := by
  rw [← Nat.card_eq_fintype_card]
  exact GaloisField.card 2 16 (by decide)

private theorem card_FP256 : Fintype.card FP256 = p256Order :=
  ZMod.card p256Order

private def emb16 : GF16 →+* GF128 :=
  (Classical.choice (FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod 2) (K := GF16) (L := GF128)
    (by rw [GaloisField.finrank 2 (by decide), GaloisField.finrank 2 (by decide)]; decide))).toRingHom

private abbrev nH (attr : Fin 4) := (v7HashProfile attr).params.row.n
private abbrev kH (attr : Fin 4) := (v7HashProfile attr).params.row.k
private abbrev wH (attr : Fin 4) := (v7HashProfile attr).params.row.k - 132
private abbrev nS := v7Sig.params.row.n
private abbrev kS := v7Sig.params.row.k
private abbrev wS := v7Sig.params.row.k - 132
private abbrev Salt256 := Fin 256 → Bool

private theorem card_Salt256 : Fintype.card Salt256 = 2 ^ 256 := by
  simp [Salt256]

private theorem zk_hash_params (attr : Fin 4) :
    132 + wH attr = kH attr ∧ 132 + wH attr + nH attr ≤ 2 ^ 16 ∧
    3 ≤ 132 + wH attr ∧ 132 + wH attr ≤ nH attr := by
  fin_cases attr <;> decide

private theorem zk_sig_params :
    132 + wS = kS ∧ 132 + wS + nS ≤ p256Order ∧ 3 ≤ 132 + wS ∧ 132 + wS ≤ nS := by
  refine ⟨by decide, ?_, by decide, by decide⟩
  have hle : 132 + wS + nS ≤ 10000 := by decide
  exact hle.trans (by unfold p256Order; norm_num)

private def toyHashDomain16 (attr : Fin 4) : Domain GF16 132 (wH attr) (nH attr) :=
  Domain.ofCardLE (by rw [card_GF16]; exact (zk_hash_params attr).2.1)

private def toyHashDomain (attr : Fin 4) : Domain GF128 132 (wH attr) (nH attr) where
  point p := emb16 ((toyHashDomain16 attr).point p)
  injective _ _ h := (toyHashDomain16 attr).injective (emb16.injective h)

private def toySigDomain : Domain FP256 132 wS nS :=
  Domain.ofCardLE (by rw [card_FP256]; exact zk_sig_params.2.1)

private def toyHashCode (attr : Fin 4) : MultiplicativeCode GF128 132 (wH attr) (nH attr) :=
  V7ColumnUniqueness.deployedCode (toyHashDomain attr) (zk_hash_params attr).2.2.2
    (by have := (zk_hash_params attr).2.2.1; omega)

private def toySigCode : MultiplicativeCode FP256 132 wS nS :=
  V7ColumnUniqueness.deployedCode toySigDomain zk_sig_params.2.2.2
    (by have := zk_sig_params.2.2.1; omega)

private def toyEmptyFrontend (F : Type) [Field F] (w : ℕ) :
    Frontend F 0 0 w Empty Unit Unit Unit Unit Unit where
  msgs _ _ := 0
  transmit _ _ _ b := b
  transmit_bijective _ _ _ := Function.bijective_id
  stmt _ _ _ := { coefficient := fun e => Empty.elim e, target := fun e => Empty.elim e }
  Valid _ _ := True
  honest_sat _ _ _ _ _ := ⟨fun e => Empty.elim e, fun r => r.elim0⟩

private def toyPoints {Resp : Type} : Points Unit Unit Unit Resp Bool where
  first _ _ := false
  second _ _ _ _ := true
  second_ne_first _ _ _ _ := by decide

private def toyZeroChallenge (F : Type) [Field F] : Ligero.V1.Challenge F 0 0 1 Empty :=
  fun _ => {
    proximity := fun _ => 0
    linear := fun e => Empty.elim e
    quadratic := fun r => r.elim0
  }

private def toyQuerySet {n : ℕ} (hlt : 132 ≤ n) : QuerySet n 132 :=
  ⟨Finset.univ.filter (fun j : Fin n => j.val < 132), by
    have hbij : (Finset.univ.filter (fun j : Fin n => j.val < 132)).card =
        (Finset.univ : Finset (Fin 132)).card := by
      refine Finset.card_bij
        (fun (j : Fin n) (hj : j ∈ Finset.univ.filter (fun j : Fin n => j.val < 132)) =>
          (⟨j.val, (Finset.mem_filter.mp hj).2⟩ : Fin 132)) ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro a _ b _ h; exact Fin.ext (congrArg (Fin.val : Fin 132 → ℕ) h)
      · intro b _; exact ⟨⟨b.val, lt_of_lt_of_le b.isLt hlt⟩, by simp [b.isLt], by ext; rfl⟩
    simpa using hbij⟩

private def toyZkHashSide (attr : Fin 4) :
    Side GF128 132 (wH attr) (nH attr) 0 0 1 Empty Salt256 Unit
      ((Salt256 × Col GF128 0 0 1) ⊕ (Unit × Unit)) Unit Bool Unit Unit Unit Unit Unit where
  C := toyHashCode attr
  Cod := { leafEnc := Sum.inl, nodeEnc := Sum.inr }
  dec₁ _ := toyZeroChallenge GF128
  dec₂ _ := toyQuerySet (by have := (zk_hash_params attr).2.2.2; omega)
  FE := toyEmptyFrontend GF128 (wH attr)
  pts := toyPoints

private def toyZkSigSide :
    Side FP256 132 wS nS 0 0 1 Empty Salt256 Unit
      ((Salt256 × Col FP256 0 0 1) ⊕ (Unit × Unit)) Unit Bool Unit Unit Unit Unit Unit where
  C := toySigCode
  Cod := { leafEnc := Sum.inl, nodeEnc := Sum.inr }
  dec₁ _ := toyZeroChallenge FP256
  dec₂ _ := toyQuerySet (by have := zk_sig_params.2.2.2; omega)
  FE := toyEmptyFrontend FP256 wS
  pts := toyPoints

private def toyRegisteredGeometry (attr : Fin 4) :
    RegisteredGeometry (toyZkHashSide attr) toyZkSigSide attr where
  hashCode := {
    domain := toyHashDomain attr
    width_le := (zk_hash_params attr).2.2.2
    width_ge := (zk_hash_params attr).2.2.1
    exactCode := rfl
  }
  sigCode := {
    domain := toySigDomain
    width_le := zk_sig_params.2.2.2
    width_ge := zk_sig_params.2.2.1
    exactCode := rfl
  }
  hashN := rfl
  sigN := rfl
  hashK := (zk_hash_params attr).1
  sigK := zk_sig_params.1
  hashOpenings := rfl
  sigOpenings := rfl
  hashField := card_GF128
  sigField := card_FP256

private abbrev ToyHashPadding (attr : Fin 4) :=
  hashPadding emb16 attr (wH attr) (r := 132) (nw := 0) (nq := 0)

private abbrev ToySigPadding : CorePadding FP256 132 0 0 → Prop := fun _ => True

private abbrev ToyHashTape (attr : Fin 4) :=
  SupportedTape (toyZkHashSide attr).C (ToyHashPadding attr)

private abbrev ToySigTape :=
  SupportedTape toyZkSigSide.C ToySigPadding

local instance instFintypeToyHashTape (attr : Fin 4) : Fintype (ToyHashTape attr) :=
  Fintype.ofFinite _

local instance instFintypeToySigTape : Fintype ToySigTape :=
  Fintype.ofFinite _

local instance instNonemptyToyHashTape (attr : Fin 4) : Nonempty (ToyHashTape attr) :=
  ⟨⟨⟨0, 0, 0, 0⟩, fun block j => by cases block <;> exact j.elim0⟩⟩

local instance instNonemptyToySigTape : Nonempty ToySigTape :=
  ⟨⟨⟨0, 0, 0, 0⟩, trivial⟩⟩

local instance instFintypeOuterCoins (attr : Fin 4) :
    Fintype (ZkGhostTwoField.OuterCoins (nH attr) nS Salt256 Unit
      ((Salt256 × Col GF128 0 0 1) ⊕ (Unit × Unit))
      ((Salt256 × Col FP256 0 0 1) ⊕ (Unit × Unit))
      GF128 Unit Bool Unit Unit Bool Unit) :=
  Fintype.ofFinite _

/-- Direct instantiation of `V7ZkProfile.v7mac_twofield_zk_deployed_padding`
at all four registered v7 hash profiles `attr : Fin 4`, proving its hypotheses
are jointly satisfiable (non-vacuous). -/
theorem v7_zk_deployed_padding_inhabited (attr : Fin 4) :
    let P₁ := toyZkHashSide attr
    let P₂ := toyZkSigSide
    let dist : TwoDistinguisher GF128 132 (wH attr) (nH attr) 0 0 1 FP256 132 wS nS 0 0 1
        Salt256 Unit
        ((Salt256 × Col GF128 0 0 1) ⊕ (Unit × Unit))
        ((Salt256 × Col FP256 0 0 1) ⊕ (Unit × Unit))
        Unit Unit Unit Unit Bool Bool Unit Unit GF128 6 Unit 0 :=
      fun _ _ => .done ()
    StatClose (((0 : ℕ) : ℚ) / 2 ^ 256 + 1 / 2 ^ 360)
      (realSampledV7 P₁ P₂ (fun _ _ _ _ => ()) (fun _ _ _ _ _ => ()) dist
        (fun _ => ()) (fun _ => ()) (fun _ => (0 : GF128))
        (T₁ := 2 * nS + 2 * nH attr) (T₂ := 2 * nS + 2 * nH attr)
        (ZkGhostSubfield.forgetSupport :
          Tag GF128 6 × (Unit × ToyHashTape attr) × (Unit × ToySigTape) → HonestTape P₁ P₂))
      (fun ω : (Tag GF128 6 × (Unit × ToyHashTape attr) × (Unit × ToySigTape)) ×
          ZkGhostTwoField.OuterCoins (nH attr) nS Salt256 Unit
            ((Salt256 × Col GF128 0 0 1) ⊕ (Unit × Unit))
            ((Salt256 × Col FP256 0 0 1) ⊕ (Unit × Unit))
            GF128 Unit Bool Unit Unit Bool Unit =>
        ghostSimExpLeak P₁ P₂ (fun _ _ _ _ => ()) (fun _ _ _ _ _ => ()) dist
          (MacSep.zeroPat (fun _ : Fin 6 => (0 : GF128)))
          (ZkGhostSubfield.forgetSupport ω.1, ω.2)) := by
  intro P₁ P₂ dist
  have h := v7mac_twofield_zk_deployed_padding P₁ P₂
    (fun _ _ _ _ => ()) (fun _ _ _ _ _ => ()) dist
    (fun _ => ()) (fun _ => ()) (fun _ => (0 : GF128))
    emb16 attr (T₁ := 2 * nS + 2 * nH attr) (T₂ := 2 * nS + 2 * nH attr)
    (toyRegisteredGeometry attr)
    card_Salt256
    (by omega) (by omega)
    (fun _ _ h => Sum.inl.inj h)
    (fun _ _ h => Sum.inl.inj h)
    (fun _ _ h => by cases h)
    (fun _ _ h => by cases h)
    (fun p => ⟨(toyHashDomain16 attr).point p, rfl⟩)
    (fun _ _ block j => by cases block <;> exact j.elim0)
    (fun _ _ _ _ => trivial)
    (fun _ _ _ _ _ => trivial)
  convert h using 1

end LfzkV1.V7ZkProfileInstance
