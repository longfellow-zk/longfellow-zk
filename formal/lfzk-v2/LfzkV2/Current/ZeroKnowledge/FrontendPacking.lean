import DualPacking.ArtinSchreierMasking
import DualPacking.ArtinSchreierBackend
import LfzkV1.LigeroZk.Distribution

/-! The packing simulator uses the same independent field coins as the
honest packer. Its public vector is obtained by the forward Artin--Schreier
map, followed by an independent field scalar. No hidden word, offset,
inverse trace map or witness search is used to produce these messages.

Only the distribution coupling recovers dependent masks and the honest
Frobenius cell. Both native affine checks then follow from the already
proved completeness of the actual packing equations. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.Packing

open Module DualPacking.ArtinSchreier
open scoped Classical

variable {K F I J : Type*} [Field K] [Fintype K] [Field F] [Fintype F]
  [Algebra K F] [Fintype I] [DecidableEq I] [Fintype J]

abbrev Tape (pivot : I) := ({i : I // i ≠ pivot} → F) × F
abbrev Payload (K F I : Type*) [Field K] [Field F] [Algebra K F] :=
  (I → Masking.TraceZero K F) × F

def publicEquiv (basis : Basis I K F) (pivot : I) (pivotOne : basis pivot = 1) :
    Tape (F := F) pivot ≃ Payload K F I :=
  Equiv.prodCongr (Masking.maskEquiv basis pivot pivotOne) (Equiv.refl F)

/-- Efficient public sampling uses only the forward linear mask map. -/
def simulate (basis : Basis I K F) (pivot : I) (coins : Tape (F := F) pivot) :
    Payload K F I := (Masking.maskMap basis pivot coins.1,coins.2)

def honest (P : Instance K F I J) (coins : Tape (F := F) P.pivot) : Instance K F I J :=
  { P with masks := coins.1, r := coins.2, b := frobenius K F coins.2 }

def coupling (P : Instance K F I J) (pivotOne : P.basis P.pivot = 1)
    (valid : P.target = P.trueValue) (delta : (I → Masking.TraceZero K F) → I → F) :
    Tape (F := F) P.pivot ≃ Tape (F := F) P.pivot :=
  (Masking.transcriptEquiv P.basis P.pivot pivotOne (Masking.honestOffset P valid) delta).trans
    (publicEquiv P.basis P.pivot pivotOne).symm

theorem coupling_view (P : Instance K F I J) (pivotOne : P.basis P.pivot = 1)
    (valid : P.target = P.trueValue) (delta : (I → Masking.TraceZero K F) → I → F)
    (coins : Tape (F := F) P.pivot) :
    simulate P.basis P.pivot (coupling P pivotOne valid delta coins) =
      Masking.transcriptEquiv P.basis P.pivot pivotOne (Masking.honestOffset P valid) delta coins :=
  (publicEquiv P.basis P.pivot pivotOne).apply_symm_apply _

theorem honest_view (P : Instance K F I J) (pivotOne : P.basis P.pivot = 1)
    (valid : P.target = P.trueValue) (delta : (I → Masking.TraceZero K F) → I → F)
    (coins : Tape (F := F) P.pivot) :
    let view := simulate P.basis P.pivot (coupling P pivotOne valid delta coins)
    (fun i => (view.1 i).val) = (honest P coins).honestU ∧
      view.2 = (honest P coins).honestA (delta view.1) := by
  rw [coupling_view]
  exact Masking.honest_transcript (honest P coins) pivotOne valid delta

theorem recovered_constraints (P : Instance K F I J) (pivotOne : P.basis P.pivot = 1)
    (valid : P.target = P.trueValue) (delta : (I → Masking.TraceZero K F) → I → F)
    (coins : Tape (F := F) P.pivot) :
    let view := simulate P.basis P.pivot coins
    let recovered := honest P ((coupling P pivotOne valid delta).symm coins)
    recovered.nativeLinearVerify (fun i => (view.1 i).val) (delta view.1) view.2 := by
  have views := honest_view P pivotOne valid delta ((coupling P pivotOne valid delta).symm coins)
  rw [(coupling P pivotOne valid delta).apply_symm_apply] at views
  dsimp only
  rw [views.1,views.2]
  apply Instance.native_linear_completeness
  · exact valid
  · rfl

theorem sameDistribution [DecidableEq F] {Observed : Type*} [DecidableEq Observed]
    (P : Instance K F I J) (pivotOne : P.basis P.pivot = 1)
    (valid : P.target = P.trueValue) (delta : (I → Masking.TraceZero K F) → I → F)
    (observe : Payload K F I → Observed) :
    LigeroFamily.SameDistribution
      (fun coins => observe (Masking.transcriptEquiv P.basis P.pivot pivotOne
        (Masking.honestOffset P valid) delta coins))
      (fun coins => observe (simulate P.basis P.pivot coins)) := by
  apply LigeroFamily.sameDistribution_of_equiv (coupling P pivotOne valid delta)
  intro coins
  rw [coupling_view]

end LfzkV2.Current.ZeroKnowledge.Frontend.Packing
