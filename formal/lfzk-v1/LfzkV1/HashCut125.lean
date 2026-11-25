import LfzkV1.CompiledZkRadius
import LfzkV1.OpeningGeometry125

/-! The retuned lift radius on the compiled v7 hash circuits. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LfzkV1.HashCut125

open LfzkV1.CompiledZk LfzkV1.CertifiedV1 LfzkV1.SoundnessAudit
open LfzkV1.CompiledLongfellow (Col)
open LfzkV1.CompiledLongfellowAdaptive (Sig)
open LfzkV1.ZkLigeroV1 LigeroFamily CodingTheory Merkle.MH

def radius (i : Fin 4) : ℕ :=
  let c := (OpeningGeometry125.result i).certificate
  c.e + c.g

theorem radius_ge (i : Fin 4) :
    (v7HashRow i).params.row.e + (v7HashRow i).params.row.g ≤ radius i := by
  fin_cases i <;> decide +kernel

theorem row_candidate_count (i : Fin 4) : (v7HashRow i).cardCand = 2 := by
  fin_cases i <;> rfl

variable {C : Type} [Fintype C] {F Msg : Type} [Field F] [Fintype F] [DecidableEq F]
  [SumcheckV1Interp F] {M nt nlin : ℕ}
variable {Enc D Salt X : Type} [Inhabited D] [DecidableEq D] [DecidableEq Enc] [Inhabited Salt]
variable {i : Fin 4} {hR : (v7HashRow i).Valid} {hr : 0 < (v7HashRow i).params.row.openings}
variable {codec : Codec Salt (Col F (v7HashRow i).params.nw (v7HashRow i).params.nq) D Enc}
variable {dec : RoleDecoders codec} {rootOfKey : D × D → D}

theorem side_lift_card_le
    (S : CircuitSide (v7HashRow i) hR hr (v7HashLogv i) C F Msg M nt nlin X dec rootOfKey)
    (σ : Sig D C X Enc) : Fintype.card (sideLiftAt S (radius i) σ) ≤ (v7HashRow i).cardCand := by
  let s := OpeningGeometry125.result i
  let c := s.certificate
  let R := v7HashRow i
  have hgeom := OpeningGeometry125.deployedGeometry i
  have hp := OpeningGeometry125.parameters i
  have hn : c.n = R.params.row.n := hgeom.1
  have hk : c.k = R.params.row.k := hgeom.2.1
  have hd : c.d = R.params.row.n - R.params.row.k + 1 := by
    rw [← hn, ← hk]
    exact hp.2.2.1
  have hkrow := Row.hkrow hR
  have hkpos : 1 ≤ R.params.row.openings + R.params.q :=
    (Nat.succ_le_of_lt hr).trans (Nat.le_add_right _ _)
  have hkn : R.params.row.openings + R.params.q ≤ R.params.row.n := by
    rw [hkrow, ← hk, ← hn]
    exact hp.2.1
  have hmin : HasMinimumDistanceAtLeast
      (R.params.row.code (Row.rowValid hR) S.dom hkrow).baseCode c.d := by
    have hrange : c.d = R.params.row.n - (R.params.row.openings + R.params.q) + 1 := by
      rw [hkrow]
      exact hd
    rw [hrange]
    exact LigeroFamily.ReedSolomon.baseCode_minimum_distance S.dom hkpos hkn
  have hradius : c.e + c.g < c.d := by fin_cases i <;> decide +kernel
  have hden : 0 < InterleavedJohnson.denominator c.n c.d (c.e + c.g) := by
    fin_cases i <;> decide +kernel
  have hdn : c.d ≤ c.n := by rw [hn]; exact hmin.distance_le_length
  have hfamily := c.listFamily hradius hdn hden
  rw [hn] at hfamily
  let oracle := extOracle nlin nt (Row.rowValid hR) S.dom hkrow hr dec
    (rootOfKey σ.1.1, σ.1.2)
  have hcard := SchemeLiftCandidate.univ_card_le_uniformFamilyBound _ oracle hmin hradius hfamily
  rw [Finset.card_univ] at hcard
  rw [row_candidate_count]
  exact hcard.trans (OpeningGeometry125.liftCount i)

/-- The same verified side, with the larger analysis lift list. -/
noncomputable def side
    (S : CircuitSide (v7HashRow i) hR hr (v7HashLogv i) C F Msg M nt nlin X dec rootOfKey) :=
  S.toZkSideAt (radius i) (radius_ge i) (side_lift_card_le S)

end LfzkV1.HashCut125
