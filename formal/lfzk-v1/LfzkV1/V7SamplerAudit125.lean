import LfzkV1.OpeningGeometry125
import LfzkV1.ReplayDecode125

/-! Checks on what the ideal decoder premises can mean for the v1 sampler. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LfzkV1.V7SamplerAudit125

open Finset LigeroFamily LfzkV1.SoundnessAudit LfzkV1.TwoFieldV1Rows

private abbrev OpeningSet (i : Fin 4) :=
  QuerySet (v7HashRow i).params.row.n (v7HashRow i).params.row.openings

/-- Even the smallest v7 hash profile has more opening sets than a
256-bit seed can reach. The bound leaves room to use only a subset of
the actual opening sets in the argument. -/
theorem opening_sets_lower_bound (i : Fin 4) :
    2 ^ 396 ≤ Fintype.card (OpeningSet i) := by
  rw [QuerySet.fintype_card, Nat.choose_eq_fast_choose]
  fin_cases i <;> decide +kernel

set_option exponentiation.threshold 400 in
/-- An arbitrary deterministic expansion of a 256-bit digest misses
opening sets required by the uniform challenge in the ideal analysis. -/
theorem digest_opening_support (i : Fin 4) {D : Type} [Fintype D]
    (hD : Fintype.card D = 2 ^ 256) (expand : D → OpeningSet i) :
    ((univ : Finset D).image expand).card ≤ 2 ^ 256 ∧
      ((univ : Finset D).image expand).card < Fintype.card (OpeningSet i) := by
  classical
  have h := card_image_le (s := (univ : Finset D)) (f := expand)
  rw [card_univ, hD] at h
  exact ⟨h, h.trans_lt ((Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 256 < 396)).trans_le
    (opening_sets_lower_bound i))⟩

/-- An exact initial decoder cannot enforce distinct pair coordinates.
This applies even if expansion uses a permutation sampled independently
at each prefix and reads two different inputs of that permutation. -/
theorem init_decoder_has_diagonal {C G F : Type} [Fintype C] [Nonempty C]
    [Fintype G] [DecidableEq G] [Fintype F] [DecidableEq F]
    (d : ExactDecoder C (G × F × F)) (g : G) (a : F) :
    ∃ coin, d.decode coin = (g, a, a) := by
  classical
  let coin : C := Classical.arbitrary C
  have hk : 0 < d.k := by
    have hp : 0 < (univ.filter fun c : C => d.decode c = d.decode coin).card :=
      card_pos.mpr ⟨coin, by simp⟩
    exact hp.trans_le (d.hbal (d.decode coin))
  have he : 0 < Fintype.card {c : C // d.decode c = (g, a, a)} := by
    rw [ReplayDecode125.card_decoder_fiber]
    exact hk
  obtain ⟨⟨c, hc⟩⟩ := Fintype.card_pos_iff.mp he
  exact ⟨c, hc⟩

end LfzkV1.V7SamplerAudit125
