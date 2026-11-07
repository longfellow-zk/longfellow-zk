import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Tactic

/-! A prior opening query guesses the complete primary response, not merely
the commitment root.  After fixing the other prover coins and the pre-proof
oracle, a candidate query fixes the earlier prefix and hence the batching
coefficients.  The fresh additive primary mask is then uniquely determined.

The prefix may depend arbitrarily on the mask: this lemma does NOT assume
that a Merkle root is independent of its committed randomness.  Canonical
opening-byte decoding and the primary-response formula are connected in the
neighboring oracle/backend modules. -/
namespace LfzkV2.Current.ZeroKnowledge.OpeningFreshness

open Finset
open scoped Classical

variable {Mask Prefix Query : Type} [AddGroup Mask]

/-- The complete earlier prefix and the masked primary response visible in
an opening query. `base` fixes the other rows and batching coefficients once
that prefix is fixed. The commitment can be an arbitrary function of mask. -/
def taggedResponse (historyOf : Mask → Prefix) (base : Prefix → Mask) (mask : Mask) : Prefix × Mask :=
  (historyOf mask,mask+base (historyOf mask))

theorem taggedResponse_injective (historyOf : Mask → Prefix) (base : Prefix → Mask) :
    Function.Injective (taggedResponse historyOf base) := by
  intro first second h
  have hp := congrArg Prod.fst h
  have hr := congrArg Prod.snd h
  change historyOf first = historyOf second at hp
  change first+base (historyOf first) = second+base (historyOf second) at hr
  rw [hp] at hr
  exact add_right_cancel hr

/-- Malformed queries decode to none. Each valid prior query names at most
one fresh mask, even when every earlier prefix depends on that mask. -/
theorem prior_hit_card [Fintype Mask] (historyOf : Mask → Prefix) (base : Prefix → Mask)
    (decode : Query → Option (Prefix × Mask)) (prior : Finset Query) :
    (univ.filter fun mask => some (taggedResponse historyOf base mask) ∈ prior.image decode).card ≤
      prior.card := by
  have hi : Function.Injective (fun mask => some (taggedResponse historyOf base mask)) := by
    intro first second h
    exact taggedResponse_injective historyOf base (Option.some.inj h)
  apply le_trans (card_le_card_of_injOn (fun mask => some (taggedResponse historyOf base mask))
    (fun mask h => (mem_filter.mp h).2) hi.injOn)
  exact card_image_le

/-- Uniform fresh masking gives a concrete query-count bound; there is no
assumed root-entropy or freshness certificate. -/
theorem prior_hit_probability [Fintype Mask] (historyOf : Mask → Prefix) (base : Prefix → Mask)
    (decode : Query → Option (Prefix × Mask)) (prior : Finset Query) :
    ((univ.filter fun mask => some (taggedResponse historyOf base mask) ∈
      prior.image decode).card : ℚ) / Fintype.card Mask ≤
      (prior.card : ℚ) / Fintype.card Mask :=
  div_le_div_of_nonneg_right (Nat.cast_le.mpr (prior_hit_card historyOf base decode prior))
    (Nat.cast_nonneg _)

/-- The Rust primary mask is sampled at the same k+s oracle-prefix points
used to transmit H. Thus no coefficient/sampling approximation is involved. -/
theorem primary_samples_card {F : Type} [Fintype F] (degree : ℕ) :
    Fintype.card (Fin degree → F) = (Fintype.card F)^degree := by
  simp only [Fintype.card_fun,Fintype.card_fin]

end LfzkV2.Current.ZeroKnowledge.OpeningFreshness
