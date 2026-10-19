import Bcs.AffineSingleton
import Lfzk.RbrZkPotentialTwoField

/-! The shared MAC challenge as its own local-domain block. Candidate
lists are extracted from a context stable under resampling that key input. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Lfzk.AffineMac
open Finset Bcs.AffineBlock Bcs.TotalOracle Bcs.TotalOracle.Footprint Lfzk.MacSep
open scoped Classical

theorem mac_oracle_sound
    {Hash C Out Key D Enc W₁ W₂ Fmac : Type}
    [Fintype Hash] [DecidableEq Hash] [Fintype C] [Nonempty C]
    [Field Fmac] [Fintype Fmac] [DecidableEq Fmac]
    (key : Key ↪ Hash) (domain : Finset Hash) (hmem : ∀ k, key k ∈ domain)
    (selected : Out → Key)
    (context : (Hash → C) → Key → (D × D) × List (Enc × D))
    (hoff : ∀ k H H', AgreeOff (key k) H H' → context H k = context H' k)
    (cands₁ : ((D × D) × List (Enc × D)) → Finset W₁)
    (cands₂ : ((D × D) × List (Enc × D)) → Finset W₂)
    {B₁ B₂ kmac nblk : ℕ}
    (hcard₁ : ∀ κ, (cands₁ κ).card ≤ B₁)
    (hcard₂ : ∀ κ, (cands₂ κ).card ≤ B₂)
    (common₁ : W₁ → Fin nblk → Fmac) (common₂ : W₂ → Fin nblk → Fmac)
    (mac₁ : W₁ → Fmac → Fin nblk → Fmac) (mac₂ : W₂ → Fmac → Fin nblk → Fmac)
    (hcoll : ∀ a₁ a₂, common₁ a₁ ≠ common₂ a₂ →
      (univ.filter fun x => mac₁ a₁ x = mac₂ a₂ x).card ≤ 1)
    (aP : ((D × D) × List (Enc × D)) → Fmac) (decode : C → Fmac)
    (hbal : ∀ x, (univ.filter fun c => decode c = x).card ≤ kmac) :
    OracleSound domain (fun out H =>
      let κ := context H (selected out)
      SepMacBad (cands₁ κ) (cands₂ κ) common₁ common₂ mac₁ mac₂
        (aP κ + decode (H (key (selected out)))))
      (Rate.diagonal ((B₁ * B₂ * kmac : ℚ) / Fintype.card C) (by positivity)) := by
  let bad := fun (x : Hash) (H : Hash → C) => ∃ k, key k = x ∧
    SepMacBad (cands₁ (context H k)) (cands₂ (context H k)) common₁ common₂ mac₁ mac₂
      (aP (context H k) + decode (H x))
  have he (k : Key) (H : Hash → C) : bad (key k) H ↔
      SepMacBad (cands₁ (context H k)) (cands₂ (context H k)) common₁ common₂ mac₁ mac₂
        (aP (context H k) + decode (H (key k))) := by
    constructor
    · rintro ⟨k', hk, hb⟩
      have := key.injective hk
      subst k'
      exact hb
    · intro h; exact ⟨k, rfl, h⟩
  have hlocal (x : Hash) (H : Hash → C) :
      average (fun c => if bad x (Function.update H x c) then (1 : ℚ) else 0) ≤
        (B₁ * B₂ * kmac : ℚ) / Fintype.card C := by
    by_cases hx : ∃ k, key k = x
    · obtain ⟨k, hk⟩ := hx
      rw [← hk]
      have hctx (c : C) : context (Function.update H (key k) c) k = context H k := by
        apply hoff
        intro z hz
        exact Function.update_of_ne hz _ _
      simp_rw [he, hctx, Function.update_self]
      unfold average
      refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
      exact Lfzk.NizkZkDeployedHash.twoFieldMacKey_local cands₁ cands₂ hcard₁ hcard₂
        common₁ common₂ mac₁ mac₂ hcoll aP decode hbal (context H k)
    · have hn (H' : Hash → C) : ¬ bad x H' := by
        intro hh
        obtain ⟨k, hk, _⟩ := hh
        exact hx ⟨k, hk⟩
      simp only [if_neg (hn _), average_const]
      positivity
  have hsupp (x : Hash) (H : Hash → C) (h : bad x H) : x ∈ domain := by
    obtain ⟨k, hk, _⟩ := h
    exact hk ▸ hmem k
  have cert := singleton_oracle_sound domain (fun out => key (selected out)) bad
    ((B₁ * B₂ * kmac : ℚ) / Fintype.card C) (by positivity) hlocal hsupp
  intro N tree
  simpa only [he] using cert N tree

end Lfzk.AffineMac
