import Bcs.FinalQuery
import Bcs.PotentialOracle
import LfzkV1.HashCut125
import LfzkV1.CompiledZkProfileSepMac

/-!
# The v7 MAC charge with projected key consistency

Only the decoded verifier share is placed in the transcript context. The
whole ideal answer is still sampled at the key point, using the exact
decoder's fiber bound. The candidate sets are fixed at the commitment cut.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace LfzkV1.MacCharge125

open Finset Bcs.TotalOracle Merkle.RandomOracle LfzkV1.MacSep
open LfzkV1.TwoFieldV1Rows
open scoped Classical

variable {Q C Out K W₁ W₂ Fmac : Type}
variable [Fintype Q] [DecidableEq Q] [Fintype C] [Nonempty C]
variable [Field Fmac] [Fintype Fmac] [DecidableEq Fmac]
variable {N nblk : ℕ}

/-- The key event for the deployed, per-block multiplier-share MAC. -/
def badKey (L₁ : Finset W₁) (L₂ : Finset W₂)
    (common₁ : W₁ → Fin nblk → Fmac) (common₂ : W₂ → Fin nblk → Fmac)
    (share₁ : W₁ → Fin nblk → Fmac) (share₂ : W₂ → Fin nblk → Fmac)
    (shift av : Fmac) : Prop :=
  SepMacBad L₁ L₂ common₁ common₂ (fun w a => shiftTag a (share₁ w) (common₁ w))
    (fun w a => shiftTag a (share₂ w) (common₂ w)) (shift + av)

/-- A pair of separately satisfying sides lands in the key event if the
shared tags agree and the decoded share is consistent with the proof. -/
theorem badKey_of_projected_consistency
    {L₁ : Finset W₁} {L₂ : Finset W₂}
    {common₁ : W₁ → Fin nblk → Fmac} {common₂ : W₂ → Fin nblk → Fmac}
    {share₁ : W₁ → Fin nblk → Fmac} {share₂ : W₂ → Fin nblk → Fmac}
    {a₁ : W₁} {a₂ : W₂} {tag : Fin nblk → Fmac}
    {shift av : Fmac} (d : ExactDecoder C Fmac) (coin : C)
    (hkey : d.decode coin = av) (h₁ : a₁ ∈ L₁) (h₂ : a₂ ∈ L₂)
    (hne : common₁ a₁ ≠ common₂ a₂)
    (hrow₁ : shiftTag (shift + av) (share₁ a₁) (common₁ a₁) = tag)
    (hrow₂ : shiftTag (shift + av) (share₂ a₂) (common₂ a₂) = tag) :
    badKey L₁ L₂ common₁ common₂ share₁ share₂ shift (d.decode coin) := by
  rw [hkey]
  exact ⟨a₁, h₁, a₂, h₂, hne, hrow₁.trans hrow₂.symm⟩

theorem badKey_coin_card_le
    (L₁ : Finset W₁) (L₂ : Finset W₂)
    (common₁ : W₁ → Fin nblk → Fmac) (common₂ : W₂ → Fin nblk → Fmac)
    (share₁ : W₁ → Fin nblk → Fmac) (share₂ : W₂ → Fin nblk → Fmac)
    (shift : Fmac) (d : ExactDecoder C Fmac)
    (h₁ : L₁.card ≤ 2) (h₂ : L₂.card ≤ 2) :
    (univ.filter fun coin : C => badKey L₁ L₂ common₁ common₂ share₁ share₂ shift
      (d.decode coin)).card ≤ 4 * d.k :=
  (sepMacBad_card_le L₁ L₂ common₁ common₂ _ _ (shiftTag_hcoll common₁ common₂ share₁ share₂)
    shift d.decode d.hbal).trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul h₁ h₂))

/-- The actual, distinct original queries that have the MAC key role. -/
noncomputable def observedKeys (tree : Tree Q C Out N) (isKey : Q → Prop) (H : Q → C) : Finset Q :=
  (queried tree H).toFinset.filter isKey

/-- Indicator of a single missing submitted key. -/
noncomputable def appendedKeyCount (tree : Tree Q C Out N) (key : Out → Q) (H : Q → C) : ℚ :=
  if key (tree.run H).1 ∈ queried tree H then 0 else 1

theorem appendedKeyCount_le_one (tree : Tree Q C Out N) (key : Out → Q) (H : Q → C) :
    appendedKeyCount tree key H ≤ 1 := by
  unfold appendedKeyCount
  split_ifs <;> norm_num

private theorem key_count_extended (tree : Tree Q C Out N) (isKey : Q → Prop)
    (key : Out → Q) (hkey : ∀ out, isKey (key out)) (H : Q → C) :
    ((observedKeys (appendFinalQuery tree key) isKey H).card : ℚ) =
      (observedKeys tree isKey H).card + appendedKeyCount tree key H := by
  have hq : queried (appendFinalQuery tree key) H =
      queried tree H ++ [key (tree.run H).1] := by
    simp [queried, appendFinalQuery, Tree.run_bind]
  have hset : observedKeys (appendFinalQuery tree key) isKey H =
      insert (key (tree.run H).1) (observedKeys tree isKey H) := by
    ext q
    simp only [observedKeys, mem_filter, hq, List.mem_toFinset, List.mem_append,
      List.mem_singleton, mem_insert]
    constructor
    · rintro ⟨h, hqKey⟩
      rcases h with hseen | heq
      · exact Or.inr ⟨hseen, hqKey⟩
      · exact Or.inl heq
    · rintro (heq | ⟨hseen, hqKey⟩)
      · subst q
        exact ⟨Or.inr rfl, hkey _⟩
      · exact ⟨Or.inl hseen, hqKey⟩
  rw [hset]
  by_cases h : key (tree.run H).1 ∈ queried tree H
  · have hm : key (tree.run H).1 ∈ observedKeys tree isKey H :=
      mem_filter.mpr ⟨List.mem_toFinset.mpr h, hkey _⟩
    simp [insert_eq_of_mem hm, appendedKeyCount, h]
  · have hn : key (tree.run H).1 ∉ observedKeys tree isKey H :=
      fun hm => h (List.mem_toFinset.mp (mem_filter.mp hm).1)
    simp [card_insert_of_notMem hn, appendedKeyCount, h]

/-- A local event at the selected point is charged to the observed points
of its role and at most one appended point. -/
theorem selected_role_event_count_le
    (tree : Tree Q C Out N) (isKey : Q → Prop) (key : Out → Q)
    (hkey : ∀ out, isKey (key out))
    (bad : Q → (Q → C) → C → Prop)
    (hoff : ∀ q H H', AgreeOff q H H' → ∀ a, bad q H a ↔ bad q H' a)
    (ε : ℚ)
    (hfiber : ∀ q H, (∑ a : C, if bad q H a then (1 : ℚ) else 0) ≤ Fintype.card C * ε)
    (event : (Q → C) → Prop)
    (hcover : ∀ H, event H → let q := key (tree.run H).1; bad q H (H q)) :
    ((univ.filter event).card : ℚ) ≤
      ε * ∑ H : Q → C,
        ((observedKeys tree isKey H).card + appendedKeyCount tree key H) := by
  classical
  let ext := appendFinalQuery tree key
  let wt (q : Q) (H : Q → C) (coin : C) : ℚ :=
    if q ∈ observedKeys ext isKey H ∧ bad q H coin then 1 else 0
  have hwtOff (q : Q) (H H' : Q → C) (h : AgreeOff q H H') (coin : C) :
      wt q H coin = wt q H' coin := by
    have hm : q ∈ observedKeys ext isKey H ↔ q ∈ observedKeys ext isKey H' := by
      simp only [observedKeys, mem_filter, List.mem_toFinset, mem_queried_iff ext q h]
    have hb := hoff q H H' h coin
    have heq := hm.and hb
    unfold wt
    by_cases hg : q ∈ observedKeys ext isKey H ∧ bad q H coin
    · rw [if_pos hg, if_pos (heq.mp hg)]
    · rw [if_neg hg, if_neg (heq.not.mp hg)]
  have hlocal (q : Q) (H : Q → C) :
      (∑ coin : C, wt q H coin) ≤
      if q ∈ observedKeys ext isKey H then Fintype.card C * ε else 0 := by
    by_cases hm : q ∈ observedKeys ext isKey H
    · simpa only [wt, hm, true_and, if_true] using hfiber q H
    · simp [wt, hm]
  have hsum (H : Q → C) :
      (∑ q : Q, ∑ coin : C, wt q H coin) ≤
      Fintype.card C * (ε * (observedKeys ext isKey H).card) := by
    calc
      _ ≤ ∑ q : Q, if q ∈ observedKeys ext isKey H then
          Fintype.card C * ε else 0 :=
        sum_le_sum (fun q _ => hlocal q H)
      _ = _ := by
        have hfilter : (univ.filter fun q => q ∈ observedKeys ext isKey H) = observedKeys ext isKey H :=
          by ext q; simp
        rw [← sum_filter, hfilter, sum_const, nsmul_eq_mul]
        ring
  have hC : (0 : ℚ) < Fintype.card C := by exact_mod_cast Fintype.card_pos (α := C)
  have hbound :
      (∑ H : Q → C, ∑ q : Q, wt q H (H q)) ≤
      ∑ H : Q → C, ε * (observedKeys ext isKey H).card := by
    apply le_of_mul_le_mul_right ?_ hC
    rw [sum_comm, sum_mul]
    simp_rw [sum_coord_mul_rat _ _ (hwtOff _)]
    rw [sum_comm, sum_mul]
    exact sum_le_sum (fun H _ => by simpa only [mul_comm] using hsum H)
  have hpoint (H : Q → C) : (if event H then (1 : ℚ) else 0) ≤ ∑ q : Q, wt q H (H q) := by
    have hnonneg (q : Q) : 0 ≤ wt q H (H q) := by unfold wt; split_ifs <;> norm_num
    by_cases h : event H
    · let q := key (tree.run H).1
      have hm : q ∈ observedKeys ext isKey H :=
        mem_filter.mpr ⟨List.mem_toFinset.mpr (appendFinalQuery_mem tree key H), hkey _⟩
      have hw : wt q H (H q) = 1 := if_pos ⟨hm, hcover H h⟩
      rw [if_pos h, ← hw]
      exact single_le_sum (fun q _ => hnonneg q) (mem_univ q)
    · rw [if_neg h]
      exact sum_nonneg (fun q _ => hnonneg q)
  rw [card_filter, Nat.cast_sum]
  have hevt :
      (∑ H : Q → C, ((if event H then 1 else 0 : ℕ) : ℚ)) =
        ∑ H : Q → C, if event H then (1 : ℚ) else 0 := by
    apply sum_congr rfl
    intro H _
    by_cases he : event H <;> simp [he]
  rw [hevt]
  calc
    _ ≤ ∑ H : Q → C, ∑ q : Q, wt q H (H q) := sum_le_sum (fun H _ => hpoint H)
    _ ≤ _ := hbound
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro H _
      rw [show ext = appendFinalQuery tree key from rfl, key_count_extended tree isKey key hkey H]

/-- Expected MAC loss with its own observed and appended counts. -/
theorem key_charge_sum_le
    (tree : Tree Q C Out N) (isKey : Q → Prop) (key : Out → Q)
    (hkey : ∀ out, isKey (key out))
    (context : Q → (Q → C) → K)
    (hoff : ∀ q H H', AgreeOff q H H' → context q H = context q H')
    (cands₁ : K → Finset W₁) (cands₂ : K → Finset W₂)
    (h₁ : ∀ κ, (cands₁ κ).card ≤ 2) (h₂ : ∀ κ, (cands₂ κ).card ≤ 2)
    (common₁ : W₁ → Fin nblk → Fmac) (common₂ : W₂ → Fin nblk → Fmac)
    (share₁ : W₁ → Fin nblk → Fmac) (share₂ : W₂ → Fin nblk → Fmac)
    (shift : K → Fmac) (d : ExactDecoder C Fmac)
    (event : (Q → C) → Prop)
    (hcover : ∀ H, event H →
      let q := key (tree.run H).1
      let κ := context q H
      badKey (cands₁ κ) (cands₂ κ) common₁ common₂ share₁ share₂ (shift κ) (d.decode (H q))) :
    ((univ.filter event).card : ℚ) ≤
      (4 / (Fintype.card Fmac : ℚ)) * ∑ H : Q → C,
        ((observedKeys tree isKey H).card + appendedKeyCount tree key H) := by
  let bad (q : Q) (H : Q → C) (coin : C) :=
    let κ := context q H
    badKey (cands₁ κ) (cands₂ κ) common₁ common₂ share₁ share₂ (shift κ) (d.decode coin)
  apply selected_role_event_count_le tree isKey key hkey bad
    (fun q H H' h _ => by simp only [bad, hoff q H H' h]) _ _ event hcover
  intro q H
  have hk : (4 * d.k : ℚ) ≤ Fintype.card C * (4 / (Fintype.card Fmac : ℚ)) := by
    have hF : (0 : ℚ) < Fintype.card Fmac := by exact_mod_cast Fintype.card_pos (α := Fmac)
    have hd : (d.k : ℚ) * Fintype.card Fmac ≤ Fintype.card C := by exact_mod_cast d.hexact
    rw [mul_div, le_div_iff₀ hF]
    nlinarith only [hd]
  have hc : ((univ.filter (bad q H)).card : ℚ) ≤ (4 * d.k : ℚ) := by
    exact_mod_cast badKey_coin_card_le (cands₁ (context q H)) (cands₂ (context q H))
      common₁ common₂ share₁ share₂ (shift (context q H)) d (h₁ _) (h₂ _)
  refine le_trans ?_ (hc.trans hk)
  rw [card_filter, Nat.cast_sum]
  apply sum_le_sum
  intro coin _
  change (if bad q H coin then (1 : ℚ) else 0) ≤ ((if bad q H coin then 1 else 0 : ℕ) : ℚ)
  by_cases hd : bad q H coin <;> simp [hd]


section Compiled

open LfzkV1.CertifiedV1 LfzkV1.SoundnessAudit LfzkV1.CompiledZk
open LfzkV1.CompiledLongfellow (Col)
open LfzkV1.CompiledLongfellowAdaptive (Sig)
open Merkle.MH

variable {D Enc X₁ X₂ Salt₁ Salt₂ : Type} [Inhabited D] [DecidableEq D] [DecidableEq Enc]
variable [Inhabited Salt₁] [Inhabited Salt₂]
variable {F₁ F₂ Msg₁ Msg₂ : Type} [Field F₁] [Fintype F₁] [DecidableEq F₁] [SumcheckV1Interp F₁]
variable [Field F₂] [Fintype F₂] [DecidableEq F₂] [SumcheckV1Interp F₂]
variable {M₁ M₂ nt₁ nt₂ nlin₁ nlin₂ : ℕ}
variable {i : Fin 4}
variable {hS : v7SigHahn.Valid} {hrS : 0 < v7SigHahn.params.row.openings}
variable {hH : (v7HashRow i).Valid} {hrH : 0 < (v7HashRow i).params.row.openings}
variable {codec₁ : Codec Salt₁ (Col F₁ v7SigHahn.params.nw v7SigHahn.params.nq) D Enc}
variable {codec₂ : Codec Salt₂ (Col F₂ (v7HashRow i).params.nw (v7HashRow i).params.nq) D Enc}
variable {dec₁ : RoleDecoders codec₁} {dec₂ : RoleDecoders codec₂}
variable {root₁ root₂ : D × D → D}
variable (S : CircuitSide v7SigHahn hS hrS 8 C F₁ Msg₁ M₁ nt₁ nlin₁ X₁ dec₁ root₁)
variable (Hside : CircuitSide (v7HashRow i) hH hrH (v7HashLogv i) C F₂ Msg₂ M₂ nt₂ nlin₂ X₂ dec₂ root₂)

private abbrev Cut (D Enc : Type) := (D × D) × List (Enc × D)

/-- The checked hash cut bounds committed witnesses as well as its lifts. -/
theorem hash_candidates_card_le [Nonempty X₂] (κ : Cut D Enc) :
    (Hside.candsAt (HashCut125.radius i) κ).card ≤ 2 :=
  (Hside.candsAt_card_le_of_side (HashCut125.radius i) (HashCut125.side_lift_card_le Hside) κ).trans_eq
    (HashCut125.row_candidate_count i)

/-- The two satisfying circuit witnesses give the key event. The hash side
uses the enlarged analysis radius while the signature side uses its
deployed-radius Hahn list. -/
theorem v7_bad_key_of_sides
    (κ : Cut D Enc) (sigKey hashKey : C) (sigPublic : X₁) (hashPublic : X₂)
    (common₁ share₁ : (Fin S.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ share₂ : (Fin Hside.c.ninp → F₂) → Fin nblk → Fmac)
    (w₁ : Fin S.c.ninp → F₁) (w₂ : Fin Hside.c.ninp → F₂)
    (hs₁ : S.toSide.Good (κ, sigKey, sigPublic) w₁)
    (hs₂ : (HashCut125.side Hside).Good (κ, hashKey, hashPublic) w₂)
    (hne : common₁ w₁ ≠ common₂ w₂)
    (shift av : Fmac) (d : ExactDecoder C Fmac) (coin : C)
    (hkey : d.decode coin = av) (tag : Fin nblk → Fmac)
    (hrow₁ : shiftTag (shift + av) (share₁ w₁) (common₁ w₁) = tag)
    (hrow₂ : shiftTag (shift + av) (share₂ w₂) (common₂ w₂) = tag) :
    badKey (S.cands κ) (Hside.candsAt (HashCut125.radius i) κ)
      common₁ common₂ share₁ share₂ shift (d.decode coin) := by
  have hc₁ := S.good_mem_cands (κ, sigKey, sigPublic) w₁ hs₁
  have hc₂ := Hside.good_mem_candsAt (HashCut125.radius i) (HashCut125.radius_ge i)
    (HashCut125.side_lift_card_le Hside) (κ, hashKey, hashPublic) w₂ hs₂
  exact badKey_of_projected_consistency d coin hkey hc₁ hc₂ hne hrow₁ hrow₂

/-- Expected v7 MAC charge using the two deployed circuits' checked
candidate list sizes. The observed count remains available for joint
accounting with field and Ligero queries. -/
theorem v7_key_charge_sum_le [Nonempty X₂]
    (tree : Tree Q C Out N) (isKey : Q → Prop) (key : Out → Q)
    (hkey : ∀ out, isKey (key out))
    (context : Q → (Q → C) → Cut D Enc)
    (hoff : ∀ q H H', AgreeOff q H H' → context q H = context q H')
    (common₁ share₁ : (Fin S.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ share₂ : (Fin Hside.c.ninp → F₂) → Fin nblk → Fmac)
    (shift : Cut D Enc → Fmac) (d : ExactDecoder C Fmac)
    (hq : Fintype.card Fmac = 2 ^ 128)
    (event : (Q → C) → Prop)
    (hcover : ∀ H, event H →
      let q := key (tree.run H).1
      let κ := context q H
      badKey (S.cands κ) (Hside.candsAt (HashCut125.radius i) κ) common₁ common₂ share₁ share₂
        (shift κ) (d.decode (H q))) :
    ((univ.filter event).card : ℚ) ≤
      (4 / (2 ^ 128 : ℚ)) * ∑ H : Q → C,
        ((observedKeys tree isKey H).card + appendedKeyCount tree key H) := by
  have hsig (κ : Cut D Enc) : (S.cands κ).card ≤ 2 := S.cands_card_le κ
  have h := key_charge_sum_le tree isKey key hkey context hoff S.cands
    (Hside.candsAt (HashCut125.radius i)) hsig (hash_candidates_card_le Hside)
    common₁ common₂ share₁ share₂ shift d event hcover
  simpa only [hq, Nat.cast_pow, Nat.cast_ofNat] using h

end Compiled

end LfzkV1.MacCharge125
