import LfzkV1.MerkleWork125Total
import LfzkV1.CompiledZkDeployedHash
import LfzkV1.SoundnessBudget125

/-!
# Composition of the v1 125-bit charges

The view estimate is conditional on a fixed Merkle tape. The product count
restores both tapes after the two openings supply the work floor. This
leaves protocol-side lemmas to show the two bounds within each view and the
global count of charged search and analytical lookup points.
-/

set_option autoImplicit false

namespace LfzkV1.SoundnessCompose125

open Finset Bcs.TotalOracleCommit Merkle.MH Merkle.RandomOracle
  LfzkV1.MerkleWork125
open scoped Classical

section Replay

private theorem replaySurvival_pos : (0 : ℚ) < 1 - 2^14 / 2^128 := by norm_num
private theorem replayError_nonneg : (0 : ℚ) ≤ 81 / 2^128 := by norm_num

attribute [local instance 10000] Classical.propDecidable

/-- The nonidentity residual, identity survival, and covered-event count
give the rounded algebraic budget on one fixed Merkle tape. -/
theorem ratio_le_of_view_split {Sample View : Type} [Fintype Sample] [Nonempty Sample]
    [DecidableEq View] (N : ℕ)
    (observe : Sample → View) (identityView : View → Prop)
    (event covered : Sample → Prop)
    (herror : ∀ v ∈ univ.image observe, ¬ identityView v →
      ((univ.filter fun s => observe s = v ∧ event s ∧ ¬ covered s).card : ℚ) ≤
        (81 / 2^128) * (univ.filter fun s => observe s = v).card)
    (hcover : ∀ v ∈ univ.image observe, identityView v →
      (1 - 2^14 / 2^128) * (univ.filter fun s => observe s = v ∧ event s).card ≤
        ((univ.filter fun s => observe s = v ∧ covered s).card : ℚ))
    (hcharge : ((univ.filter covered).card : ℚ) / Fintype.card Sample ≤
      (15016 / 1000 + N * (7001 / 1000)) / 2^128) :
    ((univ.filter event).card : ℚ) / Fintype.card Sample ≤
      (97 + N * (701 / 100)) / 2^128 := by
  let survival : ℚ := 1 - 2^14 / 2^128
  have hsurvival : 0 < survival := replaySurvival_pos
  have hsize : 0 < (Fintype.card Sample : ℚ) := by exact_mod_cast Fintype.card_pos
  have hcount := ReplayView125.card_le_of_view_split observe identityView event covered
    (81 / 2^128) survival replayError_nonneg hsurvival (by norm_num [survival]) herror hcover
  calc
    _ ≤ ((81 / 2^128) * (Fintype.card Sample : ℚ) +
        ((univ.filter covered).card : ℚ) / survival) / Fintype.card Sample :=
      div_le_div_of_nonneg_right hcount hsize.le
    _ = (81 / 2^128) + (((univ.filter covered).card : ℚ) / Fintype.card Sample) / survival := by
      rw [add_div, mul_div_cancel_right₀ _ (ne_of_gt hsize), div_right_comm]
    _ ≤ (81 / 2^128) + ((15016 / 1000 + N * (7001 / 1000)) / 2^128) / survival :=
      add_le_add_right (div_le_div_of_nonneg_right hcharge hsurvival.le) _
    _ = (81 + ((15016 : ℚ) / 1000 + N * (7001 / 1000)) / survival) / 2^128 := by
      rw [div_right_comm _ (2^128 : ℚ) survival, ← add_div]
    _ ≤ _ := SoundnessBudget125.replay_charges_le N

end Replay

section Charges

/-- Contributions from the covered cases, in order: MAC, signature,
observed field, Ligero low or bad-high, ambiguity, and the two orders
of the canonical secondary case. -/
def caseBudget (tag : Fin 6) (key signature field batch opening : ℕ) : ℚ :=
  match tag.val with
  | 0 => (4 / 2^128) * (key + 1 : ℚ)
  | 1 => (1426 / 1000 / 2^128) * (signature + 1 : ℚ)
  | 2 => (7 / 2^128) * (field : ℚ)
  | 3 => (319 / 100 / 2^128) * (batch : ℚ) + (3188 / 500 / 2^128) * (opening + 1 : ℚ)
  | 4 => (1 / 2^202) * (opening + 1 : ℚ)
  | _ => (7 / 2^128 / 2^32) * (opening : ℚ) + (7 / 2^128 / 2^108) * (field : ℚ)

attribute [local instance 10000] Classical.propDecidable

/-- The union of the covered cases respects one original query count.
The local counts are marginal expectations over the same sample space. -/
theorem role_cover_ratio_le {Sample : Type} [Fintype Sample] [Nonempty Sample] (N : ℕ)
    (covered : Sample → Prop) (cases : Fin 6 → Sample → Prop)
    (key signature field batch opening : Sample → ℕ)
    (hcover : ∀ s, covered s → ∃ j, cases j s)
    (hcount : ∀ s, key s + signature s + field s + batch s + opening s ≤ N)
    (hcases : ∀ j, ((univ.filter (cases j)).card : ℚ) ≤
      ∑ s : Sample, caseBudget j (key s) (signature s) (field s) (batch s) (opening s)) :
    ((univ.filter covered).card : ℚ) / Fintype.card Sample ≤
      (15016 / 1000 + N * (7001 / 1000)) / 2^128 := by
  have hsize : 0 < (Fintype.card Sample : ℚ) := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hsize).mpr
  have hsubset : univ.filter covered ⊆ (univ : Finset (Fin 6)).biUnion (fun j => univ.filter (cases j)) := by
    intro s hs
    obtain ⟨j, hj⟩ := hcover s (mem_filter.mp hs).2
    exact mem_biUnion.mpr ⟨j, mem_univ _, mem_filter.mpr ⟨mem_univ _, hj⟩⟩
  calc
    _ ≤ ∑ j : Fin 6, ((univ.filter (cases j)).card : ℚ) := by
      exact_mod_cast (card_le_card hsubset).trans (card_biUnion_le)
    _ ≤ ∑ j : Fin 6, ∑ s : Sample, caseBudget j (key s) (signature s) (field s) (batch s) (opening s) :=
      sum_le_sum fun j _ => hcases j
    _ = ∑ s : Sample, ∑ j : Fin 6, caseBudget j (key s) (signature s) (field s) (batch s) (opening s) :=
      sum_comm
    _ ≤ ∑ _s : Sample, (15016 / 1000 + N * (7001 / 1000)) / (2^128 : ℚ) := by
      apply sum_le_sum
      intro s _
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, caseBudget, Fin.val_zero, Fin.val_succ,
        Nat.reduceAdd, add_zero]
      convert SoundnessBudget125.covered_charges_le (key s) (signature s) (field s) (batch s) (opening s) N
        (hcount s) using 1 <;> first | rfl | (simp only [SoundnessBudget125.q]; ring)
    _ = _ := by rw [sum_const, nsmul_eq_mul, card_univ, mul_comm]

/-- Finish a fixed Merkle tape once its covered cases and replay fibers
have been bounded. The split need not choose an identity test in advance. -/
theorem fixed_tape_ratio_le {Sample View : Type} [Fintype Sample] [Nonempty Sample]
    [DecidableEq View] (N : ℕ)
    (observe : Sample → View) (event covered : Sample → Prop) (cases : Fin 6 → Sample → Prop)
    (key signature field batch opening : Sample → ℕ)
    (hcover : ∀ s, covered s → ∃ j, cases j s)
    (hcount : ∀ s, key s + signature s + field s + batch s + opening s ≤ N)
    (hcases : ∀ j, ((univ.filter (cases j)).card : ℚ) ≤
      ∑ s : Sample, caseBudget j (key s) (signature s) (field s) (batch s) (opening s))
    (hview : ∀ v ∈ univ.image observe,
      ((univ.filter fun s => observe s = v ∧ event s ∧ ¬ covered s).card : ℚ) ≤
        (81 / 2^128) * (univ.filter fun s => observe s = v).card ∨
      (1 - 2^14 / 2^128) * (univ.filter fun s => observe s = v ∧ event s).card ≤
        ((univ.filter fun s => observe s = v ∧ covered s).card : ℚ)) :
    ((univ.filter event).card : ℚ) / Fintype.card Sample ≤
      (97 + N * (701 / 100)) / 2^128 := by
  let identity (v : View) :=
    (1 - 2^14 / 2^128) * (univ.filter fun s => observe s = v ∧ event s).card ≤
      ((univ.filter fun s => observe s = v ∧ covered s).card : ℚ)
  exact ratio_le_of_view_split N observe identity event covered
    (fun v hv hn => (hview v hv).resolve_right hn) (fun _ _ h => h)
    (role_cover_ratio_le N covered cases key signature field batch opening hcover hcount hcases)

end Charges

section Merkle

variable {Enc D Pt C Out Key Salt₁ M₁ Salt₂ M₂ : Type} [DecidableEq Enc] [Inhabited D]
  [DecidableEq D] [DecidableEq Pt] [DecidableEq Key] [Fintype C] [Nonempty C]
  [Fintype Pt] [Fintype D] [Inhabited Salt₁] [Inhabited M₁] [Inhabited Salt₂]
  [Inhabited M₂] {tA N L TM fc n₁ n₂ : ℕ}
variable (S : Setup Enc D Pt C Out Key tA N L)
variable {check : Out → Tree Enc D Unit fc}
variable (left : OpeningReplay Salt₁ M₁ D Enc Out Key n₁ check)
  (right : OpeningReplay Salt₂ M₂ D Enc Out Key n₂ check)

/-- A uniform fixed-Merkle estimate for an accepted failure event on
explainable openings implies the work-normalized bound under the deployed
total-prefix challenge oracle. The opening serialization and algebraic
bound are explicit hypotheses. -/
theorem ratio_le_of_fixed_merkle
    (event : (Fin TM → D) → (Pt → C) → Prop)
    (hfc : fc ≤ 14000) (hL : L ≤ 1200) (hLpos : 0 < L)
    (hF : fc + tA ≤ TM) (hTM : 0 < TM)
    (hD : Fintype.card D = 2^256) (hsize : 2048 ≤ n₁)
    (hleft : ∀ mt ro, event mt ro →
      S.MerkleAccepts left.codec check left.rootOf left.claimOf mt ro)
    (hright : ∀ mt ro, event mt ro →
      S.MerkleAccepts right.codec check right.rootOf right.claimOf mt ro)
    (hleftOpen : ∀ mt ro, event mt ro → (left.claimOf (S.proof mt ro)).I.Nonempty)
    (hrightOpen : ∀ mt ro, event mt ro → (right.claimOf (S.proof mt ro)).I.Nonempty)
    (inputLength : Enc → ℕ) (leafLen₁ leafLen₂ nodeLen : ℕ)
    (hll : leafLen₂ ≠ leafLen₁) (hln : leafLen₂ ≠ nodeLen)
    (hl : ∀ sm, inputLength (left.codec.leafEnc sm) = leafLen₁)
    (hnl : ∀ labels, inputLength (left.codec.nodeEnc labels) = nodeLen)
    (hr : ∀ sm, inputLength (right.codec.leafEnc sm) = leafLen₂)
    (hfixed : 13 ≤ tA → ∀ mt,
      ((univ.filter fun ro : Pt → C => event mt ro ∧
        S.Explains left.dec left.rootOf left.claimOf mt ro ∧
        S.Explains right.dec right.rootOf right.claimOf mt ro).card : ℚ) /
        Fintype.card (Pt → C) ≤ (97 + N * (701 / 100)) / 2^128) :
    ((univ.filter fun ω : (Fin TM → D) × (Pt → C) => event ω.1 ω.2).card : ℚ) /
      ((Fintype.card D : ℚ)^TM * (Fintype.card C : ℚ)^Fintype.card Pt) ≤
      (if N + tA = 0 then 33628000 / 2^256 else (N + tA : ℚ) / 2^125) := by
  let Sample := (Fin TM → D) × (Pt → C)
  let good := fun (mt : Fin TM → D) (ro : Pt → C) =>
    event mt ro ∧ ¬ totalMerkleException S left right hF mt ro
  have hgood (mt : Fin TM → D) (ro : Pt → C) (he : good mt ro) :=
    totalExplains_and_work_of_good S left right hLpos hF mt ro
      (hleft mt ro he.1) (hright mt ro he.1) he.2 hsize
      (hleftOpen mt ro he.1) (hrightOpen mt ro he.1)
      inputLength leafLen₁ leafLen₂ nodeLen hll hln hl hnl hr
  have hgoodRatio : ((univ.filter fun ω : Sample => good ω.1 ω.2).card : ℚ) /
      (Fintype.card Sample : ℚ) ≤
      if 13 ≤ tA then ((97 : ℚ) + (N : ℚ) * (701 / 100)) / 2^128 else 0 := by
    apply Bcs.product_ratio_le_of_fst_fiber good
    intro mt
    split_ifs with ht
    · have hsub : (univ.filter (good mt)) ⊆
          univ.filter (fun ro : Pt → C => event mt ro ∧
            S.Explains left.dec left.rootOf left.claimOf mt ro ∧
            S.Explains right.dec right.rootOf right.claimOf mt ro) := by
        intro ro hro
        have hg := (Finset.mem_filter.mp hro).2
        have ⟨h₁, h₂, _⟩ := hgood mt ro hg
        exact Finset.mem_filter.mpr ⟨mem_univ _, hg.1, h₁, h₂⟩
      exact (div_le_div_of_nonneg_right (by exact_mod_cast card_le_card hsub)
        (Nat.cast_nonneg _)).trans (hfixed ht mt)
    · have hnil : univ.filter (good mt) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro ro hro
        exact ht (hgood mt ro (Finset.mem_filter.mp hro).2).2.2
      simp [hnil]
  let bad := univ.filter (fun ω : Sample => totalMerkleException S left right hF ω.1 ω.2)
  let accepted := univ.filter (fun ω : Sample => event ω.1 ω.2)
  let goodSet := univ.filter (fun ω : Sample => good ω.1 ω.2)
  have hsub : accepted ⊆ goodSet ∪ bad := by
    intro ω hω
    have he := (Finset.mem_filter.mp hω).2
    by_cases hb : totalMerkleException S left right hF ω.1 ω.2
    · exact mem_union_right _ (Finset.mem_filter.mpr ⟨mem_univ _, hb⟩)
    · exact mem_union_left _ (Finset.mem_filter.mpr ⟨mem_univ _, he, hb⟩)
  have hcard : accepted.card ≤ goodSet.card + bad.card :=
    (card_le_card hsub).trans (card_union_le _ _)
  have hd : (Fintype.card Sample : ℚ) =
      (Fintype.card D : ℚ)^TM * (Fintype.card C : ℚ)^Fintype.card Pt := by
    simp only [Sample, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow]
  have hp : (0 : ℚ) < Fintype.card Sample := by exact_mod_cast Fintype.card_pos
  have hp1 : (accepted.card : ℚ) / Fintype.card Sample ≤ 1 :=
    (div_le_iff₀ hp).mpr (by simpa using ((Nat.cast_le (α := ℚ)).mpr (Finset.card_le_univ accepted)))
  have hbadRatio : (bad.card : ℚ) / Fintype.card Sample ≤
      (adaptiveMerkleNumerator fc tA (L + N) : ℚ) / (2^128)^2 := by
    rw [hd]
    have h := totalMerkleException_ratio_le S left right hF hTM
    rw [hD] at h
    have hsizeD : ((2^256 : ℕ) : ℚ) = (2^128)^2 := by norm_num
    rw [hD, hsizeD]
    simpa only [hsizeD, bad, Finset.filter_congr_decidable] using h
  rw [← hd]
  apply SoundnessBudget125.bound_of_charges hp1 hfc hL
  calc
    (accepted.card : ℚ) / Fintype.card Sample ≤
        ((goodSet.card : ℚ) + bad.card) / Fintype.card Sample :=
      div_le_div_of_nonneg_right (by exact_mod_cast hcard) hp.le
    _ ≤ _ := by
      rw [add_div]
      exact add_le_add hgoodRatio hbadRatio

end Merkle


section Compiled

open Bcs RbrLongfellow LfzkV1.CertifiedV1 LfzkV1.CompiledZk
open LfzkV1.CompiledLongfellow (Col v1K)

variable {R : Row} {hR : R.Valid} {hr : 0 < R.params.row.openings}
  {logv M ninp nt nlin logw logc : ℕ}
variable {Enc D Pt C X Out Salt Msg Witness F : Type}
  [Fintype C] [DecidableEq Pt] [DecidableEq Enc] [Inhabited D] [DecidableEq D] [Inhabited Salt]
  [Field F] [Fintype F] [DecidableEq F] [SumcheckV1Interp F]
variable {codec : Codec Salt (Col F R.params.nw R.params.nq) D Enc}
  {dec : RoleDecoders codec} {rootOfKey : D × D → D}
variable (side : CompiledZkSide R hR hr logv C F Msg Witness M ninp nt nlin logw logc X dec rootOfKey)

/-- The compiled opening check authenticates exactly the decoded query's
indices. In a valid row this set is nonempty, as required for the work floor. -/
theorem opening_nonempty_of_acceptsDH {tA N L TM fc : ℕ}
    (S : Bcs.TotalOracleCommit.Setup Enc D Pt C Out (D × D) tA N L)
    (check : Out → Tree Enc D Unit fc) (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim R.params.row.n Salt (Col F R.params.nw R.params.nq) D)
    (avOf : Out → C) (pubOf : Out → X)
    (sl : (Fin L → C) → Fin (Rounds.Role.length R.params.nl R.params.rounds) → C)
    (mt : Fin TM → D) (ro : Pt → C)
    (ha : side.acceptsDH S check rootOf msgOf claimOf avOf pubOf sl mt ro) :
    (claimOf (S.proof mt ro)).I.Nonempty := by
  rcases ha with ⟨sys, _, hacc⟩
  rw [hacc.1]
  exact (v1K (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide))
    (Row.rowValid hR) side.dom (Row.hkrow hR) hr).indices_nonempty _

end Compiled

end LfzkV1.SoundnessCompose125
