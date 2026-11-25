import LfzkV1.MerkleWork125
import LfzkV1.ReplayView125
import Bcs.TotalOracleCommit

/-!
# Merkle work with deployed transcript prefixes

At a fixed challenge oracle the total-prefix model embeds into the adaptive
Merkle analysis. The empty challenge tape carries no randomness. In
particular both sides use the original cut selected by their common key.
-/

set_option autoImplicit false

namespace LfzkV1.MerkleWork125

open Finset Bcs.TotalOracleCommit Merkle.MH Merkle.RandomOracle
  Merkle.RandomOracle.TwoOracleTree
open scoped Classical

variable {Enc D Pt C Out Key Salt₁ M₁ Salt₂ M₂ : Type} [DecidableEq Enc] [Inhabited D]
  [DecidableEq D] [DecidableEq Pt] [DecidableEq Key] [Fintype C]
  [Inhabited Salt₁] [Inhabited M₁] [Inhabited Salt₂] [Inhabited M₂]
  {tA N L TM fc n₁ n₂ : ℕ}
variable (S : Setup Enc D Pt C Out Key tA N L)
variable {check : Out → Tree Enc D Unit fc}
variable (left : OpeningReplay Salt₁ M₁ D Enc Out Key n₁ check)
  (right : OpeningReplay Salt₂ M₂ D Enc Out Key n₂ check)

/-- A forward hit, a collision, or a hit against an opening's selected cut,
with the challenge oracle fixed to the supplied function. -/
def totalMerkleException (hF : fc + tA ≤ TM) (mt : Fin TM → D) (ro : Pt → C) : Prop :=
  adaptiveMerkleException n₁ (S.atOracle ro) left right hF mt Setup.emptyTape

/-- On the good Merkle branch both openings are explained at the deployed
commitment cut, and the adversary's budget must include thirteen queries. -/
theorem totalExplains_and_work_of_good (hL : 0 < L) (hF : fc + tA ≤ TM)
    (mt : Fin TM → D) (ro : Pt → C)
    (hleft : S.MerkleAccepts left.codec check left.rootOf left.claimOf mt ro)
    (hright : S.MerkleAccepts right.codec check right.rootOf right.claimOf mt ro)
    (hne : ¬ totalMerkleException S left right hF mt ro)
    (hsize : 2048 ≤ n₁)
    (hleftOpen : (left.claimOf (S.proof mt ro)).I.Nonempty)
    (hrightOpen : (right.claimOf (S.proof mt ro)).I.Nonempty)
    (inputLength : Enc → ℕ) (leafLen₁ leafLen₂ nodeLen : ℕ)
    (hll : leafLen₂ ≠ leafLen₁) (hln : leafLen₂ ≠ nodeLen)
    (hl : ∀ sm, inputLength (left.codec.leafEnc sm) = leafLen₁)
    (hnl : ∀ labels, inputLength (left.codec.nodeEnc labels) = nodeLen)
    (hr : ∀ sm, inputLength (right.codec.leafEnc sm) = leafLen₂) :
    S.Explains left.dec left.rootOf left.claimOf mt ro ∧
    S.Explains right.dec right.rootOf right.claimOf mt ro ∧ 13 ≤ tA := by
  let A := S.atOracle ro
  let ct : Fin 0 → C := Setup.emptyTape
  obtain ⟨hle, hre, hwork⟩ := explains_and_work_of_good n₁ A left right hL hF mt ct
    hleft hright hne hsize hleftOpen hrightOpen inputLength leafLen₁ leafLen₂ nodeLen hll hln
    hl hnl hr
  refine ⟨hle, hre, hwork.trans ?_⟩
  simpa only [runSlots, List.length_nil, Nat.zero_add] using
    lazyRun_seen_length_le mt default (fixRight ct A.dflt A.joint []) []

omit [DecidableEq Key] [Inhabited Salt₁] [Inhabited M₁] [Inhabited Salt₂] [Inhabited M₂] in
/-- The enlarged exception's probability in the original total-prefix
experiment. Each fixed challenge oracle uses the same Merkle numerator. -/
theorem totalMerkleException_ratio_le [Fintype Pt] [Nonempty C] [Fintype D]
    (hF : fc + tA ≤ TM) (hTM : 0 < TM) :
    ((univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
      totalMerkleException S left right hF ω.1 ω.2).card : ℚ) /
      ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^ Fintype.card Pt) ≤
      (adaptiveMerkleNumerator fc tA (L + N) : ℚ) / Fintype.card D := by
  let M := adaptiveMerkleNumerator fc tA (L + N)
  have hcard :
      (univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
        totalMerkleException S left right hF ω.1 ω.2).card ≤
      Fintype.card C ^ Fintype.card Pt * (M * Fintype.card D ^ (TM - 1)) := by
    rw [Bcs.card_filter_prod_snd]
    calc
      _ ≤ ∑ _ro : Pt → C, M * Fintype.card D ^ (TM - 1) :=
        Finset.sum_le_sum fun ro _ =>
          adaptiveMerkleException_card n₁ (S.atOracle ro) left right hF Setup.emptyTape
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, smul_eq_mul]
  have hd : (0 : ℚ) < Fintype.card D := by exact_mod_cast Fintype.card_pos
  have hc : (0 : ℚ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  have hpow : (Fintype.card D : ℚ) ^ TM =
    (Fintype.card D : ℚ) ^ (TM - 1) * Fintype.card D := by
    rw [← pow_succ, show TM - 1 + 1 = TM by omega]
  rw [div_le_iff₀ (mul_pos (pow_pos hd TM) (pow_pos hc _))]
  calc
    _ ≤ (Fintype.card C : ℚ) ^ Fintype.card Pt * (M * (Fintype.card D : ℚ) ^ (TM - 1)) := by
      exact_mod_cast hcard
    _ = _ := by
      rw [hpow]
      field_simp
      rfl


section SearchCut

open Bcs.AdaptiveCommit (stopAt)

omit [DecidableEq D] [Fintype C] in
/-- A single induction compares all stopped prefixes, including cuts in
the fixed verifier continuation after the adversarial search. -/
private theorem stoppedMerkleRun_congr {A B : Type} {replayFuel : ℕ}
    (mt : Fin TM → D) (dflt : C) (ro ro' : Pt → C)
    (i : ℕ) (replay : A → Tree Pt C B replayFuel) :
    ∀ {l r} (body : TwoOracleTree Enc D Pt C A l r) (seenL : List Enc) (seenR : List Pt),
      (∀ qa ∈ ((fixLeft mt default body seenL).run ro).2, ro' qa.1 = ro qa.1) →
      lazyRun mt default (fixRight Setup.emptyTape dflt
        (stopAt i ((answerRight ro' body).bindRight replay) seenR) seenR) seenL =
      lazyRun mt default (fixRight Setup.emptyTape dflt
        (stopAt i ((answerRight ro body).bindRight replay) seenR) seenR) seenL := by
  intro l r body
  induction body with
  | done a => intro seenL seenR _; rfl
  | queryLeft q next ih =>
      intro seenL seenR hview
      simp only [fixLeft] at hview
      simp only [answerRight, bindRight, stopAt, fixRight, lazyRun_query]
      rw [ih _ _ _ hview]
  | queryRight q next ih =>
      intro seenL seenR hview
      have hq : ro' q = ro q := hview (q, ro q) (by simp only [fixLeft, Tree.run_query, List.mem_cons,
        true_or])
      simp only [answerRight, bindRight, stopAt]
      by_cases hstop : q ∉ seenR ∧ seenR.length = i
      · simp only [if_pos hstop]
      · simp only [if_neg hstop, fixRight, hq]
        refine ih (ro q) _ _ ?_
        intro qa hqa
        apply hview qa
        exact List.mem_cons_of_mem _ hqa

omit [DecidableEq D] [Fintype C] in
/-- The selected Merkle context is a function of the search output and its
actual point/answer trace at the fixed Merkle tape. -/
theorem totalContext_eq_of_search_run (mt : Fin TM → D) (ro ro' : Pt → C)
    (hrun : (S.search mt).run ro' = (S.search mt).run ro) :
    S.context mt ro' = S.context mt ro := by
  let A := S.atOracle ro
  let A' := S.atOracle ro'
  let ct : Fin 0 → C := Setup.emptyTape
  have hagree : ∀ qa ∈ ((S.search mt).run ro).2, ro' qa.1 = ro qa.1 := by
    intro qa hqa
    have hqa' : qa ∈ ((S.search mt).run ro').2 := by rwa [hrun]
    exact (Tree.trace_sound _ ro' qa hqa').symm.trans (Tree.trace_sound _ ro qa hqa)
  have hcut (i : ℕ) : lazyRun mt default (A'.cutRun ct i) [] =
      lazyRun mt default (A.cutRun ct i) [] := by
    unfold Bcs.AdaptiveCommit.Setup.cutRun
    rw [show A'.joint = (answerRight ro' S.body).bindRight S.recompute from S.joint_atOracle ro',
      show A.joint = (answerRight ro S.body).bindRight S.recompute from S.joint_atOracle ro]
    exact stoppedMerkleRun_congr mt S.dflt ro ro' i S.recompute S.body [] [] hagree
  have hseen : A'.fsSeen mt ct = A.fsSeen mt ct := by
    apply List.ext_getElem?
    intro i
    rw [← A'.cutRun_output, ← A.cutRun_output, hcut i]
  have hout : S.proof mt ro' = S.proof mt ro := by
    rw [S.proof_eq, S.proof_eq, hrun]
  let k := S.keyOut (S.proof mt ro)
  have hi : A'.cutIdx mt ct k = A.cutIdx mt ct k := by
    unfold Bcs.AdaptiveCommit.Setup.cutIdx
    rw [hseen]
    rfl
  change A'.ctxAt mt ct (S.keyOut (S.proof mt ro')) = A.ctxAt mt ct (S.keyOut (S.proof mt ro))
  rw [hout]
  change A'.ctxAt mt ct k = A.ctxAt mt ct k
  unfold Bcs.AdaptiveCommit.Setup.ctxAt Bcs.AdaptiveCommit.Setup.cutTrace
  rw [hi, hcut]

omit [DecidableEq D] [Fintype C] in
/-- After any output-dependent analytical lookups, the selected paired
commitment context remains fixed on each replay-view fiber. -/
theorem totalContext_eq_of_replay_view (mt : Fin TM → D) (lookups : Out → List Pt)
    (ro ro' : Pt → C) (hview : ReplayView125.view (S.search mt) lookups ro' =
      ReplayView125.view (S.search mt) lookups ro) :
    S.context mt ro' = S.context mt ro :=
  totalContext_eq_of_search_run S mt ro ro' (congrArg Prod.fst hview)

end SearchCut

end LfzkV1.MerkleWork125
