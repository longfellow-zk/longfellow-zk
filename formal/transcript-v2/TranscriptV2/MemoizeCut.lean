import TranscriptV2.Memoize
import Bcs.TotalOracleCommit

/-! Cached-query normalization preserves the exact Merkle prefix before each
distinct transcript query, including after a right-only verifier continuation.
Thus it preserves first-context cuts, not merely complete prover outputs. -/
noncomputable section
namespace TranscriptV2.Memoize
open Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree Bcs.TotalOracle Finset
open Bcs.AdaptiveCommit Bcs.TotalOracleCommit
open scoped Classical

variable {QL DL P A Out Result : Type} [DecidableEq QL] [DecidableEq P]

/-- Partially evaluate transcript queries against their actual total oracle.
Only the original Merkle queries remain as externally visible calls. -/
def left (H : P → A) : {l r : ℕ} → TwoOracleTree QL DL P A Out l r → Tree QL DL Out l
  | _, _, .done out => .done out
  | _, _, .queryLeft q next => .query q fun answer => left H (next answer)
  | _, _, .queryRight q next => left H (next (H q))

omit [DecidableEq QL] in
private theorem left_stop_weaken (H : P → A) (i : ℕ) {l r : ℕ}
    (tree : TwoOracleTree QL DL P A Out l r) (seen : List P) :
    left H (stopAt i (weakenRight tree) seen) = left H (stopAt i tree seen) := by
  induction tree generalizing seen with
  | done out => rfl
  | queryLeft q next ih => simp only [weakenRight,stopAt,left]; congr; funext a; exact ih a seen
  | queryRight q next ih =>
      simp only [weakenRight,stopAt]
      split_ifs <;> simp only [left]
      all_goals exact ih _ _

omit [DecidableEq QL] in
private theorem left_stop_weakenAdd (H : P → A) (i : ℕ) {l r : ℕ}
    (tree : TwoOracleTree QL DL P A Out l r) (k : ℕ) (seen : List P) :
    left H (stopAt i (weakenRightAdd k tree) seen) = left H (stopAt i tree seen) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [weakenRightAdd,left_stop_weaken,ih]

omit [DecidableEq QL] in
private theorem actual_stop_weaken (dR : A) (i : ℕ) {l r : ℕ}
    (tree : TwoOracleTree QL DL P A Out l r) (seen seen' : List P) :
    fixRight (Fin.elim0 : Fin 0 → A) dR (stopAt i (weakenRight tree) seen) seen' =
      fixRight (Fin.elim0 : Fin 0 → A) dR (stopAt i tree seen) seen' := by
  induction tree generalizing seen seen' with
  | done out => rfl
  | queryLeft q next ih => simp only [weakenRight,stopAt,fixRight]; congr; funext a; exact ih a seen seen'
  | queryRight q next ih =>
      simp only [weakenRight,stopAt]
      split_ifs <;> simp only [fixRight]
      all_goals exact ih _ _ _

omit [DecidableEq QL] in
private theorem actual_stop_weakenAdd (dR : A) (i : ℕ) {l r : ℕ}
    (tree : TwoOracleTree QL DL P A Out l r) (k : ℕ) (seen seen' : List P) :
    fixRight (Fin.elim0 : Fin 0 → A) dR (stopAt i (weakenRightAdd k tree) seen) seen' =
      fixRight (Fin.elim0 : Fin 0 → A) dR (stopAt i tree seen) seen' := by
  induction k with
  | zero => rfl
  | succ k ih => rw [weakenRightAdd,actual_stop_weaken,ih]

omit [DecidableEq QL] in
private theorem actual_stop_continuation (H : P → A) (dR : A) (i : ℕ) (l : ℕ)
    {r : ℕ} (tree : Tree P A Out r) (seen seen' : List P) :
    fixRight (Fin.elim0 : Fin 0 → A) dR (stopAt i (liftRightAt (QL := QL) (DL := DL) l tree) seen) seen' =
      left H (stopAt i (liftRightAt (QL := QL) (DL := DL) l (answerWith (fun _ => dR) tree)) seen) := by
  induction tree generalizing seen seen' with
  | done out => rfl
  | query q next ih =>
      simp only [liftRightAt,answerWith,stopAt]
      split_ifs <;> simp only [fixRight,left]
      all_goals exact ih _ _ _

omit [DecidableEq QL] in
/-- The retained total-oracle cut runs the prover on H and its verifier
continuation on the empty tape. This equation identifies that implementation
with the simpler partially evaluated prefix used in the normalization proof. -/
theorem actual_stop_bind (H : P → A) (dR : A) (i : ℕ) {l r continuation : ℕ}
    (tree : TwoOracleTree QL DL P A Out l r) (rec : Out → Tree P A Result continuation)
    (seen seen' : List P) :
    fixRight (Fin.elim0 : Fin 0 → A) dR
      (stopAt i ((answerRight H tree).bindRight rec) seen) seen' =
      left H (stopAt i (tree.bindRight fun out => answerWith (fun _ => dR) (rec out)) seen) := by
  induction tree generalizing seen seen' with
  | done out =>
      simp only [answerRight,bindRight,actual_stop_weakenAdd,left_stop_weakenAdd]
      exact actual_stop_continuation H dR i _ _ _ _
  | queryLeft q next ih =>
      simp only [answerRight,bindRight,stopAt,fixRight,left]
      congr
      funext answer
      exact ih answer seen seen'
  | queryRight q next ih =>
      simp only [answerRight,bindRight,stopAt]
      split_ifs <;> simp only [fixRight,left]
      all_goals exact ih _ _ _

/-- Exact execution-prefix invariance, including all Merkle calls and
answers. The continuation contains verifier transcript reads but no Merkle
calls, so its query repeats require no separate budget. -/
theorem right_stopped_bind {l r continuation TL : ℕ} (fallback : Out)
    (tree : TwoOracleTree QL DL P A Out l r) (rec : Out → Tree P A Result continuation)
    (tape : Fin TL → DL) (dL : DL) (H : P → A)
    (index cap : ℕ) (seenR : List P) (cache : P → A) (seenL : List QL)
    (hcache : ∀ q ∈ seenR.toFinset, cache q = H q)
    (hcap : (TranscriptV2.seen (fixLeft tape dL tree seenL) H \ seenR.toFinset).card ≤ cap) :
    lazyRun tape dL (left H (stopAt index
      ((right fallback tree cap seenR.toFinset cache).bindRight rec) seenR)) seenL =
    lazyRun tape dL (left H (stopAt index (tree.bindRight rec) seenR)) seenL := by
  induction tree generalizing seenR cap cache seenL with
  | done out => simp only [right,bindRight,left_stop_weakenAdd]
  | queryLeft q next ih =>
      simp only [right,bindRight,stopAt,left,lazyRun_query]
      apply congrArg (fun result : Option P × (List QL × List (QL × DL)) => (result.1,result.2.1,(q,tapeAt tape dL
        ((if q ∈ seenL then seenL else seenL++[q]).idxOf q))::result.2.2))
      apply ih
      · exact hcache
      · exact hcap
  | queryRight q next ih =>
      have hs : TranscriptV2.seen (fixLeft tape dL (.queryRight q next) seenL) H =
          insert q (TranscriptV2.seen (fixLeft tape dL (next (H q)) seenL) H) := by
        simp [fixLeft,TranscriptV2.seen,queried_query]
      rw [hs] at hcap
      by_cases hq : q ∈ seenR
      · rw [right.eq_def]
        simp only [List.mem_toFinset,if_pos hq,hcache q (List.mem_toFinset.mpr hq),bindRight,stopAt]
        have hnstop : ¬(q ∉ seenR ∧ seenR.length = index) := fun h => h.1 hq
        rw [if_neg hnstop]
        simp only [left]
        apply ih
        · exact hcache
        · simpa only [Finset.insert_sdiff_of_mem _ (List.mem_toFinset.mpr hq)] using hcap
      · have hqset : q ∉ seenR.toFinset := by simpa using hq
        cases cap with
        | zero =>
            have hp : 0 < (insert q (TranscriptV2.seen
                (fixLeft tape dL (next (H q)) seenL) H) \ seenR.toFinset).card :=
              card_pos.mpr ⟨q,by simp [hqset]⟩
            omega
        | succ cap =>
            rw [right.eq_def]
            simp only [if_neg hqset,bindRight,stopAt]
            by_cases hstop : q ∉ seenR ∧ seenR.length = index
            · simp only [if_pos hstop,left]
            · simp only [if_neg hstop,left,if_neg hq]
              have hc : ∀ p ∈ (seenR++[q]).toFinset,
                  Function.update cache q (H q) p = H p := by
                intro p hp
                by_cases he : p = q
                · subst p; simp
                · simp only [List.toFinset_append,List.toFinset_cons,List.toFinset_nil,
                    Finset.union_insert,Finset.union_empty] at hp
                  have hp' : p ∈ seenR.toFinset := (mem_insert.mp hp).resolve_left he
                  simp [Function.update_of_ne he,hcache p hp']
              have hb : (TranscriptV2.seen (fixLeft tape dL (next (H q)) seenL) H \
                  (seenR++[q]).toFinset).card ≤ cap := by
                have he : insert q (TranscriptV2.seen (fixLeft tape dL (next (H q)) seenL) H) \
                    seenR.toFinset = insert q (TranscriptV2.seen
                      (fixLeft tape dL (next (H q)) seenL) H \ insert q seenR.toFinset) := by
                  ext p
                  by_cases hp : p = q
                  · subst p; simp [hqset]
                  · simp [hp]
                rw [he,card_insert_of_notMem (by simp)] at hcap
                simpa only [List.toFinset_append,List.toFinset_cons,List.toFinset_nil,
                  Finset.union_insert,Finset.union_empty] using (Nat.le_of_succ_le_succ hcap)
              simpa only [List.toFinset_append,List.toFinset_cons,List.toFinset_nil,
                Finset.union_insert,Finset.union_empty] using
                ih (H q) cap (seenR++[q]) (Function.update cache q (H q)) seenL hc hb

omit [DecidableEq P] in
private theorem left_state {l r TL : ℕ}
    (tree : TwoOracleTree QL DL P A Out l r) (tape : Fin TL → DL)
    (dL : DL) (H : P → A) (seenL : List QL) :
    ((lazyRun tape dL (left H tree) seenL).1,
      (lazyRun tape dL (left H tree) seenL).2.1) =
      ((fixLeftState tape dL tree seenL).run H).1 := by
  induction tree generalizing seenL with
  | done out => rfl
  | queryLeft q next ih => simp only [left,lazyRun_query,fixLeftState]; exact ih _ _
  | queryRight q next ih => simp only [left,fixLeftState,Tree.run_query]; exact ih _ _

/-- Complete execution also retains the left-oracle slot assignment. The
stronger prefix theorem above separately retains every extractor cut trace. -/
theorem right_left_slots {l r TL : ℕ} (fallback : Out)
    (tree : TwoOracleTree QL DL P A Out l r) (tape : Fin TL → DL)
    (dL : DL) (H : P → A) (cap : ℕ) (known : Finset P) (cache : P → A)
    (seenL : List QL) (hcache : ∀ p ∈ known, cache p = H p)
    (hcap : (TranscriptV2.seen (fixLeft tape dL tree seenL) H \ known).card ≤ cap) :
    ((lazyRun tape dL (left H (right fallback tree cap known cache)) seenL).1,
      (lazyRun tape dL (left H (right fallback tree cap known cache)) seenL).2.1) =
      ((lazyRun tape dL (left H tree) seenL).1,
        (lazyRun tape dL (left H tree) seenL).2.1) := by
  rw [left_state,left_state]
  exact right_left_state fallback tree tape dL seenL H cap known cache hcache hcap

omit [DecidableEq QL] in
private theorem actual_weaken (dR : A) {l r : ℕ}
    (tree : TwoOracleTree QL DL P A Out l r) (seen : List P) :
    fixRight (Fin.elim0 : Fin 0 → A) dR (weakenRight tree) seen =
      fixRight (Fin.elim0 : Fin 0 → A) dR tree seen := by
  induction tree generalizing seen with
  | done out => rfl
  | queryLeft q next ih => simp only [weakenRight,fixRight]; congr; funext a; exact ih a seen
  | queryRight q next ih => simp only [weakenRight,fixRight]; exact ih _ _

omit [DecidableEq QL] in
private theorem actual_weakenAdd (dR : A) {l r : ℕ}
    (tree : TwoOracleTree QL DL P A Out l r) (k : ℕ) (seen : List P) :
    fixRight (Fin.elim0 : Fin 0 → A) dR (weakenRightAdd k tree) seen =
      fixRight (Fin.elim0 : Fin 0 → A) dR tree seen := by
  induction k with
  | zero => rfl
  | succ k ih => rw [weakenRightAdd,actual_weaken,ih]

omit [DecidableEq QL] in
private theorem actual_continuation (dR : A) (l : ℕ) {r : ℕ}
    (tree : Tree P A Out r) (seen : List P) :
    fixRight (Fin.elim0 : Fin 0 → A) dR
      (liftRightAt (QL := QL) (DL := DL) l tree) seen =
      Tree.done ((tree.run (fun _ => dR)).1) := by
  induction tree generalizing seen with
  | done out => rfl
  | query q next ih => simpa only [liftRightAt,fixRight,Tree.run_query,tapeAt,Nat.not_lt_zero,↓reduceDIte] using ih dR _

omit [DecidableEq QL] in
private theorem actual_bind (H : P → A) (dR : A) {l r continuation : ℕ}
    (tree : TwoOracleTree QL DL P A Out l r) (rec : Out → Tree P A Result continuation)
    (seen : List P) :
    fixRight (Fin.elim0 : Fin 0 → A) dR ((answerRight H tree).bindRight rec) seen =
      (left H tree).map (fun out => ((rec out).run (fun _ => dR)).1) := by
  induction tree generalizing seen with
  | done out => simp only [answerRight,bindRight,actual_weakenAdd,actual_continuation,left,Merkle.RandomOracle.Tree.map]
  | queryLeft q next ih =>
      simp only [answerRight,bindRight,fixRight,left,Merkle.RandomOracle.Tree.map]
      congr; funext a; exact ih a seen
  | queryRight q next ih =>
      simp only [answerRight,bindRight,fixRight,left]
      exact ih _ _

section Setup
variable {Key : Type} [DecidableEq Key] [Inhabited DL]
variable {tA calls rounds Q TM : ℕ}
variable (S : Bcs.TotalOracleCommit.Setup QL DL P A Out Key tA calls rounds)

/-- Cache the complete setup program while preserving its public encoding
and context functions. The setup may include a right-only verifier replay. -/
def normalizeSetup (fallback : Out) (Q : ℕ) :
    Bcs.TotalOracleCommit.Setup QL DL P A Out Key tA Q rounds where
  body := normalizeRight fallback S.dflt S.body Q
  hashInput := S.hashInput
  dflt := S.dflt
  key := S.key
  keyOut := S.keyOut
  hkey := S.hkey

variable (fallback : Out) (mt : Fin TM → DL) (H : P → A)
variable (hcap : (TranscriptV2.seen (fixLeft mt default S.body []) H).card ≤ Q)

include hcap in
omit [DecidableEq Key] in
theorem normalizeSetup_proof :
    (normalizeSetup S fallback Q).proof mt H = S.proof mt H := by
  rw [Bcs.TotalOracleCommit.Setup.proof_eq,Bcs.TotalOracleCommit.Setup.proof_eq]
  exact normalizeRight_output fallback S.dflt S.body mt default H hcap

include hcap in
omit [DecidableEq Key] in
/-- The verifier continuation leaves the complete proof and Merkle slot
assignment unchanged; cached transcript answers are only local computation. -/
theorem normalizeSetup_joint_slots :
    let normalized := lazyRun mt default
      (fixRight (Fin.elim0 : Fin 0 → A) S.dflt
        ((normalizeSetup S fallback Q).atOracle H).joint []) []
    let original := lazyRun mt default
      (fixRight (Fin.elim0 : Fin 0 → A) S.dflt (S.atOracle H).joint []) []
    (normalized.1,normalized.2.1) = (original.1,original.2.1) := by
  change ((lazyRun mt default (fixRight (Fin.elim0 : Fin 0 → A) S.dflt
      ((answerRight H (normalizeRight fallback S.dflt S.body Q)).bindRight S.recompute) []) []).1,
    (lazyRun mt default (fixRight (Fin.elim0 : Fin 0 → A) S.dflt
      ((answerRight H (normalizeRight fallback S.dflt S.body Q)).bindRight S.recompute) []) []).2.1) = _
  rw [Bcs.TotalOracleCommit.Setup.joint_atOracle,actual_bind,actual_bind]
  simp only [lazyRun_map]
  have hs := right_left_slots fallback S.body mt default H Q ∅ (fun _ => S.dflt) []
    (by simp) (by simpa using hcap)
  exact congrArg (fun result : Out × List QL =>
    (((S.recompute result.1).run (fun _ => S.dflt)).1,result.2)) hs

include hcap in
omit [DecidableEq Key] in
/-- Caching does not change the lazy Merkle oracle seen by the original
verifier, including its terminal authentication check. -/
theorem normalizeSetup_merkleOracle {fc : ℕ} (check : Out → Tree QL DL Unit fc) :
    (normalizeSetup S fallback Q).merkleOracle check mt H = S.merkleOracle check mt H := by
  have hs := normalizeSetup_joint_slots S fallback mt H hcap
  change ((lazyRun mt default
      (fixRight Bcs.TotalOracleCommit.Setup.emptyTape
        ((normalizeSetup S fallback Q).atOracle H).dflt
        ((normalizeSetup S fallback Q).atOracle H).joint []) []).1,
    (lazyRun mt default
      (fixRight Bcs.TotalOracleCommit.Setup.emptyTape
        ((normalizeSetup S fallback Q).atOracle H).dflt
        ((normalizeSetup S fallback Q).atOracle H).joint []) []).2.1) =
    ((lazyRun mt default
      (fixRight Bcs.TotalOracleCommit.Setup.emptyTape (S.atOracle H).dflt
        (S.atOracle H).joint []) []).1,
    (lazyRun mt default
      (fixRight Bcs.TotalOracleCommit.Setup.emptyTape (S.atOracle H).dflt
        (S.atOracle H).joint []) []).2.1) at hs
  apply funext
  intro x
  unfold Bcs.TotalOracleCommit.Setup.merkleOracle Bcs.AdaptiveCommit.Setup.merkleOracle
    Merkle.MH.runOracle Merkle.MH.runSlots Bcs.AdaptiveCommit.Setup.merkleRun
  simp only [lazyRun_bind]
  have hout := congrArg Prod.fst hs
  have hslots := congrArg Prod.snd hs
  dsimp only at hout hslots
  rw [hout,hslots]

include hcap in
omit [DecidableEq Key] in
/-- Every ordinal cut preserves its entire Merkle execution trace. -/
theorem normalizeSetup_cutRun (index : ℕ) :
    lazyRun mt default (((normalizeSetup S fallback Q).atOracle H).cutRun
        (Fin.elim0 : Fin 0 → A) index) [] =
      lazyRun mt default ((S.atOracle H).cutRun (Fin.elim0 : Fin 0 → A) index) [] := by
  change lazyRun mt default
      (fixRight (Fin.elim0 : Fin 0 → A) S.dflt
        (stopAt index ((answerRight H (normalizeRight fallback S.dflt S.body Q)).bindRight S.recompute) []) []) [] =
    lazyRun mt default
      (fixRight (Fin.elim0 : Fin 0 → A) S.dflt
        (stopAt index ((answerRight H S.body).bindRight S.recompute) []) []) []
  rw [actual_stop_bind,actual_stop_bind]
  unfold normalizeRight
  exact right_stopped_bind fallback S.body _ mt default H index Q [] (fun _ => S.dflt) []
    (by simp) (by simpa using hcap)

include hcap in
omit [DecidableEq Key] in
/-- The fresh transcript query sequence is unchanged, so the first occurrence
of every context has the same ordinal cut. -/
theorem normalizeSetup_fsSeen :
    ((normalizeSetup S fallback Q).atOracle H).fsSeen mt (Fin.elim0 : Fin 0 → A) =
      (S.atOracle H).fsSeen mt (Fin.elim0 : Fin 0 → A) := by
  apply List.ext_getElem?
  intro i
  rw [← Bcs.AdaptiveCommit.Setup.cutRun_output,← Bcs.AdaptiveCommit.Setup.cutRun_output]
  exact congrArg Prod.fst (normalizeSetup_cutRun S fallback mt H hcap i)

include hcap in
/-- Exact first-context identity, including the full Merkle cut trace used by
the current extractor. This is derived rather than assumed after normalization. -/
theorem normalizeSetup_ctxAt (key : Key) :
    ((normalizeSetup S fallback Q).atOracle H).ctxAt mt (Fin.elim0 : Fin 0 → A) key =
      (S.atOracle H).ctxAt mt (Fin.elim0 : Fin 0 → A) key := by
  have hi : ((normalizeSetup S fallback Q).atOracle H).cutIdx mt (Fin.elim0 : Fin 0 → A) key =
      (S.atOracle H).cutIdx mt (Fin.elim0 : Fin 0 → A) key := by
    unfold Bcs.AdaptiveCommit.Setup.cutIdx
    rw [normalizeSetup_fsSeen S fallback mt H hcap]
    rfl
  unfold Bcs.AdaptiveCommit.Setup.ctxAt Bcs.AdaptiveCommit.Setup.cutTrace
  rw [hi,normalizeSetup_cutRun S fallback mt H hcap]

section Authentication
variable [DecidableEq DL] {Salt M : Type} [Inhabited Salt] [Inhabited M] {n fc : ℕ}

include hcap in
omit [DecidableEq Key] [DecidableEq DL] [Inhabited Salt] [Inhabited M] in
/-- The original verifier accepts exactly the same openings after caching. -/
theorem normalizeSetup_MerkleAccepts (codec : Merkle.MH.Codec Salt M DL QL)
    (check : Out → Tree QL DL Unit fc) (rootOf : Key → DL)
    (claimOf : Out → Merkle.MH.OpeningClaim n Salt M DL) :
    (normalizeSetup S fallback Q).MerkleAccepts codec check rootOf claimOf mt H ↔
      S.MerkleAccepts codec check rootOf claimOf mt H := by
  have hp := normalizeSetup_proof S fallback mt H hcap
  have ho := normalizeSetup_merkleOracle S fallback mt H hcap check
  unfold Bcs.TotalOracleCommit.Setup.MerkleAccepts Bcs.AdaptiveCommit.Setup.MerkleAccepts
  change Merkle.MH.Accepts
      (codec.withOracle ((normalizeSetup S fallback Q).merkleOracle check mt H)) n
      (rootOf (S.keyOut ((normalizeSetup S fallback Q).proof mt H)))
      (claimOf ((normalizeSetup S fallback Q).proof mt H)).I
      (claimOf ((normalizeSetup S fallback Q).proof mt H)).a
      (claimOf ((normalizeSetup S fallback Q).proof mt H)).pf ↔ _
  rw [hp,ho]
  rfl

include hcap in
/-- The same cut-trace extractor, not a replacement extractor, explains
exactly the same accepted opening after cached-query normalization. -/
theorem normalizeSetup_Explains {codec : Merkle.MH.Codec Salt M DL QL}
    (dec : Merkle.MH.RoleDecoders codec) (rootOf : Key → DL)
    (claimOf : Out → Merkle.MH.OpeningClaim n Salt M DL) :
    (normalizeSetup S fallback Q).Explains dec rootOf claimOf mt H ↔
      S.Explains dec rootOf claimOf mt H := by
  have hp := normalizeSetup_proof S fallback mt H hcap
  have ht := congrArg Prod.snd (normalizeSetup_ctxAt S fallback mt H hcap
    (S.keyOut (S.proof mt H)))
  unfold Bcs.AdaptiveCommit.Setup.ctxAt at ht
  dsimp only at ht
  unfold Bcs.TotalOracleCommit.Setup.Explains Bcs.AdaptiveCommit.Setup.Explains
  change (∃ extracted : Merkle.MH.Extracted n Salt M DL,
      Merkle.MH.extract dec n (rootOf (S.keyOut ((normalizeSetup S fallback Q).proof mt H)))
        (((normalizeSetup S fallback Q).atOracle H).cutTrace mt
          (Fin.elim0 : Fin 0 → A) (S.keyOut ((normalizeSetup S fallback Q).proof mt H))) = some extracted ∧
      (∀ i ∈ (claimOf ((normalizeSetup S fallback Q).proof mt H)).I,
        extracted.message i = (claimOf ((normalizeSetup S fallback Q).proof mt H)).a i) ∧
      Merkle.MH.openFromTrapdoor extracted.trapdoor
        (claimOf ((normalizeSetup S fallback Q).proof mt H)).I =
        (claimOf ((normalizeSetup S fallback Q).proof mt H)).pf) ↔ _
  rw [hp,ht]
  rfl

end Authentication

end Setup
end TranscriptV2.Memoize
