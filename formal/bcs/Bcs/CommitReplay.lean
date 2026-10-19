import Bcs.PotentialCommit

/-! Verifier challenge replay does not change the Merkle query program. -/
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace Merkle.RandomOracle.TwoOracleTree
open Bcs.TotalOracleCommit
open scoped Classical
variable {QL DL QR DR A B : Type} [DecidableEq QR] {TR : ℕ}
variable (tape : Fin TR → DR) (d : DR)

@[simp] theorem fixRight_weakenRight {l r : ℕ} (t : TwoOracleTree QL DL QR DR A l r) (seen : List QR) :
    fixRight tape d t.weakenRight seen = fixRight tape d t seen := by
  induction t generalizing seen with
  | done => rfl
  | queryLeft q next ih => simp only [weakenRight,fixRight]; congr 1; funext y; exact ih y seen
  | queryRight q next ih => simp only [weakenRight,fixRight]; exact ih _ _

@[simp] theorem fixRight_weakenRightAdd {l r : ℕ} (k : ℕ)
    (t : TwoOracleTree QL DL QR DR A l r) (seen : List QR) :
    fixRight tape d (t.weakenRightAdd k) seen = fixRight tape d t seen := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [weakenRightAdd,fixRight_weakenRight,ih]

theorem fixRight_liftRight_map_const {l r : ℕ} (t : Tree QR DR B r) (seen : List QR) (a : A) :
    (fixRight tape d (liftRightAt (QL := QL) (DL := DL) l t) seen).map (fun _ => a) = .done a := by
  induction t generalizing seen with
  | done => rfl
  | query q next ih => simp only [liftRightAt,fixRight]; exact ih _ _

theorem fixRight_liftRight_map_fst {l r : ℕ} (t : Tree QR DR B r) (seen : List QR) (a : A) :
    (fixRight tape d (liftRightAt (QL := QL) (DL := DL) l (t.map (fun b => (a,b)))) seen).map Prod.fst = .done a := by
  induction t generalizing seen with
  | done => rfl
  | query q next ih => simp only [Tree.map,liftRightAt,fixRight]; exact ih _ _

theorem fixRight_bindRight_map_fst {l r k : ℕ}
    (t : TwoOracleTree QL DL QR DR A l r) (next : A → Tree QR DR B k) (seen : List QR) :
    (fixRight tape d (t.bindRight (fun a => (next a).map (fun b => (a,b)))) seen).map Prod.fst =
      fixRight tape d t seen := by
  induction t generalizing seen with
  | done a =>
    simp only [bindRight,fixRight_weakenRightAdd,fixRight]
    exact fixRight_liftRight_map_fst tape d _ seen a
  | queryLeft q rest ih => simp only [bindRight,fixRight,Tree.map]; congr 1; funext y; exact ih y seen
  | queryRight q rest ih => simp only [bindRight,fixRight]; exact ih _ _

end Merkle.RandomOracle.TwoOracleTree

namespace Bcs.TotalOracleCommit.Setup
open Merkle Merkle.MH Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree
open scoped Classical
variable {Enc D Pt C Out Key : Type} [DecidableEq Enc] [Inhabited D] [DecidableEq Pt]
  {tA N L TM fc : ℕ}
variable (S : TotalOracleCommit.Setup Enc D Pt C Out Key tA N L)

/-- The Merkle tape sees only the prover and Merkle checker. The intermediate
challenge replay has no Merkle queries and cannot change the slot assignment. -/
theorem merkleOracle_body (check : Out → Tree Enc D Unit fc) (mt : Fin TM → D) (H : Pt → C) :
    S.merkleOracle check mt H =
      runOracle TM ((fixRight emptyTape S.dflt (answerRight H S.body) []).bind check) mt := by
  let T := fixRight emptyTape S.dflt (S.atOracle H).joint []
  have he : T.map Prod.fst = fixRight emptyTape S.dflt (answerRight H S.body) [] := by
    apply fixRight_bindRight_map_fst
  have hmap : ∀ {Q C A B E : Type} {f g : ℕ} (t : Tree Q C A f) (p : A → B)
      (c : B → Tree Q C E g), (t.map p).bind c = t.bind (fun a => c (p a)) := by
    intros Q C A B E f g t p c
    induction t with
    | done a => rfl
    | query q next ih => simp only [Merkle.RandomOracle.Tree.map,Merkle.RandomOracle.Tree.bind]; congr 1; funext y; exact ih y
  have hs := congrArg (fun t => (t.bind check)) he
  rw [hmap] at hs
  unfold merkleOracle AdaptiveCommit.Setup.merkleOracle AdaptiveCommit.Setup.merkleRun
  unfold runOracle runSlots
  rw [← hs]
  simp only [lazyRun_bind,lazyRun_map]
  rfl

/-- With no Merkle queries the commitment cut trace is empty, regardless
of the number or order of challenge queries. -/
theorem cutTrace_zero [DecidableEq Key]
    (S : TotalOracleCommit.Setup Enc D Pt C Out Key 0 N L)
    (mt : Fin TM → D) (H : Pt → C) (k : Key) :
    ((S.atOracle H).ctxAt mt emptyTape k).2 = [] := by
  change ((S.atOracle H).cutTrace mt emptyTape k) = []
  unfold AdaptiveCommit.Setup.cutTrace
  cases he : (S.atOracle H).cutRun emptyTape ((S.atOracle H).cutIdx mt emptyTape k) with
  | done _ => simp only [he,lazyRun_done]

end Bcs.TotalOracleCommit.Setup
