import LfzkV2.Current.CanonicalReplay
import LfzkV2.Current.CanonicalRuntime
import LfzkV2.Current.ByteOracleProbability
import LfzkV2.Current.RuntimeAdaptiveCommitment

/-! Oracle agreement on canonical physical inputs. Malformed typed caches
are auxiliary coordinates, so changing only those coordinates must preserve
the actual program, verifier replay and commitment extractor. These lemmas
establish that independence before taking uniform byte-oracle marginals. -/
noncomputable section
namespace LfzkV2.Current.CanonicalOracle
open Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree
open Bcs.TotalOracleCommit
open scoped Classical

section Programs
variable {Point Raw A QL DL Out : Type} {valid : Point → Prop}

private theorem answerRight_weaken (H : Point → A) {left right : ℕ}
    (body : TwoOracleTree QL DL Point A Out left right) :
    answerRight H (weakenRight body) = weakenRight (answerRight H body) := by
  induction body with
  | done _ => rfl
  | queryLeft q next ih =>
      simp only [answerRight,weakenRight]
      exact congrArg (TwoOracleTree.queryLeft q) (funext ih)
  | queryRight q next ih =>
      simp only [answerRight,weakenRight]
      exact congrArg (TwoOracleTree.queryRight q) (funext fun _ => ih (H q))

private theorem answerRight_weakenAdd (H : Point → A) {left right : ℕ}
    (body : TwoOracleTree QL DL Point A Out left right) (count : ℕ) :
    answerRight H (weakenRightAdd count body) = weakenRightAdd count (answerRight H body) := by
  induction count with
  | zero => rfl
  | succ n ih => rw [weakenRightAdd,answerRight_weaken,ih]; rfl

private theorem answerRight_lift (H : Point → A) {right : ℕ}
    (body : Tree Point A Out right) (left : ℕ) :
    answerRight H (liftRightAt (QL := QL) (DL := DL) left body) =
      liftRightAt left (answerWith H body) := by
  induction body with
  | done _ => rfl
  | query q next ih =>
      simp only [answerRight,liftRightAt,answerWith]
      exact congrArg (TwoOracleTree.queryRight q) (funext fun _ => ih (H q))

theorem answerRight_bindRight (H : Point → A) {left right more : ℕ} {Result : Type}
    (body : TwoOracleTree QL DL Point A Out left right) (continuation : Out → Tree Point A Result more) :
    answerRight H (body.bindRight continuation) =
      (answerRight H body).bindRight (fun output => answerWith H (continuation output)) := by
  induction body with
  | done output => simp only [bindRight,answerRight,answerRight_weakenAdd,answerRight_lift]
  | queryLeft q next ih =>
      simp only [bindRight,answerRight]
      exact congrArg (TwoOracleTree.queryLeft q) (funext ih)
  | queryRight q next ih =>
      simp only [bindRight,answerRight]
      exact congrArg (TwoOracleTree.queryRight q) (funext fun _ => ih (H q))

/-- The translated program reads only canonical points, even when the
original program interleaves arbitrary malformed raw queries. -/
theorem answerRight_program (codec : ByteOracleTransport.Codec Point Raw valid)
    (outside : Raw → A) (H H' : Point → A) (agree : ∀ point, valid point → H point = H' point)
    {left right : ℕ} (body : TwoOracleTree QL DL Raw A Out left right) :
    answerRight H (codec.program outside body) = answerRight H' (codec.program outside body) := by
  induction body with
  | done _ => rfl
  | queryLeft q next ih =>
      simp only [ByteOracleTransport.Codec.program,answerRight]
      exact congrArg (TwoOracleTree.queryLeft q) (funext ih)
  | queryRight q next ih =>
      cases hd : codec.decode q with
      | none =>
          simp only [ByteOracleTransport.Codec.program,hd,answerRight_weaken]
          exact congrArg weakenRight (ih (outside q))
      | some point =>
          simp only [ByteOracleTransport.Codec.program,hd,answerRight,agree point.val point.property]
          exact congrArg (TwoOracleTree.queryRight point.val) (funext fun _ => ih (H' point.val))

/-- The simulator consults its auxiliary oracle only on inputs rejected by
the canonical parser. Its values on valid bytes have no effect at all. -/
theorem program_outside_congr (codec : ByteOracleTransport.Codec Point Raw valid)
    (outside outside' : Raw → A)
    (agree : ∀ raw, codec.decode raw = none → outside raw = outside' raw)
    {left right : ℕ} (body : TwoOracleTree QL DL Raw A Out left right) :
    codec.program outside body = codec.program outside' body := by
  induction body with
  | done _ => rfl
  | queryLeft q next ih =>
      simp only [ByteOracleTransport.Codec.program]
      exact congrArg (TwoOracleTree.queryLeft q) (funext ih)
  | queryRight q next ih =>
      cases hd : codec.decode q with
      | none =>
          simp only [ByteOracleTransport.Codec.program,hd,agree q hd]
          exact congrArg weakenRight (ih (outside' q))
      | some point =>
          simp only [ByteOracleTransport.Codec.program,hd]
          exact congrArg (TwoOracleTree.queryRight point.val) (funext ih)

theorem program_oracle (codec : ByteOracleTransport.Codec Point Raw valid)
    (outside : Raw → A) (H : Point → A) {left right : ℕ}
    (body : TwoOracleTree QL DL Raw A Out left right) :
    codec.program (codec.oracle outside H) body = codec.program outside body := by
  apply program_outside_congr codec _ outside _ body
  intro raw h
  simp only [ByteOracleTransport.Codec.oracle,h]

theorem oracle_eq (codec : ByteOracleTransport.Codec Point Raw valid)
    (outside : Raw → A) (H H' : Point → A) (agree : ∀ point, valid point → H point = H' point) :
    codec.oracle outside H = codec.oracle outside H' := by
  funext raw
  unfold ByteOracleTransport.Codec.oracle
  cases hd : codec.decode raw with
  | none => rfl
  | some point => exact agree point.val point.property

theorem restrict_oracle (codec : ByteOracleTransport.Codec Point Raw valid)
    (outside : Raw → A) (H fallback : Point → A) (point : Point) (hp : valid point) :
    codec.restrict (codec.oracle outside H) fallback point = H point := by
  simp only [ByteOracleTransport.Codec.restrict,dif_pos hp,ByteOracleTransport.Codec.oracle_encode]

theorem program_run_eq [DecidableEq QL]
    (codec : ByteOracleTransport.Codec Point Raw valid)
    (outside : Raw → A) (H H' : Point → A) (agree : ∀ point, valid point → H point = H' point)
    {left right tapeSize : ℕ} (body : TwoOracleTree QL DL Raw A Out left right)
    (tape : Fin tapeSize → DL) (dflt : DL) (seen : List QL) :
    (fixLeft tape dflt (codec.program outside body) seen).run H =
      (fixLeft tape dflt (codec.program outside body) seen).run H' := by
  rw [codec.fixLeft_program,codec.run_tree,codec.run_tree,oracle_eq codec outside H H' agree]

private theorem answerWith_map (H : Point → A) {fuel : ℕ} {Result : Type}
    (body : Tree Point A Out fuel) (f : Out → Result) :
    answerWith H (body.map f) = (answerWith H body).map f := by
  induction body with
  | done _ => rfl
  | query q next ih =>
      simp only [answerWith,Merkle.RandomOracle.Tree.map]
      exact congrArg (Tree.query q) (funext fun _ => ih (H q))

end Programs

section Replay
variable {Point Link C Out : Type} {rounds : ℕ}
variable (chain : TranscriptV2.Chain Point Link C Out rounds)

private theorem answerWith_recomputeFrom (output : Out) (H H' : Point → Link × C)
    (agree : ∀ k < rounds, H (chain.point output H k) = H' (chain.point output H k))
    (remaining start : ℕ) (fits : start+remaining ≤ rounds) :
    answerWith H (chain.recomputeFrom output remaining start (chain.replay output H start)) =
      answerWith H' (chain.recomputeFrom output remaining start (chain.replay output H start)) := by
  induction remaining generalizing start with
  | zero => rfl
  | succ remaining ih =>
      have hs : start < rounds := by omega
      simp only [TranscriptV2.Chain.recomputeFrom,dif_pos hs,answerWith]
      have ha := agree start hs
      change H (chain.input (chain.replay output H start)) = H' (chain.input (chain.replay output H start)) at ha
      rw [← ha]
      apply congrArg (Tree.query (chain.input (chain.replay output H start)))
      funext answer
      have hstep : chain.advance output ⟨start,hs⟩ (chain.replay output H start)
          (H (chain.input (chain.replay output H start))) = chain.replay output H (start+1) := by
        simp only [TranscriptV2.Chain.replay,dif_pos hs]
      rw [hstep]
      exact ih (start+1) (by omega)

/-- Agreement on actual replay inputs preserves the whole answered
recomputation program, not only its final state. -/
theorem answerWith_recompute (output : Out) (H H' : Point → Link × C)
    (agree : ∀ k < rounds, H (chain.point output H k) = H' (chain.point output H k)) :
    answerWith H (chain.recompute output) = answerWith H' (chain.recompute output) := by
  rw [TranscriptV2.Chain.recompute,answerWith_map,answerWith_map]
  exact congrArg (fun body : Tree Point (Link × C) chain.State rounds => body.map (fun state => (output,state)))
    (answerWith_recomputeFrom chain output H H' agree rounds 0 (by omega))

theorem answered_program_recompute {Raw QL DL : Type} {valid : Point → Prop}
    (codec : ByteOracleTransport.Codec Point Raw valid) (outside : Raw → Link × C)
    (H H' : Point → Link × C) (agree : ∀ point, valid point → H point = H' point)
    (canonical : ∀ output H k, k < rounds → valid (chain.point output H k))
    {left right : ℕ} (body : TwoOracleTree QL DL Raw (Link × C) Out left right) :
    answerRight H ((codec.program outside body).bindRight chain.recompute) =
      answerRight H' ((codec.program outside body).bindRight chain.recompute) := by
  rw [answerRight_bindRight,answerRight_bindRight,answerRight_program codec outside H H' agree]
  congr 1
  funext output
  exact answerWith_recompute chain output H H'
    (fun k hk => agree _ (canonical output H k hk))

end Replay

section Commitment
variable {Enc D Point A Out Key : Type}
variable [DecidableEq Enc] [Inhabited D] [DecidableEq Point]
variable {left right final : ℕ}

omit [DecidableEq Enc] [Inhabited D] [DecidableEq Point] in
/-- Equality of answered programs preserves the complete commitment
experiment, including its first-context cut and verifier Merkle oracle. -/
theorem atOracle_eq (setup : Bcs.TotalOracleCommit.Setup Enc D Point A Out Key left right final)
    (H H' : Point → A) (h : answerRight H setup.body = answerRight H' setup.body) :
    setup.atOracle H = setup.atOracle H' := by
  simp only [Bcs.TotalOracleCommit.Setup.atOracle,h]

end Commitment

end LfzkV2.Current.CanonicalOracle
