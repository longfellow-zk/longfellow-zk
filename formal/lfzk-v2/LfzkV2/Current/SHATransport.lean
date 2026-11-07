import LfzkV2.Current.SHARouting
import LfzkV2.Current.ProofOutput

/-! SHA-domain routing commutes with the existing output parser,
canonical transcript codec and right-only verifier continuation. These are
structural program equalities, so they also hold inside first-context cuts. -/
noncomputable section
namespace LfzkV2.Current.SHATransport
open Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree ZeroKnowledge
open scoped Classical

variable {Raw D QT AT Out Result : Type}
variable (domain : Raw → Prop) (outside : Raw → D)

private theorem weaken_commute {left right : ℕ} (body : TwoOracleTree Raw D QT AT Out left right) :
    weakenRight (SHAOracle.weakenLeft body) = SHAOracle.weakenLeft (weakenRight body) := by
  induction body with
  | done value => rfl
  | queryLeft query next ih => simp only [weakenRight,SHAOracle.weakenLeft,ih]
  | queryRight query next ih => simp only [weakenRight,SHAOracle.weakenLeft,ih]

private theorem route_weaken {left right : ℕ} (body : TwoOracleTree Raw D QT AT Out left right) :
    SHAOracle.route domain outside (weakenRight body) = weakenRight (SHAOracle.route domain outside body) := by
  induction body with
  | done value => rfl
  | queryLeft query next ih =>
      by_cases member : domain query
      · simp only [weakenRight,SHAOracle.route,if_pos member,ih]
      · simp only [weakenRight,SHAOracle.route,if_neg member,ih,weaken_commute]
  | queryRight query next ih => simp only [weakenRight,SHAOracle.route,ih]

private theorem route_weaken_add {left right : ℕ} (body : TwoOracleTree Raw D QT AT Out left right) (extra : ℕ) :
    SHAOracle.route domain outside (weakenRightAdd extra body) = weakenRightAdd extra (SHAOracle.route domain outside body) := by
  induction extra with
  | zero => rfl
  | succ extra ih => rw [weakenRightAdd,route_weaken,ih,weakenRightAdd]

private theorem route_lift (left : ℕ) {right : ℕ} (body : Tree QT AT Out right) :
    SHAOracle.route domain outside (liftRightAt (QL := Raw) (DL := D) left body) = liftRightAt left body := by
  induction body with
  | done value => rfl
  | query query next ih => simp only [liftRightAt,SHAOracle.route,ih]

private theorem weaken_lift (left : ℕ) {right : ℕ} (body : Tree QT AT Out right) :
    SHAOracle.weakenLeft (liftRightAt (QL := Raw) (DL := D) left body) = liftRightAt (left+1) body := by
  induction body with
  | done value => rfl
  | query query next ih => simp only [liftRightAt,SHAOracle.weakenLeft,ih]

private theorem weaken_add {left right : ℕ} (body : TwoOracleTree Raw D QT AT Out left right) (extra : ℕ) :
    SHAOracle.weakenLeft (weakenRightAdd extra body) = weakenRightAdd extra (SHAOracle.weakenLeft body) := by
  induction extra with
  | zero => rfl
  | succ extra ih => rw [weakenRightAdd,← weaken_commute,ih,weakenRightAdd]

private theorem weaken_bind {left right continuation : ℕ} (body : TwoOracleTree Raw D QT AT Out left right)
    (rec : Out → Tree QT AT Result continuation) :
    (SHAOracle.weakenLeft body).bindRight rec = SHAOracle.weakenLeft (body.bindRight rec) := by
  induction body with
  | done value => simp only [SHAOracle.weakenLeft,bindRight,weaken_add,weaken_lift]
  | queryLeft query next ih => simp only [SHAOracle.weakenLeft,bindRight,ih]
  | queryRight query next ih => simp only [SHAOracle.weakenLeft,bindRight,ih]

theorem bind {left right continuation : ℕ} (body : TwoOracleTree Raw D QT AT Out left right)
    (rec : Out → Tree QT AT Result continuation) :
    SHAOracle.route domain outside (body.bindRight rec) = (SHAOracle.route domain outside body).bindRight rec := by
  induction body with
  | done value => simp only [bindRight,route_weaken_add,route_lift,SHAOracle.route]
  | queryLeft query next ih =>
      by_cases member : domain query
      · simp only [bindRight,SHAOracle.route,if_pos member,ih]
      · simp only [bindRight,SHAOracle.route,if_neg member,ih,weaken_bind]
  | queryRight query next ih => simp only [bindRight,SHAOracle.route,ih]

private theorem map_weaken (f : Out → Result) {left right : ℕ} (body : TwoOracleTree Raw D QT AT Out left right) :
    ProofOutput.map f (SHAOracle.weakenLeft body) = SHAOracle.weakenLeft (ProofOutput.map f body) := by
  induction body with
  | done value => rfl
  | queryLeft query next ih => simp only [ProofOutput.map,SHAOracle.weakenLeft,ih]
  | queryRight query next ih => simp only [ProofOutput.map,SHAOracle.weakenLeft,ih]

theorem map (f : Out → Result) {left right : ℕ} (body : TwoOracleTree Raw D QT AT Out left right) :
    SHAOracle.route domain outside (ProofOutput.map f body) = ProofOutput.map f (SHAOracle.route domain outside body) := by
  induction body with
  | done value => rfl
  | queryLeft query next ih =>
      by_cases member : domain query
      · simp only [ProofOutput.map,SHAOracle.route,if_pos member,ih]
      · simp only [ProofOutput.map,SHAOracle.route,if_neg member,ih,map_weaken]
  | queryRight query next ih => simp only [ProofOutput.map,SHAOracle.route,ih]

section Codec
variable {Input Point : Type} {valid : Point → Prop}
variable (codec : ByteOracleTransport.Codec Point Input valid) (other : Input → AT)

private theorem program_weaken {left right : ℕ} (body : TwoOracleTree Raw D Input AT Out left right) :
    codec.program other (SHAOracle.weakenLeft body) = SHAOracle.weakenLeft (codec.program other body) := by
  induction body with
  | done value => rfl
  | queryLeft query next ih => simp only [ByteOracleTransport.Codec.program,SHAOracle.weakenLeft,ih]
  | queryRight query next ih =>
      cases decoded : codec.decode query with
      | none => simp only [ByteOracleTransport.Codec.program,SHAOracle.weakenLeft,decoded,ih,weaken_commute]
      | some point => simp only [ByteOracleTransport.Codec.program,SHAOracle.weakenLeft,decoded,ih]

theorem program {left right : ℕ} (body : TwoOracleTree Raw D Input AT Out left right) :
    SHAOracle.route domain outside (codec.program other body) =
      codec.program other (SHAOracle.route domain outside body) := by
  induction body with
  | done value => rfl
  | queryLeft query next ih =>
      by_cases member : domain query
      · simp only [ByteOracleTransport.Codec.program,SHAOracle.route,if_pos member,ih]
      · simp only [ByteOracleTransport.Codec.program,SHAOracle.route,if_neg member,ih,program_weaken]
  | queryRight query next ih =>
      cases decoded : codec.decode query with
      | none => simp only [ByteOracleTransport.Codec.program,decoded,route_weaken,SHAOracle.route,ih]
      | some point => simp only [ByteOracleTransport.Codec.program,decoded,SHAOracle.route,ih]

end Codec
end LfzkV2.Current.SHATransport
