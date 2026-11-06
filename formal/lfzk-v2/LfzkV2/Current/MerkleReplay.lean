import LfzkV2.Current.Replay
import TranscriptV2.Recompute
import Bcs.PotentialCommit

/-! Adapt the current chained replay to the retained Merkle compiler. The
analysis records the verifier's final state after its ordinary boundary
queries; no annotations are added to the serialized proof. The one remaining
compiler query is the actual final-seal query. Fiat--Shamir counting uses the
original adversary, while this extended program is used for Merkle explanation. -/
namespace LfzkV2.Current.MerkleReplay
open Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree
open Replay

variable {g : Geometry} {F : Fields} {Advice Authentication Context Block C Enc D : Type}
variable (e : Encoding g F Advice Authentication Context Block C)
variable {tA Q TM : ℕ}

abbrev Annotated (g : Geometry) (F : Fields) (Advice Authentication Context Block C : Type) :=
  Output g F Advice Authentication × State g F Advice Authentication Context Block C

def setup (initialLink : Digest) (dflt : Digest × C)
    (body : TwoOracleTree Enc D (Point g F Advice Authentication Context Block) (Digest × C)
      (Output g F Advice Authentication) tA Q) :
    Bcs.TotalOracleCommit.Setup Enc D (Point g F Advice Authentication Context Block) (Digest × C)
      (Annotated g F Advice Authentication Context Block C) Context tA (g.roles.length+Q) 1 where
  body := body.bindRight (e.chain initialLink).recompute
  hashInput annotated _ := annotated.2.point
  dflt := dflt
  key := Input.context
  keyOut annotated := annotated.2.point.context
  hkey _ _ := rfl

variable [DecidableEq Enc] [Inhabited D]
variable [DecidableEq (Point g F Advice Authentication Context Block)]

/-- The extended program preserves the prover's proof and records exactly the
verifier replay. The original search still has only its `Q` query allowance. -/
theorem proof_eq (initialLink : Digest) (dflt : Digest × C)
    (body : TwoOracleTree Enc D (Point g F Advice Authentication Context Block) (Digest × C)
      (Output g F Advice Authentication) tA Q)
    (mt : Fin TM → D) (H : Point g F Advice Authentication Context Block → Digest × C) :
    (setup e initialLink dflt body).proof mt H =
      let proof := ((fixLeft mt default body []).run H).1
      (proof,(e.chain initialLink).replay proof H g.roles.length) := by
  rw [Bcs.TotalOracleCommit.Setup.proof_eq]
  simp only [Bcs.TotalOracleCommit.Setup.search, setup, fixLeft_bindRight, Tree.run_bind]
  exact (e.chain initialLink).recompute_result _ H

theorem proof_context (initialLink : Digest) (dflt : Digest × C)
    (body : TwoOracleTree Enc D (Point g F Advice Authentication Context Block) (Digest × C)
      (Output g F Advice Authentication) tA Q)
    (mt : Fin TM → D) (H : Point g F Advice Authentication Context Block → Digest × C) :
    (setup e initialLink dflt body).keyOut ((setup e initialLink dflt body).proof mt H) =
      e.context ((fixLeft mt default body []).run H).1 := by
  rw [proof_eq]
  exact e.point_context initialLink _ H g.roles.length

/-- The Merkle compiler's terminal point is precisely the body-binding seal
input, rather than an auxiliary statement-identifier or padding query. -/
theorem terminal_point (initialLink : Digest) (dflt : Digest × C)
    (body : TwoOracleTree Enc D (Point g F Advice Authentication Context Block) (Digest × C)
      (Output g F Advice Authentication) tA Q)
    (mt : Fin TM → D) (H : Point g F Advice Authentication Context Block → Digest × C) :
    (setup e initialLink dflt body).hashInput ((setup e initialLink dflt body).proof mt H) 0 =
      (e.chain initialLink).finalSealPoint ((fixLeft mt default body []).run H).1 H := by
  rw [proof_eq]
  rfl

end LfzkV2.Current.MerkleReplay
