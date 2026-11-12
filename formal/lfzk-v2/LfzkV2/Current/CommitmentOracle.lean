import LfzkV2.Current.Opening
import LfzkV2.Current.JointResponse
import LfzkV2.Joint.Pair.Basic

/-! One current Merkle commitment explains the complete two-field tuple.
The oracle used by Fiat--Shamir counting and witness selection is recovered
from this same cut. Neither participant gets a second tree or explanation.
The check has size `2*n`; the sole compiler continuation is the final seal. -/
noncomputable section
namespace LfzkV2.Current.CommitmentOracle
open RecursivePolygero LigeroFamily Merkle Merkle.MH Merkle.RandomOracle
  Merkle.RandomOracle.TwoOracleTree Replay
open scoped Classical

variable {k s n t : ℕ} (P R : Joint.Participant k s n t)
variable {g : Geometry} {F : Fields} {Advice Authentication Context Block C Enc D Salt : Type}
variable {tA Q TM : ℕ}
variable (e : Encoding g F Advice Authentication Context Block C)
variable (initialLink : Digest) (dflt : Digest × C)
variable (body : TwoOracleTree Enc D (Point g F Advice Authentication Context Block) (Digest × C)
  (Output g F Advice Authentication) tA Q)
variable [DecidableEq Enc] [Inhabited D] [DecidableEq D] [DecidableEq Context]
variable [DecidableEq (Point g F Advice Authentication Context Block)]
variable [Inhabited Salt] [Inhabited (Joint.Pair.family P R).Leaf]
variable {codec : Codec Salt (Joint.Pair.family P R).Leaf D Enc}
variable (dec : RoleDecoders codec) (rootOf : Context → D)

local notation "K" => MerkleReplay.setup e initialLink dflt body

/-- Recover all typed columns together from the trace preceding the first
query that names their committed context. -/
def tupleOracle (mt : Fin TM → D)
    (H : Point g F Advice Authentication Context Block → Digest × C) (key : Context) :
    (Joint.Pair.family P R).Oracle :=
  let ctx := ((K).atOracle H).ctxAt mt Bcs.TotalOracleCommit.Setup.emptyTape key
  (Joint.Pair.family P R).extractedOracle dec (rootOf ctx.1) ctx.2

def cutOracle (mt : Fin TM → D)
    (H : Point g F Advice Authentication Context Block → Digest × C) (key : Context) :
    JointResponse.Oracle P R :=
  Joint.Pair.oracleEquiv P R (tupleOracle P R e initialLink dflt body dec rootOf mt H key)

/-- Changing a query answer cannot change the committed tuple cut associated
with that query's context. This is the own-answer invariance used by every
backend and witness-selection charge. -/
theorem cutOracle_off (mt : Fin TM → D)
    (z : Point g F Advice Authentication Context Block)
    (H H' : Point g F Advice Authentication Context Block → Digest × C)
    (h : Bcs.TotalOracle.AgreeOff z H H') :
    cutOracle P R e initialLink dflt body dec rootOf mt H z.context =
      cutOracle P R e initialLink dflt body dec rootOf mt H' z.context := by
  apply congrArg (Joint.Pair.oracleEquiv P R)
  unfold tupleOracle
  have hc := (K).ctxAt_off mt H H' z h
  exact congrArg (fun ctx : Context × List (Enc × D) =>
    (Joint.Pair.family P R).extractedOracle dec (rootOf ctx.1) ctx.2) hc.symm

section Check
variable {Leaf Out : Type} (checkCodec : Codec Salt Leaf D Enc)
variable (claimOf : Out → OpeningClaim n Salt Leaf D)

/-- One opening check for the tuple leaf, with the standard `2*n` bound. -/
def check (out : Out) : Tree Enc D Unit (2*n) :=
  (checkPass checkCodec n (claimOf out).I (claimOf out).a (claimOf out).pf (2*n)
    fun _ => default).map fun _ => ()

omit [DecidableEq D] [DecidableEq Context]
    [DecidableEq (Point g F Advice Authentication Context Block)] [Inhabited Salt]
    [Inhabited (Joint.Pair.family P R).Leaf] in
theorem check_contains (H : Enc → D) (out : Out) (qa : Enc × D)
    (h : qa ∈ ((checkPass checkCodec n (claimOf out).I (claimOf out).a
      (claimOf out).pf (2*n) fun _ => default).run H).2) :
    qa ∈ ((check checkCodec claimOf out).run H).2 := by
  simpa only [check, Tree.run_map] using h
end Check

variable (claimOf : MerkleReplay.Annotated g F Advice Authentication Context Block C →
  OpeningClaim n Salt (Joint.Pair.family P R).Leaf D)

/-- Arithmetic acceptance on the one authenticated tuple opening. -/
def CompiledAccepts (ht : 0 < t) (σ : JointResponse.Statement P R)
    (coin : JointResponse.Coin P R) (response : JointResponse.Response P R) (query : QuerySet n t)
    (mt : Fin TM → D) (H : Point g F Advice Authentication Context Block → Digest × C) : Prop :=
  ((Joint.Pair.family P R).compiler ht).Accepts
    (codec.withOracle ((K).merkleOracle
      (check codec claimOf) mt H))
    ((Joint.Pair.statementEquiv P R).symm σ) (rootOf ((K).keyOut ((K).proof mt H)))
    ((Joint.Pair.coinEquiv P R).symm coin) ((Joint.Pair.responseEquiv P R).symm response)
    query (claimOf ((K).proof mt H))

omit [DecidableEq D] [DecidableEq Context] [Inhabited Salt]
    [Inhabited (Joint.Pair.family P R).Leaf] in
/-- The compiled verifier's authentication check is exactly the check used
by the one-tree Merkle error theorem. -/
theorem merkle_accepts (ht : 0 < t) (σ : JointResponse.Statement P R)
    (coin : JointResponse.Coin P R) (response : JointResponse.Response P R) (query : QuerySet n t)
    (mt : Fin TM → D) (H : Point g F Advice Authentication Context Block → Digest × C)
    (ha : CompiledAccepts (codec := codec) P R e initialLink dflt body rootOf claimOf ht σ coin response query mt H) :
    (K).MerkleAccepts codec (check codec claimOf) rootOf claimOf mt H :=
  ha.2.1

/-- Accepted arithmetic and the single tuple explanation imply both backend
verifiers on the identical cut oracle used in the Fiat--Shamir charges. -/
theorem verify_of_explains (ht : 0 < t) (σ : JointResponse.Statement P R)
    (coin : JointResponse.Coin P R) (response : JointResponse.Response P R) (query : QuerySet n t)
    (mt : Fin TM → D) (H : Point g F Advice Authentication Context Block → Digest × C)
    (ha : CompiledAccepts (codec := codec) P R e initialLink dflt body rootOf claimOf ht σ coin response query mt H)
    (he : (K).Explains dec rootOf claimOf mt H) :
    JointResponse.Verify P R σ
      (cutOracle P R e initialLink dflt body dec rootOf mt H ((K).keyOut ((K).proof mt H)))
      coin response query := by
  obtain ⟨extracted,hext,hagree,-⟩ := he
  have hv := (Joint.Pair.family P R).verify_of_extraction ht dec
    (codec.withOracle ((K).merkleOracle (check codec claimOf) mt H))
    ((Joint.Pair.statementEquiv P R).symm σ) (rootOf ((K).keyOut ((K).proof mt H)))
    (((K).atOracle H).cutTrace mt Bcs.TotalOracleCommit.Setup.emptyTape ((K).keyOut ((K).proof mt H)))
    ((Joint.Pair.coinEquiv P R).symm coin) ((Joint.Pair.responseEquiv P R).symm response)
    query (claimOf ((K).proof mt H)) extracted hext hagree ha
  exact (Joint.Pair.verify_iff P R σ _ coin response query).mp hv

end LfzkV2.Current.CommitmentOracle
