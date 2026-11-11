import LfzkV2.Current.RuntimeAdaptiveVerifier
import LfzkV2.Current.CommitmentOracle

/-! One shared tuple commitment for adaptive public requests. Ordinary
verifier replay is an analysis annotation; no request or annotation is added
to the serialized proof body. The final continuation is its actual seal. -/
noncomputable section
namespace LfzkV2.Current.RuntimeAdaptiveMerkle
open Application ApplicationSetup ApplicationOracle RecursivePolygero SumcheckV2
open Merkle Merkle.MH Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice Base Key C B Salt Enc Request : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable {shared maskBits adviceBits k s n t : ℕ}
variable (binary : BinaryPublic B shared maskBits adviceBits)
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable (prime : PrimePublic N shared)
variable (P : FieldBackend B k s n t) (R : FieldBackend N k s n t)
variable (cfg : RuntimeVerifier.Public (g := g) binary prime P R (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key) (C := C) (Salt := Salt))
variable (earlier : Request → Replay.Encoding g fields Advice (RuntimeVerifier.Authentication (g := g)) Key
  (RuntimeVerifier.Block (g := g) (fields := fields) (Advice := Advice) (Base := Base)) C)
local notation "Point" => RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key)
local notation "Output" => RuntimeAdaptiveVerifier.Output (g := g) (fields := fields) (Advice := Advice) (Request := Request)
local notation "First" => RuntimeVerifier.first binary prime P R cfg
local notation "Second" => RuntimeVerifier.second binary prime P R cfg
local notation "M" => RuntimeAdaptiveVerifier.chain binary prime P R cfg earlier
local notation "E" => RuntimeAdaptiveVerifier.encodings binary prime P R cfg earlier
local notation "Decoded" => RuntimeVerifier.Decoded binary prime P R cfg

abbrev Annotated := RuntimeAdaptiveVerifier.Output (g := g) (fields := fields) (Advice := Advice) (Request := Request) ×
  Replay.State g fields Advice (RuntimeVerifier.Authentication (g := g)) Key
    (RuntimeVerifier.Block (g := g) (fields := fields) (Advice := Advice) (Base := Base)) C

variable [Inhabited Salt] [Inhabited (RuntimeVerifier.Family binary prime P R cfg).Leaf]
private def emptyClaim : OpeningClaim n Salt (RuntimeVerifier.Family binary prime P R cfg).Leaf Digest where
  I := ∅
  a := fun _ => default
  pf := { nonce := fun _ => default, frontierValue := fun _ => default }

/-- Reconstruct the opening from its three inputs: the proof payload, the
bound public context and the opening answer. Transcript history and the other
cached challenges play no part in this operation. -/
def claim (proof : Replay.Output g fields Advice (RuntimeVerifier.Authentication (g := g)))
    (context : Key) (opening : C) :
    OpeningClaim n Salt (RuntimeVerifier.Family binary prime P R cfg).Leaf Digest :=
  (OrderedOpening.decode (cfg.bindSalt context) (cfg.sample opening)
    (OpeningBody.raw (First).participant (Second).participant cfg.binaryField cfg.primeField
      cfg.binaryRows cfg.primeRows cfg.openings proof)).getD (emptyClaim binary prime P R cfg)

/-- Adapter for the generic replay annotation. The default claim only
totalizes failed decoding; acceptance still requires decoding to succeed. -/
def claimOf (out : Annotated (g := g) (fields := fields) (Advice := Advice)
    (Base := Base) (Key := Key) (C := C) (Request := Request)) :
    OpeningClaim n Salt (RuntimeVerifier.Family binary prime P R cfg).Leaf Digest :=
  claim binary prime P R cfg out.1.proof out.2.point.context
    (OrderedOpening.openingAnswer (g := g) cfg.fallback out.2.answers)

variable (hashPublic : Key → Option (Fin binary.nPublic → Bool))
variable (decodePublic : Base → Option (Fin prime.nPublic → N))
variable (draw : C → RuntimeVerifier.RawSamples binary prime P R cfg)

theorem claimOf_replay (output : Output) (H : Point → Digest × C) (decoded : Decoded)
    (hd : RuntimeAdaptiveVerifier.decode binary prime P R cfg earlier hashPublic decodePublic draw output H = some decoded) :
    claimOf binary prime P R cfg (output,(M).replay output H g.roles.length) = decoded.claim := by
  have hs := RuntimeAdaptiveVerifier.decode_spec binary prime P R cfg earlier hashPublic decodePublic draw output H decoded hd
  change claimOf binary prime P R cfg
    (output,(RuntimeAdaptive.chain (E) cfg.initialLink).replay output H g.roles.length) = _
  rw [RuntimeAdaptive.replay_eq]
  unfold claimOf claim
  rw [OrderedOpening.openingAnswer_replay]
  change (OrderedOpening.decode
    (cfg.bindSalt (((E output.request).chain cfg.initialLink).point output.proof H g.roles.length).context)
    (cfg.sample (H (((E output.request).chain cfg.initialLink).point output.proof H g.openingIndex.val)).2)
    (OpeningBody.raw (First).participant (Second).participant cfg.binaryField cfg.primeField
      cfg.binaryRows cfg.primeRows cfg.openings output.proof)).getD (emptyClaim binary prime P R cfg) = decoded.claim
  rw [(E output.request).point_context cfg.initialLink output.proof H g.roles.length]
  rw [hs.2.1]
  rfl

variable (codec : Codec Salt (RuntimeVerifier.Family binary prime P R cfg).Leaf Digest Enc)
variable [DecidableEq Enc]
abbrev check : Annotated (g := g) (fields := fields) (Advice := Advice)
    (Base := Base) (Key := Key) (C := C) (Request := Request) → Tree Enc Digest Unit (2*n) :=
  CommitmentOracle.check codec (claimOf binary prime P R cfg)

section Program
variable [DecidableEq Key] [DecidableEq (RuntimeVerifier.Point (g := g) (fields := fields)
  (Advice := Advice) (Base := Base) (Key := Key))]
variable {calls tA TM : ℕ} (dflt : Digest × C)
variable (body : TwoOracleTree Enc Digest (RuntimeVerifier.Point (g := g) (fields := fields)
  (Advice := Advice) (Base := Base) (Key := Key)) (Digest × C)
  (RuntimeAdaptiveVerifier.Output (g := g) (fields := fields) (Advice := Advice) (Request := Request)) tA calls)

/-- Replay adds only analysis queries. Both participants still share one
commitment, one opening query and one tuple explanation. -/
def setup : Bcs.TotalOracleCommit.Setup Enc Digest Point (Digest × C)
    (Annotated (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key) (C := C) (Request := Request))
    Key tA (g.roles.length+calls) 1 where
  body := body.bindRight (M).recompute
  hashInput annotated _ := annotated.2.point
  dflt := dflt
  key := Input.context
  keyOut annotated := annotated.2.point.context
  hkey _ _ := rfl

abbrev originalOutput (mt : Fin TM → Digest) (H : Point → Digest × C) : Output :=
  ((fixLeft mt default body []).run H).1

omit [Inhabited Salt] [Inhabited (RuntimeVerifier.Family binary prime P R cfg).Leaf] [DecidableEq Key] in
theorem proof_eq (mt : Fin TM → Digest) (H : Point → Digest × C) :
    (setup binary prime P R cfg earlier dflt body).proof mt H =
      let output := originalOutput body mt H
      (output,(M).replay output H g.roles.length) := by
  rw [Bcs.TotalOracleCommit.Setup.proof_eq]
  simp only [Bcs.TotalOracleCommit.Setup.search,setup,fixLeft_bindRight,Tree.run_bind]
  exact (M).recompute_result _ H

omit [Inhabited Salt] [Inhabited (RuntimeVerifier.Family binary prime P R cfg).Leaf] [DecidableEq Key] in
theorem proof_context (mt : Fin TM → Digest) (H : Point → Digest × C) :
    (setup binary prime P R cfg earlier dflt body).keyOut
        ((setup binary prime P R cfg earlier dflt body).proof mt H) =
      (E (originalOutput body mt H).request).context (originalOutput body mt H).proof := by
  rw [proof_eq]
  change ((M).point (originalOutput body mt H) H g.roles.length).context = _
  rw [RuntimeAdaptiveVerifier.point_eq]
  exact (E _).point_context cfg.initialLink _ H g.roles.length

omit [Inhabited Salt] [Inhabited (RuntimeVerifier.Family binary prime P R cfg).Leaf] [DecidableEq Key] in
theorem terminal_point (mt : Fin TM → Digest) (H : Point → Digest × C) :
    (setup binary prime P R cfg earlier dflt body).hashInput
        ((setup binary prime P R cfg earlier dflt body).proof mt H) 0 =
      (M).finalSealPoint (originalOutput body mt H) H := by
  rw [proof_eq]
  rfl

abbrev merkleOracle (mt : Fin TM → Digest) (H : Point → Digest × C) : Enc → Digest :=
  (setup binary prime P R cfg earlier dflt body).merkleOracle (check binary prime P R cfg codec) mt H

def tupleOracle (dec : RoleDecoders codec) (mt : Fin TM → Digest)
    (H : Point → Digest × C) (key : Key) : (RuntimeVerifier.Family binary prime P R cfg).Oracle :=
  let ctx := ((setup binary prime P R cfg earlier dflt body).atOracle H).ctxAt mt
    Bcs.TotalOracleCommit.Setup.emptyTape key
  (RuntimeVerifier.Family binary prime P R cfg).extractedOracle dec (cfg.root ctx.1) ctx.2

def cutOracle (dec : RoleDecoders codec) (mt : Fin TM → Digest)
    (H : Point → Digest × C) (key : Key) : JointResponse.Oracle (First).participant (Second).participant :=
  Joint.Pair.oracleEquiv (First).participant (Second).participant
    (tupleOracle binary prime P R cfg earlier codec dflt body dec mt H key)

theorem cutOracle_off (dec : RoleDecoders codec) (mt : Fin TM → Digest) (point : Point)
    (H H' : Point → Digest × C) (h : Bcs.TotalOracle.AgreeOff point H H') :
    cutOracle binary prime P R cfg earlier codec dflt body dec mt H point.context =
      cutOracle binary prime P R cfg earlier codec dflt body dec mt H' point.context := by
  apply congrArg (Joint.Pair.oracleEquiv (First).participant (Second).participant)
  unfold tupleOracle
  have hc := (setup binary prime P R cfg earlier dflt body).ctxAt_off mt H H' point h
  exact congrArg (fun ctx : Key × List (Enc × Digest) =>
    (RuntimeVerifier.Family binary prime P R cfg).extractedOracle dec (cfg.root ctx.1) ctx.2) hc.symm

omit [DecidableEq Key] in
/-- Acceptance uses the actual tuple claim reconstructed from the shared
opening answer and this output's body. -/
theorem compiled_accepts_tree (mt : Fin TM → Digest) (H : Point → Digest × C) (decoded : Decoded)
    (hd : RuntimeAdaptiveVerifier.decode binary prime P R cfg earlier hashPublic decodePublic draw
      (originalOutput body mt H) H = some decoded)
    (hc : RuntimeAdaptiveVerifier.Checks binary prime P R cfg earlier codec
      (merkleOracle binary prime P R cfg earlier codec dflt body mt H) (originalOutput body mt H) H decoded) :
    ((RuntimeVerifier.Family binary prime P R cfg).compiler cfg.openingPositive).Accepts
      (codec.withOracle (merkleOracle binary prime P R cfg earlier codec dflt body mt H))
      ((Joint.Pair.statementEquiv _ _).symm decoded.statement.statement)
      (cfg.root ((setup binary prime P R cfg earlier dflt body).keyOut
        ((setup binary prime P R cfg earlier dflt body).proof mt H)))
      ((Joint.Pair.coinEquiv _ _).symm decoded.coin)
      ((Joint.Pair.responseEquiv _ _).symm (RuntimeVerifier.responses binary prime P R cfg (originalOutput body mt H).proof))
      decoded.query (claimOf binary prime P R cfg ((setup binary prime P R cfg earlier dflt body).proof mt H)) := by
  have hclaim : claimOf binary prime P R cfg ((setup binary prime P R cfg earlier dflt body).proof mt H) = decoded.claim := by
    rw [proof_eq]
    exact claimOf_replay binary prime P R cfg earlier hashPublic decodePublic draw (originalOutput body mt H) H decoded hd
  rw [proof_context,hclaim]
  exact hc.2.2.1

omit [DecidableEq Key] in
/-- Both fields use this one Merkle acceptance event, with exactly 2*n
checker queries and one final-seal continuation. -/
theorem merkle_accepts (mt : Fin TM → Digest) (H : Point → Digest × C) (decoded : Decoded)
    (hd : RuntimeAdaptiveVerifier.decode binary prime P R cfg earlier hashPublic decodePublic draw
      (originalOutput body mt H) H = some decoded)
    (hc : RuntimeAdaptiveVerifier.Checks binary prime P R cfg earlier codec
      (merkleOracle binary prime P R cfg earlier codec dflt body mt H) (originalOutput body mt H) H decoded) :
    (setup binary prime P R cfg earlier dflt body).MerkleAccepts codec
      (check binary prime P R cfg codec) cfg.root (claimOf binary prime P R cfg) mt H :=
  (compiled_accepts_tree binary prime P R cfg earlier hashPublic decodePublic draw codec dflt body mt H decoded hd hc).2.1

/-- The shared explanation authenticates exactly the cut oracle used by
adaptive selection and the global Fiat--Shamir charges. -/
theorem verify_of_explains (dec : RoleDecoders codec) (mt : Fin TM → Digest) (H : Point → Digest × C)
    (decoded : Decoded)
    (hd : RuntimeAdaptiveVerifier.decode binary prime P R cfg earlier hashPublic decodePublic draw
      (originalOutput body mt H) H = some decoded)
    (hc : RuntimeAdaptiveVerifier.Checks binary prime P R cfg earlier codec
      (merkleOracle binary prime P R cfg earlier codec dflt body mt H) (originalOutput body mt H) H decoded)
    (he : (setup binary prime P R cfg earlier dflt body).Explains dec cfg.root (claimOf binary prime P R cfg) mt H) :
    JointResponse.Verify (First).participant (Second).participant decoded.statement.statement
      (cutOracle binary prime P R cfg earlier codec dflt body dec mt H
        ((E (originalOutput body mt H).request).context (originalOutput body mt H).proof))
      decoded.coin (RuntimeVerifier.responses binary prime P R cfg (originalOutput body mt H).proof) decoded.query := by
  let K := setup binary prime P R cfg earlier dflt body
  have ha := compiled_accepts_tree binary prime P R cfg earlier hashPublic decodePublic draw codec dflt body mt H decoded hd hc
  obtain ⟨extracted,hext,hagree,-⟩ := he
  have hv := (RuntimeVerifier.Family binary prime P R cfg).verify_of_extraction cfg.openingPositive dec
    (codec.withOracle (K.merkleOracle (check binary prime P R cfg codec) mt H))
    ((Joint.Pair.statementEquiv _ _).symm decoded.statement.statement) (cfg.root (K.keyOut (K.proof mt H)))
    ((K.atOracle H).cutTrace mt Bcs.TotalOracleCommit.Setup.emptyTape (K.keyOut (K.proof mt H)))
    ((Joint.Pair.coinEquiv _ _).symm decoded.coin)
    ((Joint.Pair.responseEquiv _ _).symm (RuntimeVerifier.responses binary prime P R cfg (originalOutput body mt H).proof))
    decoded.query (claimOf binary prime P R cfg (K.proof mt H)) extracted hext hagree ha
  have result : JointResponse.Verify (First).participant (Second).participant decoded.statement.statement
      (cutOracle binary prime P R cfg earlier codec dflt body dec mt H (K.keyOut (K.proof mt H)))
      decoded.coin (RuntimeVerifier.responses binary prime P R cfg (originalOutput body mt H).proof) decoded.query :=
    (Joint.Pair.verify_iff (First).participant (Second).participant _ _ _ _ _).mp hv
  rw [proof_context] at result
  exact result

end Program
end LfzkV2.Current.RuntimeAdaptiveMerkle
