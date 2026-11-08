import LfzkV2.Current.ZeroKnowledge.OracleCanonicalAncestors
import LfzkV2.Current.ZeroKnowledge.OracleBytes
import LfzkV2.Current.ZeroKnowledge.OracleRuntime

/-! Oracle normalization preserves all canonical complete-proof replay.
The public frontend simulator's serialized body is fixed by its private
coins; oracle answers affect derived claims and reader state only. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.OracleNormalization
open CanonicalPrefix QueryRuntime
open scoped Classical
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

section Replay
variable {g : Geometry} {fields : Fields} {Advice C : Type}
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (shape : WireBlocks.Shape g fields) (setup : FingerprintPrefix.Setup) (publicCount : ℕ)
variable (binaryRequest : (Fin publicCount → Bool) → Fin shape.binaryPublic → fields .binary)
variable (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape publicCount)
variable (request : CanonicalRequest.Request shape publicCount)
variable (bodyFits : ProofBodyBounds.bodyBound repr g ≤ CanonicalPrefix.maxLength)
local notation "Point" => QueryRuntime.Runtime.Point repr shape setup publicCount
local notation "Output" => CanonicalRequest.Output (g := g) (fields := fields) (Advice := Advice)
local notation "e" => CanonicalRequest.encoding repr shape setup publicCount binaryRequest metadata request

def Agree (H H' : Point → Digest × C) : Prop :=
  ∀ point, QueryRuntime.Runtime.Canonical repr shape setup publicCount point → H point = H' point

include bodyFits in
theorem replay_eq (initial : Digest) (proof : Output) (H H' : Point → Digest × C)
    (agree : Agree repr shape setup publicCount H H') (n : ℕ) (bound : n ≤ g.roles.length) :
    ((e).chain initial).replay proof H n = ((e).chain initial).replay proof H' n := by
  apply TranscriptV2.Chain.replay_congr_prefix
  intro k before
  exact agree _ (OracleBytes.replay_canonical repr shape setup publicCount binaryRequest metadata bodyFits request
    initial proof H k (by omega))

include bodyFits in
theorem point_eq (initial : Digest) (proof : Output) (H H' : Point → Digest × C)
    (agree : Agree repr shape setup publicCount H H') (n : ℕ) (bound : n ≤ g.roles.length) :
    ((e).chain initial).point proof H n = ((e).chain initial).point proof H' n :=
  congrArg ((e).chain initial).input
    (replay_eq repr shape setup publicCount binaryRequest metadata request bodyFits initial proof H H' agree n bound)

include bodyFits in
theorem answer_eq (initial : Digest) (proof : Output) (H H' : Point → Digest × C)
    (agree : Agree repr shape setup publicCount H H') (n : ℕ) (bound : n ≤ g.roles.length) :
    H (((e).chain initial).point proof H n) = H' (((e).chain initial).point proof H' n) :=
  (agree _ (OracleBytes.replay_canonical repr shape setup publicCount binaryRequest metadata bodyFits request
    initial proof H n bound)).trans
      (congrArg H' (point_eq repr shape setup publicCount binaryRequest metadata request bodyFits initial proof H H' agree n bound))

theorem priorAnswers_eq (point : Point) (canonical : QueryRuntime.Runtime.Canonical repr shape setup publicCount point)
    (H H' : Point → Digest × C) (agree : Agree repr shape setup publicCount H H') :
    point.priorAnswers H = point.priorAnswers H' := by
  funext i
  exact congrArg Prod.snd (agree _
    (OracleCanonicalAncestors.canonical_priorPoints repr shape setup publicCount point canonical i))

theorem update_agree (H H' : Point → Digest × C) (agree : Agree repr shape setup publicCount H H')
    (point : Point) (answer : Digest × C) :
    Agree repr shape setup publicCount (Function.update H point answer) (Function.update H' point answer) := by
  intro query canonical
  by_cases same : query = point
  · subst query
    simp only [Function.update_self]
  · simp only [Function.update_of_ne same]
    exact agree query canonical

theorem normalize_agree (fits : g.roles.length < 2^64) (H fallback : Point → Digest × C)
    (outside : Bytes → Digest × C) :
    Agree repr shape setup publicCount H
      ((QueryRuntime.Runtime.codec repr shape setup publicCount fits).restrict
        ((QueryRuntime.Runtime.codec repr shape setup publicCount fits).oracle outside H) fallback) := by
  intro point canonical
  simp only [ByteOracleTransport.Codec.restrict,dif_pos canonical,ByteOracleTransport.Codec.oracle,
    (QueryRuntime.Runtime.codec repr shape setup publicCount fits).decode_encode ⟨point,canonical⟩]

include bodyFits in
theorem finalize_eq (initial : Digest) (body : Current.Body g fields Advice (OpeningBody.Authentication g))
    (H H' : Point → Digest × C) (agree : Agree repr shape setup publicCount H H') :
    OracleRuntime.finalize repr shape setup publicCount binaryRequest metadata request initial body H =
      OracleRuntime.finalize repr shape setup publicCount binaryRequest metadata request initial body H' := by
  have answers := answer_eq repr shape setup publicCount binaryRequest metadata request bodyFits initial
    (⟨body,fun _ => 0⟩ : Output) H H' agree g.roles.length (le_refl _)
  exact congrArg (fun answer : Digest × C => (⟨body,answer.1⟩ : Output)) answers

include bodyFits in
theorem program_eq (initial : Digest) (body : Current.Body g fields Advice (OpeningBody.Authentication g))
    (H H' : Point → Digest × C) (agree : Agree repr shape setup publicCount H H') (answer : Digest × C) :
    (OracleRuntime.programAndFinalize repr shape setup publicCount binaryRequest metadata request initial body H answer).1 =
      (OracleRuntime.programAndFinalize repr shape setup publicCount binaryRequest metadata request initial body H' answer).1 ∧
    Agree repr shape setup publicCount
      (OracleRuntime.programAndFinalize repr shape setup publicCount binaryRequest metadata request initial body H answer).2
      (OracleRuntime.programAndFinalize repr shape setup publicCount binaryRequest metadata request initial body H' answer).2 := by
  let old := ((e).chain initial).point (⟨body,fun _ => 0⟩ : Output) H g.openingIndex.val
  let new := ((e).chain initial).point (⟨body,fun _ => 0⟩ : Output) H' g.openingIndex.val
  have points : old = new := point_eq repr shape setup publicCount binaryRequest metadata request bodyFits initial
    (⟨body,fun _ => 0⟩ : Output) H H' agree _ (Nat.le_of_lt g.openingIndex.isLt)
  have updated : Agree repr shape setup publicCount (Function.update H old answer) (Function.update H' old answer) :=
    update_agree repr shape setup publicCount H H' agree old answer
  have tables : Function.update H' old answer = Function.update H' new answer :=
    congrArg (fun point => Function.update H' point answer) points
  constructor
  · change OracleRuntime.finalize repr shape setup publicCount binaryRequest metadata request initial body (Function.update H old answer) =
      OracleRuntime.finalize repr shape setup publicCount binaryRequest metadata request initial body (Function.update H' new answer)
    exact (finalize_eq repr shape setup publicCount binaryRequest metadata request bodyFits initial body _ _ updated).trans
      (congrArg (fun oracle => OracleRuntime.finalize repr shape setup publicCount binaryRequest metadata request initial body oracle) tables)
  · change Agree repr shape setup publicCount (Function.update H old answer) (Function.update H' new answer)
    exact (congrArg (Agree repr shape setup publicCount (Function.update H old answer)) tables).mp updated

end Replay

end LfzkV2.Current.ZeroKnowledge.OracleNormalization
