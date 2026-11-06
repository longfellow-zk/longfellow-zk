import LfzkV2.Current.QueryRuntime
import LfzkV2.Current.ByteOracleProbability

/-! The finite-window byte-oracle lift for the actual runtime query codec.
The statement keeps any independent finite tape inside the experiment, so
it applies to the joint Merkle/transcript bound. Outside-image bytes are
conditioned auxiliary answers; they are never counted as typed queries. -/
noncomputable section
namespace LfzkV2.Current.QueryRuntimeProbability
open Finset Merkle.RandomOracle
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice : Type}
variable [∀ side, Fintype (fields side)] [Fintype Advice]
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (shape : WireBlocks.Shape g fields) (setup : FingerprintPrefix.Setup) (publicCount : ℕ)
variable (fits : g.roles.length < 2^64)
variable {QL DL A Out M : Type} [Fintype DL] [Fintype A] [Fintype M] [Nonempty M]

/-- This finite set contains every possible raw call of the bounded
adversarial program and every canonical verifier input. `Bytes` itself
remains an infinite type. Extra coordinates are averaged, not charged. -/
def window {left right : ℕ} (body : TwoOracleTree QL DL Bytes A Out left right) : Finset Bytes :=
  (QueryRuntime.Runtime.codec repr shape setup publicCount fits).window body

/-- Specialization of the uniform marginal lift to the checked physical
query parser. The typed security bound is uniform in the fixed auxiliary
byte oracle and may average over the independent Merkle tape. -/
theorem joint_ratio_le {left right : ℕ}
    (body : TwoOracleTree QL DL Bytes A Out left right) (dflt : A)
    (fallback : Bytes → A) (event : M → (Bytes → A) → Prop) (bound : ℚ)
    (htyped : ∀ outside : Bytes → A,
      ((univ.filter fun pair : M × (QueryRuntime.Runtime.Point repr shape setup publicCount → A) =>
        event pair.1 ((QueryRuntime.Runtime.codec repr shape setup publicCount fits).oracle outside pair.2)).card : ℚ) /
          Fintype.card (M × (QueryRuntime.Runtime.Point repr shape setup publicCount → A)) ≤ bound) :
    ((univ.filter fun pair : M × ({raw // raw ∈ window repr shape setup publicCount fits body} → A) =>
      event pair.1 (ByteOracleTransport.Codec.extendWindow
        (window repr shape setup publicCount fits body) pair.2 fallback)).card : ℚ) /
          Fintype.card (M × ({raw // raw ∈ window repr shape setup publicCount fits body} → A)) ≤ bound :=
  (QueryRuntime.Runtime.codec repr shape setup publicCount fits).window_joint_ratio_le_full
    body dflt fallback event bound htyped

end LfzkV2.Current.QueryRuntimeProbability
