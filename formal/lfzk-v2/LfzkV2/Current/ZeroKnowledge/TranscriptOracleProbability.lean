import LfzkV2.Current.ByteOracleProbability
import LfzkV2.Current.ZeroKnowledge.SHAOracleProbability
import LfzkV2.Current.ZeroKnowledge.OracleWindow

/-! Exact probability transport from canonical transcript queries to raw
byte queries. Canonical answers and malformed-input answers are disjoint
coordinates of one ideal oracle. Unused typed coordinates disappear with
their exact uniform multiplicity, and complementary raw answers are then
averaged. Honest and simulated private tapes may have different types.

The window is any finite marginal containing every canonical encoding.
It may also contain the entire adaptive observer's possible raw queries;
neither the raw byte-string type nor a single observed trace is assumed
finite. The bound and both distributions use the same sampled raw table. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.TranscriptOracleProbability
open LigeroFamily Finset
open scoped Classical
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {Point Raw Answer R S View : Type} {valid : Point → Prop}
variable (codec : ByteOracleTransport.Codec Point Raw valid)

theorem oracle_canonical (outside : Raw → Answer) (H : Point → Answer) :
    codec.oracle outside H = codec.canonicalOracle outside (fun point => H point.val) := rfl

section Finite
variable [Fintype Point] [Fintype Raw] [Fintype Answer] [Fintype R] [Fintype S]
variable [DecidableEq Point] [DecidableEq Raw]
variable [Nonempty R] [Nonempty S]

private def coinsEquiv (Coin : Type) : (Coin × (Raw → Answer)) ≃
    (({raw // codec.decode raw = none} → Answer) × (Coin × ({point // valid point} → Answer))) :=
  (codec.oracleProductEquiv Coin).trans (Equiv.prodComm _ _)

omit [Fintype Raw] [DecidableEq Raw] in
private theorem full_marginal (dflt : Answer) (outside : Raw → Answer)
    (view : R → (Raw → Answer) → View) (event : View → Prop) :
    probOf (fun coin : R × (Point → Answer) => view coin.1 (codec.oracle outside coin.2)) event =
      probOf (fun coin : R × ({point // valid point} → Answer) =>
        view coin.1 (codec.canonicalOracle outside coin.2)) event := by
  have marginal := (ByteOracleTransport.subtypeCodec Point valid).canonical_joint_marginal dflt
    (fun coin H => event (view coin (codec.canonicalOracle outside H)))
  simp only [probOf,oracle_canonical,ByteOracleTransport.subtypeCodec,← Nat.card_eq_fintype_card] at marginal ⊢
  convert marginal using 1 <;> congr 3 <;> ext coin <;> simp

/-- A full typed-oracle bound, uniform in the complementary raw answers,
has exactly the same error for a uniform complete finite raw oracle. The
only premise is the statistical bound being transported. -/
theorem finite_statClose_full (dflt : Answer) {epsilon : ℚ} (nonnegative : 0 ≤ epsilon)
    (real : R → (Raw → Answer) → View) (simulate : S → (Raw → Answer) → View)
    (typed : ∀ outside : Raw → Answer, StatClose epsilon
      (fun coin : R × (Point → Answer) => real coin.1 (codec.oracle outside coin.2))
      (fun coin : S × (Point → Answer) => simulate coin.1 (codec.oracle outside coin.2))) :
    StatClose epsilon (fun coin : R × (Raw → Answer) => real coin.1 coin.2)
      (fun coin : S × (Raw → Answer) => simulate coin.1 coin.2) := by
  have each (outside : Raw → Answer) : StatClose epsilon
      (fun coin : R × ({point // valid point} → Answer) => real coin.1 (codec.canonicalOracle outside coin.2))
      (fun coin : S × ({point // valid point} → Answer) => simulate coin.1 (codec.canonicalOracle outside coin.2)) := by
    intro event
    rw [← full_marginal codec dflt outside real event,← full_marginal codec dflt outside simulate event]
    exact typed outside event
  have mixed := statClose_mix nonnegative
    (fun outside (coin : R × ({point // valid point} → Answer)) =>
      real coin.1 (codec.canonicalOracle (codec.outsideOracle dflt outside) coin.2))
    (fun outside (coin : S × ({point // valid point} → Answer)) =>
      simulate coin.1 (codec.canonicalOracle (codec.outsideOracle dflt outside) coin.2))
    (fun outside => each (codec.outsideOracle dflt outside))
  apply statClose_reindex (coinsEquiv (Answer := Answer) codec R) (coinsEquiv (Answer := Answer) codec S) ?_ ?_ mixed
  · intro coin
    change real coin.1 coin.2 = real coin.1
      (codec.canonicalOracle (codec.outsideOracle dflt (codec.oracleEquiv coin.2).2) (codec.oracleEquiv coin.2).1)
    rw [← codec.oracleEquiv_symm dflt,Equiv.symm_apply_apply]
  · intro coin
    change simulate coin.1 coin.2 = simulate coin.1
      (codec.canonicalOracle (codec.outsideOracle dflt (codec.oracleEquiv coin.2).2) (codec.oracleEquiv coin.2).1)
    rw [← codec.oracleEquiv_symm dflt,Equiv.symm_apply_apply]

end Finite

section Window
variable [Fintype Point] [Fintype Answer] [Fintype R] [Fintype S] [Nonempty R] [Nonempty S]
variable [DecidableEq Point] [DecidableEq Raw]
variable (window : Finset Raw) (covers : ∀ point : {point // valid point}, codec.encode point ∈ window)

def windowCodec : ByteOracleTransport.Codec Point {raw // raw ∈ window} valid where
  encode point := ⟨codec.encode point,covers point⟩
  decode raw := codec.decode raw.val
  decode_encode := codec.decode_encode
  encode_decode raw point decoded := Subtype.ext (codec.encode_decode raw.val point decoded)

omit [Fintype Point] [Fintype Answer] [DecidableEq Point] in
theorem extend_oracle (outside : {raw // raw ∈ window} → Answer) (fallback : Raw → Answer) (H : Point → Answer) :
    OracleWindow.extend window ((windowCodec codec window covers).oracle outside H) fallback =
      codec.oracle (OracleWindow.extend window outside fallback) H := by
  funext raw
  by_cases inside : raw ∈ window
  · simp only [OracleWindow.extend,dif_pos inside,ByteOracleTransport.Codec.oracle,windowCodec]
  · have malformed : codec.decode raw = none := by
      cases decoded : codec.decode raw with
      | none => rfl
      | some point =>
          apply False.elim
          apply inside
          rw [← codec.encode_decode raw point decoded]
          exact covers point
    simp only [OracleWindow.extend,dif_neg inside,ByteOracleTransport.Codec.oracle,malformed]

include covers in
/-- The entire raw ideal-oracle marginal is sampled once on each side.
The complementary malformed-input coordinates are shared within each
experiment, including before and after a programmed canonical answer. -/
theorem window_statClose_full (dflt : Answer) (fallback : Raw → Answer)
    {epsilon : ℚ} (nonnegative : 0 ≤ epsilon)
    (real : R → (Raw → Answer) → View) (simulate : S → (Raw → Answer) → View)
    (typed : ∀ outside : Raw → Answer, StatClose epsilon
      (fun coin : R × (Point → Answer) => real coin.1 (codec.oracle outside coin.2))
      (fun coin : S × (Point → Answer) => simulate coin.1 (codec.oracle outside coin.2))) :
    StatClose epsilon
      (fun coin : R × ({raw // raw ∈ window} → Answer) => real coin.1 (OracleWindow.extend window coin.2 fallback))
      (fun coin : S × ({raw // raw ∈ window} → Answer) => simulate coin.1 (OracleWindow.extend window coin.2 fallback)) := by
  apply finite_statClose_full (windowCodec codec window covers) dflt nonnegative
    (fun coin H => real coin (OracleWindow.extend window H fallback))
    (fun coin H => simulate coin (OracleWindow.extend window H fallback))
  intro outside
  simpa only [extend_oracle codec window covers] using typed (OracleWindow.extend window outside fallback)

end Window
end LfzkV2.Current.ZeroKnowledge.TranscriptOracleProbability
