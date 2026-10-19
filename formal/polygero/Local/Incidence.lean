import polygero.Local.Probability
import polygero.Algebra.Counting.RandomTargetIncidence

/-! Summed system excess for a fixed, capacity-bounded family. -/

namespace RecursivePolygero.ProfileAnalysis

open Finset Codes LigeroFamily Local Local.Polygero Counting
open LigeroFamily.PolynomialDirect (primaryCode)
open scoped Classical

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

noncomputable def localIncidence (I : Instance F) (p : HahnSystemCertificate I)
    (sigma : I.layer.Statement) (W : I.layer.Oracle)
    (T : Finset (systems I.domain I.primary_le W))
    (D : (tupleCounts I).Index → Prop) (coin : I.layer.Coin) : ℚ :=
  SystemException.incidence T (systemCap I W)
    (fun _ : Unit => fun d => systemTarget I p.positive_degree W D d)
    (fun _ coin d => coin ∈ systemExceptions p.positive_degree I.layout sigma d)
    (fun coin => coin.2 ∈ ReducedSystems.badChallenges (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask) p.threshold () coin

theorem localEnvelope_le_localIncidence
    (I : Instance F) (p : HahnSystemCertificate I)
    (sigma : I.layer.Statement) (W : I.layer.Oracle)
    (T : Finset (systems I.domain I.primary_le W))
    (D : (tupleCounts I).Index → Prop) (coin : I.layer.Coin)
    (hcover : ∀ d, p.threshold < systemCap I W d →
      systemTarget I p.positive_degree W D d ∨
        coin ∈ systemExceptions p.positive_degree I.layout sigma d → d ∈ T) :
    localEnvelope I p.toProfileParameters sigma W p.threshold D coin ≤
      localIncidence I p sigma W T D coin :=
  SystemException.envelope_le_incidence T (systemCap I W)
    (fun _ : Unit => fun d => systemTarget I p.positive_degree W D d)
    (fun _ coin d => coin ∈ systemExceptions p.positive_degree I.layout sigma d)
    (fun coin => coin.2 ∈ ReducedSystems.badChallenges (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask) p.threshold () coin hcover

/-- Unlike `localEnvelope_mean_of_hahn`, this bounds a SUM over the chosen
systems' excesses. The family must be fixed before the target randomness
and contain at most `|F|` systems. It need not contain every system; the
caller must prove coverage when using this bound for extraction failure. -/
theorem localIncidence_mean_of_hahn {Z : Type} [Fintype Z] [Nonempty Z]
    (I : Instance F) (p : HahnSystemCertificate I)
    (sigma : Z → I.layer.Statement) (W : I.layer.Oracle)
    (T : Finset (systems I.domain I.primary_le W)) (hT : T.card ≤ Nat.card F)
    (rate : ℚ) (hr0 : 0 ≤ rate) (hr1 : rate ≤ 1)
    (D : Z → (tupleCounts I).Index → Prop)
    (hD : ∀ g, mean (fun z => indicator (D z g)) ≤ rate) :
    mean (fun z => mean (localIncidence I p (sigma z) W T (D z))) ≤
      p.error + (1 - p.error) * rate := by
  apply SystemException.random_target_incidence_mean_of_small_family T (systemCap I W)
    (fun z d => systemTarget I p.positive_degree W (D z) d)
    (fun z coin d => coin ∈ systemExceptions p.positive_degree I.layout (sigma z) d)
    (fun coin => coin.2 ∈ ReducedSystems.badChallenges (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask) p.threshold p.toProfileParameters.rankError rate
    (Nat.card F) Nat.card_pos p.threshold_lt_one.le hr0 hr1 p.field_error_lt_one.le
    (rank_bad_mean I p.toProfileParameters W)
  · intro d _
    by_cases hfull : Affine.consistent (primaryCode I.domain I.primary_le)
        (oracleWords W.ordinary) W.proximityMask d.1 = univ
    · simpa only [systemTarget, exists_prop_of_true hfull] using
        hD (systemLabel I p.positive_degree W d hfull)
    · have he (z : Z) : ¬ systemTarget I p.positive_degree W (D z) d := fun ⟨h, _⟩ => hfull h
      simpa only [indicator, if_neg (he _), mean_const] using hr0
  · intro z d _
    exact systemExceptions_mean I p.toProfileParameters (sigma z) W d
  · exact hT
  · exact systemCap_excess_of_hahn I p W

end RecursivePolygero.ProfileAnalysis
