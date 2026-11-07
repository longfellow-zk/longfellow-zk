import LfzkV2.Current.ZeroKnowledge.SHAOracle
import LfzkV2.Current.ByteOracleProbability

/-! Common finite-oracle table algebra and one-sided probability bounds.
Soundness and statistical privacy share these coordinate maps without
importing each other's composition proofs. Unused coordinates of a larger
table cancel exactly. The complement is a whole function, never an
adaptively observed trace. -/
noncomputable section
namespace LfzkV2.Current.SHAProbability
open Finset ZeroKnowledge
open scoped Classical

/-- Uniform counting is independent of the chosen complete enumeration.
Keep this transport explicit when joining separately constructed marginals. -/
theorem changeFintype {X : Type} [new : Fintype X] {old : Fintype X}
    {event : X → Prop} {bound : ℚ}
    (law : (((@Finset.univ X old).filter event).card : ℚ) / @Fintype.card X old ≤ bound) :
    ((univ.filter event).card : ℚ) / Fintype.card X ≤ bound := by
  cases Subsingleton.elim old new
  exact law

section Tables
variable {Query Answer R : Type} (domain : Query → Prop)

/-- Split a whole oracle table into its domain and complement while retaining
independent experiment coins. Neither slice is an observed execution trace. -/
def coinsEquiv : (R × (Query → Answer)) ≃
    (({query // ¬domain query} → Answer) × (R × ({query // domain query} → Answer))) where
  toFun coin := (fun query => coin.2 query.val,coin.1,fun query => coin.2 query.val)
  invFun coin := (coin.2.1,(SHAOracle.split domain).symm (coin.2.2,coin.1))
  left_inv coin := by
    dsimp only
    apply Prod.ext
    · rfl
    · exact (SHAOracle.split domain).symm_apply_apply coin.2
  right_inv coin := by
    dsimp only
    apply Prod.ext
    · funext query
      simp only [SHAOracle.split,Equiv.coe_fn_symm_mk,dif_neg query.property]
    · apply Prod.ext
      · rfl
      · funext query
        simp only [SHAOracle.split,Equiv.coe_fn_symm_mk,dif_pos query.property]

end Tables

section WindowTables
variable {Raw Answer : Type} [DecidableEq Raw]
variable (small large : Finset Raw) (contains : small ⊆ large)

/-- Identify a smaller input window with its coordinates in a larger table. -/
def inclusionEquiv : {raw // raw ∈ small} ≃ {raw : {raw // raw ∈ large} // raw.val ∈ small} where
  toFun raw := ⟨⟨raw.val,contains raw.property⟩,raw.property⟩
  invFun raw := ⟨raw.val.val,raw.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Preserve the sampled complement and fill the unused inside coordinates.
This table selects a conditioning slice; it is not a programmed oracle handed
to the adversary. -/
def outsideTable (fallback : Raw → Answer)
    (outside : {raw : {raw // raw ∈ large} // raw.val ∉ small} → Answer) :
    {raw // raw ∈ large} → Answer :=
  (SHAOracle.split (fun raw : {raw // raw ∈ large} => raw.val ∈ small)).symm
    ((fun raw => fallback raw.val.val),outside)

/-- Splitting table coordinates and extending their finite marginal commute
pointwise, including on raw inputs outside the larger window. -/
theorem extend_split (fallback : Raw → Answer)
    (outside : {raw : {raw // raw ∈ large} // raw.val ∉ small} → Answer)
    (inside : {raw : {raw // raw ∈ large} // raw.val ∈ small} → Answer) :
    OracleWindow.extend large
        ((SHAOracle.split (fun raw : {raw // raw ∈ large} => raw.val ∈ small)).symm (inside,outside)) fallback =
      OracleWindow.extend small
        (fun raw => inside (inclusionEquiv small large contains raw))
        (OracleWindow.extend large (outsideTable small large fallback outside) fallback) := by
  funext raw
  by_cases member : raw ∈ small
  · have inLarge := contains member
    simp only [OracleWindow.extend,dif_pos member,dif_pos inLarge,SHAOracle.split,
      Equiv.coe_fn_symm_mk,inclusionEquiv,Equiv.coe_fn_mk]
  · by_cases inLarge : raw ∈ large
    · simp only [OracleWindow.extend,dif_neg member,dif_pos inLarge,SHAOracle.split,
        Equiv.coe_fn_symm_mk,outsideTable]
    · simp only [OracleWindow.extend,dif_neg member,dif_neg inLarge]

end WindowTables

variable {Raw Answer M : Type} [DecidableEq Raw]
variable [Fintype Answer] [Nonempty Answer] [Fintype M] [Nonempty M]

theorem window_ratio_le (small large : Finset Raw) (contains : small ⊆ large)
    (fallback : Raw → Answer) (event : M → (Raw → Answer) → Prop) (bound : ℚ)
    (each : ∀ outside : Raw → Answer,
      ((univ.filter fun coin : M × ({raw // raw ∈ small} → Answer) =>
        event coin.1 (OracleWindow.extend small coin.2 outside)).card : ℚ) /
          Fintype.card (M × ({raw // raw ∈ small} → Answer)) ≤ bound) :
    ((univ.filter fun coin : M × ({raw // raw ∈ large} → Answer) =>
      event coin.1 (OracleWindow.extend large coin.2 fallback)).card : ℚ) /
        Fintype.card (M × ({raw // raw ∈ large} → Answer)) ≤ bound := by
  let predicate := fun raw : {raw // raw ∈ large} => raw.val ∈ small
  let change := (coinsEquiv (R := M) (Answer := Answer) predicate).trans
    (Equiv.prodComm _ _)
  rw [← ByteOracleTransport.ratio_equiv change.symm
    (fun coin : M × ({raw // raw ∈ large} → Answer) =>
      event coin.1 (OracleWindow.extend large coin.2 fallback))]
  apply ByteOracleTransport.product_ratio_le
  intro outside
  let inclusion := inclusionEquiv small large contains
  let e := Equiv.prodCongr (Equiv.refl M) (Equiv.arrowCongr inclusion (Equiv.refl Answer))
  have law := each (OracleWindow.extend large
    (outsideTable small large fallback outside) fallback)
  have transported := (ByteOracleTransport.ratio_equiv e.symm
    (fun coin : M × ({raw // raw ∈ small} → Answer) =>
      event coin.1 (OracleWindow.extend small coin.2
        (OracleWindow.extend large (outsideTable small large fallback outside) fallback)))).trans_le law
  change ((univ.filter fun coin : M × ({raw : {raw // raw ∈ large} // raw.val ∈ small} → Answer) =>
    event coin.1 (OracleWindow.extend large
      ((SHAOracle.split predicate).symm (coin.2,outside)) fallback)).card : ℚ) / _ ≤ bound
  dsimp only [predicate]
  have split (inside : {raw : {raw // raw ∈ large} // raw.val ∈ small} → Answer) :=
    extend_split small large contains fallback outside inside
  simp_rw [split]
  exact transported

end LfzkV2.Current.SHAProbability
