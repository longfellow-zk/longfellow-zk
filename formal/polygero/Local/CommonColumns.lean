import polygero.Local.JointSystems
import polygero.FiatShamir.ResponseMass

/-! Response uniqueness can be established using a common subset of the two
fields' good columns. Outside the rank event, extending this subset to all
good columns preserves the assigned system. This lets joint counting reuse
the existing complete-response uniqueness theorem unchanged. -/
noncomputable section
namespace RecursivePolygero.ProfileAnalysis
open Polynomial Finset Codes LigeroFamily Local Local.Polygero NonrecursiveFS
open PolynomialClosure Shift
open LigeroFamily.PolynomialDirect (primaryCode)
open scoped Classical

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

theorem common_columns_data (I : Instance F) (p : ProfileParameters I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (c : I.layer.Coin)
    (hb : ¬ rankBad I W c) (a : I.layer.Payload)
    (d : systems I.domain I.primary_le W) (T : Finset (Fin I.n))
    (hT : T ∈ ReducedSystems.associatedSets (code I) (words I W) W.proximityMask d.1)
    (hsub : T ⊆ good I σ W c a) :
    (c.2,a.primary) ∈ ConsistencyClosure.solutions (jointMap (code I) (words I W))
      W.proximityMask d.1 ∧
      fixedConsistencyCodimension (code I) (words I W) d.1 I.s +
        ((good I σ W c a) \ d.1).card ≤ I.s := by
  have hv : (c.2,a.primary) ∈ ConsistencyClosure.solutions
      (jointMap (code I) (words I W)) W.proximityMask (good I σ W c a) := by
    intro j hj
    exact sub_eq_iff_eq_add.mpr (((mem_filter.mp hj).2).1.trans (add_comm _ _))
  have hsize : I.r+I.w+I.s+I.s+1 ≤ (good I σ W c a).card :=
    (mem_filter.mp hT).2.1.trans (card_le_card hsub)
  have hlow := ReducedSystems.low_defect_of_not_bad (code I) (words I W)
    W.proximityMask c.2 hb (good I σ W c a) hsize a.primary hv
  have hfull := ReducedSystems.Joint.associated_superset (code I) (words I W)
    W.proximityMask p.positive_degree d.1 T (good I σ W c a) hT hsub hlow ⟨_,hv⟩
  have hdata := ReducedSystems.Joint.associated_data (code I) (words I W)
    W.proximityMask d.1 (good I σ W c a) hfull (c.2,a.primary) hv
  exact ⟨hdata.1,hdata.2.le.trans hlow⟩

/-- Both transmitted polynomials are unique, even when the assignment was
made from the joint good-column set rather than this field's full good set. -/
theorem response_eq_of_common_columns (I : Instance F) (p : ProfileParameters I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (c : I.layer.Coin)
    (hb : ¬ rankBad I W c) (d : systems I.domain I.primary_le W)
    (a b : I.layer.Payload) (T U : Finset (Fin I.n))
    (hT : T ∈ ReducedSystems.associatedSets (code I) (words I W) W.proximityMask d.1)
    (hU : U ∈ ReducedSystems.associatedSets (code I) (words I W) W.proximityMask d.1)
    (hTa : T ⊆ good I σ W c a) (hUb : U ⊆ good I σ W c b)
    (hlargeT : p.largeSize ≤ T.card) (hlargeU : p.largeSize ≤ U.card) : a = b := by
  have ha := common_columns_data I p σ W c hb a d T hT hTa
  have hb' := common_columns_data I p σ W c hb b d U hU hUb
  apply response_eq_of_assigned_system I p σ W d c a b ha.1 hb'.1
  · intro payload hp
    rcases mem_insert.mp hp with he | he
    · subst payload
      exact hlargeT.trans (card_le_card hTa)
    · rw [mem_singleton.mp he]
      exact hlargeU.trans (card_le_card hUb)
  · intro payload hp
    rcases mem_insert.mp hp with he | he
    · subst payload
      exact ha.2
    · rw [mem_singleton.mp he]
      exact hb'.2

end RecursivePolygero.ProfileAnalysis
