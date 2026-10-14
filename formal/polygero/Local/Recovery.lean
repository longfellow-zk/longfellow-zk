import polygero.Local.Systems
import polygero.Algebra.PolynomialChallenges.SystemCapacity
import polygero.Local.Decoder

/-! The deterministic large-good-set alternative for the actual row decoder. -/
namespace RecursivePolygero.ProfileAnalysis
open Polynomial Finset Codes LigeroFamily Local Local.Polygero Counting
open LigeroFamily.PolynomialDirect (primaryCode)
attribute [local instance] Classical.propDecidable
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

noncomputable def systemLabel (I : Instance F) (hk : 1 ≤ I.r+I.w)
    (W : I.layer.Oracle) (d : systems I.domain I.primary_le W)
    (hfull : Affine.consistent (primaryCode I.domain I.primary_le) (oracleWords W.ordinary)
      W.proximityMask d.1 = univ) : (tupleCounts I).Index :=
  I.coreProjection (rows hk d hfull)

/-- Only fully consistent systems have a tuple that can be a target. -/
def systemTarget (I : Instance F) (hk : 1 ≤ I.r+I.w) (W : I.layer.Oracle)
    (D : (tupleCounts I).Index → Prop) (d : systems I.domain I.primary_le W) : Prop :=
  ∃ hfull, D (systemLabel I hk W d hfull)

/-- Outside the fixed rank event, a large response either encounters a system exception
for a fixed system or is recovered by the existing full-good-set decoder. -/
theorem large_response (I : Instance F)
    (hk : 1 ≤ I.r+I.w)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin)
    (payload : I.layer.Payload)
    (hglobal : globalCheck I.domain I.layout σ coin.1 payload)
    (hout : coin.2 ∉ ReducedSystems.badChallenges (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask)
    (hc : I.r+I.w+I.s+I.s+1 ≤
      (goodColumns I.domain (by have := I.primary_le; omega) I.primary_le I.layout σ W coin payload).card)
    (h2k : 2*(I.r+I.w)+I.s ≤
      (goodColumns I.domain (by have := I.primary_le; omega) I.primary_le I.layout σ W coin payload).card) :
    ∃ d : systems I.domain I.primary_le W,
      (goodColumns I.domain (by have := I.primary_le; omega) I.primary_le I.layout σ W coin payload).card ≤
        ReducedSystems.capacity (primaryCode I.domain I.primary_le)
          (oracleWords W.ordinary) W.proximityMask d.1 ∧
      (coin ∈ systemExceptions hk I.layout σ d ∨
        ∃ hfull, scanRecoverAt I σ W coin payload = some (systemLabel I hk W d hfull)) := by
  let G := goodColumns I.domain (by have := I.primary_le; omega) I.primary_le I.layout σ W coin payload
  have hp : (coin.2,payload.primary) ∈ ConsistencyClosure.solutions
      (PolynomialClosure.jointMap (primaryCode I.domain I.primary_le) (oracleWords W.ordinary))
      W.proximityMask G := by
    intro j hj
    have hj' := (mem_filter.mp hj).2.1
    change (payload.primary : F[X]).eval ((primaryCode I.domain I.primary_le).node j)-
      response (primaryCode I.domain I.primary_le) (oracleWords W.ordinary) coin.2 j = W.proximityMask j
    change (payload.primary : F[X]).eval ((primaryCode I.domain I.primary_le).node j) =
      response (primaryCode I.domain I.primary_le) (oracleWords W.ordinary) coin.2 j + W.proximityMask j at hj'
    exact sub_eq_iff_eq_add.mpr (hj'.trans (add_comm _ _))
  have hlow := ReducedSystems.low_defect_of_not_bad (primaryCode I.domain I.primary_le)
    (oracleWords W.ordinary) W.proximityMask coin.2 hout G hc payload.primary hp
  obtain ⟨D,hD,hpD,hdefect,hsize⟩ := ReducedSystems.assign (primaryCode I.domain I.primary_le)
    (oracleWords W.ordinary) W.proximityMask G hc hlow (coin.2,payload.primary) hp
  let d : systems I.domain I.primary_le W := ⟨D,hD⟩
  refine ⟨d,?_,?_⟩
  · exact hsize
  by_cases hsystemException : coin ∈ systemExceptions hk I.layout σ d
  · exact Or.inl hsystemException
  right
  have herr : (G \ D).card ≤ I.s := by omega
  obtain ⟨hfull,hsat,hrows⟩ := certify hk I.layout σ d coin payload hpD hsystemException hglobal h2k herr
  let f := rows hk d hfull
  let g := I.coreProjection f
  let S := rowAgreement (primaryCode I.domain I.primary_le) (I.coreWords W) g
  have hDS : D ⊆ S := by
    apply Subset.trans _ (I.agreement_subset_core W f)
    intro j hj
    simp only [rowAgreement,mem_filter,mem_univ,true_and]
    exact fun i => hrows i j hj
  have hsat' : I.layer.satisfies σ ((tupleCounts I).witness g) := by
    simpa only [tupleCounts,g,Instance.coreWitness_projection,Instance.layer] using hsat
  have hjoint : (G \ S).card ≤ I.s :=
    (card_le_card (show G \ S ⊆ G \ D from fun j hj =>
      mem_sdiff.mpr ⟨(mem_sdiff.mp hj).1, fun hd => (mem_sdiff.mp hj).2 (hDS hd)⟩)).trans herr
  have hnear : ∀ i, (rowErrors (primaryCode I.domain I.primary_le)
      (I.coreWords W i) G (g i)).card ≤ I.s := by
    intro i
    apply (card_le_card (show rowErrors (primaryCode I.domain I.primary_le)
      (I.coreWords W i) G (g i) ⊆ G \ S from ?_)).trans hjoint
    intro j hj
    simp only [rowErrors,puncturedErrors,mem_filter] at hj
    refine mem_sdiff.mpr ⟨hj.1,?_⟩
    intro hjS
    simp only [S,rowAgreement,mem_filter,mem_univ,true_and] at hjS
    exact hj.2 (hjS i)
  have hG : max (I.r+I.w+2*I.s+1) (2*(I.r+I.w)+I.s) ≤ G.card := by
    change I.r+I.w+I.s+I.s+1 ≤ G.card at hc
    change 2*(I.r+I.w)+I.s ≤ G.card at h2k
    omega
  have hdecode := recoverOnAt_eq_some I σ W G I.s
    (by omega) g hsat' hjoint hnear
  have hscan : scanRecoverAt I σ W coin payload = some g := by
    dsimp only [G] at hG hdecode
    simp only [scanRecoverAt,if_pos hglobal,if_pos hG]
    convert! hdecode using 1
  exact ⟨hfull,hscan⟩

end RecursivePolygero.ProfileAnalysis
