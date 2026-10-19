import polygero.Local.Recovery

/-! The concrete large-response theorem with its geometric assignment retained.
The frozen `Recovery.large_response` declaration remains unchanged. -/

namespace RecursivePolygero.ProfileAnalysis
open Polynomial Finset Codes LigeroFamily Local Local.Polygero Counting
open LigeroFamily.PolynomialDirect (primaryCode)
attribute [local instance] Classical.propDecidable
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Retain the defining associated-set witness as well as its capacity.
This lets a union of responses be charged once to the same system. -/
theorem assign_associated (I : Instance F) (W : I.layer.Oracle)
    (G : Finset (Fin I.n)) (hsize : I.r + I.w + I.s + I.s + 1 ≤ G.card)
    (hlow : fixedConsistencyCodimension (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) G I.s ≤ I.s)
    (coin : I.layer.Coin) (payload : I.layer.Payload)
    (hv : (coin.2, payload.primary) ∈ ConsistencyClosure.solutions
      (PolynomialClosure.jointMap (primaryCode I.domain I.primary_le) (oracleWords W.ordinary))
      W.proximityMask G) :
    ∃ d : systems I.domain I.primary_le W,
      (coin.2, payload.primary) ∈ ConsistencyClosure.solutions
        (PolynomialClosure.jointMap (primaryCode I.domain I.primary_le) (oracleWords W.ordinary))
        W.proximityMask d.1 ∧
      (G \ d.1).card ≤ I.s ∧
      G ∈ ReducedSystems.associatedSets (primaryCode I.domain I.primary_le)
        (oracleWords W.ordinary) W.proximityMask d.1 := by
  let C := primaryCode I.domain I.primary_le
  let rows := oracleWords W.ordinary
  let core := PolynomialClosure.canonicalCoreSet C rows G
  let D := PolynomialClosure.closure C rows W.proximityMask core
  have hne := Set.nonempty_of_mem hv
  have hd := ReducedSystems.canonical_mem_family C rows W.proximityMask G hsize hlow hne
  change fixedConsistencyCodimension C rows G I.s ≤ I.s at hlow
  obtain ⟨hc, hsub, hdrop⟩ := PolynomialClosure.canonical_core C rows G hlow (by omega)
  have hi := ConsistencyClosure.inter_closure_canonicalSubset
    (PolynomialClosure.jointMap C rows) W.proximityMask G hne
  have hdiff : G \ D = G \ core := by
    change G ∩ D = core at hi
    rw [← hi]
    exact (sdiff_inter_self_left G D).symm
  refine ⟨⟨D, hd⟩, ?_, ?_, ?_⟩
  · rw [ConsistencyClosure.solutions_closure]
    exact ConsistencyClosure.solutions_antitone _ _ hsub hv
  · rw [hdiff]
    change fixedConsistencyCodimension C rows core I.s + (G \ core).card =
      fixedConsistencyCodimension C rows G I.s at hdrop
    omega
  · exact mem_filter.mpr ⟨mem_univ _, hsize, hlow, hne, rfl⟩

/-- The geometric assignment retained for response-incidence arguments.
In particular, the primary response solves the assigned system, and at
most `s` actual good columns are omitted by that system. -/
structure ResponseAssignment (I : Instance F) (σ : I.layer.Statement)
    (W : I.layer.Oracle) (coin : I.layer.Coin) (payload : I.layer.Payload)
    (d : systems I.domain I.primary_le W) : Prop where
  primary : (coin.2, payload.primary) ∈ ConsistencyClosure.solutions
    (PolynomialClosure.jointMap (primaryCode I.domain I.primary_le) (oracleWords W.ordinary))
    W.proximityMask d.1
  omitted : ((goodColumns I.domain (by have := I.primary_le; omega) I.primary_le
    I.layout σ W coin payload) \ d.1).card ≤ I.s
  associated : (goodColumns I.domain (by have := I.primary_le; omega) I.primary_le
    I.layout σ W coin payload) ∈ ReducedSystems.associatedSets
      (primaryCode I.domain I.primary_le) (oracleWords W.ordinary) W.proximityMask d.1
  capacity : (goodColumns I.domain (by have := I.primary_le; omega) I.primary_le
    I.layout σ W coin payload).card ≤ ReducedSystems.capacity
      (primaryCode I.domain I.primary_le) (oracleWords W.ordinary) W.proximityMask d.1

/-- The large-response alternative, retaining its actual system assignment. -/
theorem large_response_assigned (I : Instance F)
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
      ResponseAssignment I σ W coin payload d ∧
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
  obtain ⟨d,hpD,herr,hassoc⟩ := assign_associated I W G hc hlow coin payload hp
  let D := d.1
  refine ⟨d,?_,?_⟩
  · exact ⟨hpD, herr, hassoc, Finset.le_sup (f := Finset.card) hassoc⟩
  by_cases hsystemException : coin ∈ systemExceptions hk I.layout σ d
  · exact Or.inl hsystemException
  right
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
