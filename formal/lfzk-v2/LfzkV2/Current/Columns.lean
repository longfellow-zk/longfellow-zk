import LfzkV2.Joint.Participant
import polygero.Local.CommonColumns
import polygero.FiatShamir.OutsideList

/-! Transport a participant's analysis sets to the shared column index. This
is only an index change: statements, coins and complete responses retain
their original field types. In particular, no response is projected away. -/
noncomputable section
namespace LfzkV2.Joint.Participant
open RecursivePolygero LigeroFamily Finset Local Local.Polygero ProfileAnalysis
open NonrecursiveFS PolynomialClosure Shift
open scoped Classical

variable {k s n t : ℕ} (P : Participant k s n t)

def columnSets : Finset (Fin P.backend.n) ≃ Finset (Fin n) :=
  Equiv.cast (congrArg (fun m => Finset (Fin m)) P.columns)

def goodColumns (σ : P.Statement) (W : P.Oracle) (c : P.Coin) (a : P.Response) :=
  P.columnSets (good P.backend σ W c a)

def associated (W : P.Oracle) (d : systems P.backend.domain P.backend.primary_le W) :
    Finset (Finset (Fin n)) :=
  univ.filter fun T => P.columnSets.symm T ∈ ReducedSystems.associatedSets
    (code P.backend) (words P.backend W) W.proximityMask d.1

@[simp] theorem columnSets_card (T : Finset (Fin P.backend.n)) :
    (P.columnSets T).card = T.card := by
  rcases P with ⟨F,hF,hfin,hdec,I,hk,hs,hn,ht,hlinear⟩
  cases hn
  rfl

@[simp] theorem columnSets_symm_card (T : Finset (Fin n)) :
    (P.columnSets.symm T).card = T.card := by
  rw [← P.columnSets_card (P.columnSets.symm T), Equiv.apply_symm_apply]

theorem verify_iff_columns (σ : P.Statement) (W : P.Oracle)
    (c : P.Coin) (a : P.Response) (Q : QuerySet n t) :
    P.backend.layer.verify σ W c a (P.localQuery Q) ↔
      globalCheck P.backend.domain P.backend.layout σ c.1 a ∧
        Q.coordinates ⊆ P.goodColumns σ W c a := by
  rcases P with ⟨F,hF,hfin,hdec,I,hk,hs,hn,ht,hlinear⟩
  cases hn
  cases ht
  simpa [Instance.layer, localQuery, goodColumns, columnSets, good, Accepts] using
    verify_openOracle_iff I.domain (by have := I.primary_le; omega)
      I.primary_le I.layout σ W c a Q

/-- A sufficiently large common set can be assigned without extending or
padding it. Both participants will therefore refer to this same set. -/
theorem assign_columns (p : ProfileParameters P.backend)
    (σ : P.Statement) (W : P.Oracle) (c : P.Coin) (a : P.Response)
    (hb : ¬ rankBad P.backend W c) (T : Finset (Fin n))
    (hT : T ⊆ P.goodColumns σ W c a) (hsize : p.coreSize ≤ T.card) :
    ∃ d : systems P.backend.domain P.backend.primary_le W, T ∈ P.associated W d := by
  rcases P with ⟨F,hF,hfin,hdec,I,hk,hs,hn,ht,hlinear⟩
  cases hn
  simp [goodColumns, associated, columnSets, Equiv.cast] at hT ⊢
  have hv : (c.2,a.primary) ∈ ConsistencyClosure.solutions
      (jointMap (code I) (words I W)) W.proximityMask T := by
    intro j hj
    exact sub_eq_iff_eq_add.mpr (((mem_filter.mp (hT hj)).2).1.trans (add_comm _ _))
  have hlow := ReducedSystems.low_defect_of_not_bad (code I) (words I W)
    W.proximityMask c.2 hb T hsize a.primary hv
  let d : systems I.domain I.primary_le W :=
    ⟨ConsistencyClosure.closure (jointMap (code I) (words I W)) W.proximityMask
      (canonicalCoreSet (code I) (words I W) T),
      ReducedSystems.canonical_mem_family (code I) (words I W) W.proximityMask
        T hsize hlow ⟨_,hv⟩⟩
  refine ⟨d, d.2, ?_⟩
  change T ∈ ReducedSystems.associatedSets (code I) (words I W) W.proximityMask d.1
  exact mem_filter.mpr ⟨mem_univ _,hsize,hlow,⟨_,hv⟩,rfl⟩

theorem associated_overlap (hk : 1 ≤ k) (W : P.Oracle)
    (d e : systems P.backend.domain P.backend.primary_le W) (T U : Finset (Fin n))
    (hT : T ∈ P.associated W d) (hU : U ∈ P.associated W e) (hne : d ≠ e) :
    (T ∩ U).card ≤ k+2*s-1 := by
  rcases P with ⟨F,hF,hfin,hdec,I,hkI,hs,hn,ht,hlinear⟩
  cases hn
  simp [associated, columnSets, Equiv.cast] at hT hU
  have h := ReducedSystems.associated_intersection (code I) (words I W) W.proximityMask
    (by omega) d.1 e.1 T U hT hU (fun he => hne (Subtype.ext he))
  simpa only [hkI, hs] using h

theorem response_eq_of_columns (p : ProfileParameters P.backend)
    (σ : P.Statement) (W : P.Oracle) (c : P.Coin) (hb : ¬ rankBad P.backend W c)
    (d : systems P.backend.domain P.backend.primary_le W)
    (a b : P.Response) (T U : Finset (Fin n))
    (hT : T ∈ P.associated W d) (hU : U ∈ P.associated W d)
    (hTa : T ⊆ P.goodColumns σ W c a) (hUb : U ⊆ P.goodColumns σ W c b)
    (hlargeT : p.largeSize ≤ T.card) (hlargeU : p.largeSize ≤ U.card) : a = b := by
  rcases P with ⟨F,hF,hfin,hdec,I,hk,hs,hn,ht,hlinear⟩
  cases hn
  simp [associated, goodColumns, columnSets, Equiv.cast] at hT hU hTa hUb
  exact response_eq_of_common_columns I p σ W c hb d a b T U hT hU hTa hUb hlargeT hlargeU

/-- Failure to recover from a large common set forces the assigned system's
ordinary one-field exception. This also applies to satisfiable statements. -/
theorem exception_of_columns (p : ProfileParameters P.backend)
    (σ : P.Statement) (W : P.Oracle) (c : P.Coin) (hb : ¬ rankBad P.backend W c)
    (d : systems P.backend.domain P.backend.primary_le W) (a : P.Response)
    (T : Finset (Fin n)) (hT : T ∈ P.associated W d)
    (hTa : T ⊆ P.goodColumns σ W c a) (hlarge : p.largeSize ≤ T.card)
    (hglobal : globalCheck P.backend.domain P.backend.layout σ c.1 a)
    (hnone : scanRecoverAt P.backend σ W c a = none) :
    c ∈ systemExceptions p.positive_degree P.backend.layout σ d := by
  rcases P with ⟨F,hF,hfin,hdec,I,hk,hs,hn,ht,hlinear⟩
  cases hn
  simp [associated, goodColumns, columnSets, Equiv.cast] at hT hTa
  have hdata := common_columns_data I p σ W c hb a d T hT hTa
  by_contra he
  obtain ⟨hfull,hsome⟩ := recover_of_assigned_system I p.positive_degree σ W d c a
    hdata.1 he hglobal (by
      simpa only [ProfileParameters.largeSize, ProfileParameters.coreSize,
        good, two_mul, Nat.add_assoc] using hlarge.trans (card_le_card hTa)) (by
      change ((good I σ W c a) \ d.1).card ≤ I.s
      exact (Nat.le_add_left _ _).trans hdata.2)
  rw [hnone] at hsome
  cases hsome

theorem outside_query_raw_le {C : Type} [Fintype C]
    (decodeQuery : C → QuerySet n t) (kQuery : ℕ)
    (hquery : ∀ Q, (univ.filter fun b : C => decodeQuery b = Q).card ≤ kQuery)
    (hkQuery : kQuery*Fintype.card (QuerySet n t) ≤ Fintype.card C)
    (σ : P.Statement) (W : P.Oracle) (c : P.Coin) (a : P.Response) (cutoff : ℕ) :
    (∑ b : C, indicator (P.backend.layer.verify σ W c a (P.localQuery (decodeQuery b)) ∧
      decodedOutsideList P.backend σ W c a cutoff)) ≤
      Fintype.card C * (((cutoff+s-1).choose t : ℚ)/n.choose t) := by
  rcases P with ⟨F,hF,hfin,hdec,I,hk,hs,hn,ht,hlinear⟩
  cases hn
  cases ht
  cases hs
  letI : DecidableEq I.layer.Query := inferInstanceAs (DecidableEq (QuerySet I.n I.t))
  change (∑ b : C, indicator (I.layer.verify σ W c a (decodeQuery b) ∧
    decodedOutsideList I σ W c a cutoff)) ≤ _
  convert! decoded_outside_query_raw_le I decodeQuery kQuery hquery hkQuery σ W c a cutoff using 1
  apply sum_congr rfl
  intro b _
  unfold indicator
  split_ifs <;> rfl

end LfzkV2.Joint.Participant
