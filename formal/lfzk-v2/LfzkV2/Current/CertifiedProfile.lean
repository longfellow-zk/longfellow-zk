import LfzkV2.Current.ParameterBounds
import LfzkV2.Current.JointMass
import LfzkV2.Current.ApplicationCharging

/-! A shared constructor for checked numerical mdoc profiles. Public protocol
specializations choose a closed catalog entry; they do not ask callers for
coding or error-budget certificates. Candidate-list caps remain explicit. -/
noncomputable section
namespace LfzkV2.Current
open RecursivePolygero ProfileAnalysis ParameterBounds Counting
open scoped Classical

structure CertifiedProfile where
  rate : ℕ
  k : ℕ
  s : ℕ
  n : ℕ
  t : ℕ
  rate_eq : n = rate*k
  activeCutoff : ℕ
  activeList : ℕ
  binaryCutoff : ℕ
  primeCutoff : ℕ
  binaryList : ℕ
  primeList : ℕ
  positive_degree : 1 ≤ k
  query_pos : 0 < t
  large_le_active : max (k+2*s+1) (2*k+s) ≤ activeCutoff
  active_le_columns : activeCutoff ≤ n
  active_list_le_field : activeList ≤ Adapter.Mdoc.binaryOrder
  active_bound : CodingTheory.UniformFamilyBound n activeCutoff (k+2*s-1) activeList
  binary_candidates : CodingTheory.UniformFamilyBound n binaryCutoff (k-1) binaryList
  prime_candidates : CodingTheory.UniformFamilyBound n primeCutoff (k-1) primeList
  binary_overlap_lt : k-1 < binaryCutoff
  prime_overlap_lt : k-1 < primeCutoff
  threshold_condition : DiscreteThreshold.Condition activeList
    (tail n t (k+2*s-1)) (tail n t (activeCutoff-1))
  threshold_lt_one : tail n t (activeCutoff-1) < 1
  binary_rank_small : rankError n k s Adapter.Mdoc.binaryOrder +
    1/(Adapter.Mdoc.binaryOrder:ℚ) < 1
  prime_rank_small : rankError n k s Adapter.Mdoc.primeOrder +
    1/(Adapter.Mdoc.primeOrder:ℚ) < 1
  parent_budget_le : parentBudget n k s t activeCutoff activeList ≤
    1999999/(1000000*(Adapter.Mdoc.binaryOrder:ℚ))
  opening_budget_le : openingBudget n s t activeCutoff binaryCutoff primeCutoff ≤
    1999999/(1000000*(Adapter.Mdoc.binaryOrder:ℚ))
  fingerprint_budget_le : (binaryList.choose 2:ℚ)/(Adapter.Mdoc.binaryOrder:ℚ)^2 +
    (primeList.choose 2:ℚ)/(Adapter.Mdoc.primeOrder:ℚ)^2 ≤
      2/((Adapter.Mdoc.binaryOrder-1:ℕ):ℚ)

namespace CertifiedProfile
variable (c : CertifiedProfile)

def threshold : ℚ := tail c.n c.t (c.activeCutoff-1)
def cutoff : ℕ × ℕ := (c.binaryCutoff,c.primeCutoff)

section Parameters
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Both concrete fields use the same checked column geometry. -/
def parameters (I : Instance F) (hn : I.n = c.n) (hk : I.r+I.w = c.k)
    (hs : I.s = c.s) (ht : I.t = c.t)
    (hq : Nat.card F = Adapter.Mdoc.binaryOrder ∨ Nat.card F = Adapter.Mdoc.primeOrder) :
    HahnSystemCertificate I := by
  have hlarge := c.large_le_active
  have hcolumns := c.active_le_columns
  let base : ProfileParameters I := {
    positive_degree := by simpa only [hk] using c.positive_degree
    large_le := by simp only [hn, hk, hs]; omega
    query_pos := by have := c.query_pos; omega
    overlap_lt := by simp only [hn, hk, hs]; omega }
  refine {
    toProfileParameters := base
    columnCutoff := c.activeCutoff
    listBound := c.activeList
    threshold := c.threshold
    large_le_cutoff := ?_
    cutoff_le_n := by simpa only [hn] using c.active_le_columns
    active_bound := ?_
    floor_le := ?_
    threshold_lt_one := c.threshold_lt_one
    excess_condition := ?_
    field_error_lt_one := ?_ }
  · simpa only [ProfileParameters.largeSize, ProfileParameters.coreSize, hk, hs, two_mul, Nat.add_assoc] using hlarge
  · apply Or.inl
    simpa only [hn, ProfileParameters.overlapSize, hk, hs, two_mul, Nat.add_assoc] using c.active_bound
  · change (((c.activeCutoff-1).choose I.t:ℚ)/I.n.choose I.t) ≤ c.threshold
    rw [hn, ht]
    exact le_rfl
  · apply Or.inr
    apply Or.inr
    have hcount : c.activeList ≤ Nat.card F := by
      rcases hq with hq | hq
      · rw [hq]; exact c.active_list_le_field
      · rw [hq]
        exact c.active_list_le_field.trans (by
          norm_num [Adapter.Mdoc.binaryOrder, Adapter.Mdoc.primeOrder])
    rw [min_eq_right hcount]
    simpa only [ProfileParameters.overlapSize, hn, hk, hs, ht, threshold, tail, two_mul, Nat.add_assoc]
      using c.threshold_condition
  · change (I.n.choose (I.r+I.w+I.s+I.s+1):ℚ)/(Nat.card F:ℚ)^(I.s+1)+
      1/(Nat.card F:ℚ) < 1
    rw [hn, hk, hs]
    rcases hq with hq | hq
    · rw [hq]
      simpa only [rankError, two_mul, Nat.add_assoc] using c.binary_rank_small
    · rw [hq]
      simpa only [rankError, two_mul, Nat.add_assoc] using c.prime_rank_small

omit [Fintype F] [DecidableEq F] in
theorem parameters_rankError (I : Instance F) (hn : I.n = c.n) (hk : I.r+I.w = c.k)
    (hs : I.s = c.s) (ht : I.t = c.t)
    (hq : Nat.card F = Adapter.Mdoc.binaryOrder ∨ Nat.card F = Adapter.Mdoc.primeOrder) :
    (c.parameters I hn hk hs ht hq).rankError = rankError c.n c.k c.s (Nat.card F) := by
  change (I.n.choose (I.r+I.w+I.s+I.s+1):ℚ)/(Nat.card F:ℚ)^(I.s+1) = _
  rw [hn, hk, hs]
  simp only [rankError, two_mul, Nat.add_assoc]
end Parameters

/-- The two actual rank terms and the bounded joint response family fit one
parent-query budget. No per-field query allowance is added. -/
theorem parameters_parent_budget_le (P R : Joint.Participant c.k c.s c.n c.t)
    (hP : Nat.card P.Carrier = Adapter.Mdoc.binaryOrder)
    (hR : Nat.card R.Carrier = Adapter.Mdoc.primeOrder) :
    let pc := c.parameters P.backend P.columns P.dimension P.batching P.openings (Or.inl hP)
    let rc := c.parameters R.backend R.columns R.dimension R.batching R.openings (Or.inr hR)
    pc.rankError+rc.rankError+JointResponse.activeHighBudget P R pc ≤
      1999999/(1000000*(Adapter.Mdoc.binaryOrder:ℚ)) := by
  intro pc rc
  rw [c.parameters_rankError P.backend P.columns P.dimension P.batching P.openings (Or.inl hP),
    c.parameters_rankError R.backend R.columns R.dimension R.batching R.openings (Or.inr hR), hP, hR]
  simpa only [JointResponse.activeHighBudget, pc, parameters, threshold, hP, hR, parentBudget]
    using c.parent_budget_le

/-- Fingerprint caps, both frontend fields and the adapter all fit the same
role maximum. Large list caps are visible in the certificate above. -/
theorem round_budget_le {B : Type} [Fintype B]
    (hB : Fintype.card B = Adapter.Mdoc.binaryOrder) (role : Role) :
    ApplicationCharging.roundBudget B Adapter.Mdoc.primeOrder Adapter.Mdoc.groupOrder
      Adapter.Mdoc.quotientBound c.binaryList c.primeList role ≤
      2/((Adapter.Mdoc.binaryOrder-1:ℕ):ℚ) := by
  cases role with
  | fingerprint => simpa only [ApplicationCharging.roundBudget, hB] using c.fingerprint_budget_le
  | inputAssertions side entries =>
      cases side <;> norm_num [ApplicationCharging.roundBudget, hB,
        Adapter.Mdoc.binaryOrder, Adapter.Mdoc.primeOrder]
  | assertions side stage entries fragments =>
      cases side <;> norm_num [ApplicationCharging.roundBudget, hB,
        Adapter.Mdoc.binaryOrder, Adapter.Mdoc.primeOrder]
  | sumcheck side stage index =>
      cases side <;> norm_num [ApplicationCharging.roundBudget, hB,
        Adapter.Mdoc.binaryOrder, Adapter.Mdoc.primeOrder]
  | terminal side stage =>
      cases side <;> norm_num [ApplicationCharging.roundBudget, hB,
        Adapter.Mdoc.binaryOrder, Adapter.Mdoc.primeOrder]
  | combine side stage entries =>
      cases side <;> norm_num [ApplicationCharging.roundBudget, hB,
        Adapter.Mdoc.binaryOrder, Adapter.Mdoc.primeOrder]
  | rowBatching | rescaling | packing | batching | opening =>
      norm_num [ApplicationCharging.roundBudget, hB,
        Adapter.Mdoc.binaryOrder, Adapter.Mdoc.primeOrder]
  | conversion =>
      exact Adapter.Mdoc.collisionBound_le.trans (by norm_num [Adapter.Mdoc.binaryOrder])

/-- Projecting complete committed tableaux cannot enlarge either selected
witness list, even when several backend lifts have the same selected cells. -/
theorem binary_projected_card {Index : Type} [Fintype Index]
    (P : Joint.Participant c.k c.s c.n c.t) (W : P.Oracle)
    (view : (Counting.tupleCounts P.backend).Index → WitnessSelection.Candidate P.Carrier Index) :
    ((committedCandidates P.backend W c.binaryCutoff).image view).card ≤ c.binaryList := by
  apply Finset.card_image_le.trans
  apply committedCandidates_card_le
  · rw [P.dimension]; exact c.binary_overlap_lt
  · simpa only [P.columns, P.dimension] using c.binary_candidates

theorem prime_projected_card {Index : Type} [Fintype Index]
    (P : Joint.Participant c.k c.s c.n c.t) (W : P.Oracle)
    (view : (Counting.tupleCounts P.backend).Index → WitnessSelection.Candidate P.Carrier Index) :
    ((committedCandidates P.backend W c.primeCutoff).image view).card ≤ c.primeList := by
  apply Finset.card_image_le.trans
  apply committedCandidates_card_le
  · rw [P.dimension]; exact c.prime_overlap_lt
  · simpa only [P.columns, P.dimension] using c.prime_candidates

end CertifiedProfile
end LfzkV2.Current
