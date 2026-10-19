import polygero.Local.CapacityConsumption
import polygero.Algebra.Counting.IntegerOccupancy

/-! Payload rigidity from a system's column capacity.

Full consistency is not necessary when two assigned responses have
enough overlap. Their primary polynomials are already equal; agreement of
their arithmetic polynomials on at least `2k` nodes gives payload equality.
The assigned-union capacity theorem supplies that overlap for all systems,
including proper systems. This is a geometric lemma, not a ROM theorem.
-/

namespace RecursivePolygero.ProfileAnalysis

open Polynomial Finset Codes LigeroFamily Local Local.Polygero Counting
open LigeroFamily.PolynomialDirect (primaryCode)
open scoped Classical

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

private noncomputable abbrev good (I : Instance F) (σ : I.layer.Statement)
    (W : I.layer.Oracle) (coin : I.layer.Coin) (u : I.layer.Payload) :=
  goodColumns I.domain (by have := I.primary_le; omega) I.primary_le I.layout σ W coin u

/-- Primary equality and overlap of `2k` actual good columns force equality
of the entire response payload. This does not require full consistency. -/
theorem payload_unique_of_good_overlap (I : Instance F) (σ : I.layer.Statement)
    (W : I.layer.Oracle) (coin : I.layer.Coin) (u v : I.layer.Payload)
    (hp : u.primary = v.primary)
    (hoverlap : 2 * (I.r + I.w) ≤ (good I σ W coin u ∩ good I σ W coin v).card) :
    u = v := by
  have ha : u.arithmetic = v.arithmetic := by
    apply Subtype.ext
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq
      (good I σ W coin u ∩ good I σ W coin v)
      (primaryCode I.domain I.primary_le).node_injective.injOn
    · exact (mem_degreeLT.mp u.arithmetic.2).trans_le (by exact_mod_cast hoverlap)
    · exact (mem_degreeLT.mp v.arithmetic.2).trans_le (by exact_mod_cast hoverlap)
    · intro j hj
      have hu := (mem_filter.mp (mem_inter.mp hj).1).2.2.1
      have hv := (mem_filter.mp (mem_inter.mp hj).2).2.2.1
      exact hu.trans hv.symm
  cases u
  cases v
  simp_all

/-- Proper systems are allowed. Two assigned responses with at least `a`
good columns are equal whenever system capacity plus `2k` is at most `2a`.
Only the rank event is excluded, as required by assigned-union capacity. -/
theorem assigned_payload_unique_of_capacity (I : Instance F) (hk : 1 ≤ I.r + I.w)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin)
    (hout : coin.2 ∉ ReducedSystems.badChallenges (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask)
    (u v : I.layer.Payload) (d : systems I.domain I.primary_le W)
    (hu : ResponseAssignment I σ W coin u d) (hv : ResponseAssignment I σ W coin v d)
    (a : ℕ) (hlu : a ≤ (good I σ W coin u).card)
    (hlv : a ≤ (good I σ W coin v).card)
    (hcapacity : ReducedSystems.capacity (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask d.1 + 2 * (I.r + I.w) ≤ 2 * a) :
    u = v := by
  have hUnion : (good I σ W coin u ∪ good I σ W coin v).card ≤
      ReducedSystems.capacity (primaryCode I.domain I.primary_le)
        (oracleWords W.ordinary) W.proximityMask d.1 := by
    have hc := assigned_union_capacity_le I hk σ W coin hout d {u, v} (by
      intro z hz
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hu
      · exact hv)
    change (({u, v} : Finset I.layer.Payload).biUnion (good I σ W coin)).card ≤ _ at hc
    simpa using hc
  apply payload_unique_of_good_overlap I σ W coin u v
    (assigned_primary_unique I σ W coin u v d hu hv)
  have hcard := card_union_add_card_inter (good I σ W coin u) (good I σ W coin v)
  omega

/-- A high response reaches the certificate's actual column cutoff, not
only the smaller threshold needed for the local decoding theorem. -/
theorem high_response_cutoff_le (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin)
    (u : I.layer.Payload)
    (hh : p.threshold < (responseCount I.layer σ W coin u : ℚ) /
      Fintype.card I.layer.Query) :
    p.columnCutoff ≤ (good I σ W coin u).card := by
  have hcount := div_le_div_of_nonneg_right
    (Nat.cast_le (α := ℚ).mpr (responseCount_le_columns I σ W coin u))
    (show (0 : ℚ) ≤ Fintype.card I.layer.Query by positivity)
  have hhigh := hh.trans_le hcount
  rw [show Fintype.card I.layer.Query = I.n.choose I.t from QuerySet.fintype_card _ _] at hhigh
  exact DirectBinomial.size_ge_of_choose_div_gt (Nat.choose_pos I.query_le) p.floor_le hhigh

/-- Actual high responses assigned to a sufficiently small-capacity system
are unique even if that system is proper. The only hypotheses beyond
assignment are the existing rank exclusion and a column-capacity inequality. -/
theorem high_assigned_payload_unique_of_capacity (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin)
    (hout : coin.2 ∉ ReducedSystems.badChallenges (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask)
    (u v : I.layer.Payload) (d : systems I.domain I.primary_le W)
    (hu : ResponseAssignment I σ W coin u d) (hv : ResponseAssignment I σ W coin v d)
    (hhu : p.threshold < (responseCount I.layer σ W coin u : ℚ) /
      Fintype.card I.layer.Query)
    (hhv : p.threshold < (responseCount I.layer σ W coin v : ℚ) /
      Fintype.card I.layer.Query)
    (hcapacity : ReducedSystems.capacity (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask d.1 + 2 * (I.r + I.w) ≤ 2 * p.columnCutoff) :
    u = v :=
  assigned_payload_unique_of_capacity I p.positive_degree σ W coin hout u v d hu hv
    p.columnCutoff (high_response_cutoff_le I p σ W coin u hhu)
    (high_response_cutoff_le I p σ W coin v hhv) hcapacity

/-- Systems above a column-capacity cutoff inherit any uniform-family
bound at that cutoff. This counts the possible residual systems after
capacity rigidity; it does not count possible payloads within them. -/
theorem large_capacity_systems_card_le (I : Instance F) (p : ProfileParameters I)
    (W : I.layer.Oracle) (cutoff L : ℕ) (hcutoff : p.overlapSize < cutoff)
    (hb : CodingTheory.UniformFamilyBound I.n cutoff p.overlapSize L) :
    (univ.filter (fun d : systems I.domain I.primary_le W =>
      cutoff ≤ ReducedSystems.capacity (primaryCode I.domain I.primary_le)
        (oracleWords W.ordinary) W.proximityMask d.1)).card ≤ L := by
  let T := univ.filter (fun d : systems I.domain I.primary_le W =>
    cutoff ≤ ReducedSystems.capacity (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask d.1)
  let E := fun d : systems I.domain I.primary_le W =>
    Classical.choose (ReducedSystems.capacity_witness (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask d.1 d.2)
  have hs (d : systems I.domain I.primary_le W) :=
    Classical.choose_spec (ReducedSystems.capacity_witness (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask d.1 d.2)
  apply DirectBinomial.active_card_le_of_uniformFamilyBound T E cutoff p.overlapSize L hcutoff _ _ hb
  · intro d hd
    exact (hs d).2 ▸ (mem_filter.mp hd).2
  · intro d _ e _ hne
    exact ReducedSystems.associated_intersection (primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask p.positive_degree d.1 e.1 (E d) (E e)
      (hs d).1 (hs e).1 (fun h => hne (Subtype.ext h))

/-- At the fixed 81/80 schedule, at most two systems escape the new
payload-rigidity criterion. These may be proper or full; full systems also
have the independent full-consistency rigidity theorem. -/
theorem fixed_nonrigid_systems_card_le_two (I : Instance F) (p : HahnSystemCertificate I)
    (W : I.layer.Oracle) (hn : I.n = 8192) (hk : I.r + I.w = 512)
    (hs : I.s = 64) (ha : p.columnCutoff = 2714) :
    (univ.filter (fun d : systems I.domain I.primary_le W =>
      ¬ (ReducedSystems.capacity (primaryCode I.domain I.primary_le)
        (oracleWords W.ordinary) W.proximityMask d.1 + 2 * (I.r + I.w) ≤
          2 * p.columnCutoff))).card ≤ 2 := by
  have hover : p.toProfileParameters.overlapSize = 639 := by
    simp [ProfileParameters.overlapSize, hk, hs]
  have hb : CodingTheory.UniformFamilyBound I.n 4405 p.toProfileParameters.overlapSize 2 := by
    rw [hn, hover]
    apply CodingTheory.IntegerOccupancy.uniformFamilyBound (h := 1)
    norm_num
  have hc := large_capacity_systems_card_le I p.toProfileParameters W 4405 2
    (by rw [hover]; norm_num) hb
  apply (card_le_card ?_).trans hc
  intro d hd
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_⟩
  have hnot := (mem_filter.mp hd).2
  omega

end RecursivePolygero.ProfileAnalysis
