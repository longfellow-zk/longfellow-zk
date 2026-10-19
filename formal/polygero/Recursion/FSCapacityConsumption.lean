import polygero.Local.CapacityConsumption
import polygero.Recursion.FSAmortization

/-! Capacity-weighted exception coverage for the actual child decoding
relation and parent-query hash inputs. The final lemmas isolate repeated
query spending; they do not assert a no-loss recursive FS theorem. -/
namespace RecursivePolygero.FiatShamir.TwoLevel
open Finset ProfileAnalysis Counting Local Local.Polygero
open scoped Classical
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {I : Instance F} (child : Child I) (p : HahnSystemCertificate I)

/-- A child witness can be selected after the parent query, from any
commitment. Only the high, parent-extraction-failing branch is included. -/
def childExceptionQuery (σ : I.layer.Statement) (W : I.layer.Oracle)
    (a : I.layer.Coin) (q : I.layer.Query) : Prop :=
  a.2 ∉ ReducedSystems.badChallenges
    (LigeroFamily.PolynomialDirect.primaryCode I.domain I.primary_le)
    (oracleWords W.ordinary) W.proximityMask ∧
  ∃ w : child.instance.layer.Witness,
    child.link.direct W q ∧ child.instance.layer.satisfies (child.link.statement σ W a q) w ∧
    p.threshold < (responseCount I.layer σ W a (child.link.decode w) : ℚ) /
      Fintype.card I.layer.Query ∧ scanRecoverAt I σ W a (child.link.decode w) = none

theorem childExceptionQuery_covered (σ : I.layer.Statement) (W : I.layer.Oracle)
    (a : I.layer.Coin) (q : I.layer.Query) :
    childExceptionQuery child p σ W a q → assignedExceptionQuery I p σ W a q := by
  rintro ⟨hout, w, hd, hs, hh, hn⟩
  have hv := (child.verify_iff σ W a q w).mp ⟨hd, hs⟩
  obtain ⟨d, ha, he⟩ := high_target_response_cases I p σ W a (child.link.decode w)
    (fun _ => False) hh (by simp [outputHit, hn]) hout
  have hhigh : d ∈ highSystems I p W := mem_filter.mpr ⟨mem_univ _,
    hh.trans_le (assigned_response_fraction_le I σ W a (child.link.decode w) d ha)⟩
  have hex : a ∈ systemExceptions p.positive_degree I.layout σ d := by
    rcases he with ⟨_, hx⟩ | ⟨_, ht | hx⟩
    · exact hx
    · obtain ⟨_, hf⟩ := ht
      exact hf.elim
    · exact hx
  exact ⟨hout, d, hhigh, hex, child.link.decode w, ha, hv⟩

theorem childExceptionQuery_conditional_le (σ : I.layer.Statement) (W : I.layer.Oracle)
    (a : I.layer.Coin) :
    mean (fun q => indicator (childExceptionQuery child p σ W a q)) ≤
      weightedExceptions I p σ W a := by
  apply le_trans (mean_mono (fun q => ?_)) (assignedExceptionQuery_conditional_le I p σ W a)
  by_cases h : childExceptionQuery child p σ W a q
  · simp [indicator, h, childExceptionQuery_covered child p σ W a q h]
  · simp only [indicator, if_neg h]
    exact indicator_nonneg _

theorem childExceptionQuery_mean_le (hsmall : p.listBound < Nat.card F)
    (σ : I.layer.Statement) (W : I.layer.Oracle) :
    mean (fun a => mean (fun q => indicator (childExceptionQuery child p σ W a q))) ≤
      (1 - p.threshold + p.listBound * p.threshold) / Nat.card F :=
  (mean_mono (childExceptionQuery_conditional_le child p σ W)).trans
    (weightedExceptions_mean_le I p hsmall σ W)

/-- This uses the actual query hash input, retaining its child commitment.
The coverage is uniform over every possible decoded child witness. -/
def queryExceptionEvent (σ : I.layer.Statement) :
    HashInput child → (HashInput child → Answer child) → Prop
  | .inr (.inl (W, V)), H => childExceptionQuery child p σ W
      (H (gamma W)).1.1 (H (query W V)).1.2
  | _, _ => False

theorem queryExceptionEvent_local (σ : I.layer.Statement) (W : I.layer.Oracle)
    (V : child.instance.layer.Oracle) (H : HashInput child → Answer child) :
    Bcs.TotalOracle.Footprint.average (fun c => indicator
      (queryExceptionEvent child p σ (query W V) (Function.update H (query W V) c))) ≤
        weightedExceptions I p σ W (H (gamma W)).1.1 := by
  simp only [queryExceptionEvent, query, gamma, Function.update_self,
    Function.update_of_ne (by simp : (Sum.inl W : HashInput child) ≠ Sum.inr (Sum.inl (W,V)))]
  change mean (fun c : Answer child => indicator
    (childExceptionQuery child p σ W (H (.inl W)).1.1 c.1.2)) ≤ _
  simp only [mean_prod, mean_const]
  exact childExceptionQuery_conditional_le child p σ W _

open Bcs.TotalOracle.Footprint Merkle.RandomOracle

noncomputable def activatedChildren {Out : Type} {N : ℕ}
    (tree : Tree (HashInput child) (Answer child) Out N)
    (H : HashInput child → Answer child) (W : I.layer.Oracle) : Finset child.instance.layer.Oracle :=
  univ.filter (fun V => hits tree H {query W V})

/-- The proposed conditional price is reused verbatim at each distinct
child-query input. This equality holds for an arbitrary adaptive tree. -/
theorem activated_exception_budget_eq {Out : Type} {N : ℕ}
    (tree : Tree (HashInput child) (Answer child) Out N)
    (H : HashInput child → Answer child) (σ : I.layer.Statement) (W : I.layer.Oracle) :
    (∑ _V ∈ activatedChildren child tree H W, weightedExceptions I p σ W (H (gamma W)).1.1) =
      (activatedChildren child tree H W).card * weightedExceptions I p σ W (H (gamma W)).1.1 := by
  simp

/-- Exact remaining obligation for this particular charging construction.
A small unconditional mean of E cannot establish this pathwise inequality. -/
theorem activated_exception_consumption_iff {Out : Type} {N : ℕ}
    (tree : Tree (HashInput child) (Answer child) Out N)
    (H : HashInput child → Answer child) (σ : I.layer.Statement) (W : I.layer.Oracle)
    (childAllowance parentAllowance : ℚ) :
    (∑ _V ∈ activatedChildren child tree H W, weightedExceptions I p σ W (H (gamma W)).1.1) ≤
      (activatedChildren child tree H W).card * childAllowance + parentAllowance ↔
    (activatedChildren child tree H W).card *
      (weightedExceptions I p σ W (H (gamma W)).1.1 - childAllowance) ≤ parentAllowance := by
  rw [activated_exception_budget_eq]
  constructor <;> intro h <;> nlinarith

/-- Already two different activated commitments repeat a positive price.
This diagnoses the proposed allocation, not an attack on Polygero. -/
theorem two_child_attempts_reuse {Out : Type} {N : ℕ}
    (tree : Tree (HashInput child) (Answer child) Out N)
    (H : HashInput child → Answer child) (σ : I.layer.Statement) (W : I.layer.Oracle)
    (V₀ V₁ : child.instance.layer.Oracle) (hne : V₀ ≠ V₁)
    (h₀ : hits tree H {query W V₀}) (h₁ : hits tree H {query W V₁})
    (hpos : 0 < weightedExceptions I p σ W (H (gamma W)).1.1) :
    weightedExceptions I p σ W (H (gamma W)).1.1 <
      ∑ _V ∈ activatedChildren child tree H W, weightedExceptions I p σ W (H (gamma W)).1.1 := by
  have hc : 2 ≤ (activatedChildren child tree H W).card := by
    calc
      2 = ({V₀, V₁} : Finset child.instance.layer.Oracle).card := by simp [hne]
      _ ≤ _ := card_le_card (by
        intro V hv
        simp only [mem_insert, mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact mem_filter.mpr ⟨mem_univ _, h₀⟩
        · exact mem_filter.mpr ⟨mem_univ _, h₁⟩)
  have hcq : (2 : ℚ) ≤ (activatedChildren child tree H W).card := by exact_mod_cast hc
  rw [activated_exception_budget_eq]
  nlinarith

end RecursivePolygero.FiatShamir.TwoLevel
