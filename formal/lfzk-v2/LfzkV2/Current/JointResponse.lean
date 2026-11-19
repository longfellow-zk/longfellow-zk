import LfzkV2.Current.Columns
import LfzkV2.Joint.Backend

/-! Counting the complete two-field Polygero response against its one shared
opening set. Labels are pairs of reduced systems, but their capacities are
maximized over actual common column sets. This is the distinction needed to
apply the one-field overlap argument without multiplying candidate counts. -/
noncomputable section
namespace LfzkV2.Current.JointResponse
open RecursivePolygero LigeroFamily Finset Local Local.Polygero ProfileAnalysis
open scoped Classical

variable {k s n t : ℕ} (P R : Joint.Participant k s n t)

abbrev Statement := P.Statement × R.Statement
abbrev Oracle := P.Oracle × R.Oracle
abbrev Coin := P.Coin × R.Coin
abbrev Response := P.Response × R.Response

def good (σ : Statement P R) (W : Oracle P R) (c : Coin P R) (a : Response P R) :=
  P.goodColumns σ.1 W.1 c.1 a.1 ∩ R.goodColumns σ.2 W.2 c.2 a.2

def Verify (σ : Statement P R) (W : Oracle P R) (c : Coin P R)
    (a : Response P R) (Q : QuerySet n t) : Prop :=
  P.backend.layer.verify σ.1 W.1 c.1 a.1 (P.localQuery Q) ∧
    R.backend.layer.verify σ.2 W.2 c.2 a.2 (R.localQuery Q)

def fraction (σ : Statement P R) (W : Oracle P R) (c : Coin P R) (a : Response P R) : ℚ :=
  ((univ.filter (Verify P R σ W c a)).card : ℚ) / n.choose t

theorem fraction_nonneg (σ : Statement P R) (W : Oracle P R) (c : Coin P R) (a : Response P R) :
    0 ≤ fraction P R σ W c a := by unfold fraction; positivity

theorem query_mean (σ : Statement P R) (W : Oracle P R) (c : Coin P R) (a : Response P R) :
    mean (fun Q => indicator (Verify P R σ W c a Q)) = fraction P R σ W c a := by
  rw [mean_indicator, QuerySet.fintype_card]
  rfl

def rankBad (W : Oracle P R) (c : Coin P R) : Prop :=
  NonrecursiveFS.rankBad P.backend W.1 c.1 ∨ NonrecursiveFS.rankBad R.backend W.2 c.2

def failure (σ : Statement P R) (W : Oracle P R) (c : Coin P R) (a : Response P R) : Prop :=
  scanRecoverAt P.backend σ.1 W.1 c.1 a.1 = none ∨
    scanRecoverAt R.backend σ.2 W.2 c.2 a.2 = none

abbrev Label (W : Oracle P R) := JointFamilies.Label (P.associated W.1) (R.associated W.2)

def associated (W : Oracle P R) (d : Label P R W) :=
  JointFamilies.associated (P.associated W.1) (R.associated W.2) d

def capacity (W : Oracle P R) (d : Label P R W) : ℚ :=
  ((JointFamilies.capacity (P.associated W.1) (R.associated W.2) d).choose t : ℚ) / n.choose t

def exception (p : ProfileParameters P.backend) (r : ProfileParameters R.backend)
    (σ : Statement P R) (W : Oracle P R) (c : Coin P R) (d : Label P R W) : Prop :=
  c.1 ∈ systemExceptions p.positive_degree P.backend.layout σ.1 d.1.1 ∨
    c.2 ∈ systemExceptions r.positive_degree R.backend.layout σ.2 d.1.2

theorem verify_iff (σ : Statement P R) (W : Oracle P R)
    (c : Coin P R) (a : Response P R) (Q : QuerySet n t) :
    Verify P R σ W c a Q ↔
      globalCheck P.backend.domain P.backend.layout σ.1 c.1.1 a.1 ∧
      globalCheck R.backend.domain R.backend.layout σ.2 c.2.1 a.2 ∧
      Q.coordinates ⊆ good P R σ W c a := by
  rw [Verify, P.verify_iff_columns, R.verify_iff_columns]
  simp only [good, subset_inter_iff]
  tauto

theorem fraction_le_columns (σ : Statement P R) (W : Oracle P R)
    (c : Coin P R) (a : Response P R) :
    fraction P R σ W c a ≤ ((good P R σ W c a).card.choose t : ℚ) / n.choose t := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast (show (univ.filter (Verify P R σ W c a)).card ≤
      (good P R σ W c a).card.choose t from by
    rw [← card_queriesWithin]
    apply card_le_card
    intro Q hQ
    exact mem_filter.mpr ⟨mem_univ _, ((verify_iff P R σ W c a Q).mp
      (mem_filter.mp hQ).2).2.2⟩)

theorem global_of_fraction (σ : Statement P R) (W : Oracle P R)
    (c : Coin P R) (a : Response P R) (h : 0 < fraction P R σ W c a) :
    globalCheck P.backend.domain P.backend.layout σ.1 c.1.1 a.1 ∧
    globalCheck R.backend.domain R.backend.layout σ.2 c.2.1 a.2 := by
  have hcount : 0 < (univ.filter (Verify P R σ W c a)).card := by
    have hh : (0 : ℚ) < (univ.filter (Verify P R σ W c a)).card :=
      ((div_pos_iff.mp h).resolve_right (fun hn =>
        (not_lt_of_ge (Nat.cast_nonneg _) hn.1))).1
    exact_mod_cast hh
  obtain ⟨Q,hQ⟩ := card_pos.mp hcount
  have hv := (verify_iff P R σ W c a Q).mp (mem_filter.mp hQ).2
  exact ⟨hv.1,hv.2.1⟩

theorem large_of_fraction (p : ProfileParameters P.backend) (r : ProfileParameters R.backend)
    (σ : Statement P R) (W : Oracle P R) (c : Coin P R) (a : Response P R)
    (ε : ℚ) (hp : p.columnFloor ≤ ε) (hr : r.columnFloor ≤ ε)
    (h : ε < fraction P R σ W c a) :
    p.largeSize ≤ (good P R σ W c a).card ∧ r.largeSize ≤ (good P R σ W c a).card := by
  have hl (b : ℕ) (hb : (((b-1).choose t : ℚ) / n.choose t) ≤ ε) :
      b ≤ (good P R σ W c a).card := by
    by_contra hsmall
    have hs : (good P R σ W c a).card ≤ b-1 := by omega
    have hc := div_le_div_of_nonneg_right
      (show ((good P R σ W c a).card.choose t : ℚ) ≤ (b-1).choose t from by
        exact_mod_cast Nat.choose_le_choose t hs) (show (0 : ℚ) ≤ n.choose t by positivity)
    exact (not_lt_of_ge ((fraction_le_columns P R σ W c a).trans (hc.trans hb)) h)
  exact ⟨hl p.largeSize (by simpa only [ProfileParameters.columnFloor, P.columns, P.openings] using hp),
    hl r.largeSize (by simpa only [ProfileParameters.columnFloor, R.columns, R.openings] using hr)⟩

theorem assign (p : ProfileParameters P.backend) (r : ProfileParameters R.backend)
    (σ : Statement P R) (W : Oracle P R) (c : Coin P R) (a : Response P R)
    (hb : ¬ rankBad P R W c)
    (hp : p.largeSize ≤ (good P R σ W c a).card)
    (hr : r.largeSize ≤ (good P R σ W c a).card) :
    ∃ d : Label P R W, good P R σ W c a ∈ associated P R W d ∧
      fraction P R σ W c a ≤ capacity P R W d := by
  obtain ⟨l,hl⟩ := P.assign_columns p σ.1 W.1 c.1 a.1 (fun h => hb (Or.inl h))
    (good P R σ W c a) inter_subset_left ((le_max_left _ _).trans hp)
  obtain ⟨r',hr'⟩ := R.assign_columns r σ.2 W.2 c.2 a.2 (fun h => hb (Or.inr h))
    (good P R σ W c a) inter_subset_right ((le_max_left _ _).trans hr)
  obtain ⟨d,_,hd,hcap⟩ := JointFamilies.common_set (P.associated W.1) (R.associated W.2)
    l r' (good P R σ W c a) hl hr'
  refine ⟨d,hd,(fraction_le_columns P R σ W c a).trans ?_⟩
  exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.choose_le_choose t hcap) (by positivity)

/-- Equal joint labels determine both complete payloads. Dropping either
payload would lose precisely the injectivity required by FS response counting. -/
theorem response_eq (p : ProfileParameters P.backend) (r : ProfileParameters R.backend)
    (σ : Statement P R) (W : Oracle P R) (c : Coin P R) (hb : ¬ rankBad P R W c)
    (d : Label P R W) (a b : Response P R)
    (ha : good P R σ W c a ∈ associated P R W d)
    (hb' : good P R σ W c b ∈ associated P R W d)
    (hp : ∀ x ∈ ({a,b} : Finset _), p.largeSize ≤ (good P R σ W c x).card)
    (hr : ∀ x ∈ ({a,b} : Finset _), r.largeSize ≤ (good P R σ W c x).card) : a = b := by
  obtain ⟨ha₁,ha₂⟩ := mem_inter.mp ha
  obtain ⟨hb₁,hb₂⟩ := mem_inter.mp hb'
  apply Prod.ext
  · exact P.response_eq_of_columns p σ.1 W.1 c.1 (fun h => hb (Or.inl h)) d.1.1
      a.1 b.1 _ _ ha₁ hb₁ inter_subset_left inter_subset_left (hp a (by simp)) (hp b (by simp))
  · exact R.response_eq_of_columns r σ.2 W.2 c.2 (fun h => hb (Or.inr h)) d.1.2
      a.2 b.2 _ _ ha₂ hb₂ inter_subset_right inter_subset_right (hr a (by simp)) (hr b (by simp))

theorem exception_of_failure (p : ProfileParameters P.backend) (r : ProfileParameters R.backend)
    (σ : Statement P R) (W : Oracle P R) (c : Coin P R) (hb : ¬ rankBad P R W c)
    (d : Label P R W) (a : Response P R)
    (ha : good P R σ W c a ∈ associated P R W d)
    (hp : p.largeSize ≤ (good P R σ W c a).card)
    (hr : r.largeSize ≤ (good P R σ W c a).card)
    (hpos : 0 < fraction P R σ W c a) (hf : failure P R σ W c a) :
    exception P R p r σ W c d := by
  have hg := global_of_fraction P R σ W c a hpos
  obtain ⟨ha₁,ha₂⟩ := mem_inter.mp ha
  rcases hf with hf | hf
  · exact Or.inl (P.exception_of_columns p σ.1 W.1 c.1 (fun h => hb (Or.inl h))
      d.1.1 a.1 _ ha₁ inter_subset_left hp hg.1 hf)
  · exact Or.inr (R.exception_of_columns r σ.2 W.2 c.2 (fun h => hb (Or.inr h))
      d.1.2 a.2 _ ha₂ inter_subset_right hr hg.2 hf)

theorem associated_overlap (hk : 1 ≤ k) (W : Oracle P R) (d e : Label P R W)
    (T U : Finset (Fin n)) (hT : T ∈ associated P R W d) (hU : U ∈ associated P R W e)
    (hne : d ≠ e) : (T ∩ U).card ≤ k+2*s-1 :=
  JointFamilies.associated_intersection _ _ (P.associated_overlap hk W.1)
    (R.associated_overlap hk W.2) d e T U hT hU hne

end LfzkV2.Current.JointResponse
