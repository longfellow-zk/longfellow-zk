import CodingTheory.ListDecoding.InterleavedJohnson
import polygero.FiatShamir.ResponseMass

/-!
# A fixed list of witnesses near the committed oracle

The list depends only on the committed core rows, before frontend challenges
or backend responses. Any certified uniform-family bound gives its size. A
successful decoder outside this list has a uniformly bounded query fraction.
-/

namespace RecursivePolygero.Counting

open Polynomial Finset Codes LigeroFamily Local
open scoped Classical
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

noncomputable def committedCandidates (I : Instance F) (W : I.layer.Oracle) (cutoff : ℕ) :
    Finset (tupleCounts I).Index :=
  univ.filter fun g => cutoff ≤
    (rowAgreement (PolynomialDirect.primaryCode I.domain I.primary_le) (I.coreWords W) g).card

/-- A fixed-size index type for the committed list. Unused indices return the
zero tuple; they add no hypothesis to the list-coverage theorem. -/
noncomputable def committedCandidate (I : Instance F) (W : I.layer.Oracle)
    (cutoff bound : ℕ) (i : Fin bound) : (tupleCounts I).Index :=
  if h : i.val < (committedCandidates I W cutoff).card then
    ((committedCandidates I W cutoff).equivFin.symm ⟨i.val,h⟩).val
  else fun _ => 0

theorem exists_committedCandidate (I : Instance F) (W : I.layer.Oracle)
    (cutoff bound : ℕ) (hbound : (committedCandidates I W cutoff).card ≤ bound)
    (g : (tupleCounts I).Index) (hg : g ∈ committedCandidates I W cutoff) :
    ∃ i : Fin bound, committedCandidate I W cutoff bound i = g := by
  let entry : ↥(committedCandidates I W cutoff) := ⟨g,hg⟩
  let j := (committedCandidates I W cutoff).equivFin entry
  let i : Fin bound := ⟨j.val, j.isLt.trans_le hbound⟩
  refine ⟨i, ?_⟩
  have hi : i.val < (committedCandidates I W cutoff).card := j.isLt
  simp only [committedCandidate, dif_pos hi]
  exact congrArg Subtype.val ((committedCandidates I W cutoff).equivFin.symm_apply_apply entry)

/-- The list bound concerns witness tuples, with overlap `k-1`; the proximity
mask and response polynomials do not enter its definition. -/
theorem committedCandidates_card_le (I : Instance F) (W : I.layer.Oracle)
    (cutoff bound : ℕ) (hcutoff : I.r+I.w-1 < cutoff)
    (hpacking : CodingTheory.UniformFamilyBound I.n cutoff (I.r+I.w-1) bound) :
    (committedCandidates I W cutoff).card ≤ bound := by
  apply DirectBinomial.active_card_le_of_uniformFamilyBound
    (committedCandidates I W cutoff)
    (fun g => rowAgreement (PolynomialDirect.primaryCode I.domain I.primary_le) (I.coreWords W) g)
    cutoff (I.r+I.w-1) bound hcutoff
  · intro g hg
    exact (mem_filter.mp hg).2
  · intro g _ h _ hne
    exact rowAgreement_inter_card_le _ _ g h hne
  · exact hpacking

/-- Johnson's symbolic certificate is one way to instantiate the fixed list;
the same interface also accepts the fast Hahn certificates. -/
theorem committedCandidates_card_le_johnson (I : Instance F) (W : I.layer.Oracle)
    (cutoff : ℕ) (hk : 1 ≤ I.r+I.w) (hcutoff : I.r+I.w-1 < cutoff) (hcn : cutoff ≤ I.n)
    (hden : 0 < CodingTheory.InterleavedJohnson.denominator I.n
      (I.n-(I.r+I.w)+1) (I.n-cutoff)) :
    (committedCandidates I W cutoff).card ≤ CodingTheory.InterleavedJohnson.listBound I.n
      (I.n-(I.r+I.w)+1) (I.n-cutoff) := by
  have hkn := I.primary_le
  apply committedCandidates_card_le I W cutoff _ hcutoff
  have hp := CodingTheory.InterleavedJohnson.uniformFamilyBound_of_denominator_pos
    (n := I.n) (d := I.n-(I.r+I.w)+1) (E := I.n-cutoff)
    (by omega) (by omega) (by omega) hden
  convert! hp using 1 <;> omega

/-- An extracted witness outside the fixed list forces a small good-column
set. This statement is uniform in both backend response polynomials. -/
theorem fraction_le_of_decoded_not_mem (I : Instance F) (σ : I.layer.Statement)
    (W : I.layer.Oracle) (coin : I.layer.Coin) (payload : I.layer.Payload)
    (g : (tupleCounts I).Index) (cutoff : ℕ)
    (hdecode : scanRecoverAt I σ W coin payload = some g)
    (hnot : g ∉ committedCandidates I W cutoff) :
    NonrecursiveFS.fraction I σ W coin payload ≤
      ((cutoff+I.s-1).choose I.t : ℚ)/I.n.choose I.t := by
  have hsmall : (rowAgreement (PolynomialDirect.primaryCode I.domain I.primary_le)
      (I.coreWords W) g).card < cutoff := by
    exact lt_of_not_ge (fun h => hnot (mem_filter.mpr ⟨mem_univ _, h⟩))
  have hcolumns := (scanRecoverAt_columns I σ W coin payload g hdecode).2.1
  have hgood : (NonrecursiveFS.good I σ W coin payload).card ≤ cutoff+I.s-1 := by
    dsimp only [NonrecursiveFS.good]
    omega
  exact (NonrecursiveFS.fraction_le_columns I σ W coin payload).trans
    (div_le_div_of_nonneg_right
      (by exact_mod_cast Nat.choose_le_choose I.t hgood) (by positivity))

theorem decoded_mem_of_fraction_gt (I : Instance F) (σ : I.layer.Statement)
    (W : I.layer.Oracle) (coin : I.layer.Coin) (payload : I.layer.Payload)
    (g : (tupleCounts I).Index) (cutoff : ℕ)
    (hdecode : scanRecoverAt I σ W coin payload = some g)
    (hlarge : ((cutoff+I.s-1).choose I.t : ℚ)/I.n.choose I.t <
      NonrecursiveFS.fraction I σ W coin payload) :
    g ∈ committedCandidates I W cutoff := by
  by_contra hn
  exact (not_lt_of_ge (fraction_le_of_decoded_not_mem I σ W coin payload g cutoff hdecode hn)) hlarge

end RecursivePolygero.Counting
