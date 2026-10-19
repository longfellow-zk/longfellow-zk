import polygero.Local.Decoder
import polygero.Recursion.FSInputs
import polygero.Protocol.Wire

/-! A concrete source of child-commitment reuse in Polygero. Adding a
low-degree polynomial to the proximity mask and to the primary response
preserves every acceptance decision and the extracted witness. Different
polynomials give different committed oracles and parent-query hash inputs.
This is an obstruction in the expanded oracle model, not an extraction-
failure attack. Recursive wire children have zero masks and exclude all
nonzero translations; that restriction is proved below. -/

namespace RecursivePolygero.ProfileAnalysis

open Polynomial Finset Codes LigeroFamily Local Local.Polygero Counting
open LigeroFamily.PolynomialDirect (primaryCode)
open scoped Classical

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

noncomputable def translateMask (I : Instance F) (W : I.layer.Oracle)
    (z : DegreeLT F (I.r+I.w+I.s)) : I.layer.Oracle :=
  ⟨W.ordinary, fun j => W.proximityMask j + (z : F[X]).eval (I.domain.point (codePosition j))⟩

noncomputable def translateResponse (I : Instance F) (R : I.layer.Payload)
    (z : DegreeLT F (I.r+I.w+I.s)) : I.layer.Payload :=
  ⟨R.primary + z, R.arithmetic⟩

theorem translateMask_injective (I : Instance F) (W : I.layer.Oracle) :
    Function.Injective (translateMask I W) := by
  intro z z' he
  apply Subtype.ext
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq (univ : Finset (Fin I.n))
    (primaryCode I.domain I.primary_le).node_injective.injOn
  · simpa only [card_univ, Fintype.card_fin] using
      (mem_degreeLT.mp z.2).trans_le (by exact_mod_cast I.primary_le)
  · simpa only [card_univ, Fintype.card_fin] using
      (mem_degreeLT.mp z'.2).trans_le (by exact_mod_cast I.primary_le)
  · intro j _
    have h := congrArg (fun U : I.layer.Oracle => U.proximityMask j) he
    exact add_left_cancel h

theorem goodColumns_translate (I : Instance F) (sigma : I.layer.Statement)
    (W : I.layer.Oracle) (coin : I.layer.Coin) (R : I.layer.Payload)
    (z : DegreeLT F (I.r+I.w+I.s)) :
    goodColumns I.domain (by have := I.primary_le; omega) I.primary_le I.layout sigma
      (translateMask I W z) coin (translateResponse I R z) =
    goodColumns I.domain (by have := I.primary_le; omega) I.primary_le I.layout sigma W coin R := by
  ext j
  simp only [goodColumns, mem_filter, mem_univ, true_and, translateMask, translateResponse,
    Submodule.coe_add, Polynomial.eval_add, ← add_assoc, add_left_inj]

theorem verify_translate_iff (I : Instance F) (sigma : I.layer.Statement)
    (W : I.layer.Oracle) (coin : I.layer.Coin) (R : I.layer.Payload)
    (z : DegreeLT F (I.r+I.w+I.s)) (q : I.layer.Query) :
    I.layer.verify sigma (translateMask I W z) coin (translateResponse I R z) q ↔
      I.layer.verify sigma W coin R q := by
  change verify _ _ _ _ _ _ _ _ = true ↔ verify _ _ _ _ _ _ _ _ = true
  rw [verify_openOracle_iff I.domain _ I.primary_le, verify_openOracle_iff I.domain _ I.primary_le]
  unfold Accepts
  rw [goodColumns_translate]
  rfl

theorem responseCount_translate (I : Instance F) (sigma : I.layer.Statement)
    (W : I.layer.Oracle) (coin : I.layer.Coin) (R : I.layer.Payload)
    (z : DegreeLT F (I.r+I.w+I.s)) :
    responseCount I.layer sigma (translateMask I W z) coin (translateResponse I R z) =
      responseCount I.layer sigma W coin R := by
  unfold responseCount
  congr 1
  ext q
  simp only [mem_filter, mem_univ, true_and, verify_translate_iff]

theorem scanRecoverAt_translate (I : Instance F) (sigma : I.layer.Statement)
    (W : I.layer.Oracle) (coin : I.layer.Coin) (R : I.layer.Payload)
    (z : DegreeLT F (I.r+I.w+I.s)) :
    scanRecoverAt I sigma (translateMask I W z) coin (translateResponse I R z) =
      scanRecoverAt I sigma W coin R := by
  unfold scanRecoverAt
  rw [goodColumns_translate]
  rfl

theorem translateMask_zero (I : Instance F) (W : I.layer.Oracle) :
    translateMask I W 0 = W := by
  cases W
  simp [translateMask]

/-- The recursive wire restriction removes the entire nontrivial mask
orbit. Thus this symmetry is not an attack on core-only child commitments. -/
theorem translateMask_unmasked_iff (I : Instance F) (W : I.layer.Oracle)
    (hW : W.proximityMask = 0) (z : DegreeLT F (I.r+I.w+I.s)) :
    (translateMask I W z).proximityMask = 0 ↔ z = 0 := by
  constructor
  · intro hz
    have he : translateMask I W z = W := by
      cases W with
      | mk ordinary mask =>
        change Local.Polygero.Oracle.mk ordinary _ = Local.Polygero.Oracle.mk ordinary mask
        congr 1
        exact hz.trans hW.symm
    apply translateMask_injective I W
    exact he.trans (translateMask_zero I W).symm
  · rintro rfl
    simpa only [translateMask_zero] using hW

theorem translated_unmasked_wire_iff (I : Instance F) (W : I.WireOracle false)
    (z : DegreeLT F (I.r+I.w+I.s)) :
    (∃ W' : I.WireOracle false,
      translateMask I (I.expandWireOracle false W) z = I.expandWireOracle false W') ↔ z = 0 := by
  constructor
  · rintro ⟨W', h⟩
    apply (translateMask_unmasked_iff I (I.expandWireOracle false W) rfl z).mp
    rw [h]
    rfl
  · rintro rfl
    exact ⟨W, translateMask_zero I _⟩

end RecursivePolygero.ProfileAnalysis

namespace RecursivePolygero.FiatShamir.TwoLevel

open Polynomial Finset Codes Local ProfileAnalysis
open scoped Classical

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {I : Instance F} (child : Child I)

/-- These verifier-equivalent child oracles give distinct actual parent
query inputs, even with the parent commitment held fixed. -/
theorem translated_query_injective (W : I.layer.Oracle) (V : child.instance.layer.Oracle) :
    Function.Injective (fun z : DegreeLT F (child.instance.r+child.instance.w+child.instance.s) =>
      (query W (translateMask child.instance V z) : HashInput child)) := by
  intro z z' h
  apply translateMask_injective child.instance V
  simpa only [query, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, true_and] using h

theorem translated_query_count (W : I.layer.Oracle) (V : child.instance.layer.Oracle) :
    (univ.image (fun z : DegreeLT F (child.instance.r+child.instance.w+child.instance.s) =>
      (query W (translateMask child.instance V z) : HashInput child))).card =
      Fintype.card F ^ (child.instance.r+child.instance.w+child.instance.s) := by
  rw [card_image_of_injective _ (translated_query_injective child W V), card_univ]
  rw [Fintype.card_congr (Polynomial.degreeLTEquiv F _).toEquiv]
  simp

variable (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)

/-- Whole-proof bad-event weights are identical throughout a child mask
orbit, for every fixed challenge tuple and target family. -/
theorem bad_translate_child (sigma : I.layer.Statement)
    (D : (Counting.tupleCounts I).Index → Prop)
    (W : I.layer.Oracle) (V : child.instance.layer.Oracle)
    (q : I.layer.Query) (R : child.instance.layer.Payload)
    (z : DegreeLT F (child.instance.r+child.instance.w+child.instance.s)) (coins : Coins child) :
    bad child p cp sigma D (W, translateMask child.instance V z, q, translateResponse child.instance R z) coins =
      bad child p cp sigma D (W,V,q,R) coins := by
  simp only [bad, twoProof, Protocol.HahnProfileProof.run, Protocol.HahnProfileProof.runTranscript,
    Protocol.chain, Chain.record, constantMessages, executionVerify, Protocol.HahnProfileProof.family,
    Bool.and_eq_true, decide_eq_true_eq, verify_translate_iff, scanRecoverAt_translate]
  cases scanRecoverAt child.instance (child.link.statement sigma W coins.1.1 coins.1.2)
    V coins.2.1 R <;> rfl

theorem budget_translate_child (sigma : I.layer.Statement)
    (D : (Counting.tupleCounts I).Index → Prop)
    (W : I.layer.Oracle) (V : child.instance.layer.Oracle)
    (q : I.layer.Query) (R : child.instance.layer.Payload)
    (z : DegreeLT F (child.instance.r+child.instance.w+child.instance.s)) :
    budget child p cp sigma D (W, translateMask child.instance V z, q, translateResponse child.instance R z) =
      budget child p cp sigma D (W,V,q,R) := by
  unfold budget
  simp_rw [bad_translate_child]

theorem mask_orbit_budget (sigma : I.layer.Statement)
    (D : (Counting.tupleCounts I).Index → Prop)
    (W : I.layer.Oracle) (V : child.instance.layer.Oracle)
    (q : I.layer.Query) (R : child.instance.layer.Payload) :
    (∑ z : DegreeLT F (child.instance.r+child.instance.w+child.instance.s),
      budget child p cp sigma D (W, translateMask child.instance V z, q, translateResponse child.instance R z)) =
    (Fintype.card F : ℚ) ^ (child.instance.r+child.instance.w+child.instance.s) *
      budget child p cp sigma D (W,V,q,R) := by
  simp_rw [budget_translate_child]
  simp only [sum_const, card_univ, nsmul_eq_mul]
  rw [Fintype.card_congr (Polynomial.degreeLTEquiv F _).toEquiv]
  simp

theorem root_load_ge_mask_orbit (sigma : I.layer.Statement)
    (D : (Counting.tupleCounts I).Index → Prop)
    (W : I.layer.Oracle) (V : child.instance.layer.Oracle)
    (q : I.layer.Query) (R : child.instance.layer.Payload) :
    (Fintype.card F : ℚ) ^ (child.instance.r+child.instance.w+child.instance.s) *
      budget child p cp sigma D (W,V,q,R) ≤
      load (budget child p cp sigma D) (gamma W) := by
  let orbit := fun z : DegreeLT F (child.instance.r+child.instance.w+child.instance.s) =>
    (W, translateMask child.instance V z, q, translateResponse child.instance R z)
  have hinj : Function.Injective orbit := by
    intro z z' h
    exact translateMask_injective child.instance V (congrArg (fun d : Proof child => d.2.1) h)
  rw [← mask_orbit_budget child p cp sigma D W V q R]
  have he : (∑ z, budget child p cp sigma D (orbit z)) =
      ∑ d ∈ univ.image orbit, if gamma W ∈ support d then budget child p cp sigma D d else 0 := by
    rw [sum_image (fun _ _ _ _ h => hinj h)]
    apply sum_congr rfl
    intro z _
    simp [orbit, support]
  change (∑ z, budget child p cp sigma D (orbit z)) ≤ _
  rw [he]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun d _ _ => by
    split_ifs
    · exact budget_nonneg child p cp sigma D d
    · exact le_rfl)

end RecursivePolygero.FiatShamir.TwoLevel
