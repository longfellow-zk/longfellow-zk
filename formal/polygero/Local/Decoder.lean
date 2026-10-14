import polygero.Local.CoreCandidates
import polygero.Local.RowRecovery

/-! Scan a response, uniquely decode every witness row on all good columns,
and validate the complete candidate. No candidate list is enumerated. -/
namespace RecursivePolygero
open Polynomial Finset Codes LigeroFamily RecursivePolygero.Local RecursivePolygero.Local.Polygero Counting
attribute [local instance] Classical.propDecidable
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Row-wise unique decoding, followed by the global agreement and relation tests.
The existential is a specification of the independent row decoders. -/
noncomputable def recoverOnAt (I : Instance F)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (S : Finset (Fin I.n)) (radius : ℕ) :
    Option (tupleCounts I).Index :=
  if h : ∃ g : Fin (Fintype.card (CoreRow I.nw I.nq)) → DegreeLT F (I.r+I.w),
      ∀ i, (rowErrors (PolynomialDirect.primaryCode I.domain I.primary_le)
        (I.coreWords W i) S (g i)).card ≤ radius then
    if (S \ rowAgreement (PolynomialDirect.primaryCode I.domain I.primary_le) (I.coreWords W) h.choose).card ≤ radius ∧ I.layer.satisfies σ (I.coreWitness h.choose) then
      some h.choose else none
  else none

theorem recoverOnAt_valid (I : Instance F)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (S : Finset (Fin I.n)) (radius : ℕ)
    (g : (tupleCounts I).Index) (h : recoverOnAt I σ W S radius = some g) :
    I.layer.satisfies σ ((tupleCounts I).witness g) := by
  unfold recoverOnAt at h
  split_ifs at h with he hg
  cases Option.some.inj h
  exact hg.2

theorem recoverOnAt_eq_some (I : Instance F)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (S : Finset (Fin I.n)) (radius : ℕ)
    (hsize : I.r+I.w+2*radius ≤ S.card) (g : (tupleCounts I).Index)
    (hsat : I.layer.satisfies σ ((tupleCounts I).witness g))
    (hjoint : (S \ rowAgreement (PolynomialDirect.primaryCode I.domain I.primary_le) (I.coreWords W) g).card ≤ radius)
    (hnear : ∀ i, (rowErrors (PolynomialDirect.primaryCode I.domain I.primary_le)
      (I.coreWords W i) S (g i)).card ≤ radius) :
    recoverOnAt I σ W S radius = some g := by
  have he : ∃ f : Fin (Fintype.card (CoreRow I.nw I.nq)) → DegreeLT F (I.r+I.w),
      ∀ i, (rowErrors (PolynomialDirect.primaryCode I.domain I.primary_le)
        (I.coreWords W i) S (f i)).card ≤ radius := ⟨g, hnear⟩
  have hg : he.choose = g := by
    funext i
    have hleft := recoverRow_eq_some _ _ _ hsize _ (he.choose_spec i)
    have hright := recoverRow_eq_some _ _ _ hsize _ (hnear i)
    exact Option.some.inj (hleft.symm.trans hright)
  change I.layer.satisfies σ (I.coreWitness g) at hsat
  simp only [recoverOnAt, dif_pos he, hg, hjoint, hsat, and_self, ↓reduceIte]

/-- Every decoder satisfying the punctured-code contract gives the same
row-wise extractor, after the common-error and satisfaction checks. -/
theorem recoverOnAt_decoder (I : Instance F)
    (decoder : PuncturedDecoder
      (fun f : DegreeLT F (I.r+I.w) => fun j => (f : F[X]).eval
        ((PolynomialDirect.primaryCode I.domain I.primary_le).node j))
      (fun S radius => I.r+I.w+2*radius ≤ S.card))
    (σ : I.layer.Statement) (W : I.layer.Oracle) (S : Finset (Fin I.n)) (radius : ℕ)
    (hsize : I.r+I.w+2*radius ≤ S.card) (g : (tupleCounts I).Index) :
    recoverOnAt I σ W S radius = some g ↔
      I.layer.satisfies σ ((tupleCounts I).witness g) ∧
      (S \ rowAgreement (PolynomialDirect.primaryCode I.domain I.primary_le) (I.coreWords W) g).card ≤ radius ∧
      ∀ i, decoder.decode (I.coreWords W i) S radius = some (g i) := by
  constructor
  · intro h
    refine ⟨recoverOnAt_valid I σ W S radius g h, ?_⟩
    unfold recoverOnAt at h
    split_ifs at h with he hg
    cases Option.some.inj h
    refine ⟨hg.1, ?_⟩
    intro i
    exact decoder.complete _ _ _ hsize _ (he.choose_spec i)
  · rintro ⟨hsat, hjoint, hrows⟩
    exact recoverOnAt_eq_some I σ W S radius hsize g hsat hjoint
      (fun i => decoder.valid _ _ _ _ (hrows i))

/-- The specification decoder is one instance of the generic row-wise interface. -/
theorem recoverOnAt_rowwise (I : Instance F)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (S : Finset (Fin I.n)) (radius : ℕ)
    (hsize : I.r+I.w+2*radius ≤ S.card) (g : (tupleCounts I).Index) :
    recoverOnAt I σ W S radius = some g ↔
      I.layer.satisfies σ ((tupleCounts I).witness g) ∧
      (S \ rowAgreement (PolynomialDirect.primaryCode I.domain I.primary_le) (I.coreWords W) g).card ≤ radius ∧
      ∀ i, recoverRow (PolynomialDirect.primaryCode I.domain I.primary_le)
        (I.coreWords W i) S (I.r+I.w) radius = some (g i) :=
  recoverOnAt_decoder I (puncturedRowDecoder
    (PolynomialDirect.primaryCode I.domain I.primary_le) (I.r+I.w)) σ W S radius hsize g

noncomputable def scanRecoverAt (I : Instance F)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin)
    (response : I.layer.Payload) :
    Option (tupleCounts I).Index :=
  if globalCheck I.domain I.layout σ coin.1 response then
    let G := goodColumns I.domain (by have := I.primary_le; omega) I.primary_le
      I.layout σ W coin response
    if max (I.r+I.w+2*I.s+1) (2*(I.r+I.w)+I.s) ≤ G.card then
      recoverOnAt I σ W G I.s
    else none
  else none

theorem scanRecoverAt_valid (I : Instance F)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin)
    (response : I.layer.Payload)
    (g : (tupleCounts I).Index) (h : scanRecoverAt I σ W coin response = some g) :
    I.layer.satisfies σ ((tupleCounts I).witness g) := by
  unfold scanRecoverAt at h
  dsimp only at h
  split_ifs at h with hglobal hsize
  exact recoverOnAt_valid I σ W _ _ g h

/-- Every successful scan has one common error set of size at most `s`,
including on exceptional challenges. -/
theorem scanRecoverAt_columns (I : Instance F)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin)
    (response : I.layer.Payload) (g : (tupleCounts I).Index)
    (h : scanRecoverAt I σ W coin response = some g) :
    let G := goodColumns I.domain (by have := I.primary_le; omega) I.primary_le
      I.layout σ W coin response
    let D := rowAgreement (PolynomialDirect.primaryCode I.domain I.primary_le) (I.coreWords W) g
    (G \ D).card ≤ I.s ∧ G.card ≤ min I.n (D.card+I.s) ∧
      max (2*(I.r+I.w)) (I.r+I.w+I.s+1) ≤ D.card := by
  unfold scanRecoverAt at h
  dsimp only at h ⊢
  split_ifs at h with hglobal hsize
  unfold recoverOnAt at h
  split_ifs at h with he hg
  cases Option.some.inj h
  have hc := card_sdiff_add_card_inter
    (goodColumns I.domain (by have := I.primary_le; omega) I.primary_le I.layout σ W coin response)
    (rowAgreement (PolynomialDirect.primaryCode I.domain I.primary_le) (I.coreWords W) he.choose)
  have hi := card_le_card (inter_subset_right (s₁ :=
    goodColumns I.domain (by have := I.primary_le; omega) I.primary_le I.layout σ W coin response)
    (s₂ := rowAgreement (PolynomialDirect.primaryCode I.domain I.primary_le) (I.coreWords W) he.choose))
  have hn : (goodColumns I.domain (by have := I.primary_le; omega) I.primary_le I.layout σ W coin response).card ≤ I.n :=
    (card_le_univ _).trans_eq (Fintype.card_fin _)
  omega

end RecursivePolygero
