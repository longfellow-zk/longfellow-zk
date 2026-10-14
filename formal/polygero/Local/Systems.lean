import polygero.Local.FullConsistency
import polygero.Algebra.PolynomialChallenges.CutoffChallenges

/-! System exceptions for the fixed reduced systems. Proper systems use
primary consistency; fully consistent systems use arithmetic cancellation. -/
namespace RecursivePolygero.ProfileAnalysis
open Polynomial Finset Codes LigeroFamily Local Local.Polygero
open LigeroFamily.PolynomialDirect (primaryCode decodedLinearResidual decodedZRMaskSum)
attribute [local instance] Classical.propDecidable
variable {F Equations : Type} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Equations] [DecidableEq Equations]
variable {q r w n nw nq s : ℕ}
variable (D : ReedSolomon.Domain F r w n) (hprimary : r+w+s ≤ n)
variable (oracle : Oracle F nw nq n)

noncomputable abbrev systems := ReducedSystems.family (primaryCode D hprimary)
  (oracleWords oracle.ordinary) oracle.proximityMask

variable {D hprimary oracle}

omit [Fintype F] [DecidableEq F] in
theorem geometry (d : systems D hprimary oracle) :
    ReducedSystems.Geometry (primaryCode D hprimary) (oracleWords oracle.ordinary)
      oracle.proximityMask d.1 :=
  ReducedSystems.geometry _ _ _ d.1 d.2

noncomputable def rows (hk : 1 ≤ r+w)
    (d : systems D hprimary oracle)
    (hfull : Affine.consistent (primaryCode D hprimary) (oracleWords oracle.ordinary)
      oracle.proximityMask d.1 = univ) : Fin (rowCount nw nq) → DegreeLT F (r+w) :=
  Classical.choose (Classical.choose_spec (affine_rows_of_full_consistency _ _ _ d.1 hk
    (by have := (geometry d).core.large; omega) hfull))

theorem rows_spec (hk : 1 ≤ r+w)
    (d : systems D hprimary oracle)
    (hfull : Affine.consistent (primaryCode D hprimary) (oracleWords oracle.ordinary)
      oracle.proximityMask d.1 = univ) :
    ∀ i j, j ∈ d.1 → oracleWords oracle.ordinary i j =
      (rows hk d hfull i : F[X]).eval ((primaryCode D hprimary).node j) :=
  (Classical.choose_spec (Classical.choose_spec (affine_rows_of_full_consistency _ _ _ d.1 hk
    (by have := (geometry d).core.large; omega) hfull))).2

noncomputable def systemExceptions (hk : 1 ≤ r+w)
    (layout : ConstraintLayout F q w) (statement : ConstraintSystem F nw nq q Equations)
    (d : systems D hprimary oracle) : Finset (Coin F Equations nw nq s) :=
  if hfull : Affine.consistent (primaryCode D hprimary) (oracleWords oracle.ordinary)
      oracle.proximityMask d.1 = univ then
    if decodedLinearResidual D layout statement (extendRows (rows hk d hfull)) = 0 then ∅
    else (affineEquationSolutions
      (decodedLinearResidual D layout statement (extendRows (rows hk d hfull)))
      (-decodedZRMaskSum D layout (extendRows (rows hk d hfull)))) ×ˢ univ
  else univ ×ˢ Affine.consistent (primaryCode D hprimary) (oracleWords oracle.ordinary)
    oracle.proximityMask d.1

theorem systemExceptions_card (hk : 1 ≤ r+w)
    (layout : ConstraintLayout F q w) (statement : ConstraintSystem F nw nq q Equations)
    (d : systems D hprimary oracle) :
    (systemExceptions hk layout statement d).card*Nat.card F ≤ Nat.card (Coin F Equations nw nq s) := by
  unfold systemExceptions
  split_ifs with hfull hres
  · simp
  · have ha := polynomialArithmeticMatches_card (D := D) layout statement (rows hk d hfull) hres
    simpa only [card_product,card_univ,Nat.card_eq_fintype_card,Fintype.card_prod,
      mul_assoc,mul_comm,mul_left_comm] using
      Nat.mul_le_mul_right (Fintype.card (Challenge F (rowCount nw nq) s)) ha
  · have ha := Affine.consistent_card_mul_field_le_of_proper (primaryCode D hprimary)
      (oracleWords oracle.ordinary) oracle.proximityMask d.1 hfull
    simpa only [card_product,card_univ,Nat.card_eq_fintype_card,Fintype.card_prod,
      mul_assoc] using Nat.mul_le_mul_left (Fintype.card (Equations → F)) ha

/-- An assigned but nonexceptional system certifies a satisfying tuple. Polynomial
identities are proved on its intersection with the actual good columns. -/
theorem certify (hk : 1 ≤ r+w)
    (layout : ConstraintLayout F q w) (statement : ConstraintSystem F nw nq q Equations)
    (d : systems D hprimary oracle)
    (coin : Coin F Equations nw nq s) (payload : LigeroPayload F (r+w) s)
    (hp : (coin.2,payload.primary) ∈ ConsistencyClosure.solutions
      (PolynomialClosure.jointMap (primaryCode D hprimary) (oracleWords oracle.ordinary))
      oracle.proximityMask d.1)
    (hout : coin ∉ systemExceptions hk layout statement d)
    (hglobal : globalCheck D layout statement coin.1 payload)
    (hlarge : 2*(r+w)+s ≤
      (goodColumns D (by omega) hprimary layout statement oracle coin payload).card)
    (herr : ((goodColumns D (by omega) hprimary layout statement oracle coin payload) \ d.1).card ≤ s) :
    ∃ hfull : Affine.consistent (primaryCode D hprimary) (oracleWords oracle.ordinary)
      oracle.proximityMask d.1 = univ,
    statement.Satisfies (rowWitness (D := D) layout (rows hk d hfull)) ∧
      (∀ i j, j ∈ d.1 → oracleWords oracle.ordinary i j =
        (rows hk d hfull i : F[X]).eval ((primaryCode D hprimary).node j)) := by
  have hfull : Affine.consistent (primaryCode D hprimary) (oracleWords oracle.ordinary)
      oracle.proximityMask d.1 = univ := by
    contrapose! hout with hn
    rw [systemExceptions,dif_neg hn]
    exact mem_product.mpr ⟨mem_univ _,mem_filter.mpr ⟨mem_univ _,
      (PolynomialClosure.exists_joint_iff _ _ _ _ coin.2).mp ⟨payload.primary,hp⟩⟩⟩
  refine ⟨hfull, ?_⟩
  let f := rows hk d hfull
  let G := goodColumns D (by omega) hprimary layout statement oracle coin payload
  have hrows := rows_spec hk d hfull
  have hsize : 2*(r+w) ≤ (G ∩ d.1).card := by
    have h := card_sdiff_add_card_inter G d.1
    change (G \ d.1).card ≤ s at herr
    change 2*(r+w)+s ≤ G.card at hlarge
    omega
  obtain ⟨hcanonical,hproducts⟩ := identities_of_agreement (by omega) layout statement coin payload
    f (G ∩ d.1) hk hsize inter_subset_left (fun i j hj => hrows i j (mem_inter.mp hj).2)
  have hprod : ∀ g : Fin nq,
      (extendRows (V := DegreeLT F (r+w)) f (PolynomialDirect.leftIndex g) : F[X]) *
        (extendRows (V := DegreeLT F (r+w)) f (PolynomialDirect.rightIndex g) : F[X]) =
      (extendRows (V := DegreeLT F (r+w)) f (PolynomialDirect.outputIndex g) : F[X]) := by
    simpa only [PolynomialDirect.leftIndex,PolynomialDirect.rightIndex,PolynomialDirect.outputIndex,
      extendRows_core,leftIndex,rightIndex,outputIndex] using hproducts
  have hres : decodedLinearResidual D layout statement (extendRows f) = 0 := by
    contrapose! hout with hn
    have hc := candidateTests_of_checks D (by omega) hprimary layout statement coin.1 payload f
      hglobal hcanonical hproducts
    have hc' : coin.1 ∈ affineEquationSolutions
        (decodedLinearResidual D layout statement (extendRows f))
        (-decodedZRMaskSum D layout (extendRows f)) := by
      simpa only [candidateTests,PolynomialDirect.ListSoundness.candidateTests,if_pos hprod] using hc
    rw [systemExceptions,dif_pos hfull,if_neg hn]
    exact mem_product.mpr ⟨hc',mem_univ _⟩
  refine ⟨⟨?_,PolynomialDirect.decodedMessages_quadratic D layout (extendRows f) hprod⟩,hrows⟩
  intro e
  exact sub_eq_zero.mp (congrFun hres e)

end RecursivePolygero.ProfileAnalysis
