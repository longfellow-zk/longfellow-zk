import Lfzk.AffineForkAgreement
import Lfzk.AffineLocal
import Lfzk.V1StrongV7Hash1HybridNumeric

/-! The four-block fork allocation preserves the checked 116-bit envelope.
The numerical/composition theorem explicitly requires the failure cover
and four OracleSound certificates. It is not an end-to-end Merkle bridge
for the changed forked transcript. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Lfzk.AffineFork
open Finset Bcs.AffineBlock Bcs.TotalOracle Merkle.RandomOracle
open Lfzk.CertifiedV1 Lfzk.AffineSide Lfzk.V1StrongV7Hash1HybridNumeric
open scoped Classical

variable {Key Ctx Msg₁ Msg₂ : Type} {R₁ R₂ : Lfzk.CertifiedV1.Row}

def blockRole : Input Key Ctx Msg₁ Msg₂ R₁ R₂ → Fin 4
  | .inl _ => 3
  | .inr (.inl p) => if p.role.slot < Rounds.Role.layerBase R₁.params.rounds R₁.params.nl + 1 then 0 else 1
  | .inr (.inr _) => 2

noncomputable def blockDomain [Fintype Key] [Fintype Ctx] [Fintype Msg₁] [Fintype Msg₂]
    (i : Fin 4) : Finset (Input Key Ctx Msg₁ Msg₂ R₁ R₂) :=
  univ.filter (fun p => blockRole p = i)

theorem blockDomains_disjoint [Fintype Key] [Fintype Ctx] [Fintype Msg₁] [Fintype Msg₂] :
    Pairwise (fun i j => Disjoint
      (blockDomain (Key := Key) (Ctx := Ctx) (Msg₁ := Msg₁) (Msg₂ := Msg₂) (R₁ := R₁) (R₂ := R₂) i)
      (blockDomain (Key := Key) (Ctx := Ctx) (Msg₁ := Msg₁) (Msg₂ := Msg₂) (R₁ := R₁) (R₂ := R₂) j)) := by
  intro i j hn
  apply disjoint_left.mpr
  intro x hi hj
  exact hn ((mem_filter.mp hi).2.symm.trans (mem_filter.mp hj).2)

private theorem sigC_nonneg : 0 ≤ sigChallenge :=
  add_nonneg (Lfzk.LigeroV1LayerStep.fail_nonneg _) (Lfzk.LigeroV1LayerStep.arith_nonneg _)
private theorem sigQ_nonneg : 0 ≤ sigQuery := Lfzk.LigeroV1LayerStep.cover_nonneg _

noncomputable def hybridRates (cardC : ℕ) : Fin 4 → Rate := ![
  sideRate v7Hash1 3 cardC 0 0 (by norm_num) (by norm_num),
  Lfzk.AffineBlockInstances.ligeroRate 0,
  sideRate v7SigHahn 8 cardC (cardC * sigChallenge) (cardC * sigQuery)
    (mul_nonneg (Nat.cast_nonneg _) sigC_nonneg) (mul_nonneg (Nat.cast_nonneg _) sigQ_nonneg),
  Rate.diagonal (4 / 2^128) (by positivity)]

/-- The exact normalized side budgets fit the existing hybrid arithmetic;
no new numerical trust is introduced here. -/
theorem hybridRates_le (cardC : ℕ) (hC : 0 < cardC) :
    (∑ i, (hybridRates cardC i).intercept) ≤ coreUpper ∧
      ∀ i, (hybridRates cardC i).slope ≤ queryUpper := by
  have hh := sideRate_le_density v7Hash1 3 cardC hC (by decide)
    0 0 (by norm_num) (by norm_num)
    (Lfzk.NizkZk.zkCoefficient_nonneg _ _) (Lfzk.NizkZk.zkCoefficient_nonneg _ _)
  have hgrid := Lfzk.GradedCoreGrid.v7GradedCosts_le_coefficient (0 : Fin 4)
  have hs := sideRate_le_density v7SigHahn 8 cardC hC (by decide)
    sigChallenge sigQuery sigC_nonneg sigQ_nonneg hgrid.2.2.1 hgrid.2.2.2
  have hd := (Lfzk.V1StrongV7Numeric.density_lt_six (0 : Fin 4)).le
  simp only [mul_zero] at hh
  dsimp only at hh hs
  have hk0 : 0 ≤ max (max (v7Hash1.zkCoefficient 3) (v7SigHahn.zkCoefficient 8)) (4 / 2^128) :=
    (show (0 : ℚ) ≤ 4 / 2^128 by positivity).trans (le_max_right _ _)
  have hk1 := (le_max_left (v7Hash1.zkCoefficient 3) (v7SigHahn.zkCoefficient 8)).trans
    (le_max_left _ ((4 : ℚ) / 2^128))
  have hk2 := (le_max_right (v7Hash1.zkCoefficient 3) (v7SigHahn.zkCoefficient 8)).trans
    (le_max_left _ ((4 : ℚ) / 2^128))
  have hk3 := le_max_right (max (v7Hash1.zkCoefficient 3) (v7SigHahn.zkCoefficient 8)) ((4 : ℚ) / 2^128)
  constructor
  · simp only [hybridRates, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.sum_univ_zero, add_zero, Lfzk.AffineBlockInstances.ligeroRate, Rate.diagonal]
    unfold coreUpper
    linarith [hh.1, hs.1]
  · intro i
    fin_cases i
    · exact hh.2.trans (hk1.trans (le_add_of_nonneg_right (by positivity)))
    · exact hd.trans (le_add_of_nonneg_left hk0)
    · exact hs.2.trans (hk2.trans (le_add_of_nonneg_right (by positivity)))
    · exact hk3.trans (le_add_of_nonneg_right (by positivity))

/-- The local-domain composition introduces no extra security-bit loss.
All four certificates refer to one shared adaptive experiment. This
conditional interface isolates the remaining concrete transcript cover. -/
theorem hybrid_bound_116
    {Hash C Out : Type} [Fintype Hash] [DecidableEq Hash] [Fintype C] [Nonempty C]
    (domains : Fin 4 → Finset Hash)
    (events : Fin 4 → Out → (Hash → C) → Prop)
    (cert : ∀ i, OracleSound (domains i) (events i) (hybridRates (Fintype.card C) i))
    (failure : Out → (Hash → C) → Prop)
    (cover : ∀ out H, failure out H → ∃ i, events i out H)
    (hd : Pairwise (fun i j => Disjoint (domains i) (domains j)))
    {N : ℕ} (tree : Tree Hash C Out N) :
    Bcs.FiniteProbability.density (fun H => failure (tree.run H).1 H) ≤
      (1 + N : ℚ) / 2^116 := by
  have hb := hybridRates_le (Fintype.card C) Fintype.card_pos
  have hq : 0 ≤ queryUpper := ((hybridRates _ 0).slope_nonneg).trans (hb.2 0)
  have h := oracle_parallel domains events (hybridRates (Fintype.card C)) cert failure cover hd
    queryUpper hq hb.2 tree
  have he := Lfzk.V1StrongV7Hash1HybridNumeric.rhs_le_116 N 0 (by positivity)
  have hm : 0 ≤ 2 * (Bcs.AdaptiveCommit.adaptiveNumerator fc 0 (L + N) : ℚ) / 2^256 := by positivity
  norm_num only [Nat.cast_zero, add_zero] at he
  linarith [hb.1]

/-- Numerical room for the original-size adaptive commitment reduction.
The caller must separately establish this reduction for its forked setup. -/
theorem hybrid_bound_with_commit_116
    {Hash C Out : Type} [Fintype Hash] [DecidableEq Hash] [Fintype C] [Nonempty C]
    (domains : Fin 4 → Finset Hash)
    (events : Fin 4 → Out → (Hash → C) → Prop)
    (cert : ∀ i, OracleSound (domains i) (events i) (hybridRates (Fintype.card C) i))
    (failure : Out → (Hash → C) → Prop)
    (cover : ∀ out H, failure out H → ∃ i, events i out H)
    (hd : Pairwise (fun i j => Disjoint (domains i) (domains j)))
    {N : ℕ} (tree : Tree Hash C Out N) (tA : ℕ) (htA : tA ≤ 2^116) :
    Bcs.FiniteProbability.density (fun H => failure (tree.run H).1 H) +
      2 * (Bcs.AdaptiveCommit.adaptiveNumerator fc tA (L + N) : ℚ) / 2^256 ≤
      (1 + N + tA : ℚ) / 2^116 := by
  have hb := hybridRates_le (Fintype.card C) Fintype.card_pos
  have hq : 0 ≤ queryUpper := ((hybridRates _ 0).slope_nonneg).trans (hb.2 0)
  have h := oracle_parallel domains events (hybridRates (Fintype.card C)) cert failure cover hd
    queryUpper hq hb.2 tree
  have he := Lfzk.V1StrongV7Hash1HybridNumeric.rhs_le_116 N tA htA
  linarith [hb.1]

end Lfzk.AffineFork
