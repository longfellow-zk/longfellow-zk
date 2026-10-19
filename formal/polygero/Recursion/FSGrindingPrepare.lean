import polygero.Recursion.FSGrindingTree

/-! The preparation interface for the concrete three-region grinding
construction. A favorable root coin chooses one fixed payload and one
fixed parent-query region, before any child-query answer is sampled. -/

namespace RecursivePolygero.FiatShamir.TwoLevel
open Finset Codes Polynomial ProfileAnalysis Local Local.Polygero LigeroFamily
open scoped Classical

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {I : Instance F}

section Prepare
variable (sigma : I.layer.Statement) (roots : F → I.layer.Oracle)
  (payload : I.layer.Coin → Fin 3 → I.layer.Payload)
  (eligible : I.layer.Coin → Fin 3 → Prop)
  (good : Fin 3 → I.layer.Query → Prop)
  (hparent : ∀ c coin i, eligible coin i → ∀ Q, good i Q →
    I.layer.verify sigma (roots c) coin (payload coin i) Q)

noncomputable def regionPrepare (W : I.layer.Oracle) (coin : I.layer.Coin) :
    Option (GrindingReady sigma W coin) :=
  if hw : ∃ c, roots c = W then
    if hi : ∃ i, eligible coin i then
      some ⟨payload coin (Classical.choose hi), good (Classical.choose hi), by
        intro Q hQ
        rw [← Classical.choose_spec hw]
        exact hparent (Classical.choose hw) coin (Classical.choose hi)
          (Classical.choose_spec hi) Q hQ⟩
    else none
  else none

theorem regionPrepare_root_isSome (c : F) (coin : I.layer.Coin) :
    (regionPrepare sigma roots payload eligible good hparent (roots c) coin).isSome = true ↔
      ∃ i, eligible coin i := by
  unfold regionPrepare
  split_ifs with hw hi
  · simp only [Option.isSome_some, true_iff]
    exact hi
  · simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    exact hi
  · exact (hw ⟨c, rfl⟩).elim

/-- Every returned certificate has the same good-query probability, even
though the selected region depends on the observed root coin. -/
theorem regionPrepare_good_mean (rho : ℚ)
    (hgood : ∀ i, mean (fun Q => indicator (good i Q)) = rho)
    (W : I.layer.Oracle) (coin : I.layer.Coin) (ready : GrindingReady sigma W coin)
    (hready : regionPrepare sigma roots payload eligible good hparent W coin = some ready) :
    mean (fun Q => indicator (ready.goodQueries Q)) = rho := by
  unfold regionPrepare at hready
  split_ifs at hready with hw hi
  · have he := Option.some.inj hready
    subst ready
    exact hgood (Classical.choose hi)

theorem regionPrepare_root_mean (mu : ℚ)
    (hcoin : mean (fun coin => indicator (∃ i, eligible coin i)) = mu) (c : F) :
    mean (fun coin => indicator
      ((regionPrepare sigma roots payload eligible good hparent (roots c) coin).isSome = true)) = mu := by
  convert hcoin using 1
  apply mean_congr
  intro coin
  congr 1
  exact propext (regionPrepare_root_isSome sigma roots payload eligible good hparent c coin)

end Prepare

/-- A genuine core-only family of parent commitments. The selected entry
is part of every commitment; no transcript padding is used. -/
noncomputable def wireRoots (I : Instance F) (base : I.WireOracle false)
    (row : I.WireRow false) (col : Fin I.n) (c : F) : I.layer.Oracle :=
  I.expandWireOracle false (varyWireEntry I base row col c)

theorem wireRoots_injective (I : Instance F) (base : I.WireOracle false)
    (row : I.WireRow false) (col : Fin I.n) :
    Function.Injective (wireRoots I base row col) := by
  intro c c' he
  have h := congrArg (fun W : I.layer.Oracle => W.ordinary.core row.1 row.2 col) he
  cases row
  simpa only [wireRoots, Instance.expandWireOracle, varyWireEntry,
    Function.update_self] using h

/-- A spare-column family preserves every parent acceptance in a region
that excludes that column. -/
theorem wireRoots_parent_accepts (I : Instance F) (base : I.WireOracle false)
    (row : I.WireRow false) (col : Fin I.n) (c : F) (sigma : I.layer.Statement)
    (coin : I.layer.Coin) (payload : I.layer.Payload) (Q : I.layer.Query)
    (havoid : col ∉ Q.coordinates)
    (hv : I.layer.verify sigma (I.expandWireOracle false base) coin payload Q) :
    I.layer.verify sigma (wireRoots I base row col c) coin payload Q :=
  (varyWireEntry_verify_iff I sigma base row col c coin payload Q havoid).mpr hv

section Mixture
open GrindingAlgebra
variable {q r w n : ℕ} (D : ReedSolomon.Domain F r w n)
  (layout : ConstraintLayout F q w) (d s t : ℕ) (hprimary : r+w+s ≤ n)
  (hquery : t ≤ n) (hk : 1 ≤ r+w) (j : Slots d q)
  (g : DegreeLT F (r+w))
  (hg : (g : Polynomial F).eval (D.point (logicalWitnessPosition layout j.2)) = 1)
  (label : Fin n → F) (values : Fin 3 → F) (regions : Fin 3 → Finset (Fin n))
  (spare : Fin n)
  (hregions : ∀ i col, col ∈ regions i →
    label col = values i ∨ (g : Polynomial F).eval (D.point (codePosition col)) = 0)
  (hspare : ∀ i, spare ∉ regions i)

local notation "I₀" => linearInstance D layout d s t hprimary hquery

noncomputable def mixtureRoots (c : F) : (I₀).layer.Oracle :=
  wireRoots I₀ ((I₀).compressWireOracle false (mixtureOracle D j.1 g label))
    ⟨.linear,j.1⟩ spare c

theorem mixtureRoots_injective :
    Function.Injective (mixtureRoots D layout d s t hprimary hquery j g label spare) :=
  wireRoots_injective I₀ _ _ spare

include hg hregions hspare in
/-- The region preparation premise is discharged by actual Polygero
algebra and actual spare-entry variation. -/
theorem mixtureRoots_parent (c : F) (coin : (I₀).layer.Coin) (i : Fin 3)
    (he : (coin.1 false, coin.1 true) ∈ exceptionLine (values i))
    (Q : (I₀).layer.Query) (hQ : Q.coordinates ⊆ regions i) :
    (I₀).layer.verify (contradictoryStatement j)
      (mixtureRoots D layout d s t hprimary hquery j g label spare c) coin
      (canonicalPayload I₀ hk (contradictoryStatement j) coin (candidateRows j.1 g (values i))) Q := by
  apply wireRoots_parent_accepts
  · exact fun hc => hspare i (hQ hc)
  · rw [mixtureOracle_wire]
    apply mixture_accepts D layout d s t hprimary hquery hk j g hg label (values i) coin
    · exact (mem_filter.mp he).2
    · intro col hc
      exact hregions i col (hQ hc)

noncomputable def mixturePrepare : ∀ (W : (I₀).layer.Oracle) (coin : (I₀).layer.Coin),
    Option (GrindingReady (I := I₀) (contradictoryStatement j) W coin) :=
  regionPrepare (I := I₀) (contradictoryStatement j)
    (mixtureRoots D layout d s t hprimary hquery j g label spare)
    (fun coin i => canonicalPayload I₀ hk (contradictoryStatement j) coin (candidateRows j.1 g (values i)))
    (fun coin i => (coin.1 false, coin.1 true) ∈ exceptionLine (values i))
    (fun i Q => Q.coordinates ⊆ regions i)
    (mixtureRoots_parent D layout d s t hprimary hquery hk j g hg label values regions spare hregions hspare)

local notation "prepare₀" => mixturePrepare D layout d s t hprimary hquery hk j g hg
  label values regions spare hregions hspare

theorem mixturePrepare_root_isSome (c : F) (coin : (I₀).layer.Coin) :
    (prepare₀ (mixtureRoots D layout d s t hprimary hquery j g label spare c) coin).isSome = true ↔
      ∃ i, (coin.1 false, coin.1 true) ∈ exceptionLine (values i) := by
  unfold mixturePrepare
  apply regionPrepare_root_isSome

theorem mixturePrepare_good_mean (rho : ℚ)
    (hrho : ∀ i, mean (fun Q : QuerySet n t => indicator (Q.coordinates ⊆ regions i)) = rho)
    (W : (I₀).layer.Oracle) (coin : (I₀).layer.Coin)
    (ready : GrindingReady (I := I₀) (contradictoryStatement j) W coin)
    (hready : prepare₀ W coin = some ready) :
    mean (fun Q => indicator (ready.goodQueries Q)) = rho := by
  unfold mixturePrepare at hready
  exact regionPrepare_good_mean (I := I₀) _ _ _ _ _ _ rho hrho W coin ready hready

end Mixture

open GrindingAlgebra
theorem three_regions_eligible_mean (d s : ℕ) (values : Fin 3 → F)
    (hv : Function.Injective values) :
    mean (fun coin : Coin F Bool d 0 s => indicator
      (∃ i : Fin 3, (coin.1 false, coin.1 true) ∈ exceptionLine (values i))) =
      3 / (Fintype.card F : ℚ) - 2 / (Fintype.card F : ℚ)^2 := by
  have he (coin : Coin F Bool d 0 s) :
      (∃ i : Fin 3, (coin.1 false, coin.1 true) ∈ exceptionLine (values i)) ↔
      (coin.1 false, coin.1 true) ∈
        (exceptionLine (values 0) ∪ exceptionLine (values 1)) ∪ exceptionLine (values 2) := by
    simp only [mem_union]
    constructor
    · rintro ⟨i,hi⟩
      fin_cases i
      · exact Or.inl (Or.inl hi)
      · exact Or.inl (Or.inr hi)
      · exact Or.inr hi
    · rintro ((h | h) | h)
      · exact ⟨0,h⟩
      · exact ⟨1,h⟩
      · exact ⟨2,h⟩
  have h01 : values 0 ≠ values 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (hv h)
  have h02 : values 0 ≠ values 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (hv h)
  have h12 : values 1 ≠ values 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (hv h)
  convert three_coin_exceptions_mean d s (values 0) (values 1) (values 2) h01 h02 h12 using 1
  apply mean_congr
  intro coin
  congr 1
  exact propext (he coin)

end RecursivePolygero.FiatShamir.TwoLevel
