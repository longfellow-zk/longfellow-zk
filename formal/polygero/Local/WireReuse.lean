import polygero.Protocol.Wire
import polygero.Recursion.FSInputs

/-! Reuse that survives the core-only recursive wire format. Varying one
committed core entry gives `|F|` different commitments while preserving
every opening and verification decision on queries avoiding that column.
For false statements this also preserves the extraction-failure weight.
No positive failure probability or impossibility of no-loss FS is asserted. -/

namespace RecursivePolygero.ProfileAnalysis

open Finset LigeroFamily Local.Polygero Counting
open scoped Classical

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

noncomputable def varyWireEntry (I : Instance F) (W : I.WireOracle false)
    (row : I.WireRow false) (col : Fin I.n) (c : F) : I.WireOracle false :=
  Function.update W row (Function.update (W row) col c)

omit [Fintype F] [DecidableEq F] in
theorem varyWireEntry_injective (I : Instance F) (W : I.WireOracle false)
    (row : I.WireRow false) (col : Fin I.n) :
    Function.Injective (varyWireEntry I W row col) := by
  intro c c' h
  have hh := congrArg (fun U : I.WireOracle false => U row col) h
  simpa only [varyWireEntry, Function.update_self] using hh

theorem varyWireEntry_opening (I : Instance F) (W : I.WireOracle false)
    (row : I.WireRow false) (col : Fin I.n) (c : F)
    (q : I.layer.Query) (hq : col ∉ q.coordinates) :
    openOracle (I.expandWireOracle false (varyWireEntry I W row col c)) q =
      openOracle (I.expandWireOracle false W) q := by
  rw [← I.wireOpening_eq false (varyWireEntry I W row col c) q, ← I.wireOpening_eq false W q]
  congr 1
  funext r j
  have hj : j.1 ≠ col := by intro h; exact hq (h ▸ j.2)
  by_cases hr : r = row
  · subst r
    simp [varyWireEntry, hj]
  · simp [varyWireEntry, hr]

theorem varyWireEntry_verify_iff (I : Instance F) (sigma : I.layer.Statement)
    (W : I.WireOracle false) (row : I.WireRow false) (col : Fin I.n) (c : F)
    (coin : I.layer.Coin) (R : I.layer.Payload) (q : I.layer.Query) (hq : col ∉ q.coordinates) :
    I.layer.verify sigma (I.expandWireOracle false (varyWireEntry I W row col c)) coin R q ↔
      I.layer.verify sigma (I.expandWireOracle false W) coin R q := by
  change verify _ _ _ _ _ _ _ _ = true ↔ verify _ _ _ _ _ _ _ _ = true
  rw [varyWireEntry_opening I W row col c q hq]

theorem query_avoids_mean (n t : ℕ) (col : Fin n) :
    mean (fun q : QuerySet n t => indicator (col ∉ q.coordinates)) =
      ((n-1).choose t : ℚ) / n.choose t := by
  rw [mean_indicator]
  calc
    _ = ((queriesWithin (r := t) (univ.erase col)).card : ℚ) / Fintype.card (QuerySet n t) := by
      apply congrArg (fun s : Finset (QuerySet n t) => (s.card : ℚ) / Fintype.card (QuerySet n t))
      ext q
      simp [queriesWithin, Finset.mem_filter, Finset.mem_attach, Finset.subset_erase]
    _ = _ := by rw [card_queriesWithin, QuerySet.fintype_card]; simp

end RecursivePolygero.ProfileAnalysis

namespace RecursivePolygero.FiatShamir.TwoLevel

open Finset ProfileAnalysis
open scoped Classical

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {I : Instance F} (child : Child I)

/-- This family stays in the actual unmasked child wire format. -/
theorem varied_wire_query_injective (W : I.layer.Oracle) (V : child.instance.WireOracle false)
    (row : child.instance.WireRow false) (col : Fin child.instance.n) :
    Function.Injective (fun c : F => (query W
      (child.instance.expandWireOracle false (varyWireEntry child.instance V row col c)) : HashInput child)) := by
  intro c c' h
  have he := congrArg Prod.snd (Sum.inl.inj (Sum.inr.inj h))
  apply varyWireEntry_injective child.instance V row col
  funext r j
  exact congrArg (fun U : child.instance.layer.Oracle => U.ordinary.core r.1 r.2 j) he

theorem varied_wire_query_count (W : I.layer.Oracle) (V : child.instance.WireOracle false)
    (row : child.instance.WireRow false) (col : Fin child.instance.n) :
    (univ.image (fun c : F => (query W
      (child.instance.expandWireOracle false (varyWireEntry child.instance V row col c)) : HashInput child))).card =
      Fintype.card F := by
  rw [card_image_of_injective _ (varied_wire_query_injective child W V row col), card_univ]

variable (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)

private theorem bad_eq_verify_of_false (sigma : I.layer.Statement)
    (hfalse : ∀ witness, ¬ I.layer.satisfies sigma witness)
    (d : Proof child) (coins : Coins child) :
    bad child p cp sigma (fun _ => False) d coins =
      indicator (executionVerify (Protocol.step child (.terminal child.instance)).chain
        sigma d.1 (constantMessages child d) coins = true) := by
  have hn : (twoProof child p cp).run sigma d.1 (constantMessages child d) coins = none := by
    cases he : (twoProof child p cp).run sigma d.1 (constantMessages child d) coins with
    | none => rfl
    | some g => exact (hfalse _ ((twoProof child p cp).run_valid _ _ _ _ g he)).elim
  simp only [bad, hn, Counting.outputHit, and_true]

/-- On a false parent statement, entry variation preserves the actual
accepting-extraction-failure weight on every terminal query avoiding the
modified column. No equality of extracted child labels is needed. -/
theorem bad_varyWireEntry_of_false (sigma : I.layer.Statement)
    (hfalse : ∀ witness, ¬ I.layer.satisfies sigma witness)
    (W : I.layer.Oracle) (V : child.instance.WireOracle false)
    (row : child.instance.WireRow false) (col : Fin child.instance.n) (c : F)
    (q : I.layer.Query) (R : child.instance.layer.Payload) (coins : Coins child)
    (havoid : col ∉ coins.2.2.coordinates) :
    bad child p cp sigma (fun _ => False)
        (W, child.instance.expandWireOracle false (varyWireEntry child.instance V row col c), q, R) coins =
      bad child p cp sigma (fun _ => False)
        (W, child.instance.expandWireOracle false V, q, R) coins := by
  rw [bad_eq_verify_of_false child p cp sigma hfalse,
    bad_eq_verify_of_false child p cp sigma hfalse]
  congr 1
  apply propext
  simp only [Protocol.chain, constantMessages, executionVerify, Bool.and_eq_true, decide_eq_true_eq]
  exact and_congr_right fun _ => varyWireEntry_verify_iff child.instance _ V row col c _ R _ havoid

noncomputable def avoidingBudget (sigma : I.layer.Statement)
    (W : I.layer.Oracle) (V : child.instance.WireOracle false)
    (col : Fin child.instance.n) (q : I.layer.Query) (R : child.instance.layer.Payload) : ℚ :=
  mean (fun coins : Coins child => if coins.1.2 = q ∧ col ∉ coins.2.2.coordinates then
    bad child p cp sigma (fun _ => False)
      (W, child.instance.expandWireOracle false V, q, R) coins else 0)

/-- A genuine wire-format load obstruction for whole-proof certificates,
conditional on positive avoiding-query failure mass. This is not a lower
bound on an adaptive adversary's success or a refutation of no-loss FS. -/
theorem root_load_ge_wire_orbit (sigma : I.layer.Statement)
    (hfalse : ∀ witness, ¬ I.layer.satisfies sigma witness)
    (W : I.layer.Oracle) (V : child.instance.WireOracle false)
    (row : child.instance.WireRow false) (col : Fin child.instance.n)
    (q : I.layer.Query) (R : child.instance.layer.Payload) :
    (Fintype.card F : ℚ) * avoidingBudget child p cp sigma W V col q R ≤
      load (budget child p cp sigma (fun _ => False)) (gamma W) := by
  let orbit : F → Proof child := fun c => (W,
    child.instance.expandWireOracle false (varyWireEntry child.instance V row col c), q, R)
  have hinj : Function.Injective orbit := by
    intro c c' h
    apply varied_wire_query_injective child W V row col
    exact congrArg (fun d : Proof child => query d.1 d.2.1) h
  have hb (c : F) : avoidingBudget child p cp sigma W V col q R ≤
      budget child p cp sigma (fun _ => False) (orbit c) := by
    apply mean_mono
    intro coins
    dsimp only [orbit]
    by_cases hq : coins.1.2 = q
    · by_cases ha : col ∉ coins.2.2.coordinates
      · simp only [hq, ha, if_true]
        exact (bad_varyWireEntry_of_false child p cp sigma hfalse W V row col c q R coins ha).ge
      · simp only [hq, ha, and_false, if_false, if_true]
        exact indicator_nonneg _
    · simp only [hq, false_and, if_false, le_refl]
  have he : (∑ c, budget child p cp sigma (fun _ => False) (orbit c)) =
      ∑ d ∈ univ.image orbit, if gamma W ∈ support d then
        budget child p cp sigma (fun _ => False) d else 0 := by
    rw [sum_image (fun _ _ _ _ h => hinj h)]
    apply sum_congr rfl
    intro c _
    simp [orbit, support]
  calc
    _ = ∑ _c : F, avoidingBudget child p cp sigma W V col q R := by simp
    _ ≤ ∑ c, budget child p cp sigma (fun _ => False) (orbit c) := sum_le_sum fun c _ => hb c
    _ ≤ _ := by
      rw [he]
      exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun d _ _ => by
        split_ifs
        · exact budget_nonneg child p cp sigma (fun _ => False) d
        · exact le_rfl)

end RecursivePolygero.FiatShamir.TwoLevel
