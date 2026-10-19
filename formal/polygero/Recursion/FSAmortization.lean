import polygero.Recursion.FSInputs

/-!
# The exact parent-charge obligation for two-level Polygero

The parent footprint is the entire typed hash namespace carrying `W`.
Its first hit is fresh even when a descendant input is queried first.
The local envelope and the load of these parent footprints are proved
here. Consumption of the parent potential by grouped seam certificates
remains an explicit hypothesis; the scalar mean does not imply it.
-/

namespace RecursivePolygero.FiatShamir.TwoLevel

open Finset ProfileAnalysis Bcs.TotalOracle.Footprint Merkle.RandomOracle
open scoped Classical

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {I : Instance F} (child : Child I)
variable (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)

/-- All descendants, as well as the root challenge input itself. -/
noncomputable def rootFiber (w : I.layer.Oracle) : Finset (HashInput child) :=
  univ.filter (fun x => root x = w)

theorem gamma_mem_rootFiber (w : I.layer.Oracle) :
    gamma w ∈ rootFiber child w := by simp [rootFiber, root, gamma]

/-- Every actual hash point charges exactly one parent namespace. -/
theorem rootFiber_load (x : HashInput child) (kappa : ℚ) :
    (∑ w : I.layer.Oracle, if x ∈ rootFiber child w then kappa else 0) = kappa := by
  simp [rootFiber]

noncomputable def parentPotential (sigma : I.layer.Statement)
    (w : I.layer.Oracle) (H : HashInput child → Answer child) : ℚ :=
  (1 - cp.error) * localEnvelope I p.toProfileParameters sigma w p.threshold
    (fun _ => False) (H (gamma w)).1.1

/-- The actual parent envelope can be charged at the first query anywhere
in its namespace. This proves freshness and its price, but not reuse. -/
theorem parentPotential_local (sigma : I.layer.Statement) (w : I.layer.Oracle)
    (off : Outside (rootFiber child w) → Answer child) :
    average (fun on => parentPotential child p cp sigma w
      ((split (rootFiber child w)).symm (on, off))) ≤ (1 - cp.error) * p.error := by
  let x : Inside (rootFiber child w) := ⟨gamma w, gamma_mem_rootFiber child w⟩
  let f : Answer child → ℚ := fun c => (1 - cp.error) *
    localEnvelope I p.toProfileParameters sigma w p.threshold (fun _ => False) c.1.1
  have he (on : Inside (rootFiber child w) → Answer child) :
      parentPotential child p cp sigma w ((split (rootFiber child w)).symm (on, off)) =
        f (on x) := by
    have hi := congrArg Prod.fst
      ((split (C := Answer child) (rootFiber child w)).apply_symm_apply (on, off))
    have hx : (split (rootFiber child w)).symm (on, off) (gamma w) = on x := congrFun hi x
    simp only [parentPotential, hx, f, x]
  simp_rw [he]
  rw [average_eval x f]
  change mean f ≤ _
  simp only [f, mean_prod, mean_const, mean_mul_left]
  have hp := localEnvelope_mean_of_hahn (Z := Unit) I p (fun _ => sigma) w 0
    (by norm_num) (by norm_num) (fun _ _ => False) (by intro g; simp [indicator])
  simp only [mean_const, mul_zero, add_zero] at hp
  exact mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr cp.error_lt_one.le)

/-- Conditional sharp compiler with the actual Polygero parent potentials.
The child certificates must cover extraction failure and admit the displayed
pathwise consumption inequality. In particular, paying a separate copy of
the incoming envelope at every child attempt does not discharge `hcharge`.
Any proper-system residual must already be covered and paid here. -/
theorem fs_no_loss_of_parent_charge
    {J : Type} [Fintype J] {N : ℕ}
    (sigma : I.layer.Statement) (tree : Tree (HashInput child) (Answer child) (Proof child) N)
    (supports : J → Finset (HashInput child))
    (weights : J → (HashInput child → Answer child) → ℚ)
    (budgets : ∀ j, (Outside (supports j) → Answer child) → ℚ)
    (event : (HashInput child → Answer child) → Prop)
    (hweight : ∀ j H, 0 ≤ weights j H)
    (hlocal : ∀ j off, average (fun on =>
      weights j ((split (supports j)).symm (on, off))) ≤ budgets j off)
    (hcover : ∀ H, event H → 1 ≤ ∑ j,
      if hits (Bcs.TotalOracle.appendFinalQuery tree terminal) H (supports j)
        then weights j H else 0)
    (hcharge : ∀ H,
      (∑ j, if hits (Bcs.TotalOracle.appendFinalQuery tree terminal) H (supports j)
        then budgets j (fun z => H z.1) else 0) ≤
      (N + 1) * cp.error + ∑ w : I.layer.Oracle,
        if hits (Bcs.TotalOracle.appendFinalQuery tree terminal) H (rootFiber child w)
          then parentPotential child p cp sigma w H else 0) :
    Bcs.FiniteProbability.density event ≤ (N + 1) * twoError p.error cp.error := by
  have hn : 0 ≤ (1 - cp.error) * p.error :=
    mul_nonneg (sub_nonneg.mpr cp.error_lt_one.le) p.error_nonneg
  have h := event_le_of_parent_charge tree terminal supports weights budgets
    (rootFiber child) (parentPotential child p cp sigma) (fun _ => (1 - cp.error) * p.error)
    event ((N + 1) * cp.error) ((1 - cp.error) * p.error) ((1 - cp.error) * p.error)
    hweight hlocal hcover hcharge (parentPotential_local child p cp sigma)
    (fun _ => hn) hn
    (fun x => le_of_eq (rootFiber_load child x _))
    (fun out => le_of_eq (rootFiber_load child (terminal out) _))
  convert h using 1
  unfold twoError
  ring

end RecursivePolygero.FiatShamir.TwoLevel
