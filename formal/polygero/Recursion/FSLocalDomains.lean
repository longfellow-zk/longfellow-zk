import polygero.Recursion.AffineBlock
import Bcs.AffineSingleton

/-! The four list-fallback events own disjoint hash roles. The intercept
is the existing complete budget, but adaptive queries pay only the maximum
role price. This does not assume parent-envelope consumption. -/
namespace RecursivePolygero.FiatShamir.TwoLevel
open Finset ProfileAnalysis Bcs.AffineBlock Bcs.TotalOracle.Footprint
open scoped Classical
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {I : Instance F} (child : Child I)
variable (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)

def hashRole : HashInput child → Fin 4
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr (.inl _)) => 2
  | .inr (.inr (.inr _)) => 3

noncomputable def roleDomain (i : Fin 4) : Finset (HashInput child) :=
  univ.filter (fun x => hashRole child x = i)

theorem roleDomain_disjoint : Pairwise (fun i j =>
    Disjoint (roleDomain child i) (roleDomain child j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro x hi hj
  exact hij ((mem_filter.mp hi).2.symm.trans (mem_filter.mp hj).2)

noncomputable def roleRate : Fin 4 → Rate := ![
  Rate.diagonal (listError I p) (listError_nonneg I p),
  Rate.diagonal (cp.listBound * p.threshold) (mul_nonneg (Nat.cast_nonneg _) p.threshold_nonneg),
  Rate.diagonal (listError child.instance cp) (listError_nonneg child.instance cp),
  Rate.diagonal cp.threshold cp.threshold_nonneg]

noncomputable def roleFailure (sigma : I.layer.Statement) :
    Fin 4 → Proof child → (HashInput child → Answer child) → Prop := ![
  fun d H => rootEvent child p sigma (gamma d.1) H,
  fun d H => queryEvent child p cp sigma (query d.1 d.2.1) H,
  fun d H => childEvent child cp sigma (childGamma d.1 d.2.1 d.2.2.1) H,
  fun d H => terminalEvent child cp sigma (terminal d) H]

theorem role_oracle_sound (hp : p.listBound < Nat.card F) (hcp : cp.listBound < Nat.card F)
    (sigma : I.layer.Statement) (i : Fin 4) :
    OracleSound (roleDomain child i) (roleFailure child p cp sigma i) (roleRate child p cp i) := by
  fin_cases i
  · apply singleton_oracle_sound (roleDomain child 0) (fun d : Proof child => gamma d.1)
      (rootEvent child p sigma) (listError I p) (listError_nonneg I p)
      (rootEvent_local child p hp sigma)
    intro x H h
    rcases x with W | (wv | (wvq | d)) <;> simp_all [rootEvent, roleDomain, hashRole]
  · apply singleton_oracle_sound (roleDomain child 1) (fun d : Proof child => query d.1 d.2.1)
      (queryEvent child p cp sigma) (cp.listBound * p.threshold)
      (mul_nonneg (Nat.cast_nonneg _) p.threshold_nonneg)
      (queryEvent_local child p cp hcp sigma)
    intro x H h
    rcases x with W | (wv | (wvq | d)) <;> simp_all [queryEvent, roleDomain, hashRole]
  · apply singleton_oracle_sound (roleDomain child 2)
      (fun d : Proof child => childGamma d.1 d.2.1 d.2.2.1)
      (childEvent child cp sigma) (listError child.instance cp) (listError_nonneg child.instance cp)
      (childEvent_local child cp hcp sigma)
    intro x H h
    rcases x with W | (wv | (wvq | d)) <;> simp_all [childEvent, roleDomain, hashRole]
  · apply singleton_oracle_sound (roleDomain child 3) terminal
      (terminalEvent child cp sigma) cp.threshold cp.threshold_nonneg
      (terminalEvent_local child cp sigma)
    intro x H h
    rcases x with W | (wv | (wvq | d)) <;> simp_all [terminalEvent, roleDomain, hashRole]

theorem role_failure_cover (sigma : I.layer.Statement) (d : Proof child)
    (H : HashInput child → Answer child)
    (h : failure child p cp sigma (fun _ => False) H d) :
    ∃ i, roleFailure child p cp sigma i d H := by
  rcases failure_list_cover child p cp sigma H d h with h | h | h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩
  · exact ⟨2, h⟩
  · exact ⟨3, h⟩

/-- Closure as a local-domain certificate, reusable in larger compositions.
Every typed role is included, but the slope is the largest role price. -/
theorem fs_list_oracle_sound (hp : p.listBound < Nat.card F) (hcp : cp.listBound < Nat.card F)
    (sigma : I.layer.Statement) :
    OracleSound (univ.biUnion (roleDomain child))
      (fun d H => failure child p cp sigma (fun _ => False) H d)
      (aggregate (roleRate child p cp) (maxSlope (roleRate child p cp))
        (maxSlope_nonneg (roleRate child p cp))) :=
  oracle_parallel_certificate (roleDomain child) (roleFailure child p cp sigma)
    (roleRate child p cp) (role_oracle_sound child p cp hp hcp sigma)
    (fun d H => failure child p cp sigma (fun _ => False) H d)
    (role_failure_cover child p cp sigma) (roleDomain_disjoint child)
    (maxSlope (roleRate child p cp)) (maxSlope_nonneg (roleRate child p cp))
    (slope_le_maxSlope (roleRate child p cp))

theorem fs_list_affine_bound (hp : p.listBound < Nat.card F) (hcp : cp.listBound < Nat.card F)
    (sigma : I.layer.Statement) {N : ℕ}
    (tree : Merkle.RandomOracle.Tree (HashInput child) (Answer child) (Proof child) N) :
    Bcs.FiniteProbability.density (fun H => failure child p cp sigma (fun _ => False) H (tree.run H).1) ≤
      listBudget child p cp + N * maxSlope (roleRate child p cp) := by
  have h := oracle_parallel_max (roleDomain child) (roleFailure child p cp sigma)
    (roleRate child p cp) (role_oracle_sound child p cp hp hcp sigma)
    (fun d H => failure child p cp sigma (fun _ => False) H d)
    (role_failure_cover child p cp sigma) (roleDomain_disjoint child) tree
  simpa [roleRate, Rate.diagonal, Fin.sum_univ_succ, listBudget, add_assoc] using h

end RecursivePolygero.FiatShamir.TwoLevel
