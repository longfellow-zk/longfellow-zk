import polygero.Recursion.FSTransfer

/-!
# A typed, non-reabsorbing two-level FS transcript

The public statement/context is fixed throughout this module. Commitments
are represented by their uniquely determined oracles. A parent opening is
canonical and includes its query positions, so its transcript key is `q`.
This specifies an ideal transform, not a byte serializer or a Merkle theorem.
Challenges are not reabsorbed. The four tags are disjoint constructors.
-/

namespace RecursivePolygero.FiatShamir.TwoLevel

open Finset ProfileAnalysis SystemException Bcs.TotalOracle.Footprint
open scoped Classical

abbrev Candidate (W V Q R : Type) := W × V × Q × R
abbrev Input (W V Q R : Type) := W ⊕ ((W × V) ⊕ ((W × V × Q) ⊕ Candidate W V Q R))

variable {W V Q R : Type}

def gamma (w : W) : Input W V Q R := .inl w
def query (w : W) (v : V) : Input W V Q R := .inr (.inl (w, v))
def childGamma (w : W) (v : V) (q : Q) : Input W V Q R := .inr (.inr (.inl (w, v, q)))
def terminal (d : Candidate W V Q R) : Input W V Q R := .inr (.inr (.inr d))

def root : Input W V Q R → W
  | .inl w => w
  | .inr (.inl wv) => wv.1
  | .inr (.inr (.inl wvq)) => wvq.1
  | .inr (.inr (.inr d)) => d.1

noncomputable def support (d : Candidate W V Q R) : Finset (Input W V Q R) :=
  {gamma d.1, query d.1 d.2.1, childGamma d.1 d.2.1 d.2.2.1, terminal d}

theorem terminal_mem (d : Candidate W V Q R) : terminal d ∈ support d := by
  simp [support]

theorem root_eq_of_mem (d : Candidate W V Q R) (x : Input W V Q R)
    (h : x ∈ support d) : root x = d.1 := by
  simp only [support, mem_insert, mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl <;> rfl

/-- Four independent answers, with all other answers held out. -/
noncomputable def supportEquiv (d : Candidate W V Q R) (C : Type) :
    (Inside (support d) → C) ≃ (C × C × C × C) where
  toFun h := (h ⟨gamma d.1, by simp [support]⟩,
    h ⟨query d.1 d.2.1, by simp [support]⟩,
    h ⟨childGamma d.1 d.2.1 d.2.2.1, by simp [support]⟩,
    h ⟨terminal d, terminal_mem d⟩)
  invFun c x := if x.1 = gamma d.1 then c.1 else
    if x.1 = query d.1 d.2.1 then c.2.1 else
    if x.1 = childGamma d.1 d.2.1 d.2.2.1 then c.2.2.1 else c.2.2.2
  left_inv h := by
    funext x
    obtain ⟨x, hx⟩ := x
    simp only [support, mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;>
      simp [gamma, query, childGamma, terminal]
  right_inv c := by simp [gamma, query, childGamma, terminal]

section Loads

variable [Fintype W] [Fintype V] [Fintype Q] [Fintype R]

noncomputable def load (budget : Candidate W V Q R → ℚ) (x : Input W V Q R) : ℚ :=
  ∑ d, if x ∈ support d then budget d else 0

theorem load_gamma (budget : Candidate W V Q R → ℚ) (w : W) :
    load budget (gamma w) = ∑ v, ∑ q, ∑ r, budget (w, v, q, r) := by
  simp [load, support, gamma, query, childGamma, terminal, Fintype.sum_prod_type]
  rw [sum_eq_single w]
  · simp
  · intro w' _ h; simp [Ne.symm h]
  · simp

theorem load_query (budget : Candidate W V Q R → ℚ) (w : W) (v : V) :
    load budget (query w v) = ∑ q, ∑ r, budget (w, v, q, r) := by
  simp [load, support, gamma, query, childGamma, terminal, Fintype.sum_prod_type,
    Prod.mk.injEq, ite_and]
  rw [sum_eq_single v]
  · simp
  · intro v' _ h; simp [Ne.symm h]
  · simp

theorem load_childGamma (budget : Candidate W V Q R → ℚ) (w : W) (v : V) (q : Q) :
    load budget (childGamma w v q) = ∑ r, budget (w, v, q, r) := by
  simp [load, support, gamma, query, childGamma, terminal, Fintype.sum_prod_type,
    Prod.mk.injEq, ite_and]
  rw [sum_eq_single q]
  · simp
  · intro q' _ h; simp [Ne.symm h]
  · simp

theorem load_terminal (budget : Candidate W V Q R → ℚ) (d : Candidate W V Q R) :
    load budget (terminal d) = budget d := by
  simp [load, support, gamma, query, childGamma, terminal]

theorem load_le_root (budget : Candidate W V Q R → ℚ) (hn : ∀ d, 0 ≤ budget d)
    (x : Input W V Q R) : load budget x ≤ load budget (gamma (root x)) := by
  apply sum_le_sum
  intro d _
  by_cases hx : x ∈ support d
  · have hr : gamma (root x) ∈ support d := by rw [root_eq_of_mem d x hx]; simp [support]
    simp [hx, hr]
  · simp only [hx, if_false]
    split_ifs <;> simp [hn]

/-- For these whole-proof footprints the root inequality is both necessary
and sufficient for the shared-query condition of the FS compiler. -/
theorem query_load_iff (budget : Candidate W V Q R → ℚ) (hn : ∀ d, 0 ≤ budget d) (kappa : ℚ) :
    (∀ x, load budget x ≤ kappa) ↔
      ∀ w, (∑ v, ∑ q, ∑ r, budget (w, v, q, r)) ≤ kappa := by
  constructor
  · intro h w; simpa only [load_gamma] using h (gamma w)
  · intro h x
    exact (load_le_root budget hn x).trans (by simpa only [load_gamma] using h (root x))

/-- Exact fanout of the root coordinate, even when all certificates have
the same small local budget. Local soundness alone cannot remove it. -/
theorem constant_load_gamma (rho : ℚ) (w : W) :
    load (fun _ : Candidate W V Q R => rho) (gamma w) =
      Fintype.card V * Fintype.card Q * Fintype.card R * rho := by
  rw [load_gamma]
  simp [mul_assoc, mul_left_comm, mul_comm]

end Loads

section Polygero

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {I : Instance F} (child : Child I)

abbrev Proof := Candidate I.layer.Oracle child.instance.layer.Oracle
  I.layer.Query child.instance.layer.Payload
abbrev HashInput := Input I.layer.Oracle child.instance.layer.Oracle
  I.layer.Query child.instance.layer.Payload
abbrev Coins := (Protocol.step child (.terminal child.instance)).chain.Coins

/-- Each role uses one component of an ideal uniform product answer.
Unused components make this one homogeneous finite random oracle without
assuming an impossible bijection from four answers to four challenges. -/
abbrev Answer := (I.layer.Coin × I.layer.Query) ×
  (child.instance.layer.Coin × child.instance.layer.Query)

def constantMessages (d : Proof child) :
    Strategy (Protocol.step child (.terminal child.instance)).chain :=
  (fun _ => d.2.1, fun _ _ _ => d.2.2.2)

def proofCoins (H : HashInput child → Answer child) (d : Proof child) : Coins child :=
  (((H (gamma d.1)).1.1, (H (query d.1 d.2.1)).1.2),
    ((H (childGamma d.1 d.2.1 d.2.2.1)).2.1, (H (terminal d)).2.2))

/-- The claimed query is checked. It lets the final point be determined by
the submitted proof, as required by the appended-final-query compiler. -/
noncomputable def accepts (sigma : I.layer.Statement)
    (H : HashInput child → Answer child) (d : Proof child) : Prop :=
  (H (query d.1 d.2.1)).1.2 = d.2.2.1 ∧
  executionVerify (Protocol.step child (.terminal child.instance)).chain sigma d.1
    (constantMessages child d) (proofCoins child H d) = true

theorem accepts_iff (sigma : I.layer.Statement)
    (H : HashInput child → Answer child) (d : Proof child) :
    accepts child sigma H d ↔
      (H (query d.1 d.2.1)).1.2 = d.2.2.1 ∧ child.link.direct d.1 d.2.2.1 ∧
      child.instance.layer.verify
        (child.link.statement sigma d.1 (H (gamma d.1)).1.1 d.2.2.1) d.2.1
        (H (childGamma d.1 d.2.1 d.2.2.1)).2.1 d.2.2.2 (H (terminal d)).2.2 := by
  unfold accepts proofCoins constantMessages
  simp only [Protocol.chain, executionVerify, Bool.and_eq_true, decide_eq_true_eq]
  constructor <;> rintro ⟨hq, hd, hv⟩ <;> exact ⟨hq, hq ▸ hd, hq ▸ hv⟩

variable (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)

noncomputable def bad (sigma : I.layer.Statement) (D : (Counting.tupleCounts I).Index → Prop)
    (d : Proof child) (coins : Coins child) : ℚ :=
  indicator (executionVerify (Protocol.step child (.terminal child.instance)).chain sigma d.1
    (constantMessages child d) coins = true ∧
    Counting.outputHit D ((twoProof child p cp).run sigma d.1 (constantMessages child d) coins))

noncomputable def weight (sigma : I.layer.Statement) (D : (Counting.tupleCounts I).Index → Prop)
    (d : Proof child) (H : HashInput child → Answer child) : ℚ :=
  if (H (query d.1 d.2.1)).1.2 = d.2.2.1 then
    bad child p cp sigma D d (proofCoins child H d) else 0

noncomputable def failure (sigma : I.layer.Statement) (D : (Counting.tupleCounts I).Index → Prop)
    (H : HashInput child → Answer child) (d : Proof child) : Prop :=
  accepts child sigma H d ∧
    Counting.outputHit D ((twoProof child p cp).run sigma d.1
      (constantMessages child d) (proofCoins child H d))

theorem failure_empty_iff (sigma : I.layer.Statement)
    (H : HashInput child → Answer child) (d : Proof child) :
    failure child p cp sigma (fun _ => False) H d ↔
      accepts child sigma H d ∧ (twoProof child p cp).run sigma d.1
        (constantMessages child d) (proofCoins child H d) = none := by
  unfold failure
  cases (twoProof child p cp).run sigma d.1
    (constantMessages child d) (proofCoins child H d) <;> simp [Counting.outputHit]

/-- Concrete coverage: every accepting extraction failure (or target hit)
selects a unit-paying four-coordinate certificate containing its final input. -/
theorem failure_coverage (sigma : I.layer.Statement) (D : (Counting.tupleCounts I).Index → Prop)
    (H : HashInput child → Answer child) (d : Proof child)
    (h : failure child p cp sigma D H d) :
    terminal d ∈ support d ∧ weight child p cp sigma D d H = 1 := by
  obtain ⟨⟨hq, hv⟩, he⟩ := h
  exact ⟨terminal_mem d, by simp [weight, hq, bad, indicator, hv, he]⟩

/-- The parent-query gate is essential: it is paid with its actual sampling
probability, rather than giving every claimed query a full local budget. -/
noncomputable def budget (sigma : I.layer.Statement) (D : (Counting.tupleCounts I).Index → Prop)
    (d : Proof child) : ℚ :=
  mean (fun coins : Coins child => if coins.1.2 = d.2.2.1 then
    bad child p cp sigma D d coins else 0)

theorem budget_nonneg (sigma : I.layer.Statement) (D : (Counting.tupleCounts I).Index → Prop)
    (d : Proof child) : 0 ≤ budget child p cp sigma D d := by
  apply le_trans (le_of_eq (mean_const (I := Coins child) (0 : ℚ)).symm)
  apply mean_mono
  intro coins
  split_ifs <;> simp [bad, indicator_nonneg]

/-- Exact local resampling identity for the actual four hash inputs. The
remaining oracle answers can be arbitrary. Product projection is balanced;
no hash-to-field approximation or coin-space bijection is assumed. -/
theorem local_average (sigma : I.layer.Statement) (D : (Counting.tupleCounts I).Index → Prop)
    (d : Proof child) (off : Outside (support d) → Answer child) :
    average (fun on => weight child p cp sigma D d ((split (support d)).symm (on, off))) =
      budget child p cp sigma D d := by
  let e := supportEquiv d (Answer child)
  let f : (Answer child × Answer child × Answer child × Answer child) → ℚ := fun c =>
    if c.2.1.1.2 = d.2.2.1 then
      bad child p cp sigma D d ((c.1.1.1, c.2.1.1.2), (c.2.2.1.2.1, c.2.2.2.2.2)) else 0
  have he (on : Inside (support d) → Answer child) :
      weight child p cp sigma D d ((split (support d)).symm (on, off)) = f (e on) := by
    have hi := congrArg Prod.fst ((split (C := Answer child) (support d)).apply_symm_apply (on, off))
    have hx (x : Inside (support d)) : (split (support d)).symm (on, off) x.1 = on x :=
      congrFun hi x
    unfold weight proofCoins
    rw [hx ⟨_, by simp [support]⟩, hx ⟨_, by simp [support]⟩,
      hx ⟨_, by simp [support]⟩, hx ⟨_, terminal_mem d⟩]
    rfl
  simp_rw [he]
  have hmean : average (fun on => f (e on)) = mean f := by
    unfold average mean
    rw [Fintype.card_congr e, Fintype.sum_equiv e _ f (fun _ => rfl)]
  rw [hmean]
  change mean f = mean (fun coins : Answer child => if coins.1.2 = d.2.2.1 then
    bad child p cp sigma D d coins else 0)
  simp only [f, mean_prod, mean_const]
  rfl

/-- Summing the exact budgets over the claimed parent query restores the
interactive experiment for the fixed messages `v,r`. -/
theorem sum_budget_query (sigma : I.layer.Statement) (D : (Counting.tupleCounts I).Index → Prop)
    (w : I.layer.Oracle) (v : child.instance.layer.Oracle) (r : child.instance.layer.Payload)
    (q₀ : I.layer.Query) :
    (∑ q, budget child p cp sigma D (w, v, q, r)) =
      mean (bad child p cp sigma D (w, v, q₀, r)) := by
  unfold budget
  rw [← mean_finset_sum]
  apply mean_congr
  intro coins
  have hirrel (q : I.layer.Query) :
      bad child p cp sigma D (w, v, q, r) coins =
        bad child p cp sigma D (w, v, q₀, r) coins := rfl
  simp only [hirrel]
  simp

/-- Empty targets are extraction failure. No union over query locations is
lost, but this bound still fixes both prover messages. -/
theorem sum_budget_query_le (sigma : I.layer.Statement)
    (w : I.layer.Oracle) (v : child.instance.layer.Oracle) (r : child.instance.layer.Payload) :
    (∑ q, budget child p cp sigma (fun _ => False) (w, v, q, r)) ≤
      twoError p.error cp.error := by
  let q₀ : I.layer.Query := Classical.choice inferInstance
  rw [sum_budget_query child p cp sigma _ w v r q₀]
  have h := twoLevel_randomTarget_le child p cp (Z := Unit) (fun _ => sigma) w
    (fun _ => constantMessages child (w, v, q₀, r)) (fun _ _ => False) 0
    (by norm_num) (by norm_num) (by intro g; simp [indicator])
  change (mean fun coins => indicator (_ ∧ _)) ≤ _
  simp only [mean_const, transfer, mul_zero, add_zero,
    Protocol.HahnProfileProof.familyProbability] at h
  convert h using 1
  congr 1

theorem root_load_le (sigma : I.layer.Statement) (w : I.layer.Oracle) :
    load (budget child p cp sigma (fun _ => False)) (gamma w) ≤
      Fintype.card child.instance.layer.Oracle * Fintype.card child.instance.layer.Payload *
        twoError p.error cp.error := by
  rw [load_gamma]
  calc
    _ = ∑ v, ∑ r, ∑ q, budget child p cp sigma (fun _ => False) (w, v, q, r) := by
      congr 1; funext v; exact sum_comm
    _ ≤ ∑ _v : child.instance.layer.Oracle, ∑ _r : child.instance.layer.Payload,
        twoError p.error cp.error :=
      sum_le_sum fun v _ => sum_le_sum fun r _ => sum_budget_query_le child p cp sigma w v r
    _ = _ := by simp [mul_assoc]

theorem query_load_le (sigma : I.layer.Statement) (w : I.layer.Oracle)
    (v : child.instance.layer.Oracle) :
    load (budget child p cp sigma (fun _ => False)) (query w v) ≤
      Fintype.card child.instance.layer.Payload * twoError p.error cp.error := by
  rw [load_query, sum_comm]
  calc
    _ ≤ ∑ _r : child.instance.layer.Payload, twoError p.error cp.error :=
      sum_le_sum fun r _ => sum_budget_query_le child p cp sigma w v r
    _ = _ := by simp

theorem child_load_le (sigma : I.layer.Statement) (w : I.layer.Oracle)
    (v : child.instance.layer.Oracle) (q : I.layer.Query) :
    load (budget child p cp sigma (fun _ => False)) (childGamma w v q) ≤
      Fintype.card child.instance.layer.Payload * twoError p.error cp.error := by
  rw [load_childGamma]
  have hs := single_le_sum
    (fun q (_ : q ∈ (univ : Finset I.layer.Query)) =>
      sum_nonneg (s := univ) (fun r _ => budget_nonneg child p cp sigma (fun _ => False) (w, v, q, r)))
    (mem_univ q)
  exact hs.trans (by simpa only [load_query] using query_load_le child p cp sigma w v)

theorem final_budget_le (sigma : I.layer.Statement) (d : Proof child) :
    budget child p cp sigma (fun _ => False) d ≤ twoError p.error cp.error := by
  have hs := single_le_sum
    (fun q (_ : q ∈ (univ : Finset I.layer.Query)) =>
      budget_nonneg child p cp sigma (fun _ => False) (d.1, d.2.1, q, d.2.2.2))
    (mem_univ d.2.2.1)
  exact hs.trans (sum_budget_query_le child p cp sigma d.1 d.2.1 d.2.2.2)

/-- Operational adaptive-ROM theorem. `rootBudget` is an explicit finite
sum of proved local probabilities, rather than an adversary soundness
assumption. It identifies exactly what no-loss whole-proof charging needs. -/
theorem fs_of_root_load (sigma : I.layer.Statement) {N : ℕ}
    (tree : Merkle.RandomOracle.Tree (HashInput child) (Answer child) (Proof child) N)
    (kappa : ℚ) (hk : 0 ≤ kappa)
    (rootBudget : ∀ w, load (budget child p cp sigma (fun _ => False)) (gamma w) ≤ kappa) :
    Bcs.FiniteProbability.density (fun H =>
      failure child p cp sigma (fun _ => False) H (tree.run H).1) ≤
        twoError p.error cp.error + N * kappa := by
  apply selected_event_le tree terminal support (weight child p cp sigma (fun _ => False))
    (fun d _ => budget child p cp sigma (fun _ => False) d) _ _ _
  · intro d H; unfold weight; split_ifs <;> simp [bad, indicator_nonneg]
  · intro d _; exact budget_nonneg child p cp sigma _ d
  · exact hk
  · intro d off; exact (local_average child p cp sigma _ d off).le
  · intro H x
    exact (load_le_root _ (budget_nonneg child p cp sigma _) x).trans (rootBudget (root x))
  · intro H d
    exact (load_terminal _ d).trans_le (final_budget_le child p cp sigma d)
  · intro H hf
    obtain ⟨hm, hw⟩ := failure_coverage child p cp sigma _ H (tree.run H).1 hf
    exact ⟨(tree.run H).1, hm, hw.ge⟩

/-- A complete, conservative instantiation. It loses the number of child
oracles times the number of terminal responses; the query-location factor
has been removed by exact gating. This is not the conjectured no-loss rate. -/
theorem fs_finite_message_bound (sigma : I.layer.Statement) {N : ℕ}
    (tree : Merkle.RandomOracle.Tree (HashInput child) (Answer child) (Proof child) N) :
    Bcs.FiniteProbability.density (fun H =>
      failure child p cp sigma (fun _ => False) H (tree.run H).1) ≤
        twoError p.error cp.error + N *
          (Fintype.card child.instance.layer.Oracle * Fintype.card child.instance.layer.Payload *
            twoError p.error cp.error) := by
  apply fs_of_root_load child p cp sigma tree _ _ (root_load_le child p cp sigma)
  have h : 0 ≤ twoError p.error cp.error := by
    unfold twoError
    exact add_nonneg p.error_nonneg (mul_nonneg (sub_nonneg.mpr p.error_lt_one.le) cp.error_nonneg)
  positivity

/-- The precise extra inequality required to recover the no-loss slope in
this certificate scheme. The transfer theorem does not prove this premise. -/
theorem fs_no_loss_of_root_load (sigma : I.layer.Statement) {N : ℕ}
    (tree : Merkle.RandomOracle.Tree (HashInput child) (Answer child) (Proof child) N)
    (rootBudget : ∀ w,
      (∑ v, ∑ q, ∑ r, budget child p cp sigma (fun _ => False) (w, v, q, r)) ≤
        twoError p.error cp.error) :
    Bcs.FiniteProbability.density (fun H =>
      failure child p cp sigma (fun _ => False) H (tree.run H).1) ≤
        (N + 1) * twoError p.error cp.error := by
  have hn : 0 ≤ twoError p.error cp.error := by
    unfold twoError
    exact add_nonneg p.error_nonneg (mul_nonneg (sub_nonneg.mpr p.error_lt_one.le) cp.error_nonneg)
  have h := fs_of_root_load child p cp sigma tree _ hn
    (fun w => by simpa only [load_gamma] using rootBudget w)
  convert h using 1
  ring

end Polygero
end RecursivePolygero.FiatShamir.TwoLevel
