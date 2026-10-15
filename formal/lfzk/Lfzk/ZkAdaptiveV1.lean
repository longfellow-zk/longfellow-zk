import Lfzk.LigeroZk.V1ResponseAdaptive
import Lfzk.ZkHiding

/-!
# An explicit Ligero V1 simulator, for a statement chosen *after* the commitment

`Ligero.V1.ZeroKnowledge.v1_unbounded_perfect_response_adaptive_zero_knowledge` is stated in the
IPCP model: the statement is fixed first, then the prover commits, and its simulator runs the
honest prover on a reference witness chosen noncomputably.  Longfellow does it the other way
round.  `ZkProver::commit` commits the witness and the pad before any statement exists; the
Ligero statement (`verifier_constraints`, `zk_prover.h:L130`) is built afterwards from the
sumcheck transcript, whose challenges are hashes of a prefix that **starts with the Merkle root**.
So the statement is a function of the commitment, and the fixed-statement theorem does not apply.

This file proves the V1 fact the compiled composition needs instead, with a simulator that never
holds a witness.

## The simulator

Fix the query set `q` and the challenge `ch` (in the compiled protocol both come from the
programmed Ligero oracle, so the simulator knows `q` before it answers).  On its own tape `ρ'` the
simulator

* commits to the **all-zero tableau** (`v1Oracle 0 ρ'`): its opened columns at `q` are uniform,
  since every core row carries `r = |q|` uniform padding values;
* answers with the honest V1 formulas on that tableau (`simResp`).  The proximity and quadratic
  responses of the zero tableau already pass the verifier's checks.  The linear response needs
  the statement's target: it adds `linCorr C q t`, the base-code row whose witness part is
  `t = combinedTarget` at the first slot and `0` elsewhere, and which vanishes on `q`.

`linCorr` is the unique such row (`linCorr_unique`: `|witness positions ∪ q| = w + r = k`, the
code's dimension), so it is a function of public data — the code, the query and the statement's
target — not a choice of a witness.  Lean picks it with `Classical.choose`, exactly as it picks the
honest prover's own encoding `C.encode`; concretely it is an interpolation.

## The fact

Let the statement be **any** function `S` of the opened columns at `q` (in the composition: of the
Merkle root, which after the hiding hybrid is a function of the opened columns and the Merkle
coins), satisfied by the committed messages `m` for every value of its argument.  Then the pair

```
(opened columns at q,  response at the statement S(opened))
```

has *exactly* the same distribution, over a uniform V1 tape, as the simulator's pair

```
(opened columns of the all-zero messages at q,  simResp at S(opened))
```

That is `adaptive_translate`, and `statClose_adaptive` is its distribution form.

## Why it holds

The proof is a change of variables on the prover tape, `toSim`:

* the core paddings are translated from `m` to the zero messages keeping the opened columns
  (`translatedCorePadding`, V1's own core translation);
* each mask absorbs the difference between the real canonical response and the simulator's:
  `linAdj` (real − zero-tableau − `linCorr`, a legal linear mask since its witness sum is
  `t − 0 − t`), `quadAdj` and `proxAdj`.  Each difference vanishes on `q`, so the opened mask
  columns do not move.

`toSim` keeps the opened columns, so the statement — a function of those columns — is the same
before and after; that is what makes the adaptive map well defined although the adjustment
depends on the statement.  It is injective (equal images have equal opened columns, hence the same
statement, and each coordinate is a translation), hence a bijection of the finite tape.

## What is and is not assumed

Nothing about the protocol beyond `Ligero.V1`'s definitions and its core translation
(`Lfzk.LigeroZk.CoreTranslation`).  The simulator reads the statement, the query and the challenge,
never `m`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace Lfzk.ZkAdaptiveV1

open LigeroFamily LigeroFamily.ZeroKnowledge Ligero.V1 Ligero.V1.ZeroKnowledge
open MultiplicativeCode

variable {F Equations : Type} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Equations] [DecidableEq Equations]
variable {r w n nw nq reps : ℕ} {C : MultiplicativeCode F r w n}

/-! ## The commitment and the response, separated -/

/-- **The V1 commitment, before any statement exists.**  The oracle the honest V1 prover commits
is a function of the messages and the tape alone (`V1HonestEncoding.oracle` of
`V1ProverRandomness.encoding`); the statement index of the encoding only carries the satisfaction
proof.  This is the commitment `ZkProver::commit` makes. -/
noncomputable def v1Oracle (m : CoreMessages F nw nq w) (ρ : V1ProverRandomness C nw nq reps) :
    Oracle F nw nq n reps where
  core block row j := C.encode (ρ.corePadding block row) (m block row) (codePosition j)
  checkedMask _ impossible := NoMask.elim impossible
  directMask h kind j := match kind with
    | .linear => (ρ.linearMask h : EvaluationRow F r w n) (codePosition j)
    | .quadratic => (ρ.quadraticMask h : EvaluationRow F r w n) (codePosition j)
  proximityBlind h j := (ρ.proximityBlind h : EvaluationRow F r w n) (codePosition j)

omit [Fintype F] [DecidableEq F] [DecidableEq Equations] in
/-- The honest encoding's oracle *is* `v1Oracle`, at every statement it satisfies. -/
theorem encoding_oracle {s : ConstraintSystem F nw nq w Equations} (m : CoreMessages F nw nq w)
    (h : s.Satisfies m) (ρ : V1ProverRandomness C nw nq reps) :
    (ρ.encoding m h).oracle = v1Oracle m ρ := rfl

/-- **The honest V1 response at statement `s`.**  `v1HonestProver` is the total honest prover
(the null prover off the language), so this is defined for every statement; it is the honest
response whenever `s` is satisfied by `m` (`v1Resp_of_sat`). -/
noncomputable def v1Resp (s : ConstraintSystem F nw nq w Equations) (m : CoreMessages F nw nq w)
    (ρ : V1ProverRandomness C nw nq reps) (ch : Challenge F nw nq reps Equations) :
    LigeroFamily.Response F r w n reps :=
  (v1HonestProver C s m ρ).respond s ((v1HonestProver C s m ρ).commit s) ch

theorem v1Resp_of_sat {s : ConstraintSystem F nw nq w Equations} {m : CoreMessages F nw nq w}
    (h : s.Satisfies m) (ρ : V1ProverRandomness C nw nq reps)
    (ch : Challenge F nw nq reps Equations) :
    v1Resp s m ρ ch = (ρ.encoding m h).response ch := by
  unfold v1Resp v1HonestProver
  simp only [h, dite_true]
  rfl

theorem v1HonestProver_commit {s : ConstraintSystem F nw nq w Equations}
    {m : CoreMessages F nw nq w} (h : s.Satisfies m) (ρ : V1ProverRandomness C nw nq reps) :
    (v1HonestProver C s m ρ).commit s = v1Oracle m ρ := by
  unfold v1HonestProver
  simp only [h, dite_true]
  rfl

/-! ## The public linear correction -/

/-- Public witness-suffix prescription: `t` at the first witness slot, `0` elsewhere. -/
def firstSlot (t : F) : Fin w → F := fun i => if (i : ℕ) = 0 then t else 0

theorem sum_firstSlot (hw : 0 < w) (t : F) : ∑ i : Fin w, firstSlot t i = t := by
  rw [Finset.sum_eq_single ⟨0, hw⟩]
  · simp [firstSlot]
  · intro b _ hb
    simp only [firstSlot, ite_eq_right_iff]
    intro h
    exact absurd (Fin.ext h) hb
  · simp

/-- **The public linear correction**: a base row with witness sum `t` vanishing on the query.
A choice of a *public* object (and unique, since `|witness ∪ Q| = k`). -/
noncomputable def linCorr (C : MultiplicativeCode F r w n) (q : QuerySet n r) (t : F) :
    EvaluationRow F r w n :=
  Classical.choose
    (exists_base_witness_query C q.coordinates (QuerySet.card_coordinates q) (firstSlot t))

theorem linCorr_mem (q : QuerySet n r) (t : F) : linCorr C q t ∈ C.base :=
  (Classical.choose_spec
    (exists_base_witness_query C q.coordinates (QuerySet.card_coordinates q) (firstSlot t))).1

theorem linCorr_witness (q : QuerySet n r) (t : F) (i : Fin w) :
    linCorr C q t (witnessPosition i) = firstSlot t i :=
  (Classical.choose_spec
    (exists_base_witness_query C q.coordinates (QuerySet.card_coordinates q) (firstSlot t))).2.1 i

theorem linCorr_query (q : QuerySet n r) (t : F) (j : ↥q.coordinates) :
    linCorr C q t (codePosition j.1) = 0 :=
  (Classical.choose_spec
    (exists_base_witness_query C q.coordinates (QuerySet.card_coordinates q) (firstSlot t))).2.2
    j.1 j.2

/-- **`linCorr` is the only such row**: a base row is determined by its values at the `w + r = k`
witness and query positions (`MultiplicativeCode.base_unique`).  So the simulator's one choice is
of a public object, fixed by the code, the query and the target. -/
theorem linCorr_unique (q : QuerySet n r) (t : F) {row : EvaluationRow F r w n} (hrow : row ∈ C.base)
    (hwit : ∀ i, row (witnessPosition i) = firstSlot t i)
    (hq : ∀ j ∈ q.coordinates, row (codePosition j) = 0) :
    row = linCorr C q t := by
  classical
  refine C.base_unique hrow (linCorr_mem q t)
    (witnessPositions r w n ∪ codePositions (r := r) (w := w) q.coordinates) ?_ ?_
  · rw [card_witnessPositions_union_codePositions, QuerySet.card_coordinates, C.k_eq,
      Nat.add_comm]
  · intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hi
      rw [hwit, linCorr_witness]
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      rw [hq j hj, linCorr_query q t ⟨j, hj⟩]

/-! ## Satisfaction-free core lemmas -/

theorem linearCore_mem (s : ConstraintSystem F nw nq w Equations) (wt : Equations → F)
    (rows : (block : CoreBlock) → Fin (block.rowCount nw nq) → EvaluationRow F r w n)
    (h : ∀ b i, rows b i ∈ C.base) : Verifier.linearCore C s wt rows ∈ C.response := by
  unfold Verifier.linearCore
  apply Submodule.sum_mem
  intro block _
  apply Submodule.sum_mem
  intro row _
  exact C.mul_mem (C.encode_mem 0 (s.A wt block row)) (h block row)

theorem quadraticCore_mem (wt : Fin nq → F)
    (rows : (block : CoreBlock) → Fin (block.rowCount nw nq) → EvaluationRow F r w n)
    (h : ∀ b i, rows b i ∈ C.base) : Verifier.quadraticCore wt rows ∈ C.response := by
  unfold Verifier.quadraticCore
  apply Submodule.sum_mem
  intro row _
  apply C.response.smul_mem
  apply C.response.sub_mem
  · exact C.mul_mem (h .left row) (h .right row)
  · exact C.base_le_response (h .output row)

/-- Zero-tableau core rows on a padding. -/
noncomputable def zeroCore (C : MultiplicativeCode F r w n)
    (pad : (block : CoreBlock) → Fin (block.rowCount nw nq) → Fin r → F) :
    (block : CoreBlock) → Fin (block.rowCount nw nq) → EvaluationRow F r w n :=
  fun b row => C.encode (pad b row) 0

theorem linearCore_zero_witness (s : ConstraintSystem F nw nq w Equations) (wt : Equations → F)
    (pad : (block : CoreBlock) → Fin (block.rowCount nw nq) → Fin r → F) (i : Fin w) :
    Verifier.linearCore C s wt (zeroCore C pad) (witnessPosition i) = 0 := by
  simp [Verifier.linearCore, Verifier.coefficientRow, Finset.sum_apply, zeroCore]

theorem quadraticCore_zero_witness (wt : Fin nq → F)
    (pad : (block : CoreBlock) → Fin (block.rowCount nw nq) → Fin r → F) (i : Fin w) :
    Verifier.quadraticCore wt (zeroCore C pad) (witnessPosition i) = 0 := by
  simp [Verifier.quadraticCore, Finset.sum_apply, zeroCore]

/-! ## The simulator's response -/

/-- **Witness-free V1 response**: the honest formulas on the all-zero tableau of the tape, plus the
public correction `linCorr` on each linear row. -/
noncomputable def simResp (s : ConstraintSystem F nw nq w Equations) (q : QuerySet n r)
    (ch : Challenge F nw nq reps Equations) (ρ : V1ProverRandomness C nw nq reps) :
    LigeroFamily.Response F r w n reps where
  proximity h :=
    (∑ row : SchemeTestedRow NoMask nw nq reps, (ch h).proximity row •
      match row with
      | Sum.inl core => zeroCore C ρ.corePadding core.1 core.2
      | Sum.inr impossible => NoMask.elim impossible.2) +
    (ρ.proximityBlind h : EvaluationRow F r w n)
  linear h :=
    Verifier.linearCore C s (ch h).linear (zeroCore C ρ.corePadding) +
      (ρ.linearMask h : EvaluationRow F r w n) + linCorr C q (s.combinedTarget (ch h).linear)
  quadratic h :=
    Verifier.quadraticCore (ch h).quadratic (zeroCore C ρ.corePadding) +
      (ρ.quadraticMask h : EvaluationRow F r w n)

/-! ## The change of variables, real tape → simulator tape -/

section Translate

variable {s : ConstraintSystem F nw nq w Equations} (m : CoreMessages F nw nq w)
  (hsat : s.Satisfies m) (q : QuerySet n r) (ch : Challenge F nw nq reps Equations)

/-- Real core rows. -/
noncomputable def realRows (ρ : V1ProverRandomness C nw nq reps) :
    (block : CoreBlock) → Fin (block.rowCount nw nq) → EvaluationRow F r w n :=
  fun b row => C.encode (ρ.corePadding b row) (m b row)

/-- Shifted (zero-tableau) core rows. -/
noncomputable def simRows (ρ : V1ProverRandomness C nw nq reps) :
    (block : CoreBlock) → Fin (block.rowCount nw nq) → EvaluationRow F r w n :=
  zeroCore C (V1ProverRandomness.translatedCorePadding m 0 q ρ)

theorem core_query (ρ : V1ProverRandomness C nw nq reps) (b : CoreBlock)
    (row : Fin (b.rowCount nw nq)) (j : ↥q.coordinates) :
    simRows m q ρ b row (codePosition j.1) = realRows m ρ b row (codePosition j.1) := by
  exact congrFun (translateCorePadding_opening C q (m b row) 0 (ρ.corePadding b row)) j


/-- Linear adjustment: real canonical − simulated canonical − public correction.  A legal V1
linear mask (response row, zero witness sum). -/
noncomputable def linAdj (ρ : V1ProverRandomness C nw nq reps) (h : Fin reps) :
    V1LinearMaskSpace C := by
  refine ⟨Verifier.linearCore C s (ch h).linear (realRows m ρ) -
      Verifier.linearCore C s (ch h).linear (simRows m q ρ) -
      linCorr C q (s.combinedTarget (ch h).linear), ?_, ?_⟩
  · exact C.response.sub_mem
      (C.response.sub_mem (linearCore_mem s _ _ fun _ _ => C.encode_mem _ _)
        (linearCore_mem s _ _ fun _ _ => C.encode_mem _ _))
      (C.base_le_response (linCorr_mem q _))
  · have ha : ∑ i : Fin w, Verifier.linearCore C s (ch h).linear (realRows m ρ) (witnessPosition i)
        = s.combinedTarget (ch h).linear :=
      (ρ.encoding m hsat).honestCore.linearResponse_sum (ch h).linear
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, ha, simRows, linearCore_zero_witness,
      sub_zero, linCorr_witness]
    rcases Nat.eq_zero_or_pos w with hw | hw
    · subst hw
      simp only [Finset.univ_eq_empty, Finset.sum_empty] at ha ⊢
      rw [← ha, sub_zero]
    · rw [sum_firstSlot hw, sub_self]

/-- Quadratic adjustment: real canonical − simulated canonical (both vanish on the witness). -/
noncomputable def quadAdj (ρ : V1ProverRandomness C nw nq reps) (h : Fin reps) :
    V1QuadraticMaskSpace C := by
  refine ⟨Verifier.quadraticCore (ch h).quadratic (realRows m ρ) -
      Verifier.quadraticCore (ch h).quadratic (simRows m q ρ), ?_, ?_⟩
  · exact C.response.sub_mem (quadraticCore_mem _ _ fun _ _ => C.encode_mem _ _)
      (quadraticCore_mem _ _ fun _ _ => C.encode_mem _ _)
  · intro i
    have h1 : Verifier.quadraticCore (ch h).quadratic (realRows m ρ) (witnessPosition i) = 0 :=
      (ρ.encoding m hsat).honestCore.quadraticResponse_witness (ch h).quadratic i
    simp only [Pi.sub_apply, h1, simRows, quadraticCore_zero_witness, sub_zero]

/-- Proximity adjustment. -/
noncomputable def proxAdj (ρ : V1ProverRandomness C nw nq reps) (h : Fin reps) : C.base := by
  refine ⟨∑ row : SchemeTestedRow NoMask nw nq reps, (ch h).proximity row •
      (match row with
      | Sum.inl core => realRows m ρ core.1 core.2 - simRows m q ρ core.1 core.2
      | Sum.inr impossible => NoMask.elim impossible.2), ?_⟩
  apply Submodule.sum_mem
  intro row _
  cases row with
  | inl core => exact C.base.smul_mem _ (C.base.sub_mem (C.encode_mem _ _) (C.encode_mem _ _))
  | inr impossible => exact NoMask.elim impossible.2

/-- **Real tape → simulator tape.** -/
noncomputable def toSim (ρ : V1ProverRandomness C nw nq reps) : V1ProverRandomness C nw nq reps where
  corePadding := V1ProverRandomness.translatedCorePadding m 0 q ρ
  linearMask h := ρ.linearMask h + linAdj m hsat q ch ρ h
  quadraticMask h := ρ.quadraticMask h + quadAdj m hsat q ch ρ h
  proximityBlind h := ρ.proximityBlind h + proxAdj m q ch ρ h

theorem linAdj_query (ρ : V1ProverRandomness C nw nq reps) (h : Fin reps) (j : ↥q.coordinates) :
    (linAdj m hsat q ch ρ h : EvaluationRow F r w n) (codePosition j.1) = 0 := by
  simp only [linAdj, Pi.sub_apply, linCorr_query, sub_zero]
  rw [sub_eq_zero]
  simp only [Verifier.linearCore, Finset.sum_apply, rowMul_apply]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro row _
  rw [core_query]

theorem quadAdj_query (ρ : V1ProverRandomness C nw nq reps) (h : Fin reps) (j : ↥q.coordinates) :
    (quadAdj m hsat q ch ρ h : EvaluationRow F r w n) (codePosition j.1) = 0 := by
  simp only [quadAdj, Pi.sub_apply]
  rw [sub_eq_zero]
  simp only [Verifier.quadraticCore, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, rowMul_apply,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro row _
  rw [core_query, core_query, core_query]

theorem proxAdj_query (ρ : V1ProverRandomness C nw nq reps) (h : Fin reps) (j : ↥q.coordinates) :
    (proxAdj m q ch ρ h : EvaluationRow F r w n) (codePosition j.1) = 0 := by
  simp only [proxAdj, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro row _
  cases row with
  | inl core =>
      change (ch h).proximity (Sum.inl core) *
        (realRows m ρ core.1 core.2 (codePosition j.1) -
          simRows m q ρ core.1 core.2 (codePosition j.1)) = 0
      rw [core_query, sub_self, mul_zero]
  | inr impossible => exact NoMask.elim impossible.2

/-- The simulator tape opens the zero tableau exactly where the real tape opens the real one. -/
theorem toSim_opening (ρ : V1ProverRandomness C nw nq reps) :
    openSchemeOracle (v1Oracle 0 (toSim m hsat q ch ρ)) q = openSchemeOracle (v1Oracle m ρ) q := by
  funext j
  apply SchemeColumn.ext
  · funext b row
    exact core_query m q ρ b row j
  · funext h impossible
    exact NoMask.elim impossible
  · funext h kind
    cases kind <;>
      simp only [openSchemeOracle, SchemeOracle.column, v1Oracle, toSim, Submodule.coe_add,
        Pi.add_apply]
    · rw [linAdj_query, add_zero]
    · rw [quadAdj_query, add_zero]
  · funext h
    simp only [openSchemeOracle, SchemeOracle.column, v1Oracle, toSim, Submodule.coe_add,
      Pi.add_apply]
    rw [proxAdj_query, add_zero]

/-- The explicit simulator's response on the translated tape is the real response. -/
theorem toSim_response (ρ : V1ProverRandomness C nw nq reps) :
    simResp s q ch (toSim m hsat q ch ρ) = (ρ.encoding m hsat).response ch := by
  apply Response.ext
  · funext h
    simp only [simResp, toSim, V1HonestEncoding.response, V1HonestEncoding.proximityResponse,
      V1ProverRandomness.encoding, proxAdj, Submodule.coe_add, Fintype.sum_sum_type]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, smul_sub,
      Finset.sum_sub_distrib, simRows, realRows]
    abel
  · funext h position
    simp only [simResp, toSim, V1HonestEncoding.response, V1HonestEncoding.linearResponse,
      V1ProverRandomness.encoding, linAdj, Submodule.coe_add, Pi.add_apply, Pi.sub_apply,
      simRows]
    ring_nf
    rfl
  · funext h position
    simp only [simResp, toSim, V1HonestEncoding.response, V1HonestEncoding.quadraticResponse,
      V1ProverRandomness.encoding, quadAdj, Submodule.coe_add, Pi.add_apply, Pi.sub_apply,
      simRows]
    ring_nf
    rfl

theorem toSim_injective : Function.Injective (toSim (C := C) (reps := reps) m hsat q ch) := by
  intro a b hab
  have hcore : a.corePadding = b.corePadding := by
    have hc := congrArg V1ProverRandomness.corePadding hab
    funext blk row
    exact (translateCorePaddingEquiv C q (m blk row) ((0 : CoreMessages F nw nq w) blk row)).injective
      (congrFun (congrFun hc blk) row)
  have hl : ∀ h, linAdj m hsat q ch a h = linAdj m hsat q ch b h := by
    intro h; cases a; cases b; subst hcore; rfl
  have hq : ∀ h, quadAdj m hsat q ch a h = quadAdj m hsat q ch b h := by
    intro h; cases a; cases b; subst hcore; rfl
  have hp : ∀ h, proxAdj m q ch a h = proxAdj m q ch b h := by
    intro h; cases a; cases b; subst hcore; rfl
  have hlin : a.linearMask = b.linearMask := by
    funext h
    have heq := congrFun (congrArg V1ProverRandomness.linearMask hab) h
    change a.linearMask h + linAdj m hsat q ch a h = b.linearMask h + linAdj m hsat q ch b h at heq
    rw [hl h] at heq
    exact add_right_cancel heq
  have hquad : a.quadraticMask = b.quadraticMask := by
    funext h
    have heq := congrFun (congrArg V1ProverRandomness.quadraticMask hab) h
    change a.quadraticMask h + quadAdj m hsat q ch a h = b.quadraticMask h + quadAdj m hsat q ch b h
      at heq
    rw [hq h] at heq
    exact add_right_cancel heq
  have hblind : a.proximityBlind = b.proximityBlind := by
    funext h
    have heq := congrFun (congrArg V1ProverRandomness.proximityBlind hab) h
    change a.proximityBlind h + proxAdj m q ch a h = b.proximityBlind h + proxAdj m q ch b h at heq
    rw [hp h] at heq
    exact add_right_cancel heq
  cases a; cases b
  simp_all

end Translate

/-! ## The adaptive statement -/

section Adaptive

variable (m : CoreMessages F nw nq w) (q : QuerySet n r) (ch : Challenge F nw nq reps Equations)
variable (S : Opening F nw nq reps n r q → ConstraintSystem F nw nq w Equations)

/-- **The simulator's response at an adaptive statement**: `simResp` at the statement read off the
simulator's own opened columns (those of the all-zero tableau on its tape). -/
noncomputable def adaptiveSimResp (ρ' : V1ProverRandomness C nw nq reps) :
    LigeroFamily.Response F r w n reps :=
  simResp (S (openSchemeOracle (v1Oracle 0 ρ') q)) q ch ρ'

variable (hsat : ∀ o, (S o).Satisfies m)
include hsat

noncomputable def adaptiveMap (ρ : V1ProverRandomness C nw nq reps) :
    V1ProverRandomness C nw nq reps :=
  toSim m (hsat (openSchemeOracle (v1Oracle m ρ) q)) q ch ρ

theorem open_adaptiveMap (ρ : V1ProverRandomness C nw nq reps) :
    openSchemeOracle (v1Oracle 0 (adaptiveMap m q ch S hsat ρ)) q
      = openSchemeOracle (v1Oracle m ρ) q :=
  toSim_opening m _ q ch ρ

theorem adaptiveMap_injective :
    Function.Injective (adaptiveMap (C := C) (reps := reps) m q ch S hsat) := by
  intro a b hab
  have ho : openSchemeOracle (v1Oracle m a) q = openSchemeOracle (v1Oracle m b) q := by
    rw [← open_adaptiveMap m q ch S hsat a, ← open_adaptiveMap m q ch S hsat b, hab]
  have h' : toSim m (hsat (openSchemeOracle (v1Oracle m a) q)) q ch a
      = toSim m (hsat (openSchemeOracle (v1Oracle m a) q)) q ch b := by
    have hb : adaptiveMap m q ch S hsat b
        = toSim m (hsat (openSchemeOracle (v1Oracle m a) q)) q ch b := by
      unfold adaptiveMap
      rw [ho]
    rw [← hb]
    exact hab
  exact toSim_injective m _ q ch h'

noncomputable def adaptiveEquiv : V1ProverRandomness C nw nq reps ≃ V1ProverRandomness C nw nq reps :=
  Equiv.ofBijective (adaptiveMap m q ch S hsat)
    (adaptiveMap_injective m q ch S hsat).bijective_of_finite

theorem adaptive_translate (ρ : V1ProverRandomness C nw nq reps) :
    openSchemeOracle (v1Oracle 0 (adaptiveEquiv m q ch S hsat ρ)) q
        = openSchemeOracle (v1Oracle m ρ) q ∧
      adaptiveSimResp q ch S (adaptiveEquiv m q ch S hsat ρ)
        = v1Resp (S (openSchemeOracle (v1Oracle m ρ) q)) m ρ ch := by
  have hopen := open_adaptiveMap m q ch S hsat ρ
  refine ⟨hopen, ?_⟩
  change adaptiveSimResp q ch S (adaptiveMap m q ch S hsat ρ) = _
  rw [adaptiveSimResp, hopen, v1Resp_of_sat (hsat _)]
  exact toSim_response m _ q ch ρ

/--
**The distribution form.**  For every post-processing `Ψ` of (opened columns, response), the real
pair and the simulated pair are `0`-close: identically distributed.
-/
theorem statClose_adaptive {V : Type}
    (Ψ : Opening F nw nq reps n r q → LigeroFamily.Response F r w n reps → V) :
    StatClose 0
      (fun ρ : V1ProverRandomness C nw nq reps =>
        Ψ (openSchemeOracle (v1Oracle m ρ) q)
          (v1Resp (S (openSchemeOracle (v1Oracle m ρ) q)) m ρ ch))
      (fun ρ' : V1ProverRandomness C nw nq reps =>
        Ψ (openSchemeOracle (v1Oracle 0 ρ') q) (adaptiveSimResp q ch S ρ')) := by
  intro P
  have h := probOf_equiv (adaptiveEquiv m q ch S hsat)
    (fun ρ' : V1ProverRandomness C nw nq reps =>
      Ψ (openSchemeOracle (v1Oracle 0 ρ') q) (adaptiveSimResp q ch S ρ')) P
  have hpt : (fun ρ : V1ProverRandomness C nw nq reps =>
        Ψ (openSchemeOracle (v1Oracle 0 (adaptiveEquiv m q ch S hsat ρ)) q)
        (adaptiveSimResp q ch S (adaptiveEquiv m q ch S hsat ρ)))
      = fun ρ => Ψ (openSchemeOracle (v1Oracle m ρ) q)
          (v1Resp (S (openSchemeOracle (v1Oracle m ρ) q)) m ρ ch) := by
    funext ρ
    obtain ⟨h1, h2⟩ := adaptive_translate m q ch S hsat ρ
    rw [h1, h2]
  rw [hpt] at h
  rw [h, sub_self, abs_zero]

end Adaptive

end Lfzk.ZkAdaptiveV1
