import Lfzk.LigeroZk.V1ResponseAdaptive
import Lfzk.ZkHiding

/-!
# Ligero V1 zero knowledge when the statement is chosen *after* the commitment

`Ligero.V1.ZeroKnowledge.v1_unbounded_perfect_response_adaptive_zero_knowledge` is stated in the
IPCP model: the statement is fixed first, then the prover commits.  Longfellow does it the other
way round.  `ZkProver::commit` commits the witness and the pad before any statement exists; the
Ligero statement (`verifier_constraints`, `zk_prover.h:L130`) is built afterwards from the
sumcheck transcript, whose challenges are hashes of a prefix that **starts with the Merkle root**.
So the statement is a function of the commitment, and the fixed-statement theorem does not apply.

This file proves the V1 fact the compiled composition needs instead.

## The fact

Fix the query set `q` and the challenge `ch`.  Let the statement be **any** function `S` of the
opened columns at `q` (in the composition: of the Merkle root, which after the hiding hybrid is a
function of the opened columns and the Merkle coins), satisfied by the committed messages `m` for
every value of its argument.  Then the pair

```
(opened columns at q,  response at the statement S(opened))
```

has *exactly* the same distribution, over a uniform V1 tape, as the simulator's pair

```
(opened columns of the all-zero messages at q,  response of the reference witness of S(opened))
```

where the simulator's response is computed on its tape with the core paddings shifted from the zero
messages to the reference witness (`coreShift`), which keeps the opened core columns.  That is
`adaptive_translate`, and `statClose_adaptive` is its distribution form.

## Why it holds

The proof is a change of variables on the prover tape, `adaptiveEquiv`:

* first V1's own translation (`translateRandomness`, from `m` to the reference witness of the
  statement), which keeps the opened columns and the response;
* then the core-only translation back to the zero messages, which keeps the opened columns.

Both translations keep the opened columns, so the statement — a function of those columns — is
the same before and after; that is what makes the composite well defined although the second
translation's target depends on the statement.  Injectivity: equal images have equal opened
columns, hence the same statement and reference witness, and both translations are injective.

## What is and is not assumed

Nothing about the protocol: the two translation lemmas are `Ligero.V1`'s
(`Lfzk.LigeroZk.V1TapeTranslation`).  The simulator reads the statement, the query and the
challenge, never `m`; it uses `referenceMessages`, chosen noncomputably, so it is unbounded.
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

/-! ## Shifting the core paddings -/

/-- **Shift the core paddings from messages `m₀` to `m₁`, keeping the columns opened at `q`.**
The masks and the proximity blind are untouched.  This is the core half of V1's tape translation,
`V1ProverRandomness.translatedCorePadding`, which needs no statement. -/
noncomputable def coreShift (m₀ m₁ : CoreMessages F nw nq w) (q : QuerySet n r)
    (ρ : V1ProverRandomness C nw nq reps) : V1ProverRandomness C nw nq reps :=
  { ρ with corePadding := V1ProverRandomness.translatedCorePadding m₀ m₁ q ρ }

omit [DecidableEq Equations] [Fintype Equations] in
/-- The shift keeps the opened columns. -/
theorem open_coreShift (m₀ m₁ : CoreMessages F nw nq w) (q : QuerySet n r)
    (ρ : V1ProverRandomness C nw nq reps) :
    openSchemeOracle (v1Oracle m₁ (coreShift m₀ m₁ q ρ)) q
      = openSchemeOracle (v1Oracle m₀ ρ) q := by
  funext j
  apply SchemeColumn.ext
  · funext block row
    exact congrFun (translateCorePadding_opening C q (m₀ block row) (m₁ block row)
      (ρ.corePadding block row)) j
  · funext h impossible
    exact NoMask.elim impossible
  · rfl
  · rfl

omit [DecidableEq Equations] [Fintype Equations] in
/-- Shifting there and back is the identity. -/
theorem coreShift_coreShift (m₀ m₁ : CoreMessages F nw nq w) (q : QuerySet n r)
    (ρ : V1ProverRandomness C nw nq reps) :
    coreShift m₁ m₀ q (coreShift m₀ m₁ q ρ) = ρ := by
  cases ρ with
  | mk core lin quad blind =>
    simp only [coreShift, V1ProverRandomness.mk.injEq, and_true]
    funext block row
    simp only [V1ProverRandomness.translatedCorePadding, translateCorePadding,
      translateCorePaddingEquiv, Equiv.trans_apply, Equiv.apply_symm_apply,
      Equiv.symm_apply_apply]

omit [DecidableEq Equations] [Fintype Equations] in
theorem coreShift_injective (m₀ m₁ : CoreMessages F nw nq w) (q : QuerySet n r) :
    Function.Injective (coreShift (C := C) (reps := reps) m₀ m₁ q) := by
  intro a b h
  rw [← coreShift_coreShift m₀ m₁ q a, ← coreShift_coreShift m₀ m₁ q b, h]

/-! ## The simulator's response -/

/-- **The simulator's response.**  At the statement `S o`, where `o` is the simulator's own opened
columns (those of the all-zero messages on its tape), answer as the honest prover holding the
statement's reference witness, on the tape whose core paddings are shifted from the zero messages
to that witness.  It never reads a witness. -/
noncomputable def simResp {q : QuerySet n r}
    (S : Opening F nw nq reps n r q → ConstraintSystem F nw nq w Equations)
    (ch : Challenge F nw nq reps Equations) (ρ' : V1ProverRandomness C nw nq reps) :
    LigeroFamily.Response F r w n reps :=
  v1Resp (S (openSchemeOracle (v1Oracle 0 ρ') q))
    (referenceMessages (S (openSchemeOracle (v1Oracle 0 ρ') q)))
    (coreShift 0 (referenceMessages (S (openSchemeOracle (v1Oracle 0 ρ') q))) q ρ') ch

/-! ## The change of variables -/

section Translate

variable (m : CoreMessages F nw nq w) (q : QuerySet n r) (ch : Challenge F nw nq reps Equations)
variable (S : Opening F nw nq reps n r q → ConstraintSystem F nw nq w Equations)
variable (hsat : ∀ o, (S o).Satisfies m)
include hsat

theorem ref_sat (o : Opening F nw nq reps n r q) :
    (S o).Satisfies (referenceMessages (S o)) :=
  referenceMessages_satisfies (S o) ⟨m, hsat o⟩

/-- V1's own translation, from `m` to the reference witness of `S o`, at `q` and `ch`. -/
noncomputable def toRef (o : Opening F nw nq reps n r q) :
    V1ProverRandomness C nw nq reps → V1ProverRandomness C nw nq reps :=
  V1ProverRandomness.translateRandomness m (referenceMessages (S o)) (hsat o)
    (ref_sat m q S hsat o) q ch

/-- The change of variables at a fixed value `o` of the statement's argument. -/
noncomputable def adaptiveMapAt (o : Opening F nw nq reps n r q)
    (ρ : V1ProverRandomness C nw nq reps) : V1ProverRandomness C nw nq reps :=
  coreShift (referenceMessages (S o)) 0 q (toRef m q ch S hsat o ρ)

theorem open_adaptiveMapAt (o : Opening F nw nq reps n r q)
    (ρ : V1ProverRandomness C nw nq reps) :
    openSchemeOracle (v1Oracle 0 (adaptiveMapAt m q ch S hsat o ρ)) q
      = openSchemeOracle (v1Oracle m ρ) q := by
  rw [adaptiveMapAt, open_coreShift]
  have h := V1ProverRandomness.translateRandomness_opening m (referenceMessages (S o)) (hsat o)
    (ref_sat m q S hsat o) q ch ρ
  rwa [encoding_oracle, encoding_oracle] at h

/-- **The change of variables**: read the statement off the real opened columns, then translate. -/
noncomputable def adaptiveMap (ρ : V1ProverRandomness C nw nq reps) :
    V1ProverRandomness C nw nq reps :=
  adaptiveMapAt m q ch S hsat (openSchemeOracle (v1Oracle m ρ) q) ρ

theorem open_adaptiveMap (ρ : V1ProverRandomness C nw nq reps) :
    openSchemeOracle (v1Oracle 0 (adaptiveMap m q ch S hsat ρ)) q
      = openSchemeOracle (v1Oracle m ρ) q :=
  open_adaptiveMapAt m q ch S hsat _ ρ

theorem adaptiveMap_injective :
    Function.Injective (adaptiveMap (C := C) (reps := reps) m q ch S hsat) := by
  intro a b hab
  have ho : openSchemeOracle (v1Oracle m a) q = openSchemeOracle (v1Oracle m b) q := by
    rw [← open_adaptiveMap m q ch S hsat a, ← open_adaptiveMap m q ch S hsat b, hab]
  have h' : adaptiveMapAt m q ch S hsat (openSchemeOracle (v1Oracle m a) q) a
      = adaptiveMapAt m q ch S hsat (openSchemeOracle (v1Oracle m a) q) b := by
    have hb : adaptiveMap m q ch S hsat b
        = adaptiveMapAt m q ch S hsat (openSchemeOracle (v1Oracle m a) q) b := by
      rw [adaptiveMap, ho]
    rw [← hb]
    exact hab
  have h'' := coreShift_injective _ _ q h'
  exact V1ProverRandomness.translateRandomness_injective m _ (hsat _) (ref_sat m q S hsat _) q
    ch h''

/-- The change of variables as an equivalence of the (finite, uniform) V1 tape. -/
noncomputable def adaptiveEquiv : V1ProverRandomness C nw nq reps ≃ V1ProverRandomness C nw nq reps :=
  Equiv.ofBijective (adaptiveMap m q ch S hsat)
    (adaptiveMap_injective m q ch S hsat).bijective_of_finite

/--
**Adaptive-statement translation.**  Under the change of variables `adaptiveEquiv`, the
simulator's opened columns are the real ones, and the simulator's response at the statement read
off its own opened columns is the real response at the statement read off the real opened
columns.
-/
theorem adaptive_translate (ρ : V1ProverRandomness C nw nq reps) :
    openSchemeOracle (v1Oracle 0 (adaptiveEquiv m q ch S hsat ρ)) q
        = openSchemeOracle (v1Oracle m ρ) q ∧
      simResp S ch (adaptiveEquiv m q ch S hsat ρ)
        = v1Resp (S (openSchemeOracle (v1Oracle m ρ) q)) m ρ ch := by
  have hopen := open_adaptiveMap m q ch S hsat ρ
  refine ⟨hopen, ?_⟩
  change simResp S ch (adaptiveMap m q ch S hsat ρ) = _
  set o := openSchemeOracle (v1Oracle m ρ) q with ho
  rw [simResp, hopen]
  -- unshift the core paddings: the simulator's response tape is V1's translated tape
  have hshift : coreShift 0 (referenceMessages (S o)) q (adaptiveMap m q ch S hsat ρ)
      = toRef m q ch S hsat o ρ := by
    rw [adaptiveMap, adaptiveMapAt, ← ho, coreShift_coreShift]
  rw [hshift, v1Resp_of_sat (ref_sat m q S hsat o), v1Resp_of_sat (hsat o), toRef]
  exact V1ProverRandomness.translateRandomness_response m (referenceMessages (S o)) (hsat o)
    (ref_sat m q S hsat o) q ch ρ

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
        Ψ (openSchemeOracle (v1Oracle 0 ρ') q) (simResp S ch ρ')) := by
  intro P
  have h := probOf_equiv (adaptiveEquiv m q ch S hsat)
    (fun ρ' : V1ProverRandomness C nw nq reps =>
      Ψ (openSchemeOracle (v1Oracle 0 ρ') q) (simResp S ch ρ')) P
  have hpt : (fun ρ : V1ProverRandomness C nw nq reps =>
        Ψ (openSchemeOracle (v1Oracle 0 (adaptiveEquiv m q ch S hsat ρ)) q)
        (simResp S ch (adaptiveEquiv m q ch S hsat ρ)))
      = fun ρ => Ψ (openSchemeOracle (v1Oracle m ρ) q)
          (v1Resp (S (openSchemeOracle (v1Oracle m ρ) q)) m ρ ch) := by
    funext ρ
    obtain ⟨h1, h2⟩ := adaptive_translate m q ch S hsat ρ
    rw [h1, h2]
  rw [hpt] at h
  rw [h, sub_self, abs_zero]

end Translate

end Lfzk.ZkAdaptiveV1
