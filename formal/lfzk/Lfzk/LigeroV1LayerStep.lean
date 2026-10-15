import Lfzk.RbrSplit
import Lfzk.LigeroV1Rows

/-!
# LayerStep's Ligero half, from Ligero V1

`RbrSplit.LigeroData` is the Ligero half of the Longfellow LayerStep: a query test, an escaping set
containing every undoomed challenge, and a bound on a doomed challenge's accepting queries.  This
file builds it from `Lfzk.LigeroV1Rows.Row.rbr_soundness` — that is, from
`Ligero.V1.ligerov1_roundByRound_profiled` on the `formal/ligero` analysis, at a certified V1 row
and the concrete Reed–Solomon code — so none of the three is assumed.

| `LigeroData` field | built from |
|---|---|
| doom predicate | `classifier.ProfiledDoomedAfter ft at` |
| `escaping` | `classifier.profiledEscaping ft at` |
| `hesc` | the theorem's third conjunct |
| `accepting` | `accepting`, the V1 policy's accepting queries (`= classifier.acceptingQueries`) |
| `bq`, `hbq` | `queryCount = ⌊cover · C(n, r)⌋`, from the theorem's first conjunct |

`accepting` is stated without the classifier, so a caller can state acceptance obligations about it
before the classifier exists.

## The two budgets, through the decoders

`ligBudget_le` and `queryBudget_le` turn the theorem's two densities into LayerStep's two slot
counts by `Bcs.card_preimage_le_of_balanced`:

```text
kchal · |escaping|  ≤  ⌊(fail + arith) · |C|⌋      if  kchal · |X| ≤ |C|
kq    · bq          ≤  ⌊cover · |C|⌋               if  kq · |Q| ≤ |C|
```

The side conditions say the decoders are **exactly balanced**.  They cannot be dropped:
`card_preimage_le_of_balanced` charges `kchal` per bad challenge, and a `C → X` decoder has
`kchal ≥ |C|/|X|`, so the count is at most `(fail + arith) · |C|` only when
`kchal · |X| ≤ |C|`.  For V1
`X = Ligero.V1.Challenge F nw nq 1 Equations` is a vector of `|tested rows| + |Equations| + nq`
field elements, so this needs `|C| ≥ |X|`: a 128-bit coin cannot carry the Ligero challenge.

## What is still a premise

The V1 theorem's own: a certified row (`Row.Valid`), `CoreRowsNonempty nw nq`,
`|F| = row.fieldSize`, a Reed–Solomon domain with `r + w = k`, an IPCP prover, and
**`¬ statement.Language`**.  The Ligero statement and prover are fixed per commitment: LayerStep's
doom predicate at `.challenged x` reads `x` only, so a Ligero statement that depended on the
sumcheck prefix would not fit this LayerStep.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.LigeroV1LayerStep

open Finset LigeroFamily CodingTheory
open Lfzk.LigeroV1Rows

/-- The V1 linear-combination challenge: LayerStep's `X`. -/
abbrev Chal (F Equations : Type) (nw nq : ℕ) := Ligero.V1.Challenge F nw nq 1 Equations

/-- The V1 query: an `openings`-subset of the `n` columns, LayerStep's `Q`. -/
abbrev Qry (row : Row) := QuerySet row.n row.openings

/-- One V1 instance at a commitment: the Ligero statement and the IPCP prover answering it. -/
structure Instance (row : Row) (F Equations : Type) (nw nq w : ℕ) where
  statement : ConstraintSystem F nw nq w Equations
  prover : IPCPProver (ConstraintSystem F nw nq w Equations)
    (Ligero.V1.Oracle F nw nq row.n 1) (Ligero.V1.Challenge F nw nq 1 Equations)
    (Response F row.openings w row.n 1)

variable {F Equations : Type} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Equations] [DecidableEq Equations]
variable {row : Row} {nw nq w : ℕ}

/-- The row's Reed–Solomon multiplicative code over the domain `D` (`Row.code`). -/
noncomputable abbrev code (h : row.Valid) (D : ReedSolomon.Domain F row.openings w row.n)
    (hkrow : row.openings + w = row.k) : MultiplicativeCode F row.openings w row.n :=
  Row.code h D hkrow

/-- **The V1 verifier's accepting queries** at a challenge, for the instance's prover: the queries
on which `SchemeVerifier.policy C Ligero.V1.scheme` accepts the prover's response against the
committed oracle's opened columns. -/
noncomputable def accepting (h : row.Valid) (D : ReedSolomon.Domain F row.openings w row.n)
    (hkrow : row.openings + w = row.k) (I : Instance row F Equations nw nq w)
    (x : Chal F Equations nw nq) : Finset (Qry row) := by
  classical
  exact univ.filter fun query =>
    (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1)
      (code h D hkrow) Ligero.V1.scheme).accepts I.statement x
      (I.prover.respond I.statement (I.prover.commit I.statement) x) query
      (openSchemeOracle (I.prover.commit I.statement) query)

/-- The query round's count, `⌊cover · C(n, r)⌋`. -/
def queryCount (row : Row) : ℕ := ⌊row.cover * (row.n.choose row.openings : ℚ)⌋₊

theorem fail_nonneg (row : Row) : 0 ≤ row.fail := by unfold Row.fail; positivity
theorem arith_nonneg (row : Row) : 0 ≤ row.arith := by unfold Row.arith; positivity
theorem cover_nonneg (row : Row) : 0 ≤ row.cover := by
  unfold Row.cover hypergeometricRatio; positivity

theorem openings_le (h : row.Valid) : row.openings ≤ row.n := Row.openings_le h

/--
**LayerStep's Ligero half, from the V1 theorem.**

At a valid row and a false Ligero statement there is a doom predicate on V1 challenges and a
`LigeroData` over it whose query test is `accepting`, whose escaping set has density at most
`fail + arith`, and whose query bound is `queryCount`.

Proof: `Row.rbr_soundness` at the Reed–Solomon code; the doom predicate is the classifier's `ProfiledDoomedAfter` at the row's two
thresholds, `escaping` its `profiledEscaping`, and `hbq` its query density bound read at the
floor.
-/
theorem exists_ligeroData (C : Type) (h : row.Valid) (hrows : CoreRowsNonempty nw nq)
    (hfield : Fintype.card F = row.fieldSize) (D : ReedSolomon.Domain F row.openings w row.n)
    (hkrow : row.openings + w = row.k) (I : Instance row F Equations nw nq w)
    (hfalse : ¬ I.statement.Language) :
    ∃ (LigDoomed : Chal F Equations nw nq → Prop)
      (LD : RbrSplit.LigeroData C (Chal F Equations nw nq) (Qry row) LigDoomed),
      LD.accepting = (fun _ _ => accepting h D hkrow I) ∧
      (LD.escaping.card : ℚ) ≤ (row.fail + row.arith) * Fintype.card (Chal F Equations nw nq) ∧
      LD.bq = queryCount row := by
  classical
  obtain ⟨cl, hq, hesc, hcov⟩ := Row.rbr_soundness h hrows hfield D hkrow
    I.statement I.prover hfalse
  have hchoose : (0 : ℚ) < (row.n.choose row.openings : ℚ) := by
    exact_mod_cast Nat.choose_pos (openings_le h)
  have hcard : ((cl.profiledEscaping row.failureThreshold row.arithmeticThreshold).card : ℚ)
      ≤ (row.fail + row.arith) * Fintype.card (Ligero.V1.Challenge F nw nq 1 Equations) := by
    rcases Nat.eq_zero_or_pos (Fintype.card (Ligero.V1.Challenge F nw nq 1 Equations))
      with hX | hX
    · haveI : IsEmpty (Ligero.V1.Challenge F nw nq 1 Equations) :=
        Fintype.card_eq_zero_iff.mp hX
      rw [Finset.eq_empty_of_isEmpty
        (cl.profiledEscaping row.failureThreshold row.arithmeticThreshold),
        Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg (add_nonneg (fail_nonneg row) (arith_nonneg row)) (Nat.cast_nonneg _)
    · have hXpos : (0 : ℚ) <
          (Fintype.card (Ligero.V1.Challenge F nw nq 1 Equations) : ℚ) := by
        exact_mod_cast hX
      rw [div_le_iff₀ hXpos] at hesc
      exact hesc
  refine ⟨cl.ProfiledDoomedAfter row.failureThreshold row.arithmeticThreshold,
    { accepting := fun _ _ => accepting h D hkrow I
      escaping := cl.profiledEscaping row.failureThreshold row.arithmeticThreshold
      hesc := hcov
      bq := queryCount row
      hbq := ?_ }, rfl, hcard, rfl⟩
  intro m pref x hx
  show (accepting h D hkrow I x).card ≤ queryCount row
  have hdens := hq x hx
  have hacc : cl.acceptingQueries x = accepting h D hkrow I x := rfl
  rw [hacc, div_le_iff₀ hchoose] at hdens
  exact Nat.le_floor hdens

/-! ## The two slot counts, through exactly balanced decoders -/

/-- `k · card ≤ ⌊ρ · |C|⌋` from `card ≤ ρ · |Y|` and `k · |Y| ≤ |C|`. -/
theorem mul_le_floor {k card cardY cardC : ℕ} {ρ : ℚ} (hρ : 0 ≤ ρ)
    (hcard : (card : ℚ) ≤ ρ * cardY) (hbal : k * cardY ≤ cardC) :
    k * card ≤ ⌊ρ * cardC⌋₊ := by
  apply Nat.le_floor
  have hbalQ : ((k : ℚ) * cardY) ≤ cardC := by exact_mod_cast hbal
  calc ((k * card : ℕ) : ℚ) = (k : ℚ) * card := by push_cast; ring
    _ ≤ (k : ℚ) * (ρ * cardY) := mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg _)
    _ = ρ * ((k : ℚ) * cardY) := by ring
    _ ≤ ρ * cardC := mul_le_mul_of_nonneg_left hbalQ hρ

omit [Field F] [DecidableEq F] [DecidableEq Equations] in
/-- **The Ligero challenge slot's count.**  `kchal · |escaping| ≤ ⌊(fail + arith) · |C|⌋`, for an
exactly balanced challenge decoder. -/
theorem ligBudget_le {C : Type} {LigDoomed : Chal F Equations nw nq → Prop}
    {LD : RbrSplit.LigeroData C (Chal F Equations nw nq) (Qry row) LigDoomed} {kchal cardC : ℕ}
    (hesc : (LD.escaping.card : ℚ) ≤ (row.fail + row.arith) * Fintype.card (Chal F Equations nw nq))
    (hbal : kchal * Fintype.card (Chal F Equations nw nq) ≤ cardC) :
    kchal * LD.escaping.card ≤ ⌊(row.fail + row.arith) * cardC⌋₊ :=
  mul_le_floor (add_nonneg (fail_nonneg row) (arith_nonneg row)) hesc hbal

/-- **The Ligero query slot's count.**  `kq · queryCount ≤ ⌊cover · |C|⌋`, for an exactly
balanced query decoder; `|Q| = C(n, r)` is `QuerySet.fintype_card`. -/
theorem queryBudget_le {kq cardC : ℕ} (hbal : kq * Fintype.card (Qry row) ≤ cardC) :
    kq * queryCount row ≤ ⌊row.cover * cardC⌋₊ := by
  refine mul_le_floor (cover_nonneg row) (cardY := row.n.choose row.openings) ?_ ?_
  · exact Nat.floor_le (mul_nonneg (cover_nonneg row) (Nat.cast_nonneg _))
  · simpa [QuerySet.fintype_card] using hbal

end Lfzk.LigeroV1LayerStep
