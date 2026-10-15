import Lfzk.RbrZkSplit
import Lfzk.Encode
import Lfzk.CompiledLongfellowAdaptive

/-!
# The zero-knowledge LayerStep's Ligero half, from Ligero V1 at `NoDecodedSolution`

`Lfzk.RbrZkSplit.ZkLigeroData` asks for a Ligero classifier at every **built system no candidate
satisfies**.  This file builds it from `formal/ligero`'s V1 round-by-round theorem, with the
candidates being the committed oracle's **lift list** and nothing assumed about any statement's
truth.

## The pieces

* `Row.rbr_soundness_noDecoded` — `LigeroV1Rows.Row.rbr_soundness` with its premise
  `¬ statement.Language` replaced by `NoDecodedSolution` (no lift-list member decodes to a
  satisfying tableau).  Same proof: `Row.rbr_soundness` itself only uses the falsity through
  `NoDecodedSolution.of_not_language`.
* `Lift h D hkrow O` — the lift list `SchemeLiftCandidate (row.code …) O (e + g)` of a committed
  V1 oracle `O`, and `asgOf pl ℓ` — a member's assignment, the committed columns and the pad read off
  its decoded tableau at the placement `pl` (`Encode.decode`).  `lift_card_le`: the list has at most
  `row.listBound` members (`SchemeLiftCandidate.univ_card_le_listBound`).
* `noDecoded_of_noSat` — **the doom at the Ligero slot is derived**: if no member's assignment
  satisfies a built system that fits the tableau, then no member decodes to a tableau satisfying its
  encoding `Encode.encodeLig pl nlin sys` (`Encode.sat_decode_encodeLig`, contrapositive), which is
  `NoDecodedSolution`.
* `exists_zkLigeroData` — the Ligero half, with the query test `acceptingR` at the system's encoded
  statement and the committed oracle, read at the response the query slot's message carries; the
  classifier is built at the **maximizing** response strategy (`CompiledLongfellowAdaptive.maxProver`),
  so a doomed challenge has at most `queryCount` accepting queries whatever the response.  Escaping
  density `fail + arith`.

## What is still a premise

The V1 theorem's own: a certified row, `CoreRowsNonempty`, `|F| = row.fieldSize`, a Reed–Solomon
domain with `r + w = k`.  Nothing about the statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.ZkLigeroV1

open Finset LigeroFamily CodingTheory Lfzk.LigeroV1Rows Lfzk.RbrZkLongfellow Lfzk.RbrZkSplit
  Lfzk.CompiledLongfellowAdaptive
open scoped Classical

/-! ## 1. Ligero V1 at `NoDecodedSolution` -/

/-- **`Row.rbr_soundness`, at `NoDecodedSolution`.**  The conclusion is `Row.rbr_soundness`'s; the
premise is that no member of the committed oracle's lift list at radius `e + g` decodes to a
satisfying tableau. -/
theorem Row.rbr_soundness_noDecoded {row : Row} (h : row.Valid)
    {F Equations : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations] {w nw nq : ℕ}
    (hrows : CoreRowsNonempty nw nq)
    (hfield : Fintype.card F = row.fieldSize)
    (D : ReedSolomon.Domain F row.openings w row.n)
    (hkrow : row.openings + w = row.k)
    (statement : ConstraintSystem F nw nq w Equations)
    (prover : IPCPProver
      (ConstraintSystem F nw nq w Equations)
      (Ligero.V1.Oracle F nw nq row.n 1)
      (Ligero.V1.Challenge F nw nq 1 Equations)
      (Response F row.openings w row.n 1))
    (hnd : NoDecodedSolution (row.code h D hkrow) (prover.commit statement) (row.e + row.g)
      statement) :
    ∃ classifier : PolicyDoublyProfiledSoundnessClassifier
        (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq)
          (repetitions := 1) (row.code h D hkrow) Ligero.V1.scheme)
        (prover.commit statement) statement
        (fun challenge ↦ prover.respond statement (prover.commit statement) challenge)
        (row.failureProfileAt (Fintype.card F))
        (maskAgreementProfile (Fintype.card F) row.n row.listBound row.certificate.maskStart
          row.certificate.maskBound)
        (Fintype.card F)
        (SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator (Fintype.card F) row.g)
        row.e row.g,
      (∀ challenge, classifier.ProfiledDoomedAfter
          row.failureThreshold row.arithmeticThreshold challenge →
        ((classifier.acceptingQueries challenge).card : ℚ) /
            (row.n.choose row.openings) ≤ row.cover)
      ∧ ((classifier.profiledEscaping
            row.failureThreshold row.arithmeticThreshold).card : ℚ) /
            Fintype.card (Ligero.V1.Challenge F nw nq 1 Equations) ≤ row.fail + row.arith
      ∧ (∀ challenge, ¬ classifier.ProfiledDoomedAfter
            row.failureThreshold row.arithmeticThreshold challenge →
          challenge ∈ classifier.profiledEscaping
            row.failureThreshold row.arithmeticThreshold) := by
  obtain ⟨hk, hmin, ⟨P⟩⟩ := Row.rsFacts h D hkrow
  have hcond := row.result.lineConditions (Row.parametersValid h) hfield hmin P
  have mask := Ligero.Examples.Grid.V1Certificate.v1MaskRange row.certificate (Row.kpos h)
    (Row.response_le h) (Row.maskValid h) (row.code h D hkrow) hk
  obtain ⟨classifier, hq, hesc, hmem⟩ :=
    Ligero.V1.ligerov1_roundByRound_mask_profiled hrows (row.code h D hkrow) statement prover
      hnd hmin hcond (Row.liftList_card_le h D hkrow _) mask
      row.failureThreshold row.arithmeticThreshold
      (Row.failureThreshold_le h) (Row.arithmeticThreshold_le h)
  refine ⟨classifier, fun challenge hdoom ↦ hq challenge hdoom, ?_, hmem⟩
  refine hesc.trans (le_of_eq ?_)
  simp only [hfield]
  rfl

/-! ## 2. The lift list and its members' assignments -/

section Lift

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {row : Row} {nw nq qw ninp M nt : ℕ}

/-- **The lift list of a committed V1 oracle**, at radius `e + g`. -/
abbrev Lift (h : row.Valid) (D : ReedSolomon.Domain F row.openings qw row.n)
    (hkrow : row.openings + qw = row.k) (O : Ligero.V1.Oracle F nw nq row.n 1) : Type :=
  SchemeLiftCandidate (row.code h D hkrow) O (row.e + row.g)

/-- **A lift-list member's assignment**: the committed columns and the pad, read off its decoded
tableau at the placement. -/
noncomputable def asgOf (pl : Encode.Placement ninp M qw nw nq nt) {h : row.Valid}
    {D : ReedSolomon.Domain F row.openings qw row.n} {hkrow : row.openings + qw = row.k}
    {O : Ligero.V1.Oracle F nw nq row.n 1} (ℓ : Lift h D hkrow O) : LigeroAssignment ninp M F :=
  Encode.decode pl ℓ.decodedMessages

/-- The same decoded assignment at an arbitrary extraction radius. -/
noncomputable def asgAt (pl : Encode.Placement ninp M qw nw nq nt) {h : row.Valid}
    {D : ReedSolomon.Domain F row.openings qw row.n}
    {hkrow : row.openings + qw = row.k}
    {O : Ligero.V1.Oracle F nw nq row.n 1} (radius : ℕ)
    (ℓ : SchemeLiftCandidate (row.code h D hkrow) O radius) :
    LigeroAssignment ninp M F :=
  Encode.decode pl ℓ.decodedMessages

omit [Fintype F] in
@[simp] theorem asgAt_widen (pl : Encode.Placement ninp M qw nw nq nt)
    {h : row.Valid} {D : ReedSolomon.Domain F row.openings qw row.n}
    {hkrow : row.openings + qw = row.k} {O : Ligero.V1.Oracle F nw nq row.n 1}
    {small large : ℕ}
    (ℓ : SchemeLiftCandidate (row.code h D hkrow) O small) (hr : small ≤ large) :
    asgAt pl large (ℓ.widen hr) = asgAt pl small ℓ := by
  simp [asgAt]

omit [Fintype F] in
/-- Failure of extraction at the larger radius implies failure at the existing
round-by-round radius, using the same decoded assignments. -/
theorem noSat_of_larger_radius (pl : Encode.Placement ninp M qw nw nq nt)
    {h : row.Valid} {D : ReedSolomon.Domain F row.openings qw row.n}
    {hkrow : row.openings + qw = row.k} {O : Ligero.V1.Oracle F nw nq row.n 1}
    {small large : ℕ} (hr : small ≤ large) (sys : LigeroSystem ninp M F)
    (hlarge : NoSat (asgAt pl large (h := h) (D := D) (hkrow := hkrow) (O := O)) sys) :
    NoSat (asgAt pl small (h := h) (D := D) (hkrow := hkrow) (O := O)) sys := by
  intro ℓ hsat
  exact hlarge (ℓ.widen hr) (by simpa using hsat)

/-- **The lift list has at most `listBound` members.** -/
theorem lift_card_le (h : row.Valid) (D : ReedSolomon.Domain F row.openings qw row.n)
    (hkrow : row.openings + qw = row.k) (O : Ligero.V1.Oracle F nw nq row.n 1) :
    Fintype.card (Lift h D hkrow O) ≤ row.listBound :=
  Row.liftList_card_le h D hkrow O

/-- The Ligero statement a built system encodes to. -/
noncomputable def stmtOf (pl : Encode.Placement ninp M qw nw nq nt) (nlin : ℕ)
    (sys : LigeroSystem ninp M F) :
    ConstraintSystem F nw nq qw (Fin nlin ⊕ (Fin nt × Encode.QSide)) :=
  Encode.encodeLig pl nlin sys

omit [Fintype F] in
/--
**Doom at the Ligero slot, derived.**  If no lift-list member's assignment satisfies a built system
that fits the tableau, then no member decodes to a tableau satisfying the system's encoding:
`NoDecodedSolution`, the premise `Row.rbr_soundness_noDecoded` charges.
-/
theorem noDecoded_of_noSat (pl : Encode.Placement ninp M qw nw nq nt) (nlin : ℕ)
    (h : row.Valid) (D : ReedSolomon.Domain F row.openings qw row.n)
    (hkrow : row.openings + qw = row.k) (O : Ligero.V1.Oracle F nw nq row.n 1)
    (sys : LigeroSystem ninp M F) (hlin : sys.linear.length ≤ nlin) (hquad : sys.quad.length ≤ nt)
    (hns : NoSat (asgOf pl (h := h) (D := D) (hkrow := hkrow) (O := O)) sys) :
    NoDecodedSolution (row.code h D hkrow) O (row.e + row.g) (stmtOf pl nlin sys) :=
  fun ℓ hsat => hns ℓ (Encode.sat_decode_encodeLig pl hlin hquad _ hsat)

omit [Fintype F] in
/-- The same circuit-to-encoded-statement implication at an arbitrary radius.
This permits the flat extraction certificate to use its own larger lift list. -/
theorem noDecoded_of_noSatAt (pl : Encode.Placement ninp M qw nw nq nt) (nlin radius : ℕ)
    (h : row.Valid) (D : ReedSolomon.Domain F row.openings qw row.n)
    (hkrow : row.openings + qw = row.k) (O : Ligero.V1.Oracle F nw nq row.n 1)
    (sys : LigeroSystem ninp M F) (hlin : sys.linear.length ≤ nlin)
    (hquad : sys.quad.length ≤ nt)
    (hns : NoSat (asgAt pl radius (h := h) (D := D) (hkrow := hkrow) (O := O)) sys) :
    NoDecodedSolution (row.code h D hkrow) O radius (stmtOf pl nlin sys) :=
  fun ℓ hsat => hns ℓ (Encode.sat_decode_encodeLig pl hlin hquad _ hsat)

end Lift

/-! ## 3. The Ligero half -/

section Half

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {row : Row} {nw nq qw : ℕ} {Equations : Type} [Fintype Equations] [DecidableEq Equations]

/-- **One system's Ligero facts, at a statement no lift-list member decodes to satisfy**: a doom
predicate, an escaping set of density `fail + arith`, and at most `queryCount` accepting queries
at a doomed challenge **at every response** (the classifier is at the maximizing prover). -/
theorem exists_sysData (h : row.Valid) (hrows : CoreRowsNonempty nw nq)
    (hfield : Fintype.card F = row.fieldSize) (D : ReedSolomon.Domain F row.openings qw row.n)
    (hkrow : row.openings + qw = row.k) (I : OracleInstance row F Equations nw nq qw)
    (hnd : NoDecodedSolution (row.code h D hkrow) I.oracle (row.e + row.g) I.statement) :
    ∃ (Doom : LigeroV1LayerStep.Chal F Equations nw nq → Prop)
      (esc : Finset (LigeroV1LayerStep.Chal F Equations nw nq)),
      (∀ x, ¬ Doom x → x ∈ esc) ∧
      (esc.card : ℚ) ≤ (row.fail + row.arith)
        * Fintype.card (LigeroV1LayerStep.Chal F Equations nw nq) ∧
      ∀ (x : LigeroV1LayerStep.Chal F Equations nw nq)
        (ρ : Response F row.openings qw row.n 1), Doom x →
        (acceptingR h D hkrow I ρ x).card ≤ LigeroV1LayerStep.queryCount row := by
  classical
  obtain ⟨cl, hq, hesc, hcov⟩ := Row.rbr_soundness_noDecoded h hrows hfield D hkrow I.statement
    (maxProver h D hkrow I) hnd
  have hchoose : (0 : ℚ) < (row.n.choose row.openings : ℚ) := by
    exact_mod_cast Nat.choose_pos (Row.openings_le h)
  have hcard : ((cl.profiledEscaping row.failureThreshold row.arithmeticThreshold).card : ℚ)
      ≤ (row.fail + row.arith) * Fintype.card (Ligero.V1.Challenge F nw nq 1 Equations) := by
    rcases Nat.eq_zero_or_pos (Fintype.card (Ligero.V1.Challenge F nw nq 1 Equations))
      with hX | hX
    · haveI : IsEmpty (Ligero.V1.Challenge F nw nq 1 Equations) :=
        Fintype.card_eq_zero_iff.mp hX
      rw [Finset.eq_empty_of_isEmpty
        (cl.profiledEscaping row.failureThreshold row.arithmeticThreshold),
        Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg (add_nonneg (LigeroV1LayerStep.fail_nonneg row)
        (LigeroV1LayerStep.arith_nonneg row)) (Nat.cast_nonneg _)
    · have hXpos : (0 : ℚ) <
          (Fintype.card (Ligero.V1.Challenge F nw nq 1 Equations) : ℚ) := by
        exact_mod_cast hX
      rw [div_le_iff₀ hXpos] at hesc
      exact hesc
  refine ⟨cl.ProfiledDoomedAfter row.failureThreshold row.arithmeticThreshold,
    cl.profiledEscaping row.failureThreshold row.arithmeticThreshold, hcov, hcard, ?_⟩
  intro x ρ hx
  have hdens := hq x hx
  have hacc : cl.acceptingQueries x = acceptingR h D hkrow I (maxResponse h D hkrow I x) x := rfl
  rw [hacc, div_le_iff₀ hchoose] at hdens
  exact le_trans (card_acceptingR_le_max h D hkrow I ρ x) (Nat.le_floor hdens)

end Half

section Build

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {row : Row} {nw nq qw ninp M nt nlin : ℕ}
variable {C Msg Gpt : Type} {logw logc : ℕ}

/-- The zero-knowledge LayerStep's Ligero challenge type at a V1 row: V1's challenge over the
encoded statement's equations. -/
abbrev Chal (F : Type) [Field F] (nw nq nlin nt : ℕ) :=
  LigeroV1LayerStep.Chal F (Fin nlin ⊕ (Fin nt × Encode.QSide)) nw nq

/-- **The V1 query test at a built system**: V1's policy on the committed oracle's opened
columns, at the system's encoded statement, the response and the challenge. -/
noncomputable def accZ (h : row.Valid) (D : ReedSolomon.Domain F row.openings qw row.n)
    (hkrow : row.openings + qw = row.k) (pl : Encode.Placement ninp M qw nw nq nt) (nlin : ℕ)
    (O : Ligero.V1.Oracle F nw nq row.n 1) (respOf : Msg → Response F row.openings qw row.n 1)
    (_m : ℕ) (_pref : Fin _m → C) (msg : Msg) (sys : LigeroSystem ninp M F)
    (x : Chal F nw nq nlin nt) : Finset (LigeroV1LayerStep.Qry row) :=
  acceptingR h D hkrow ⟨stmtOf pl nlin sys, O⟩ (respOf msg) x

/--
**The zero-knowledge LayerStep's Ligero half, from Ligero V1.**

At a valid row and a committed oracle `O`, for the code `V` whose tableau is the placement's, there
is a `ZkLigeroData` over the lift list's assignments whose query test is `accZ` (V1's policy at the
built system's encoding, at the message's response), whose escaping set at every fitting system no
member satisfies has density at most `fail + arith`, and whose query bound is `queryCount`.
**No premise about any statement's truth.**
-/
theorem exists_zkLigeroData (V : RbrZkLongfellow.ZkCode C F (Chal F nw nq nlin nt)
      (LigeroV1LayerStep.Qry row) Msg Gpt M ninp logw logc)
    (hnlin : V.nlin = nlin) (hnt : V.nt = nt)
    (pl : Encode.Placement ninp M qw nw nq nt)
    (h : row.Valid) (hrows : CoreRowsNonempty nw nq) (hfield : Fintype.card F = row.fieldSize)
    (D : ReedSolomon.Domain F row.openings qw row.n) (hkrow : row.openings + qw = row.k)
    (O : Ligero.V1.Oracle F nw nq row.n 1) (respOf : Msg → Response F row.openings qw row.n 1) :
    ∃ LD : ZkLigeroData C (Chal F nw nq nlin nt) (LigeroV1LayerStep.Qry row) Msg V
        (asgOf pl (h := h) (D := D) (hkrow := hkrow) (O := O)),
      LD.accepting = accZ h D hkrow pl nlin O respOf ∧
      (∀ sys, Fits V sys → NoSat (asgOf pl (h := h) (D := D) (hkrow := hkrow) (O := O)) sys →
        ((LD.escaping sys).card : ℚ) ≤ (row.fail + row.arith)
          * Fintype.card (Chal F nw nq nlin nt)) ∧
      LD.bq = LigeroV1LayerStep.queryCount row := by
  classical
  have key : ∀ sys : LigeroSystem ninp M F, ∃ (Doom : Chal F nw nq nlin nt → Prop)
      (esc : Finset (Chal F nw nq nlin nt)),
      (Fits V sys → NoSat (asgOf pl (h := h) (D := D) (hkrow := hkrow) (O := O)) sys →
        (∀ x, ¬ Doom x → x ∈ esc) ∧
        (esc.card : ℚ) ≤ (row.fail + row.arith) * Fintype.card (Chal F nw nq nlin nt)) ∧
      ∀ (x : Chal F nw nq nlin nt) (ρ : Response F row.openings qw row.n 1), Doom x →
        (acceptingR h D hkrow ⟨stmtOf pl nlin sys, O⟩ ρ x).card
          ≤ LigeroV1LayerStep.queryCount row := by
    intro sys
    by_cases hs : Fits V sys ∧ NoSat (asgOf pl (h := h) (D := D) (hkrow := hkrow) (O := O)) sys
    · have hnd := noDecoded_of_noSat pl nlin h D hkrow O sys (hnlin ▸ hs.1.1) (hnt ▸ hs.1.2) hs.2
      obtain ⟨Doom, esc, hesc, hcard, hbq⟩ := exists_sysData h hrows hfield D hkrow
        ⟨stmtOf pl nlin sys, O⟩ hnd
      exact ⟨Doom, esc, fun _ _ => ⟨hesc, hcard⟩, hbq⟩
    · refine ⟨fun _ => False, ∅, fun h1 h2 => absurd ⟨h1, h2⟩ hs, fun _ _ hx => hx.elim⟩
  choose Doom esc hesc hbq using key
  refine ⟨{ LigDoomed := Doom
            accepting := accZ h D hkrow pl nlin O respOf
            escaping := esc
            hesc := fun sys hf hn => (hesc sys hf hn).1
            bq := LigeroV1LayerStep.queryCount row
            hbq := fun _ _ msg sys x hx => hbq sys x (respOf msg) hx }, rfl,
    fun sys hf hn => (hesc sys hf hn).2, rfl⟩

end Build

end Lfzk.ZkLigeroV1
