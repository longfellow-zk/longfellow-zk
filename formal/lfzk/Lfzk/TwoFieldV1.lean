import Lfzk.CertifiedV1
import Lfzk.TwoFieldLongfellow

/-!
# Two Ligero-V1 Longfellow sides and one MAC slot

`Lfzk.TwoFieldLongfellow.twofield_longfellow_ratio_le` composes two Longfellow sides through the MAC
with no ratio hypothesis, but its sides are `LongfellowFamily`s built on `RbrLongfellow.LayerStepData`,
whose Ligero step is six bare fields.  This file is the same composition with **two
`Lfzk.CertifiedV1` sides**, whose Ligero step is built from the V1 theorem
(`Ligero.V1.ligerov1_roundByRound_profiled`, through `CertifiedV1.Row.nizk_ratio_le_family_bound`):

```text
Pr over (pre, tape) [ both compiled verifiers accept  ∧  the composed extractor fails ]
    ≤  R₁.bound  +  R₂.bound  +  kmac / |C|                      twofield_v1_ratio_le
    ≤  R₁.bound  +  R₂.bound  +  1 / |Fmac|      (kmac·|Fmac| ≤ |C|)   twofield_v1_ratio_le_exact
```

`Rᵢ.bound` is the certified V1 row's exact rational (`CostV1.Params.nizkBound` in densities), so a
two-field row can compare the sum against its own target (`Lfzk.TwoFieldV1Rows`).

## The pieces

1. `side_ratio_le`: `CertifiedV1.Row.nizk_ratio_le_family_bound` with the hash tape's length a
   variable `tlen` and `R.tape = tlen`.  Two sides must share one hash tape `Fin tlen → D`, and their
   rows are two different structures, so their `tape` fields agree only propositionally.
2. `V1Family`: the V1 sibling of `TwoFieldLongfellow.LongfellowFamily`.  Everything the prover
   chooses — adversary, statement, Ligero instance, honest values, satisfaction predicate, field half
   of LayerStep — is a function of the absorbed coordinate `z` (the merged tape off this side's slots,
   including the MAC key coin) and, where LayerStep needs it, of the commitment `pre`.
3. `V1Family.sideBound`: the side as a `TwoFieldBridge.SideBound`, with `bound := R.bound` and
   `sound` a theorem at every `z`.  The extractor is `TwoFieldBridge.chooseE`, so the side's failure
   event is "no satisfying candidate" and the V1 theorem's `hfail` is `id`.
4. `twofield_v1_ratio_le`: `TwoFieldBridge.twofield_merged_ratio_le` at two `sideBound`s.

## What each side still assumes

Exactly `CertifiedV1.Row.nizk_ratio_le_family`'s premises, at every absorbed `z`, and nothing else:

* `hfalse` — when no candidate satisfies the side's circuit, the commitment's Ligero statement is
  false (Ligero's extractor; what the V1 theorem needs);
* `hright` — the compiled verifier's acceptance, with extraction explaining it, implies LayerStep
  reaches `.accepted`, where LayerStep's query test is the V1 verifier's (README gap 1's
  transliteration debt, including that `lig z pre`'s IPCP prover answers as the adversary does);
* `hexact` — the four coin decoders of the field half are exactly balanced
  (`RbrSplit.FieldData.Exact`; satisfiable on one shared alphabet for both sides at once:
  `Lfzk.TwoFieldV1Rows.twoField_coins_exact`);
* `field` — the field half of LayerStep, with `RbrLongfellow`'s premises (`hzero0/1`, `hclaim`,
  `harith`, the boundary maps);
* the protocol's ordinary premises: `|F| = row.fieldSize`, a Reed–Solomon domain, `|Cand|`, `|D|`, and
  the Merkle fuels `ht₁`, `hT`, `hT1` (satisfiable at the row: `Lfzk.TwoFieldV1Rows.fuel_satisfiable`);
* **`hrow`, the MAC row** — a satisfying candidate's witness satisfies the MAC equation at the shared
  key and tag.  The arithmetization assumption (`assert_mac`), kept as an explicit, named hypothesis
  of every composed theorem.

The MAC slot's own data — `decode`, `aP` (a function of the hash tape alone: causality (C3) of
`TwoFieldBridge`), `kmac`, `hbal` — and `1 ≤ T` are the composition's.

## What this does not model

`TwoFieldLongfellow`'s caveat applies verbatim: the merged experiment is the conjunction of two side
verifiers on one sample space, with each side's adversary a family indexed by that side's absorbed
coordinate, and the two sides' Merkle terms are charged on one shared hash tape separately.  There is
no formal two-field driver and so no theorem that every interleaving adversary decomposes into the two
families (`two-field-plan.md` §1).  The Ligero statement and its prover are fixed per commitment, as in
`CertifiedV1`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.TwoFieldV1

open Finset Bcs Merkle Merkle.MH Merkle.RandomOracle
open scoped Classical
open Lfzk.Mac Lfzk.TwoField Lfzk.TwoFieldNizk Lfzk.TwoFieldBridge Lfzk.CertifiedV1

/-! ## 1. One side, at a hash tape of variable length -/

/--
**`CertifiedV1.Row.nizk_ratio_le_family_bound` at a hash tape of length `tlen = R.tape`.**

The same theorem; `tlen` is a variable so that two rows with equal `tape` numerals can share one
prefix type `Fin tlen → D`.
-/
theorem side_ratio_le {R : Row} (h : R.Valid) {tlen : ℕ} (htl : R.tape = tlen)
    {C Cand : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
    {F Equations Witness : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype Equations] [DecidableEq Equations]
    {logw logc nc nv : ℕ}
    {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
    {Enc D Salt M Aux Aux' : Type} {n respondFuel revealFuel : ℕ}
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    {codec : Codec Salt M D Enc} (dec : RoleDecoders codec)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (A : Adversary Enc D Salt M Challenge Response Query Aux Aux'
      n R.commitFuel respondFuel revealFuel)
    (challengeOf : (Fin (Rounds.Role.length R.params.nl R.params.rounds) → C) → Challenge)
    (queryOf : (Fin (Rounds.Role.length R.params.nl R.params.rounds) → C) → Query)
    (statement : (Fin tlen → D) ×
      (Fin (Rounds.Role.length R.params.nl R.params.rounds) → C) → Statement)
    {Fails : (Fin tlen → D) → Prop}
    (hF : Fintype.card F = R.params.row.fieldSize)
    (dom : LigeroFamily.ReedSolomon.Domain F R.params.row.openings R.params.q R.params.row.n)
    (lig : ∀ _pre : Fin tlen → D,
      LigeroV1LayerStep.Instance R.params.row F Equations R.params.nw R.params.nq R.params.q)
    (hfalse : ∀ pre : Fin tlen → D, Fails pre → ¬ (lig pre).statement.Language)
    (H : ∀ _pre : Fin tlen → D, RbrLongfellow.Honest F Cand logw logc)
    (Sat : (Fin tlen → D) → Cand → Prop)
    (Ffam : ∀ pre : Fin tlen → D,
      RbrSplit.FieldData C F (LigeroV1LayerStep.Chal F Equations R.params.nw R.params.nq)
        (LigeroV1LayerStep.Qry R.params.row) Cand Witness nc nv logw logc (H pre) (Sat pre))
    (hexact : ∀ pre : Fin tlen → D, (Ffam pre).Exact)
    (hfail : ∀ pre : Fin tlen → D, Fails pre → ∀ cand : Cand, ¬ Sat pre cand)
    (hright : ∀ pre : Fin tlen → D, Fails pre →
      ∀ tape : Fin (Rounds.Role.length R.params.nl R.params.rounds) → C,
        (CompiledAccepts K A codec (statement (pre, tape))
            (challengeOf tape) (queryOf tape) pre ∧
          ExtractionExplains codec dec n R.commitFuel (revealFuel + respondFuel) tlen
            A.commit (A.openingStage (challengeOf tape) (queryOf tape)) pre) →
        RbrSplit.LayerStepAccepts
          (RbrSplit.stepsOf (nl := R.params.nl) (w := R.params.rounds) (Ffam pre)
            (fun _ _ => LigeroV1LayerStep.accepting (Row.rowValid h) dom (Row.hkrow h) (lig pre)))
          tape)
    (ht₁ : R.commitFuel ≤ tlen)
    (hT : 2 * n + (revealFuel + respondFuel) + R.commitFuel ≤ tlen) (hT1 : 1 ≤ tlen)
    (hcand : Fintype.card Cand = R.cardCand)
    (hD : Fintype.card D = 2 ^ R.params.digestBits) :
    ((univ.filter fun omega : (Fin tlen → D) ×
          (Fin (Rounds.Role.length R.params.nl R.params.rounds) → C) =>
        CompiledAccepts K A codec (statement omega)
            (challengeOf omega.2) (queryOf omega.2) omega.1 ∧ Fails omega.1).card : ℚ)
        / (Fintype.card (Fin tlen → D) *
            (Fintype.card C : ℚ) ^ Rounds.Role.length R.params.nl R.params.rounds)
      ≤ R.bound := by
  subst htl
  exact Row.nizk_ratio_le_family_bound h dec K A challengeOf queryOf statement hF dom lig hfalse
    H Sat Ffam hexact hfail hright ht₁ hT hT1 hcand hD

/-! ## 2. One side, as a family over the absorbed coordinate -/

/--
**One Ligero-V1 Longfellow side of a two-field argument.**

The protocol — the certified row `R` and its validity `hR`, compiler `K`, codec decoders `dec`, the
verifier's challenge and query derivations, the Reed–Solomon domain `dom` — is fixed.  Everything the
prover chooses is a function of the absorbed coordinate `z`; LayerStep's honest values, satisfaction
predicate, Ligero instance and field half are in addition functions of the commitment `pre`.

The fields after `field` are `CertifiedV1.Row.nizk_ratio_le_family`'s premises at every `z`, with
`Fails pre := ∀ cand, ¬ Sat z pre cand` (the failure event of the choosing extractor); the last seven
are the protocol's ordinary numeric premises.
-/
structure V1Family (R : Row) (hR : R.Valid) (Z : Type) (C : Type) [Fintype C]
    (Cand F Equations Witness : Type) [Fintype Cand] [Field F] [Fintype F] [DecidableEq F]
    [SumcheckInterp F] [Fintype Equations] [DecidableEq Equations]
    (nc nv logw logc : ℕ)
    {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
    {Enc D Salt M : Type} [Fintype D] [Inhabited D] [DecidableEq D] [DecidableEq Enc]
    [Inhabited Salt] [Inhabited M]
    (Aux Aux' : Type) (tlen n respondFuel revealFuel : ℕ)
    {codec : Codec Salt M D Enc} (dec : RoleDecoders codec)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (challengeOf : (Fin (Rounds.Role.length R.params.nl R.params.rounds) → C) → Challenge)
    (queryOf : (Fin (Rounds.Role.length R.params.nl R.params.rounds) → C) → Query)
    (dom : LigeroFamily.ReedSolomon.Domain F R.params.row.openings R.params.q R.params.row.n) where
  /-- The side's adversary, at each value of the coordinates it does not read. -/
  A : Z → Adversary Enc D Salt M Challenge Response Query Aux Aux'
    n R.commitFuel respondFuel revealFuel
  /-- The side's statement — in a two-field argument it includes the MAC key and tag. -/
  statement : Z → (Fin tlen → D) × (Fin (Rounds.Role.length R.params.nl R.params.rounds) → C) →
    Statement
  /-- The commitment's Ligero V1 instance: statement and IPCP prover. -/
  lig : Z → (Fin tlen → D) →
    LigeroV1LayerStep.Instance R.params.row F Equations R.params.nw R.params.nq R.params.q
  /-- LayerStep's honest values, per commitment. -/
  H : Z → (Fin tlen → D) → RbrLongfellow.Honest F Cand logw logc
  /-- Which candidates satisfy the side's circuit, per commitment. -/
  Sat : Z → (Fin tlen → D) → Cand → Prop
  /-- The field half of LayerStep, per commitment. -/
  field : ∀ (z : Z) (pre : Fin tlen → D),
    RbrSplit.FieldData C F (LigeroV1LayerStep.Chal F Equations R.params.nw R.params.nq)
      (LigeroV1LayerStep.Qry R.params.row) Cand Witness nc nv logw logc (H z pre) (Sat z pre)
  /-- Its decoders are exactly balanced. -/
  hexact : ∀ (z : Z) (pre : Fin tlen → D), (field z pre).Exact
  /-- **Ligero's extractor**: no satisfying candidate means a false Ligero statement. -/
  hfalse : ∀ (z : Z) (pre : Fin tlen → D), (∀ cand : Cand, ¬ Sat z pre cand) →
    ¬ (lig z pre).statement.Language
  /-- **Acceptance implies LayerStep accepts**, with the V1 verifier's query test. -/
  hright : ∀ (z : Z) (pre : Fin tlen → D), (∀ cand : Cand, ¬ Sat z pre cand) →
    ∀ tape : Fin (Rounds.Role.length R.params.nl R.params.rounds) → C,
      (CompiledAccepts K (A z) codec (statement z (pre, tape))
          (challengeOf tape) (queryOf tape) pre ∧
        ExtractionExplains codec dec n R.commitFuel (revealFuel + respondFuel) tlen
          (A z).commit ((A z).openingStage (challengeOf tape) (queryOf tape)) pre) →
      RbrSplit.LayerStepAccepts
        (RbrSplit.stepsOf (nl := R.params.nl) (w := R.params.rounds) (field z pre)
          (fun _ _ => LigeroV1LayerStep.accepting (Row.rowValid hR) dom (Row.hkrow hR) (lig z pre)))
        tape
  /-- The side's row and the shared hash tape agree on its length. -/
  htape : R.tape = tlen
  hF : Fintype.card F = R.params.row.fieldSize
  hcand : Fintype.card Cand = R.cardCand
  hD : Fintype.card D = 2 ^ R.params.digestBits
  /-- The Merkle extractor's fuels. -/
  ht₁ : R.commitFuel ≤ tlen
  hT : 2 * n + (revealFuel + respondFuel) + R.commitFuel ≤ tlen
  hT1 : 1 ≤ tlen

namespace V1Family

variable {R : Row} {hR : R.Valid} {Z : Type} {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {Cand F Equations Witness : Type} [Fintype Cand] [Nonempty Cand] [Field F] [Fintype F]
  [DecidableEq F] [SumcheckInterp F] [Fintype Equations] [DecidableEq Equations]
variable {nc nv logw logc : ℕ}
variable {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
variable {Enc D Salt M : Type} [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc]
  [Inhabited Salt] [Inhabited M]
variable {Aux Aux' : Type} {tlen n respondFuel revealFuel : ℕ}
variable {codec : Codec Salt M D Enc} {dec : RoleDecoders codec}
variable {K : Compiler Statement Oracle Challenge Response Query Opening M n}
variable {challengeOf : (Fin (Rounds.Role.length R.params.nl R.params.rounds) → C) → Challenge}
variable {queryOf : (Fin (Rounds.Role.length R.params.nl R.params.rounds) → C) → Query}
variable {dom : LigeroFamily.ReedSolomon.Domain F R.params.row.openings R.params.q R.params.row.n}
variable (L : V1Family R hR Z C Cand F Equations Witness nc nv logw logc Aux Aux' tlen n
  respondFuel revealFuel dec K challengeOf queryOf dom)

/-- The side's **compiled** verifier at absorbed coordinate `z`. -/
def accepts (z : Z)
    (x : (Fin tlen → D) × (Fin (Rounds.Role.length R.params.nl R.params.rounds) → C)) : Prop :=
  CompiledAccepts K (L.A z) codec (L.statement z x) (challengeOf x.2) (queryOf x.2) x.1

/-- A good witness: the witness of a candidate that satisfies the side's circuit. -/
def good (z : Z) (x : (Fin tlen → D) × (Fin (Rounds.Role.length R.params.nl R.params.rounds) → C))
    (a : Witness) : Prop :=
  ∃ cand : Cand, L.Sat z x.1 cand ∧ (L.field z x.1).wOf cand = a

omit [DecidableEq C] [Nonempty C] [Nonempty Cand] in
/-- **No good witness iff no satisfying candidate**: the extractor's failure is the V1 theorem's
`Fails`, and its `hfail` is `id`. -/
theorem good_iff (z : Z)
    (x : (Fin tlen → D) × (Fin (Rounds.Role.length R.params.nl R.params.rounds) → C)) :
    (∀ a, ¬ L.good z x a) ↔ ∀ cand : Cand, ¬ L.Sat z x.1 cand := by
  constructor
  · intro h cand hsat
    exact h _ ⟨cand, hsat, rfl⟩
  · rintro h a ⟨cand, hsat, _⟩
    exact h cand hsat

/--
**The single-field V1 bound, at every absorbed coordinate.**  `side_ratio_le` at `L`'s data, with
`Fails pre := ∀ cand, ¬ Sat z pre cand`.
-/
theorem ratio_le (z : Z) :
    ((univ.filter fun omega : (Fin tlen → D) ×
          (Fin (Rounds.Role.length R.params.nl R.params.rounds) → C) =>
        CompiledAccepts K (L.A z) codec (L.statement z omega)
            (challengeOf omega.2) (queryOf omega.2) omega.1 ∧
          ∀ cand : Cand, ¬ L.Sat z omega.1 cand).card : ℚ)
        / (Fintype.card (Fin tlen → D) *
            (Fintype.card C : ℚ) ^ Rounds.Role.length R.params.nl R.params.rounds)
      ≤ R.bound := by
  refine le_trans (le_of_eq ?_) (side_ratio_le hR L.htape dec K (L.A z) challengeOf queryOf
    (L.statement z) (Fails := fun pre => ∀ cand : Cand, ¬ L.Sat z pre cand) L.hF dom (L.lig z)
    (L.hfalse z) (L.H z) (L.Sat z) (L.field z) (L.hexact z) (fun _ h => h) (L.hright z)
    L.ht₁ L.hT L.hT1 L.hcand L.hD)
  congr 3
  ext x
  simp only [Finset.mem_filter]

/-- **The side, as a `SideBound`**, with the row's exact bound. -/
noncomputable def sideBound :
    SideBound Z (Fin tlen → D) C (Rounds.Role.length R.params.nl R.params.rounds) Witness where
  accepts := L.accepts
  good := L.good
  bound := R.bound
  sound z := by
    have h := L.ratio_le z
    refine le_trans (le_of_eq ?_) h
    congr 3
    exact Finset.filter_congr (fun x _ => and_congr_right fun _ => L.good_iff z x)

@[simp] theorem sideBound_bound : L.sideBound.bound = R.bound := rfl

end V1Family

/-! ## 3. Two sides on one tape -/

namespace V1Family

variable {R : Row} {hR : R.Valid} {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {D : Type} [Fintype D] [DecidableEq D] [Inhabited D]
variable {Fmac : Type} [Field Fmac] {nblk tlen T : ℕ}
variable {Cand F Equations Witness : Type} [Fintype Cand] [Nonempty Cand] [Field F] [Fintype F]
  [DecidableEq F] [SumcheckInterp F] [Fintype Equations] [DecidableEq Equations]
variable {nc nv logw logc : ℕ}
variable {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
variable {Enc Salt M : Type} [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
variable {Aux Aux' : Type} {n respondFuel revealFuel : ℕ}
variable {codec : Codec Salt M D Enc} {dec : RoleDecoders codec}
variable {K : Compiler Statement Oracle Challenge Response Query Opening M n}
variable {challengeOf : (Fin (Rounds.Role.length R.params.nl R.params.rounds) → C) → Challenge}
variable {queryOf : (Fin (Rounds.Role.length R.params.nl R.params.rounds) → C) → Query}
variable {dom : LigeroFamily.ReedSolomon.Domain F R.params.row.openings R.params.q R.params.row.n}
variable {ι : Fin (Rounds.Role.length R.params.nl R.params.rounds) → Fin T}
variable (L : V1Family R hR (Rest ι → C) C Cand F Equations Witness nc nv logw logc Aux Aux'
  tlen n respondFuel revealFuel dec K challengeOf queryOf dom)

/-- **The MAC row, per candidate, lifted to the merged sample space.**  `hrow` is the
arithmetization assumption, and it stays a hypothesis. -/
theorem mergedRow {keyA : (Fin tlen → D) × (Fin T → C) → Fmac}
    {keyB tag : (Fin tlen → D) × (Fin T → C) → Fin nblk → Fmac}
    (common : Witness → Fin nblk → Fmac)
    (hrow : ∀ (ω : (Fin tlen → D) × (Fin T → C)) (cand : Cand),
      L.accepts (restOf ι ω.2) (ω.1, ω.2 ∘ ι) → L.Sat (restOf ι ω.2) ω.1 cand →
      macTag (keyA ω) (keyB ω) (common ((L.field (restOf ι ω.2) ω.1).wOf cand)) = tag ω) :
    ∀ (ω : (Fin tlen → D) × (Fin T → C)) (a : Witness),
      L.sideBound.mergedAccepts ω → L.sideBound.mergedGood ω a →
      macTag (keyA ω) (keyB ω) (common a) = tag ω := by
  rintro ω a hacc ⟨cand, hsat, rfl⟩
  exact hrow ω cand hacc hsat

/-- **One V1 side as a `MacBound` on the merged tape.** -/
noncomputable def macSide {keyA : (Fin tlen → D) × (Fin T → C) → Fmac}
    {keyB tag : (Fin tlen → D) × (Fin T → C) → Fin nblk → Fmac}
    (common : Witness → Fin nblk → Fmac)
    (hrow : ∀ (ω : (Fin tlen → D) × (Fin T → C)) (cand : Cand),
      L.accepts (restOf ι ω.2) (ω.1, ω.2 ∘ ι) → L.Sat (restOf ι ω.2) ω.1 cand →
      macTag (keyA ω) (keyB ω) (common ((L.field (restOf ι ω.2) ω.1).wOf cand)) = tag ω) :
    MacBound Fmac nblk ((Fin tlen → D) × (Fin T → C)) keyA keyB tag Witness :=
  L.sideBound.toMacBound common (L.mergedRow common hrow)

/-- `macSide`'s acceptance is the side's compiled verifier on its own slots. -/
@[simp] theorem macSide_accepts {keyA : (Fin tlen → D) × (Fin T → C) → Fmac}
    {keyB tag : (Fin tlen → D) × (Fin T → C) → Fin nblk → Fmac}
    (common : Witness → Fin nblk → Fmac)
    (hrow : ∀ (ω : (Fin tlen → D) × (Fin T → C)) (cand : Cand),
      L.accepts (restOf ι ω.2) (ω.1, ω.2 ∘ ι) → L.Sat (restOf ι ω.2) ω.1 cand →
      macTag (keyA ω) (keyB ω) (common ((L.field (restOf ι ω.2) ω.1).wOf cand)) = tag ω)
    (ω : (Fin tlen → D) × (Fin T → C)) :
    (L.macSide common hrow).accepts ω
      = CompiledAccepts K (L.A (restOf ι ω.2)) codec (L.statement (restOf ι ω.2) (ω.1, ω.2 ∘ ι))
          (challengeOf (ω.2 ∘ ι)) (queryOf (ω.2 ∘ ι)) ω.1 := rfl

/-- `macSide`'s extractor fails exactly when no candidate satisfies the side's circuit. -/
theorem macSide_E_eq_none_iff {keyA : (Fin tlen → D) × (Fin T → C) → Fmac}
    {keyB tag : (Fin tlen → D) × (Fin T → C) → Fin nblk → Fmac}
    (common : Witness → Fin nblk → Fmac)
    (hrow : ∀ (ω : (Fin tlen → D) × (Fin T → C)) (cand : Cand),
      L.accepts (restOf ι ω.2) (ω.1, ω.2 ∘ ι) → L.Sat (restOf ι ω.2) ω.1 cand →
      macTag (keyA ω) (keyB ω) (common ((L.field (restOf ι ω.2) ω.1).wOf cand)) = tag ω)
    (ω : (Fin tlen → D) × (Fin T → C)) :
    (L.macSide common hrow).E ω = none ↔ ∀ cand : Cand, ¬ L.Sat (restOf ι ω.2) ω.1 cand :=
  (chooseE_eq_none_iff _ ω).trans (L.good_iff _ _)

/-- An extracted witness is a satisfying candidate's witness. -/
theorem macSide_E_spec {keyA : (Fin tlen → D) × (Fin T → C) → Fmac}
    {keyB tag : (Fin tlen → D) × (Fin T → C) → Fin nblk → Fmac}
    (common : Witness → Fin nblk → Fmac)
    (hrow : ∀ (ω : (Fin tlen → D) × (Fin T → C)) (cand : Cand),
      L.accepts (restOf ι ω.2) (ω.1, ω.2 ∘ ι) → L.Sat (restOf ι ω.2) ω.1 cand →
      macTag (keyA ω) (keyB ω) (common ((L.field (restOf ι ω.2) ω.1).wOf cand)) = tag ω)
    {ω : (Fin tlen → D) × (Fin T → C)} {a : Witness}
    (h : (L.macSide common hrow).E ω = some a) :
    ∃ cand : Cand, L.Sat (restOf ι ω.2) ω.1 cand ∧ (L.field (restOf ι ω.2) ω.1).wOf cand = a :=
  chooseE_spec h

end V1Family

/-! ## 4. The composed theorem -/

section Compose

open V1Family

variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {D : Type} [Fintype D] [DecidableEq D] [Inhabited D]
-- no `[DecidableEq Fmac]`: see the comment at `Lfzk.TwoFieldNizk`'s variable block
variable {Fmac : Type} [Field Fmac] {nblk tlen T : ℕ}
-- side 1
variable {R₁ : Row} {h₁ : R₁.Valid}
variable {Cand₁ F₁ Equations₁ Witness₁ : Type} [Fintype Cand₁] [Nonempty Cand₁] [Field F₁]
  [Fintype F₁] [DecidableEq F₁] [SumcheckInterp F₁] [Fintype Equations₁] [DecidableEq Equations₁]
variable {nc₁ nv₁ logw₁ logc₁ : ℕ}
variable {Statement₁ Oracle₁ Challenge₁ Response₁ Query₁ : Type} {Opening₁ : Query₁ → Type}
variable {Enc₁ Salt₁ M₁ : Type} [DecidableEq Enc₁] [Inhabited Salt₁] [Inhabited M₁]
variable {Aux₁ Aux₁' : Type} {n₁ respondFuel₁ revealFuel₁ : ℕ}
variable {codec₁ : Codec Salt₁ M₁ D Enc₁} {dec₁ : RoleDecoders codec₁}
variable {K₁ : Compiler Statement₁ Oracle₁ Challenge₁ Response₁ Query₁ Opening₁ M₁ n₁}
variable {challengeOf₁ : (Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) → C) → Challenge₁}
variable {queryOf₁ : (Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) → C) → Query₁}
variable {dom₁ : LigeroFamily.ReedSolomon.Domain F₁ R₁.params.row.openings R₁.params.q
  R₁.params.row.n}
-- side 2
variable {R₂ : Row} {h₂ : R₂.Valid}
variable {Cand₂ F₂ Equations₂ Witness₂ : Type} [Fintype Cand₂] [Nonempty Cand₂] [Field F₂]
  [Fintype F₂] [DecidableEq F₂] [SumcheckInterp F₂] [Fintype Equations₂] [DecidableEq Equations₂]
variable {nc₂ nv₂ logw₂ logc₂ : ℕ}
variable {Statement₂ Oracle₂ Challenge₂ Response₂ Query₂ : Type} {Opening₂ : Query₂ → Type}
variable {Enc₂ Salt₂ M₂ : Type} [DecidableEq Enc₂] [Inhabited Salt₂] [Inhabited M₂]
variable {Aux₂ Aux₂' : Type} {n₂ respondFuel₂ revealFuel₂ : ℕ}
variable {codec₂ : Codec Salt₂ M₂ D Enc₂} {dec₂ : RoleDecoders codec₂}
variable {K₂ : Compiler Statement₂ Oracle₂ Challenge₂ Response₂ Query₂ Opening₂ M₂ n₂}
variable {challengeOf₂ : (Fin (Rounds.Role.length R₂.params.nl R₂.params.rounds) → C) → Challenge₂}
variable {queryOf₂ : (Fin (Rounds.Role.length R₂.params.nl R₂.params.rounds) → C) → Query₂}
variable {dom₂ : LigeroFamily.ReedSolomon.Domain F₂ R₂.params.row.openings R₂.params.q
  R₂.params.row.n}

/--
**Two Ligero-V1 Longfellow sides and one MAC slot, end to end.**

Side `i` is a `V1Family` at the certified V1 row `Rᵢ`, over the merged tape's slots off `sch.ιᵢ`; the
MAC key is `aP pre + decode (tape sch.s)`, with `aP` a function of the shared hash tape alone; `hrowᵢ`
is side `i`'s MAC row.  Then

```text
Pr over (pre, tape) [ both compiled verifiers accept  ∧  the composed extractor fails ]
    ≤  R₁.bound  +  R₂.bound  +  kmac / |C|
```

There is no ratio hypothesis.  Each side's bound on the merged tape is
`CertifiedV1.Row.nizk_ratio_le_family_bound` at every absorbed coordinate (`V1Family.ratio_le`),
moved onto the merged tape by `TwoFieldBridge.ratio_transfer`; the MAC term is
`TwoFieldNizk.mac_slot_ratio`.
-/
theorem twofield_v1_ratio_le
    (sch : Schedule (Rounds.Role.length R₁.params.nl R₁.params.rounds)
      (Rounds.Role.length R₂.params.nl R₂.params.rounds) T)
    (L₁ : V1Family R₁ h₁ (Rest sch.ι₁ → C) C Cand₁ F₁ Equations₁ Witness₁ nc₁ nv₁ logw₁ logc₁
      Aux₁ Aux₁' tlen n₁ respondFuel₁ revealFuel₁ dec₁ K₁ challengeOf₁ queryOf₁ dom₁)
    (L₂ : V1Family R₂ h₂ (Rest sch.ι₂ → C) C Cand₂ F₂ Equations₂ Witness₂ nc₂ nv₂ logw₂ logc₂
      Aux₂ Aux₂' tlen n₂ respondFuel₂ revealFuel₂ dec₂ K₂ challengeOf₂ queryOf₂ dom₂)
    (decode : C → Fmac) (aP : (Fin tlen → D) → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    {keyB tag : (Fin tlen → D) × (Fin T → C) → Fin nblk → Fmac}
    (common₁ : Witness₁ → Fin nblk → Fmac)
    (hrow₁ : ∀ (ω : (Fin tlen → D) × (Fin T → C)) (cand : Cand₁),
      L₁.accepts (restOf sch.ι₁ ω.2) (ω.1, ω.2 ∘ sch.ι₁) → L₁.Sat (restOf sch.ι₁ ω.2) ω.1 cand →
      macTag (aP ω.1 + decode (ω.2 sch.s)) (keyB ω)
        (common₁ ((L₁.field (restOf sch.ι₁ ω.2) ω.1).wOf cand)) = tag ω)
    (common₂ : Witness₂ → Fin nblk → Fmac)
    (hrow₂ : ∀ (ω : (Fin tlen → D) × (Fin T → C)) (cand : Cand₂),
      L₂.accepts (restOf sch.ι₂ ω.2) (ω.1, ω.2 ∘ sch.ι₂) → L₂.Sat (restOf sch.ι₂ ω.2) ω.1 cand →
      macTag (aP ω.1 + decode (ω.2 sch.s)) (keyB ω)
        (common₂ ((L₂.field (restOf sch.ι₂ ω.2) ω.1).wOf cand)) = tag ω)
    (hT : 1 ≤ T) :
    ((univ.filter fun ω : (Fin tlen → D) × (Fin T → C) =>
        (L₁.macSide common₁ hrow₁).accepts ω ∧ (L₂.macSide common₂ hrow₂).accepts ω ∧
          composedE (L₁.macSide common₁ hrow₁) (L₂.macSide common₂ hrow₂) ω = none).card : ℚ)
        / (Fintype.card (Fin tlen → D) * (Fintype.card C : ℚ) ^ T)
      ≤ R₁.bound + R₂.bound + (kmac : ℚ) / (Fintype.card C : ℚ) :=
  twofield_merged_ratio_le sch decode aP kmac hbal
    L₁.sideBound common₁ (L₁.mergedRow common₁ hrow₁)
    L₂.sideBound common₂ (L₂.mergedRow common₂ hrow₂) hT

omit [DecidableEq C] in
/-- **An exactly balanced key decoder costs `1/|Fmac|`.**  `kmac/|C| ≤ 1/|Fmac|` from
`kmac · |Fmac| ≤ |C|`. -/
theorem mac_term_le [Fintype Fmac] {kmac : ℕ} (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C) :
    (kmac : ℚ) / (Fintype.card C : ℚ) ≤ 1 / (Fintype.card Fmac : ℚ) := by
  have hC : (0 : ℚ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  have hF : (0 : ℚ) < Fintype.card Fmac := by exact_mod_cast Fintype.card_pos
  rw [div_le_div_iff₀ hC hF, one_mul]
  exact_mod_cast hmac

/--
**At an exactly balanced key decoder**: the MAC slot costs `1/|Fmac|`, the interactive analysis's
number (`Lfzk.Mac.macKeyBad_card`), whatever the coin alphabet.

```text
Pr [ both accept  ∧  the composed extractor fails ]  ≤  R₁.bound + R₂.bound + 1/|Fmac|
```
-/
theorem twofield_v1_ratio_le_exact [Fintype Fmac]
    (sch : Schedule (Rounds.Role.length R₁.params.nl R₁.params.rounds)
      (Rounds.Role.length R₂.params.nl R₂.params.rounds) T)
    (L₁ : V1Family R₁ h₁ (Rest sch.ι₁ → C) C Cand₁ F₁ Equations₁ Witness₁ nc₁ nv₁ logw₁ logc₁
      Aux₁ Aux₁' tlen n₁ respondFuel₁ revealFuel₁ dec₁ K₁ challengeOf₁ queryOf₁ dom₁)
    (L₂ : V1Family R₂ h₂ (Rest sch.ι₂ → C) C Cand₂ F₂ Equations₂ Witness₂ nc₂ nv₂ logw₂ logc₂
      Aux₂ Aux₂' tlen n₂ respondFuel₂ revealFuel₂ dec₂ K₂ challengeOf₂ queryOf₂ dom₂)
    (decode : C → Fmac) (aP : (Fin tlen → D) → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    {keyB tag : (Fin tlen → D) × (Fin T → C) → Fin nblk → Fmac}
    (common₁ : Witness₁ → Fin nblk → Fmac)
    (hrow₁ : ∀ (ω : (Fin tlen → D) × (Fin T → C)) (cand : Cand₁),
      L₁.accepts (restOf sch.ι₁ ω.2) (ω.1, ω.2 ∘ sch.ι₁) → L₁.Sat (restOf sch.ι₁ ω.2) ω.1 cand →
      macTag (aP ω.1 + decode (ω.2 sch.s)) (keyB ω)
        (common₁ ((L₁.field (restOf sch.ι₁ ω.2) ω.1).wOf cand)) = tag ω)
    (common₂ : Witness₂ → Fin nblk → Fmac)
    (hrow₂ : ∀ (ω : (Fin tlen → D) × (Fin T → C)) (cand : Cand₂),
      L₂.accepts (restOf sch.ι₂ ω.2) (ω.1, ω.2 ∘ sch.ι₂) → L₂.Sat (restOf sch.ι₂ ω.2) ω.1 cand →
      macTag (aP ω.1 + decode (ω.2 sch.s)) (keyB ω)
        (common₂ ((L₂.field (restOf sch.ι₂ ω.2) ω.1).wOf cand)) = tag ω)
    (hT : 1 ≤ T) :
    ((univ.filter fun ω : (Fin tlen → D) × (Fin T → C) =>
        (L₁.macSide common₁ hrow₁).accepts ω ∧ (L₂.macSide common₂ hrow₂).accepts ω ∧
          composedE (L₁.macSide common₁ hrow₁) (L₂.macSide common₂ hrow₂) ω = none).card : ℚ)
        / (Fintype.card (Fin tlen → D) * (Fintype.card C : ℚ) ^ T)
      ≤ R₁.bound + R₂.bound + 1 / (Fintype.card Fmac : ℚ) := by
  refine le_trans (twofield_v1_ratio_le sch L₁ L₂ decode aP kmac hbal common₁ hrow₁ common₂ hrow₂
    hT) ?_
  have := mac_term_le (C := C) hmac
  linarith

/--
**At Protocol 3.8's schedule.**  `twofield_v1_ratio_le_exact` at `Schedule.keyFirst`: the key
challenge `k_v` at slot `0`, then side 1's coins, then side 2's, on a tape of length `1 + T₁ + T₂`.
-/
theorem twofield_v1_ratio_le_keyFirst [Fintype Fmac]
    (L₁ : V1Family R₁ h₁
      (Rest (Schedule.keyFirst (Rounds.Role.length R₁.params.nl R₁.params.rounds)
        (Rounds.Role.length R₂.params.nl R₂.params.rounds)).ι₁ → C)
      C Cand₁ F₁ Equations₁ Witness₁ nc₁ nv₁ logw₁ logc₁
      Aux₁ Aux₁' tlen n₁ respondFuel₁ revealFuel₁ dec₁ K₁ challengeOf₁ queryOf₁ dom₁)
    (L₂ : V1Family R₂ h₂
      (Rest (Schedule.keyFirst (Rounds.Role.length R₁.params.nl R₁.params.rounds)
        (Rounds.Role.length R₂.params.nl R₂.params.rounds)).ι₂ → C)
      C Cand₂ F₂ Equations₂ Witness₂ nc₂ nv₂ logw₂ logc₂
      Aux₂ Aux₂' tlen n₂ respondFuel₂ revealFuel₂ dec₂ K₂ challengeOf₂ queryOf₂ dom₂)
    (decode : C → Fmac) (aP : (Fin tlen → D) → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    {keyB tag : (Fin tlen → D) ×
      (Fin (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds
        + Rounds.Role.length R₂.params.nl R₂.params.rounds) → C) → Fin nblk → Fmac}
    (common₁ : Witness₁ → Fin nblk → Fmac)
    (hrow₁ : ∀ (ω : (Fin tlen → D) ×
        (Fin (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds
          + Rounds.Role.length R₂.params.nl R₂.params.rounds) → C)) (cand : Cand₁),
      L₁.accepts (restOf (Schedule.keyFirst _ _).ι₁ ω.2) (ω.1, ω.2 ∘ (Schedule.keyFirst _ _).ι₁) →
      L₁.Sat (restOf (Schedule.keyFirst _ _).ι₁ ω.2) ω.1 cand →
      macTag (aP ω.1 + decode (ω.2 (Schedule.keyFirst _ _).s)) (keyB ω)
        (common₁ ((L₁.field (restOf (Schedule.keyFirst _ _).ι₁ ω.2) ω.1).wOf cand)) = tag ω)
    (common₂ : Witness₂ → Fin nblk → Fmac)
    (hrow₂ : ∀ (ω : (Fin tlen → D) ×
        (Fin (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds
          + Rounds.Role.length R₂.params.nl R₂.params.rounds) → C)) (cand : Cand₂),
      L₂.accepts (restOf (Schedule.keyFirst _ _).ι₂ ω.2) (ω.1, ω.2 ∘ (Schedule.keyFirst _ _).ι₂) →
      L₂.Sat (restOf (Schedule.keyFirst _ _).ι₂ ω.2) ω.1 cand →
      macTag (aP ω.1 + decode (ω.2 (Schedule.keyFirst _ _).s)) (keyB ω)
        (common₂ ((L₂.field (restOf (Schedule.keyFirst _ _).ι₂ ω.2) ω.1).wOf cand)) = tag ω) :
    ((univ.filter fun ω : (Fin tlen → D) ×
          (Fin (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds
            + Rounds.Role.length R₂.params.nl R₂.params.rounds) → C) =>
        (L₁.macSide common₁ hrow₁).accepts ω ∧ (L₂.macSide common₂ hrow₂).accepts ω ∧
          composedE (L₁.macSide common₁ hrow₁) (L₂.macSide common₂ hrow₂) ω = none).card : ℚ)
        / (Fintype.card (Fin tlen → D) *
            (Fintype.card C : ℚ) ^ (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds
              + Rounds.Role.length R₂.params.nl R₂.params.rounds))
      ≤ R₁.bound + R₂.bound + 1 / (Fintype.card Fmac : ℚ) :=
  twofield_v1_ratio_le_exact (Schedule.keyFirst _ _) L₁ L₂ decode aP kmac hbal hmac
    common₁ hrow₁ common₂ hrow₂ (by omega)

end Compose

end Lfzk.TwoFieldV1
