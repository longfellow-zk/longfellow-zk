import Lfzk.TwoFieldBridge
import Lfzk.NizkMerkle

/-!
# Two Longfellow sides and one MAC slot, end to end

`Lfzk.TwoFieldBridge.twofield_merged_ratio_le` composes two sides given as `SideBound`s — each a
single-field bound at every absorbed coordinate.  This file builds a `SideBound` from **Longfellow
LayerStep data**, so that the composed statement takes LayerStep data and nothing else:

```
Pr over (pre, tape) [ both compiled verifiers accept  ∧  the composed extractor fails ]
    ≤  lfBound₁  +  lfBound₂  +  kmac / |C|
lfBoundᵢ  =  |Candᵢ|·(nlᵢ·bpairᵢ + (∑ wᵢ)·broundᵢ + binᵢ + bligᵢ + bqueryᵢ)/|C|
             + merkleNumerator(commitFuelᵢ, tlen)/|D|
```

`twofield_longfellow_ratio_le` has **no** ratio hypothesis: neither `TwoFieldNizk`'s `h₁`/`h₂` nor
`TwoFieldCertified`'s `hE`/`hS`.  Each side's bound is `Lfzk.Nizk.nizk_ratio_le_merkle` at every
absorbed coordinate (`LongfellowFamily.ratio_le`), moved onto the merged tape by
`TwoFieldBridge.ratio_transfer`.

## The side's statement may depend on the key — so `Sat` is per commitment

The single-field `Certified.Row.nizk_ratio_le_longfellow` fixes the honest values `H`, the
satisfaction predicate `Sat` and Ligero's doom `LigDoomed` **once**, for every commitment.  A
two-field side cannot use that form: its circuit takes the MAC key and tag as public inputs, the key
is `aP pre + decode (tape s)`, and so its `Sat` depends on the commitment `pre` and on the key coin.
A fixed `Sat` would make the MAC row `Sat cand → macTag (key ω) … = tag ω` unsatisfiable as the key
varies.

`Lfzk.Nizk.nizk_ratio_le_merkle` already takes one `Bcs.Rbr` *per commitment*, and
`RbrLongfellow.LayerStepData.rbr` builds one from LayerStep data whose `H`, `Sat`, `LigDoomed` are whatever that
commitment's are.  So `LongfellowFamily` lets all three vary with `(z, pre)` — `z` the absorbed
coordinate, which contains the key coin (`Schedule.key_rest₁`) — and nothing about LayerStep changes.

## `hfail` is discharged by the choice of extractor

The single-field theorems take a failure event `Fails pre` and `hfail : Fails pre → ∀ cand, ¬ Sat
cand`.  Here the extractor is `TwoFieldBridge.chooseE` — output a satisfying candidate's witness when
there is one — so its failure event *is* `∀ cand, ¬ Sat z pre cand` (`good_iff`), and `hfail` is
`id`.  The side's knowledge error is exactly the event the Longfellow theorem bounds.

## Which Ligero variant

Nothing here mentions one.  `RbrLongfellow.LayerStepData` carries Ligero only as a doom predicate, an
escaping `Finset`, an accepting-column test and two budget inequalities, so a V3 row and a V1 row
(`Ligero.Examples.Grid.RbrCertifiedV1`) instantiate `LongfellowFamily` the same way.  A single-field
theorem that is *not* stated through `LayerStepData` plugs in one level down, by producing a
`TwoFieldBridge.SideBound`; the only shape it must have is the per-commitment `Sat` above.

## What each side still assumes

All of it is per side, named, and unchanged from the single-field development:

* `LongfellowFamily.LayerStep` — `RbrLongfellow.LayerStepData` at every `(z, pre)`: the circuit, the decoders and
  their balances, layer 0's facts (`hzero0`, `hzero1`, `hclaim`, `harith` — the last is
  `ArithmetizedCircuit.arith`), the two Ligero `Finset`s, and the budget inequalities;
* `LongfellowFamily.hright` — the compiled verifier's acceptance implies LayerStep reaches `.accepted`
  (README gap 1's transliteration debt);
* the four fuel inequalities of the Merkle extractor (`hlen`, `ht₁`, `hT`, `hT1`);
* **`hrow`, the MAC row** — satisfying side `i`'s circuit implies the MAC equation on the decoded
  common value at the shared key and tag.  This is an *arithmetization* assumption about the circuit
  (`assert_mac`), the same kind of item as `harith`, and it is kept as an explicit hypothesis of the
  headline theorem rather than folded into anything.

## What this does not model

The merged experiment is the conjunction of two side verifiers on one sample space `Pre × (Fin T →
C)`, with each side's adversary a family indexed by that side's absorbed coordinate.  The prefix
`pre : Fin tlen → D` is one hash tape **shared** by the two sides' commitment stages, and each side's
Merkle term is charged on it separately.  There is no formal two-field *driver* — a single adversary
interleaving both sides' random-oracle queries — and so no theorem that every such adversary
decomposes into the two families; `two-field-plan.md` §1 records that no such driver exists in the
source either.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.TwoFieldLongfellow

open Finset Bcs Merkle Merkle.MH Merkle.RandomOracle
open scoped Classical
open Lfzk.Mac Lfzk.TwoField Lfzk.TwoFieldNizk Lfzk.TwoFieldBridge

/-- **The single-field Longfellow bound** — `Lfzk.Nizk.nizk_ratio_le_merkle`'s right-hand side, at
explicit numerals. -/
def lfBound (cardCand cardC cardD nl : ℕ) (w : ℕ → ℕ)
    (bpair bround bin blig bquery commitFuel tlen : ℕ) : ℚ :=
  ((cardCand * (nl * bpair + (∑ i ∈ Finset.range nl, w i) * bround + bin + blig + bquery) : ℕ)
      : ℚ) / (cardC : ℚ)
    + (merkleNumerator commitFuel tlen : ℚ) / (cardD : ℚ)

/-! ## One side, as a family over the absorbed coordinate -/

/--
**One Longfellow side of a two-field argument.**

The protocol — compiler `K`, codec and decoders `dec`, the verifier's challenge and query derivations
`challengeOf`, `queryOf`, the five class budgets — is fixed.  Everything the prover chooses is a
function of the absorbed coordinate `z` (the merged tape off this side's slots: the other side's
coins and the key coin), and LayerStep's honest values, satisfaction predicate and Ligero doom are in
addition functions of the commitment `pre`.

`LayerStep` and `hright` are exactly `Lfzk.Nizk.nizk_ratio_le_merkle_longfellow`'s `Dfam` and `hright`, at
every `z`, with `H`, `Sat` and `LigDoomed` allowed to depend on `pre`.
-/
structure LongfellowFamily (Z : Type)
    (C : Type) [Fintype C]
    (Cand F X Q Witness : Type) [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [DecidableEq X] [Fintype Q] [DecidableEq Q]
    (nc nv logw logc nl : ℕ) (w : ℕ → ℕ) (bpair bround bin blig bquery : ℕ)
    {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
    {Enc D Salt M : Type} [Inhabited D] [DecidableEq D] [DecidableEq Enc]
    [Inhabited Salt] [Inhabited M]
    (Aux Aux' : Type) (tlen n commitFuel respondFuel revealFuel : ℕ)
    {codec : Codec Salt M D Enc} (dec : RoleDecoders codec)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (challengeOf : (Fin (Rounds.Role.length nl w) → C) → Challenge)
    (queryOf : (Fin (Rounds.Role.length nl w) → C) → Query) where
  /-- The side's adversary, at each value of the coordinates it does not read. -/
  A : Z → Adversary Enc D Salt M Challenge Response Query Aux Aux'
    n commitFuel respondFuel revealFuel
  /-- The side's statement — in a two-field argument it includes the MAC key and tag. -/
  statement : Z → (Fin tlen → D) × (Fin (Rounds.Role.length nl w) → C) → Statement
  /-- LayerStep's honest values, per commitment. -/
  H : Z → (Fin tlen → D) → RbrLongfellow.Honest F Cand logw logc
  /-- Which candidates satisfy the side's circuit, per commitment. -/
  Sat : Z → (Fin tlen → D) → Cand → Prop
  /-- Ligero's doom, per commitment. -/
  LigDoomed : Z → (Fin tlen → D) → X → Prop
  /-- LayerStep data, per commitment. -/
  layerStep : ∀ (z : Z) (pre : Fin tlen → D), RbrLongfellow.LayerStepData C F X Q Cand Witness nc nv
    logw logc nl w (H z pre) (Sat z pre) (LigDoomed z pre) bpair bround bin blig bquery
  /-- The compiled verifier's acceptance implies LayerStep reaches `.accepted`. -/
  hright : ∀ (z : Z) (pre : Fin tlen → D),
    RbrLongfellow.RightOfAccepts (H := H z pre) (Sat z pre) (LigDoomed z pre) (layerStep z pre).steps
      (fun tape =>
        CompiledAccepts K (A z) codec (statement z (pre, tape))
            (challengeOf tape) (queryOf tape) pre ∧
          ExtractionExplains codec dec n commitFuel (revealFuel + respondFuel) tlen
            (A z).commit ((A z).openingStage (challengeOf tape) (queryOf tape)) pre)

namespace LongfellowFamily

variable {Z : Type} {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {Cand F X Q Witness : Type} [Fintype Cand] [Field F] [Fintype F] [DecidableEq F]
  [SumcheckInterp F] [DecidableEq X] [Fintype Q] [DecidableEq Q]
variable {nc nv logw logc nl : ℕ} {w : ℕ → ℕ} {bpair bround bin blig bquery : ℕ}
variable {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
variable {Enc D Salt M : Type} [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc]
  [Inhabited Salt] [Inhabited M]
variable {Aux Aux' : Type} {tlen n commitFuel respondFuel revealFuel : ℕ}
variable {codec : Codec Salt M D Enc} {dec : RoleDecoders codec}
variable {K : Compiler Statement Oracle Challenge Response Query Opening M n}
variable {challengeOf : (Fin (Rounds.Role.length nl w) → C) → Challenge}
variable {queryOf : (Fin (Rounds.Role.length nl w) → C) → Query}
variable (L : LongfellowFamily Z C Cand F X Q Witness nc nv logw logc nl w
  bpair bround bin blig bquery Aux Aux' tlen n commitFuel respondFuel revealFuel dec K
  challengeOf queryOf)

/-- The side's **compiled** verifier — what a real verifier decides — at absorbed coordinate `z`. -/
def accepts (z : Z) (x : (Fin tlen → D) × (Fin (Rounds.Role.length nl w) → C)) : Prop :=
  CompiledAccepts K (L.A z) codec (L.statement z x) (challengeOf x.2) (queryOf x.2) x.1

/-- A good witness: the witness of a candidate that satisfies the side's circuit. -/
def good (z : Z) (x : (Fin tlen → D) × (Fin (Rounds.Role.length nl w) → C)) (a : Witness) :
    Prop :=
  ∃ cand : Cand, L.Sat z x.1 cand ∧ (L.layerStep z x.1).wOf cand = a

omit [DecidableEq C] [Nonempty C] [Fintype Cand] [Fintype D] in
/-- **No good witness iff no satisfying candidate** — so the extractor's failure is LayerStep's
`Fails`, and `hfail` is `id`. -/
theorem good_iff (z : Z) (x : (Fin tlen → D) × (Fin (Rounds.Role.length nl w) → C)) :
    (∀ a, ¬ L.good z x a) ↔ ∀ cand : Cand, ¬ L.Sat z x.1 cand := by
  constructor
  · intro h cand hsat
    exact h _ ⟨cand, hsat, rfl⟩
  · rintro h a ⟨cand, hsat, _⟩
    exact h cand hsat

/--
**The single-field bound, at every absorbed coordinate.**

`Lfzk.Nizk.nizk_ratio_le_merkle` with the round-by-round family built from `L.LayerStep z` — whose `H`,
`Sat`, `LigDoomed` vary with the commitment — and `Fails pre := ∀ cand, ¬ Sat z pre cand`, so the
`hfail` LayerStep needs is `id`.
-/
theorem ratio_le (hlen : 1 ≤ Rounds.Role.length nl w) (ht₁ : commitFuel ≤ tlen)
    (hT : 2 * n + (revealFuel + respondFuel) + commitFuel ≤ tlen) (hT1 : 1 ≤ tlen) (z : Z) :
    ((univ.filter fun omega : (Fin tlen → D) × (Fin (Rounds.Role.length nl w) → C) =>
        CompiledAccepts K (L.A z) codec (L.statement z omega)
            (challengeOf omega.2) (queryOf omega.2) omega.1 ∧
          ∀ cand : Cand, ¬ L.Sat z omega.1 cand).card : ℚ)
        / (Fintype.card (Fin tlen → D) *
            (Fintype.card C : ℚ) ^ Rounds.Role.length nl w)
      ≤ lfBound (Fintype.card Cand) (Fintype.card C) (Fintype.card D) nl w
          bpair bround bin blig bquery commitFuel tlen := by
  unfold lfBound
  -- `nizk_ratio_le_merkle`'s filter carries the `DecidablePred` of an abstract `Fails`; here
  -- `Fails` is concrete, so the two filters agree up to that instance only
  refine le_trans (le_of_eq ?_) (Lfzk.Nizk.nizk_ratio_le_merkle (Cand := Cand) dec K (L.A z) challengeOf queryOf (L.statement z)
    (Fails := fun pre => ∀ cand : Cand, ¬ L.Sat z pre cand)
    (fun pre => (L.layerStep z pre).rbr (Fails := ∀ cand : Cand, ¬ L.Sat z pre cand)
      (fun h => h) (L.hright z pre))
    bpair bround bin blig bquery
    (fun pre i => le_of_eq (congrFun ((L.layerStep z pre).rbr_beta
      (Fails := ∀ cand : Cand, ¬ L.Sat z pre cand) (fun h => h) (L.hright z pre)) i))
    hlen ht₁ hT hT1)
  congr 3
  ext x
  simp only [Finset.mem_filter]

/--
**The side, as a `SideBound`.**  Acceptance is the compiled verifier, goodness is "the witness of a
satisfying candidate", the bound is `lfBound`, and `sound` is `ratio_le` — a theorem, at every `z`.
-/
noncomputable def sideBound (hlen : 1 ≤ Rounds.Role.length nl w) (ht₁ : commitFuel ≤ tlen)
    (hT : 2 * n + (revealFuel + respondFuel) + commitFuel ≤ tlen) (hT1 : 1 ≤ tlen) :
    SideBound Z (Fin tlen → D) C (Rounds.Role.length nl w) Witness where
  accepts := L.accepts
  good := L.good
  bound := lfBound (Fintype.card Cand) (Fintype.card C) (Fintype.card D) nl w
    bpair bround bin blig bquery commitFuel tlen
  sound z := by
    have h := L.ratio_le hlen ht₁ hT hT1 z
    refine le_trans (le_of_eq ?_) h
    congr 3
    exact Finset.filter_congr (fun x _ => and_congr_right fun _ => L.good_iff z x)

end LongfellowFamily

/-! ## Two sides on one tape -/

namespace LongfellowFamily

variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {D : Type} [Fintype D] [DecidableEq D] [Inhabited D]
variable {Fmac : Type} [Field Fmac] {nblk tlen T : ℕ}
variable {Cand F X Q Witness : Type} [Fintype Cand] [Field F] [Fintype F] [DecidableEq F]
  [SumcheckInterp F] [DecidableEq X] [Fintype Q] [DecidableEq Q]
variable {nc nv logw logc nl : ℕ} {w : ℕ → ℕ} {bpair bround bin blig bquery : ℕ}
variable {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
variable {Enc Salt M : Type} [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
variable {Aux Aux' : Type} {n commitFuel respondFuel revealFuel : ℕ}
variable {codec : Codec Salt M D Enc} {dec : RoleDecoders codec}
variable {K : Compiler Statement Oracle Challenge Response Query Opening M n}
variable {challengeOf : (Fin (Rounds.Role.length nl w) → C) → Challenge}
variable {queryOf : (Fin (Rounds.Role.length nl w) → C) → Query}
variable {ι : Fin (Rounds.Role.length nl w) → Fin T}
variable (L : LongfellowFamily (Rest ι → C) C Cand F X Q Witness nc nv logw logc nl w
  bpair bround bin blig bquery Aux Aux' tlen n commitFuel respondFuel revealFuel dec K
  challengeOf queryOf)

/--
**The MAC row, per candidate, lifted to the merged sample space.**

`hrow` is the form a circuit designer states: at a merged sample where this side's compiled verifier
accepts, a satisfying candidate's witness decodes to a common value satisfying the MAC equation at
the shared key and tag.  This is the arithmetization assumption, and it stays a hypothesis.
-/
theorem mergedRow (hlen : 1 ≤ Rounds.Role.length nl w) (ht₁ : commitFuel ≤ tlen)
    (hT : 2 * n + (revealFuel + respondFuel) + commitFuel ≤ tlen) (hT1 : 1 ≤ tlen)
    {keyA : (Fin tlen → D) × (Fin T → C) → Fmac}
    {keyB tag : (Fin tlen → D) × (Fin T → C) → Fin nblk → Fmac}
    (common : Witness → Fin nblk → Fmac)
    (hrow : ∀ (ω : (Fin tlen → D) × (Fin T → C)) (cand : Cand),
      L.accepts (restOf ι ω.2) (ω.1, ω.2 ∘ ι) → L.Sat (restOf ι ω.2) ω.1 cand →
      macTag (keyA ω) (keyB ω) (common ((L.layerStep (restOf ι ω.2) ω.1).wOf cand)) = tag ω) :
    ∀ (ω : (Fin tlen → D) × (Fin T → C)) (a : Witness),
      (L.sideBound hlen ht₁ hT hT1).mergedAccepts ω → (L.sideBound hlen ht₁ hT hT1).mergedGood ω a →
      macTag (keyA ω) (keyB ω) (common a) = tag ω := by
  rintro ω a hacc ⟨cand, hsat, rfl⟩
  exact hrow ω cand hacc hsat

/-- **One Longfellow side as a `MacBound` on the merged tape.** -/
noncomputable def macSide (hlen : 1 ≤ Rounds.Role.length nl w) (ht₁ : commitFuel ≤ tlen)
    (hT : 2 * n + (revealFuel + respondFuel) + commitFuel ≤ tlen) (hT1 : 1 ≤ tlen)
    {keyA : (Fin tlen → D) × (Fin T → C) → Fmac}
    {keyB tag : (Fin tlen → D) × (Fin T → C) → Fin nblk → Fmac}
    (common : Witness → Fin nblk → Fmac)
    (hrow : ∀ (ω : (Fin tlen → D) × (Fin T → C)) (cand : Cand),
      L.accepts (restOf ι ω.2) (ω.1, ω.2 ∘ ι) → L.Sat (restOf ι ω.2) ω.1 cand →
      macTag (keyA ω) (keyB ω) (common ((L.layerStep (restOf ι ω.2) ω.1).wOf cand)) = tag ω) :
    MacBound Fmac nblk ((Fin tlen → D) × (Fin T → C)) keyA keyB tag Witness :=
  (L.sideBound hlen ht₁ hT hT1).toMacBound common (L.mergedRow hlen ht₁ hT hT1 common hrow)

/-- `macSide`'s acceptance is the side's compiled verifier on its own slots. -/
@[simp] theorem macSide_accepts (hlen : 1 ≤ Rounds.Role.length nl w) (ht₁ : commitFuel ≤ tlen)
    (hT : 2 * n + (revealFuel + respondFuel) + commitFuel ≤ tlen) (hT1 : 1 ≤ tlen)
    {keyA : (Fin tlen → D) × (Fin T → C) → Fmac}
    {keyB tag : (Fin tlen → D) × (Fin T → C) → Fin nblk → Fmac}
    (common : Witness → Fin nblk → Fmac)
    (hrow : ∀ (ω : (Fin tlen → D) × (Fin T → C)) (cand : Cand),
      L.accepts (restOf ι ω.2) (ω.1, ω.2 ∘ ι) → L.Sat (restOf ι ω.2) ω.1 cand →
      macTag (keyA ω) (keyB ω) (common ((L.layerStep (restOf ι ω.2) ω.1).wOf cand)) = tag ω)
    (ω : (Fin tlen → D) × (Fin T → C)) :
    (L.macSide hlen ht₁ hT hT1 common hrow).accepts ω
      = CompiledAccepts K (L.A (restOf ι ω.2)) codec (L.statement (restOf ι ω.2) (ω.1, ω.2 ∘ ι))
          (challengeOf (ω.2 ∘ ι)) (queryOf (ω.2 ∘ ι)) ω.1 := rfl

/-- `macSide`'s extractor fails exactly when no candidate satisfies the side's circuit. -/
theorem macSide_E_eq_none_iff (hlen : 1 ≤ Rounds.Role.length nl w) (ht₁ : commitFuel ≤ tlen)
    (hT : 2 * n + (revealFuel + respondFuel) + commitFuel ≤ tlen) (hT1 : 1 ≤ tlen)
    {keyA : (Fin tlen → D) × (Fin T → C) → Fmac}
    {keyB tag : (Fin tlen → D) × (Fin T → C) → Fin nblk → Fmac}
    (common : Witness → Fin nblk → Fmac)
    (hrow : ∀ (ω : (Fin tlen → D) × (Fin T → C)) (cand : Cand),
      L.accepts (restOf ι ω.2) (ω.1, ω.2 ∘ ι) → L.Sat (restOf ι ω.2) ω.1 cand →
      macTag (keyA ω) (keyB ω) (common ((L.layerStep (restOf ι ω.2) ω.1).wOf cand)) = tag ω)
    (ω : (Fin tlen → D) × (Fin T → C)) :
    (L.macSide hlen ht₁ hT hT1 common hrow).E ω = none
      ↔ ∀ cand : Cand, ¬ L.Sat (restOf ι ω.2) ω.1 cand :=
  (chooseE_eq_none_iff _ ω).trans (L.good_iff _ _)

/-- An extracted witness is a satisfying candidate's witness. -/
theorem macSide_E_spec (hlen : 1 ≤ Rounds.Role.length nl w) (ht₁ : commitFuel ≤ tlen)
    (hT : 2 * n + (revealFuel + respondFuel) + commitFuel ≤ tlen) (hT1 : 1 ≤ tlen)
    {keyA : (Fin tlen → D) × (Fin T → C) → Fmac}
    {keyB tag : (Fin tlen → D) × (Fin T → C) → Fin nblk → Fmac}
    (common : Witness → Fin nblk → Fmac)
    (hrow : ∀ (ω : (Fin tlen → D) × (Fin T → C)) (cand : Cand),
      L.accepts (restOf ι ω.2) (ω.1, ω.2 ∘ ι) → L.Sat (restOf ι ω.2) ω.1 cand →
      macTag (keyA ω) (keyB ω) (common ((L.layerStep (restOf ι ω.2) ω.1).wOf cand)) = tag ω)
    {ω : (Fin tlen → D) × (Fin T → C)} {a : Witness}
    (h : (L.macSide hlen ht₁ hT hT1 common hrow).E ω = some a) :
    ∃ cand : Cand, L.Sat (restOf ι ω.2) ω.1 cand ∧ (L.layerStep (restOf ι ω.2) ω.1).wOf cand = a :=
  chooseE_spec h

end LongfellowFamily

section Compose

open LongfellowFamily

variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {D : Type} [Fintype D] [DecidableEq D] [Inhabited D]
-- no `[DecidableEq Fmac]`: see the comment at `Lfzk.TwoFieldNizk`'s variable block
variable {Fmac : Type} [Field Fmac] {nblk tlen T : ℕ}
-- side 1
variable {Cand₁ F₁ X₁ Q₁ Witness₁ : Type} [Fintype Cand₁] [Field F₁] [Fintype F₁]
  [DecidableEq F₁] [SumcheckInterp F₁] [DecidableEq X₁] [Fintype Q₁] [DecidableEq Q₁]
variable {nc₁ nv₁ logw₁ logc₁ nl₁ : ℕ} {w₁ : ℕ → ℕ} {bpair₁ bround₁ bin₁ blig₁ bquery₁ : ℕ}
variable {Statement₁ Oracle₁ Challenge₁ Response₁ Query₁ : Type} {Opening₁ : Query₁ → Type}
variable {Enc₁ Salt₁ M₁ : Type} [DecidableEq Enc₁] [Inhabited Salt₁] [Inhabited M₁]
variable {Aux₁ Aux₁' : Type} {n₁ commitFuel₁ respondFuel₁ revealFuel₁ : ℕ}
variable {codec₁ : Codec Salt₁ M₁ D Enc₁} {dec₁ : RoleDecoders codec₁}
variable {K₁ : Compiler Statement₁ Oracle₁ Challenge₁ Response₁ Query₁ Opening₁ M₁ n₁}
variable {challengeOf₁ : (Fin (Rounds.Role.length nl₁ w₁) → C) → Challenge₁}
variable {queryOf₁ : (Fin (Rounds.Role.length nl₁ w₁) → C) → Query₁}
-- side 2
variable {Cand₂ F₂ X₂ Q₂ Witness₂ : Type} [Fintype Cand₂] [Field F₂] [Fintype F₂]
  [DecidableEq F₂] [SumcheckInterp F₂] [DecidableEq X₂] [Fintype Q₂] [DecidableEq Q₂]
variable {nc₂ nv₂ logw₂ logc₂ nl₂ : ℕ} {w₂ : ℕ → ℕ} {bpair₂ bround₂ bin₂ blig₂ bquery₂ : ℕ}
variable {Statement₂ Oracle₂ Challenge₂ Response₂ Query₂ : Type} {Opening₂ : Query₂ → Type}
variable {Enc₂ Salt₂ M₂ : Type} [DecidableEq Enc₂] [Inhabited Salt₂] [Inhabited M₂]
variable {Aux₂ Aux₂' : Type} {n₂ commitFuel₂ respondFuel₂ revealFuel₂ : ℕ}
variable {codec₂ : Codec Salt₂ M₂ D Enc₂} {dec₂ : RoleDecoders codec₂}
variable {K₂ : Compiler Statement₂ Oracle₂ Challenge₂ Response₂ Query₂ Opening₂ M₂ n₂}
variable {challengeOf₂ : (Fin (Rounds.Role.length nl₂ w₂) → C) → Challenge₂}
variable {queryOf₂ : (Fin (Rounds.Role.length nl₂ w₂) → C) → Query₂}

/--
**Two Longfellow sides and one MAC slot, end to end.**

Side `i` is a `LongfellowFamily` over the merged tape's slots off `sch.ιᵢ`, with its own LayerStep data,
`hright` and fuel inequalities; the MAC key is `aP pre + decode (tape sch.s)`, with `aP` a function of
the shared hash tape alone (causality (C3)); `hrowᵢ` is side `i`'s MAC row.  Then

```
Pr over (pre, tape) [ both compiled verifiers accept  ∧  the composed extractor fails ]
    ≤  lfBound₁  +  lfBound₂  +  kmac / |C|
```

There is no hypothesis about any ratio.  Each side's knowledge-error bound on the merged tape is
`LongfellowFamily.ratio_le` (the single-field theorem, at every absorbed coordinate) transferred by
`TwoFieldBridge.ratio_transfer`; the MAC term is `TwoFieldNizk.mac_slot_ratio`; the union bound is
`TwoField.composed_fail_card_le`.
-/
theorem twofield_longfellow_ratio_le
    (sch : Schedule (Rounds.Role.length nl₁ w₁) (Rounds.Role.length nl₂ w₂) T)
    (L₁ : LongfellowFamily (Rest sch.ι₁ → C) C Cand₁ F₁ X₁ Q₁ Witness₁ nc₁ nv₁ logw₁ logc₁ nl₁ w₁
      bpair₁ bround₁ bin₁ blig₁ bquery₁ Aux₁ Aux₁' tlen n₁ commitFuel₁ respondFuel₁ revealFuel₁
      dec₁ K₁ challengeOf₁ queryOf₁)
    (hlen₁ : 1 ≤ Rounds.Role.length nl₁ w₁) (ht₁₁ : commitFuel₁ ≤ tlen)
    (hT₁ : 2 * n₁ + (revealFuel₁ + respondFuel₁) + commitFuel₁ ≤ tlen)
    (L₂ : LongfellowFamily (Rest sch.ι₂ → C) C Cand₂ F₂ X₂ Q₂ Witness₂ nc₂ nv₂ logw₂ logc₂ nl₂ w₂
      bpair₂ bround₂ bin₂ blig₂ bquery₂ Aux₂ Aux₂' tlen n₂ commitFuel₂ respondFuel₂ revealFuel₂
      dec₂ K₂ challengeOf₂ queryOf₂)
    (hlen₂ : 1 ≤ Rounds.Role.length nl₂ w₂) (ht₁₂ : commitFuel₂ ≤ tlen)
    (hT₂ : 2 * n₂ + (revealFuel₂ + respondFuel₂) + commitFuel₂ ≤ tlen)
    (hT1 : 1 ≤ tlen)
    (decode : C → Fmac) (aP : (Fin tlen → D) → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    {keyB tag : (Fin tlen → D) × (Fin T → C) → Fin nblk → Fmac}
    (common₁ : Witness₁ → Fin nblk → Fmac)
    (hrow₁ : ∀ (ω : (Fin tlen → D) × (Fin T → C)) (cand : Cand₁),
      L₁.accepts (restOf sch.ι₁ ω.2) (ω.1, ω.2 ∘ sch.ι₁) → L₁.Sat (restOf sch.ι₁ ω.2) ω.1 cand →
      macTag (aP ω.1 + decode (ω.2 sch.s)) (keyB ω)
        (common₁ ((L₁.layerStep (restOf sch.ι₁ ω.2) ω.1).wOf cand)) = tag ω)
    (common₂ : Witness₂ → Fin nblk → Fmac)
    (hrow₂ : ∀ (ω : (Fin tlen → D) × (Fin T → C)) (cand : Cand₂),
      L₂.accepts (restOf sch.ι₂ ω.2) (ω.1, ω.2 ∘ sch.ι₂) → L₂.Sat (restOf sch.ι₂ ω.2) ω.1 cand →
      macTag (aP ω.1 + decode (ω.2 sch.s)) (keyB ω)
        (common₂ ((L₂.layerStep (restOf sch.ι₂ ω.2) ω.1).wOf cand)) = tag ω)
    (hT : 1 ≤ T) :
    ((univ.filter fun ω : (Fin tlen → D) × (Fin T → C) =>
        (L₁.macSide hlen₁ ht₁₁ hT₁ hT1 common₁ hrow₁).accepts ω ∧
          (L₂.macSide hlen₂ ht₁₂ hT₂ hT1 common₂ hrow₂).accepts ω ∧
          composedE (L₁.macSide hlen₁ ht₁₁ hT₁ hT1 common₁ hrow₁)
            (L₂.macSide hlen₂ ht₁₂ hT₂ hT1 common₂ hrow₂) ω = none).card : ℚ)
        / (Fintype.card (Fin tlen → D) * (Fintype.card C : ℚ) ^ T)
      ≤ lfBound (Fintype.card Cand₁) (Fintype.card C) (Fintype.card D) nl₁ w₁
            bpair₁ bround₁ bin₁ blig₁ bquery₁ commitFuel₁ tlen
        + lfBound (Fintype.card Cand₂) (Fintype.card C) (Fintype.card D) nl₂ w₂
            bpair₂ bround₂ bin₂ blig₂ bquery₂ commitFuel₂ tlen
        + (kmac : ℚ) / (Fintype.card C : ℚ) :=
  twofield_merged_ratio_le sch decode aP kmac hbal
    (L₁.sideBound hlen₁ ht₁₁ hT₁ hT1) common₁ (L₁.mergedRow hlen₁ ht₁₁ hT₁ hT1 common₁ hrow₁)
    (L₂.sideBound hlen₂ ht₁₂ hT₂ hT1) common₂ (L₂.mergedRow hlen₂ ht₁₂ hT₂ hT1 common₂ hrow₂) hT

/--
**At Protocol 3.8's schedule.**  `twofield_longfellow_ratio_le` at `Schedule.keyFirst`: the key
challenge `k_v` at slot `0`, then side 1's coins, then side 2's, on a tape of length
`1 + T₁ + T₂`.  The key slot is outside both sides' own coins (`keyFirst`'s `s_not₁`, `s_not₂`), which
is what lets each side's statement take the key as a public input; the tape-length side condition
`1 ≤ T` is discharged.
-/
theorem twofield_longfellow_ratio_le_keyFirst
    (L₁ : LongfellowFamily
      (Rest (Schedule.keyFirst (Rounds.Role.length nl₁ w₁) (Rounds.Role.length nl₂ w₂)).ι₁ → C)
      C Cand₁ F₁ X₁ Q₁ Witness₁ nc₁ nv₁ logw₁ logc₁ nl₁ w₁
      bpair₁ bround₁ bin₁ blig₁ bquery₁ Aux₁ Aux₁' tlen n₁ commitFuel₁ respondFuel₁ revealFuel₁
      dec₁ K₁ challengeOf₁ queryOf₁)
    (hlen₁ : 1 ≤ Rounds.Role.length nl₁ w₁) (ht₁₁ : commitFuel₁ ≤ tlen)
    (hT₁ : 2 * n₁ + (revealFuel₁ + respondFuel₁) + commitFuel₁ ≤ tlen)
    (L₂ : LongfellowFamily
      (Rest (Schedule.keyFirst (Rounds.Role.length nl₁ w₁) (Rounds.Role.length nl₂ w₂)).ι₂ → C)
      C Cand₂ F₂ X₂ Q₂ Witness₂ nc₂ nv₂ logw₂ logc₂ nl₂ w₂
      bpair₂ bround₂ bin₂ blig₂ bquery₂ Aux₂ Aux₂' tlen n₂ commitFuel₂ respondFuel₂ revealFuel₂
      dec₂ K₂ challengeOf₂ queryOf₂)
    (hlen₂ : 1 ≤ Rounds.Role.length nl₂ w₂) (ht₁₂ : commitFuel₂ ≤ tlen)
    (hT₂ : 2 * n₂ + (revealFuel₂ + respondFuel₂) + commitFuel₂ ≤ tlen)
    (hT1 : 1 ≤ tlen)
    (decode : C → Fmac) (aP : (Fin tlen → D) → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    {keyB tag : (Fin tlen → D) ×
      (Fin (1 + Rounds.Role.length nl₁ w₁ + Rounds.Role.length nl₂ w₂) → C) → Fin nblk → Fmac}
    (common₁ : Witness₁ → Fin nblk → Fmac)
    (hrow₁ : ∀ (ω : (Fin tlen → D) ×
        (Fin (1 + Rounds.Role.length nl₁ w₁ + Rounds.Role.length nl₂ w₂) → C)) (cand : Cand₁),
      L₁.accepts (restOf (Schedule.keyFirst _ _).ι₁ ω.2) (ω.1, ω.2 ∘ (Schedule.keyFirst _ _).ι₁) →
      L₁.Sat (restOf (Schedule.keyFirst _ _).ι₁ ω.2) ω.1 cand →
      macTag (aP ω.1 + decode (ω.2 (Schedule.keyFirst _ _).s)) (keyB ω)
        (common₁ ((L₁.layerStep (restOf (Schedule.keyFirst _ _).ι₁ ω.2) ω.1).wOf cand)) = tag ω)
    (common₂ : Witness₂ → Fin nblk → Fmac)
    (hrow₂ : ∀ (ω : (Fin tlen → D) ×
        (Fin (1 + Rounds.Role.length nl₁ w₁ + Rounds.Role.length nl₂ w₂) → C)) (cand : Cand₂),
      L₂.accepts (restOf (Schedule.keyFirst _ _).ι₂ ω.2) (ω.1, ω.2 ∘ (Schedule.keyFirst _ _).ι₂) →
      L₂.Sat (restOf (Schedule.keyFirst _ _).ι₂ ω.2) ω.1 cand →
      macTag (aP ω.1 + decode (ω.2 (Schedule.keyFirst _ _).s)) (keyB ω)
        (common₂ ((L₂.layerStep (restOf (Schedule.keyFirst _ _).ι₂ ω.2) ω.1).wOf cand)) = tag ω) :
    ((univ.filter fun ω : (Fin tlen → D) ×
          (Fin (1 + Rounds.Role.length nl₁ w₁ + Rounds.Role.length nl₂ w₂) → C) =>
        (L₁.macSide hlen₁ ht₁₁ hT₁ hT1 common₁ hrow₁).accepts ω ∧
          (L₂.macSide hlen₂ ht₁₂ hT₂ hT1 common₂ hrow₂).accepts ω ∧
          composedE (L₁.macSide hlen₁ ht₁₁ hT₁ hT1 common₁ hrow₁)
            (L₂.macSide hlen₂ ht₁₂ hT₂ hT1 common₂ hrow₂) ω = none).card : ℚ)
        / (Fintype.card (Fin tlen → D) *
            (Fintype.card C : ℚ) ^ (1 + Rounds.Role.length nl₁ w₁ + Rounds.Role.length nl₂ w₂))
      ≤ lfBound (Fintype.card Cand₁) (Fintype.card C) (Fintype.card D) nl₁ w₁
            bpair₁ bround₁ bin₁ blig₁ bquery₁ commitFuel₁ tlen
        + lfBound (Fintype.card Cand₂) (Fintype.card C) (Fintype.card D) nl₂ w₂
            bpair₂ bround₂ bin₂ blig₂ bquery₂ commitFuel₂ tlen
        + (kmac : ℚ) / (Fintype.card C : ℚ) :=
  twofield_longfellow_ratio_le (Schedule.keyFirst _ _) L₁ hlen₁ ht₁₁ hT₁ L₂ hlen₂ ht₁₂ hT₂ hT1
    decode aP kmac hbal common₁ hrow₁ common₂ hrow₂ (by omega)

end Compose

end Lfzk.TwoFieldLongfellow
