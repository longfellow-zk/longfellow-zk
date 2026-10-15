import Lfzk.TwoFieldV1
import Lfzk.TwoFieldV1Fields
import Lfzk.ProfileMonoV1

/-!
# A certified two-field V1 row, shown not to be vacuous

`Lfzk.TwoFieldV1.twofield_v1_ratio_le_exact` composes two certified V1 sides through the MAC.  This
file fixes the numerals: a `TwoFieldRowV1` is two `CertifiedV1.Row`s and the MAC field's size, and
`Valid` checks, decidably,

1. both sides are valid `CertifiedV1` rows (each with its own `2n + commitFuel < tape`, `logc = 0`);
2. **one hash tape**: the two rows record the same `tape` and the same digest width;
3. **two fields**: the ECDSA side is over a prime (`fieldOrder ≠ 0`), the SHA side binary;
4. **room for both sides' leaves at once**: `(2n₁ + commitFuel₁) + (2n₂ + commitFuel₂) < tape`;
5. **both Reed–Solomon domains fit**: `r + w + n ≤ |F|` on each side, so a domain exists
   (`LigeroFamily.ReedSolomon.Domain.ofCardLE`);
6. `0 < |Fmac|`, the composed bound `ecdsa.bound + sha.bound + 1/|Fmac|` is at most `2^-lam`, and the
   two modelled sizes are under `sizeBound`.

## The old rows were vacuous; this one is not

The V3 two-field row (`Lfzk.Certified.twoFieldRows`) failed in two ways, both proved in Lean by the
two-field session:

* `commitFuel = tape`, so the Merkle fuel premise `hT` forced `n = 0`
  (`TwoFieldLongfellow.twoFieldRow_fuel_unsat`);
* `bpair = 2` and `bpair = 2^128` recorded as numerals below `2|F|`, so no `LayerStepData` existed
  (`twoFieldRows_ecdsa_layerStepData_isEmpty`, `twoFieldRows_sha_layerStepData_isEmpty`).

Before any `lam` is quoted, this file proves that `p256sha`'s numerals trigger neither, and more:

* **fuel** (`fuel_satisfiable`, `p256sha_fuel`): both sides' `ht₁`, `hT`, `hT1` hold at once on the
  shared tape, at the two sides' column counts and positive opening fuel for both adversaries;
* **decoders** (`twoField_coins_exact`, `ExactDecoder`): on **one** coin alphabet
  `(X₁ × Q₁ × F₁²) × ((X₂ × Q₂ × F₂²) × Fmac)` all nine decoders — four per side and the MAC key's —
  are exactly balanced; `FieldData.withDecoders` re-decodes *any* field half onto them, giving
  `FieldData.Exact` (`hexact`) and the MAC slot's `kmac · |Fmac| ≤ |C|` (`hmac`).  The V1 LayerStep
  budgets are then not numerals at all: `pairBudget |C| |F| = ⌊2|C|/|F|⌋ ≥ 2|F|` (`pair_room`), so the
  layer-0 pair inequality holds (`field_budgets_of_exact`) — the V3 mode cannot occur;
* **fields** (`p256sha_premises_satisfiable`): `ZMod p` (with `p` proved prime by a kernel-checked
  Pratt certificate, `TwoFieldV1Fields.p256Order_prime`) and `GaloisField 2 128` have the rows'
  cardinalities and `SumcheckInterp` instances; both domains exist; the candidate and digest types
  exist.

## What is still a hypothesis

`p256sha_nizk_ratio_le` (and `_keyFirst`) quote `2^-114` for the two-field statement.  Their premises
are exactly `TwoFieldV1.twofield_v1_ratio_le_exact`'s, per side (see `Lfzk.TwoFieldV1`): `hfalse`,
`hright`, `hexact`, the field half of LayerStep, the protocol's numeric premises, and **`hrow₁`,
`hrow₂`, the MAC rows** (the arithmetization assumption that each circuit enforces the MAC); plus the
MAC slot's `decode`, `hbal`, `hmac`, and `|Fmac| = 2^128`.  The numeric and type-level ones are
jointly satisfiable (above); `hfalse`, `hright`, `hrow` and LayerStep's own premises are statements
about the circuits and the compiled verifier and are not discharged here.

## The circuit shape

Both sides are the deployed v8 circuits' shapes (`CertifiedV1.v8Sig`, `CertifiedV1.v8Hash`: 21 and
20 layers, 520 and 610 sumcheck slots) at V1 with 132 openings: `LigeroV1Rows.v8Sig` (121 bits
round by round) on the ECDSA side and `LigeroV1Rows.v8Hash` (115) on the SHA side.
`TwoFieldRowV1.valid_of_profile_le` carries validity to every narrower pair of profiles
(`Lfzk.ProfileMonoV1`), so the row covers the 1-, 2- and 3-attribute hash circuits as well.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.TwoFieldV1Rows

open Finset

/-! ## Exactly balanced decoders on one shared alphabet -/

/-- A decoder `C → Y` that is at most `k`-to-one, with `k · |Y| ≤ |C|`: exactly balanced. -/
structure ExactDecoder (C Y : Type) [Fintype C] [Fintype Y] [DecidableEq Y] where
  decode : C → Y
  k : ℕ
  hbal : ∀ y : Y, (univ.filter fun c : C => decode c = y).card ≤ k
  hexact : k * Fintype.card Y ≤ Fintype.card C

theorem card_filter_comp_fst {A B Y : Type} [Fintype A] [Fintype B] [DecidableEq Y]
    (d : A → Y) (y : Y) :
    (univ.filter fun c : A × B => d c.1 = y).card
      = (univ.filter fun a : A => d a = y).card * Fintype.card B := by
  rw [← Finset.card_univ (α := B), ← Finset.card_product]
  congr 1
  ext ⟨a, b⟩
  simp

theorem card_filter_comp_snd {A B Y : Type} [Fintype A] [Fintype B] [DecidableEq Y]
    (d : B → Y) (y : Y) :
    (univ.filter fun c : A × B => d c.2 = y).card
      = Fintype.card A * (univ.filter fun b : B => d b = y).card := by
  rw [← Finset.card_univ (α := A), ← Finset.card_product]
  congr 1
  ext ⟨a, b⟩
  simp

namespace ExactDecoder

/-- The identity is exactly balanced. -/
def self (Y : Type) [Fintype Y] [DecidableEq Y] : ExactDecoder Y Y where
  decode y := y
  k := 1
  hbal y := by simp [Finset.filter_eq']
  hexact := by simp

/-- Read the first coordinate: the balance multiplies by the second coordinate's size. -/
def fst {A Y : Type} [Fintype A] [Fintype Y] [DecidableEq Y] (d : ExactDecoder A Y)
    (B : Type) [Fintype B] : ExactDecoder (A × B) Y where
  decode c := d.decode c.1
  k := d.k * Fintype.card B
  hbal y := by
    rw [card_filter_comp_fst]
    exact Nat.mul_le_mul_right _ (d.hbal y)
  hexact := by
    rw [Fintype.card_prod]
    calc d.k * Fintype.card B * Fintype.card Y = d.k * Fintype.card Y * Fintype.card B := by ring
      _ ≤ Fintype.card A * Fintype.card B := Nat.mul_le_mul_right _ d.hexact

/-- Read the second coordinate. -/
def snd {B Y : Type} [Fintype B] [Fintype Y] [DecidableEq Y] (d : ExactDecoder B Y)
    (A : Type) [Fintype A] : ExactDecoder (A × B) Y where
  decode c := d.decode c.2
  k := Fintype.card A * d.k
  hbal y := by
    rw [card_filter_comp_snd]
    exact Nat.mul_le_mul_left _ (d.hbal y)
  hexact := by
    rw [Fintype.card_prod]
    calc Fintype.card A * d.k * Fintype.card Y = Fintype.card A * (d.k * Fintype.card Y) := by
          ring
      _ ≤ Fintype.card A * Fintype.card B := Nat.mul_le_mul_left _ d.hexact

end ExactDecoder

section Coins

variable (F X Q : Type) [Field F] [Fintype F] [DecidableEq F] [Fintype X] [DecidableEq X]
  [Fintype Q] [DecidableEq Q]

/-- One side's own coins: a Ligero challenge, a query, and a layer pair. -/
abbrev SideCoins := X × Q × (F × F)

/-- The side's Ligero challenge decoder. -/
def chalD : ExactDecoder (SideCoins F X Q) X := (ExactDecoder.self X).fst (Q × (F × F))

/-- The side's query decoder. -/
def queryD : ExactDecoder (SideCoins F X Q) Q :=
  ((ExactDecoder.self Q).fst (F × F)).snd X

/-- The side's pair decoder. -/
def pairD : ExactDecoder (SideCoins F X Q) (F × F) :=
  ((ExactDecoder.self (F × F)).snd Q).snd X

/-- The side's field-element decoder: the first coordinate of the pair. -/
def eltD : ExactDecoder (SideCoins F X Q) F :=
  (((ExactDecoder.self F).fst F).snd Q).snd X

end Coins

section TwoCoins

variable (F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac : Type)
  [Field F₁] [Fintype F₁] [DecidableEq F₁] [Fintype X₁] [DecidableEq X₁]
  [Fintype Q₁] [DecidableEq Q₁]
  [Field F₂] [Fintype F₂] [DecidableEq F₂] [Fintype X₂] [DecidableEq X₂]
  [Fintype Q₂] [DecidableEq Q₂]
  [Fintype Fmac] [DecidableEq Fmac]

/-- **One coin alphabet for the whole two-field argument**: side 1's coins, side 2's coins, and the
MAC key coin. -/
abbrev TwoFieldCoins := SideCoins F₁ X₁ Q₁ × (SideCoins F₂ X₂ Q₂ × Fmac)

/-- Side 1's four decoders on the shared alphabet. -/
def side₁ : ExactDecoder (TwoFieldCoins F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac) (F₁ × F₁) ×
    ExactDecoder (TwoFieldCoins F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac) F₁ ×
    ExactDecoder (TwoFieldCoins F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac) X₁ ×
    ExactDecoder (TwoFieldCoins F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac) Q₁ :=
  ((pairD F₁ X₁ Q₁).fst _, (eltD F₁ X₁ Q₁).fst _, (chalD F₁ X₁ Q₁).fst _,
    (queryD F₁ X₁ Q₁).fst _)

/-- Side 2's four decoders on the shared alphabet. -/
def side₂ : ExactDecoder (TwoFieldCoins F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac) (F₂ × F₂) ×
    ExactDecoder (TwoFieldCoins F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac) F₂ ×
    ExactDecoder (TwoFieldCoins F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac) X₂ ×
    ExactDecoder (TwoFieldCoins F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac) Q₂ :=
  (((pairD F₂ X₂ Q₂).fst Fmac).snd _, ((eltD F₂ X₂ Q₂).fst Fmac).snd _,
    ((chalD F₂ X₂ Q₂).fst Fmac).snd _, ((queryD F₂ X₂ Q₂).fst Fmac).snd _)

/-- The MAC key's decoder on the shared alphabet. -/
def macD : ExactDecoder (TwoFieldCoins F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac) Fmac :=
  ((ExactDecoder.self Fmac).snd (SideCoins F₂ X₂ Q₂)).snd (SideCoins F₁ X₁ Q₁)

end TwoCoins

/-! ### Re-decoding a field half -/

section Redecode

variable {C F X Q Cand Witness : Type} [Fintype C] [Field F] [Fintype F] [DecidableEq F]
  [SumcheckInterp F] [Fintype X] [DecidableEq X] [Fintype Q] [DecidableEq Q]
variable {nc nv logw logc : ℕ} {H : RbrLongfellow.Honest F Cand logw logc} {Sat : Cand → Prop}

/-- **Re-decode a field half.**  Replace its four coin decoders and their balances; nothing else in
`RbrSplit.FieldData` reads them. -/
def withDecoders (FD : RbrSplit.FieldData C F X Q Cand Witness nc nv logw logc H Sat)
    (dp : ExactDecoder C (F × F)) (dF : ExactDecoder C F) (dX : ExactDecoder C X)
    (dQ : ExactDecoder C Q) : RbrSplit.FieldData C F X Q Cand Witness nc nv logw logc H Sat :=
  { FD with
    decodePair := dp.decode, decodeF := dF.decode, decodeChal := dX.decode,
    decodeQuery := dQ.decode, kpair := dp.k, k := dF.k, kchal := dX.k, kq := dQ.k,
    hbalPair := dp.hbal, hbalF := dF.hbal, hbalChal := dX.hbal, hbalQuery := dQ.hbal }

/-- **Exactly balanced decoders make a field half `Exact`.** -/
theorem withDecoders_exact (FD : RbrSplit.FieldData C F X Q Cand Witness nc nv logw logc H Sat)
    (dp : ExactDecoder C (F × F)) (dF : ExactDecoder C F) (dX : ExactDecoder C X)
    (dQ : ExactDecoder C Q) : (withDecoders FD dp dF dX dQ).Exact := by
  refine ⟨?_, dF.hexact, dX.hexact, dQ.hexact⟩
  have := dp.hexact
  rwa [Fintype.card_prod] at this

omit [SumcheckInterp F] in
/-- **The V1 pair budget always has room for the layer-0 decoder.**  Over a non-empty alphabet an
exactly balanced pair decoder forces `|F|² ≤ |C|`, so `⌊2|C|/|F|⌋ ≥ 2|F|`: the bound the V3 rows'
`bpair` numerals violated (`RbrLongfellow.LayerStepData.two_card_le_bpair`) holds automatically. -/
theorem pair_room [Nonempty C] (dp : ExactDecoder C (F × F)) :
    2 * Fintype.card F ≤ CertifiedV1.pairBudget (Fintype.card C) (Fintype.card F) := by
  obtain ⟨c⟩ := ‹Nonempty C›
  have hk : 1 ≤ dp.k := le_trans
    (Finset.card_pos.mpr ⟨c, by simp⟩) (dp.hbal (dp.decode c))
  have hF : 0 < Fintype.card F := Fintype.card_pos
  have hsq : Fintype.card F * Fintype.card F ≤ Fintype.card C := by
    have := dp.hexact
    rw [Fintype.card_prod] at this
    calc Fintype.card F * Fintype.card F = 1 * (Fintype.card F * Fintype.card F) := by ring
      _ ≤ dp.k * (Fintype.card F * Fintype.card F) := Nat.mul_le_mul_right _ hk
      _ ≤ Fintype.card C := this
  unfold CertifiedV1.pairBudget
  rw [Nat.le_div_iff_mul_le hF]
  calc 2 * Fintype.card F * Fintype.card F = 2 * (Fintype.card F * Fintype.card F) := by ring
    _ ≤ 2 * Fintype.card C := Nat.mul_le_mul_left 2 hsq

/-- **LayerStep's field budgets hold at the V1 numerals**: `RbrSplit.Budgets`' four field-round
inequalities at `bpair = bround = ⌊2|C|/|F|⌋`, `bin = ⌊|C|/|F|⌋`, for any re-decoded field half. -/
theorem field_budgets_of_exact (FD : RbrSplit.FieldData C F X Q Cand Witness nc nv logw logc H Sat)
    (dp : ExactDecoder C (F × F)) (dF : ExactDecoder C F) (dX : ExactDecoder C X)
    (dQ : ExactDecoder C Q) :
    (withDecoders FD dp dF dX dQ).kpair * (2 * Fintype.card F)
        ≤ CertifiedV1.pairBudget (Fintype.card C) (Fintype.card F) ∧
      (withDecoders FD dp dF dX dQ).k * 1
        ≤ CertifiedV1.pairBudget (Fintype.card C) (Fintype.card F) ∧
      (withDecoders FD dp dF dX dQ).k * 2
        ≤ CertifiedV1.pairBudget (Fintype.card C) (Fintype.card F) ∧
      (withDecoders FD dp dF dX dQ).k * 1
        ≤ CertifiedV1.inBudget (Fintype.card C) (Fintype.card F) :=
  (withDecoders_exact FD dp dF dX dQ).field_budgets

end Redecode

/--
**The decoders can be exactly balanced, for both sides and the MAC at once.**

On `TwoFieldCoins`, any field half of side 1 and any field half of side 2 re-decode to `Exact` field
halves (`hexact` of both `V1Family`s), and the MAC key decoder satisfies `kmac · |Fmac| ≤ |C|`
(`hmac` of `TwoFieldV1.twofield_v1_ratio_le_exact`).  The two-field analogue of
`RbrSplit.product_coins_exact`.
-/
theorem twoField_coins_exact {F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac : Type}
    [Field F₁] [Fintype F₁] [DecidableEq F₁] [SumcheckInterp F₁] [Fintype X₁] [DecidableEq X₁]
    [Fintype Q₁] [DecidableEq Q₁]
    [Field F₂] [Fintype F₂] [DecidableEq F₂] [SumcheckInterp F₂] [Fintype X₂] [DecidableEq X₂]
    [Fintype Q₂] [DecidableEq Q₂]
    [Fintype Fmac] [DecidableEq Fmac]
    {Cand₁ Witness₁ Cand₂ Witness₂ : Type} {nc₁ nv₁ logw₁ logc₁ nc₂ nv₂ logw₂ logc₂ : ℕ}
    {H₁ : RbrLongfellow.Honest F₁ Cand₁ logw₁ logc₁} {Sat₁ : Cand₁ → Prop}
    {H₂ : RbrLongfellow.Honest F₂ Cand₂ logw₂ logc₂} {Sat₂ : Cand₂ → Prop}
    (FD₁ : RbrSplit.FieldData (TwoFieldCoins F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac) F₁ X₁ Q₁ Cand₁ Witness₁
      nc₁ nv₁ logw₁ logc₁ H₁ Sat₁)
    (FD₂ : RbrSplit.FieldData (TwoFieldCoins F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac) F₂ X₂ Q₂ Cand₂ Witness₂
      nc₂ nv₂ logw₂ logc₂ H₂ Sat₂) :
    (withDecoders FD₁ (side₁ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac).1 (side₁ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac).2.1
        (side₁ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac).2.2.1 (side₁ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac).2.2.2).Exact ∧
      (withDecoders FD₂ (side₂ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac).1 (side₂ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac).2.1
        (side₂ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac).2.2.1 (side₂ F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac).2.2.2).Exact ∧
      (∀ x : Fmac, (univ.filter fun c : TwoFieldCoins F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac =>
          (macD F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac).decode c = x).card
        ≤ (macD F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac).k) ∧
      (macD F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac).k * Fintype.card Fmac
        ≤ Fintype.card (TwoFieldCoins F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac) :=
  ⟨withDecoders_exact _ _ _ _ _, withDecoders_exact _ _ _ _ _,
    (macD F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac).hbal, (macD F₁ X₁ Q₁ F₂ X₂ Q₂ Fmac).hexact⟩

/-! ## The two-field row -/

/-- One certified **two-field** V1 row: the two sides of Protocol 3.8 and the MAC field's size. -/
structure TwoFieldRowV1 where
  /-- The prime-field side — ECDSA over `P-256`'s base field. -/
  ecdsa : CertifiedV1.Row
  /-- The binary side — SHA-256 over `GF(2^128)`. -/
  sha : CertifiedV1.Row
  /-- `|Fmac|`; the MAC slot costs `1/|Fmac|` at an exactly balanced key decoder. -/
  macFieldSize : ℕ
  /-- The composed security target, in bits. -/
  lam : ℕ
  /-- Modelled composed proof size, in bytes. -/
  sizeBound : ℕ

namespace TwoFieldRowV1

variable (R : TwoFieldRowV1)

/-- The composed bound — `TwoFieldV1.twofield_v1_ratio_le_exact`'s right-hand side. -/
def bound : ℚ := R.ecdsa.bound + R.sha.bound + 1 / (R.macFieldSize : ℚ)

/-- A checked two-field row; see the module docstring for the conjuncts. -/
def Valid : Prop :=
  R.ecdsa.Valid ∧ R.sha.Valid ∧
    R.ecdsa.tape = R.sha.tape ∧
    R.ecdsa.params.digestBits = R.sha.params.digestBits ∧
    R.ecdsa.params.row.fieldOrder ≠ 0 ∧ R.sha.params.row.fieldOrder = 0 ∧
    (2 * R.ecdsa.params.row.n + R.ecdsa.commitFuel)
        + (2 * R.sha.params.row.n + R.sha.commitFuel) < R.sha.tape ∧
    R.ecdsa.params.row.openings + R.ecdsa.params.q + R.ecdsa.params.row.n
        ≤ R.ecdsa.params.row.fieldSize ∧
    R.sha.params.row.openings + R.sha.params.q + R.sha.params.row.n
        ≤ R.sha.params.row.fieldSize ∧
    0 < R.macFieldSize ∧
    R.bound ≤ (1 : ℚ) / 2 ^ R.lam ∧
    R.ecdsa.params.proofBytes + R.sha.params.proofBytes ≤ R.sizeBound

instance : Decidable R.Valid := by
  unfold Valid CertifiedV1.Row.Valid LigeroFamily.CoreRowsNonempty
  infer_instance

def validBool : Bool := decide R.Valid

/-- The recorded `lam` is the composed bound's exact integer bit level. -/
def Sharp : Prop := ¬ R.bound ≤ (1 : ℚ) / 2 ^ (R.lam + 1)

instance : Decidable R.Sharp := by unfold Sharp; infer_instance

def sharpBool : Bool := decide R.Sharp

variable {R}

theorem ecdsa_valid (h : R.Valid) : R.ecdsa.Valid := h.1
theorem sha_valid (h : R.Valid) : R.sha.Valid := h.2.1

/-- **One hash tape.** -/
theorem tape_eq (h : R.Valid) : R.ecdsa.tape = R.sha.tape := h.2.2.1

/-- **One digest.** -/
theorem digest_eq (h : R.Valid) : R.ecdsa.params.digestBits = R.sha.params.digestBits :=
  h.2.2.2.1

/-- **Two fields**, a prime one and a binary one. -/
theorem two_fields (h : R.Valid) :
    R.ecdsa.params.row.fieldOrder ≠ 0 ∧ R.sha.params.row.fieldOrder = 0 :=
  ⟨h.2.2.2.2.1, h.2.2.2.2.2.1⟩

/-- **Room for both sides' leaves and commitment fuels on the shared tape.** -/
theorem room (h : R.Valid) :
    (2 * R.ecdsa.params.row.n + R.ecdsa.commitFuel)
      + (2 * R.sha.params.row.n + R.sha.commitFuel) < R.sha.tape := h.2.2.2.2.2.2.1

theorem rs_fits_ecdsa (h : R.Valid) :
    R.ecdsa.params.row.openings + R.ecdsa.params.q + R.ecdsa.params.row.n
      ≤ R.ecdsa.params.row.fieldSize := h.2.2.2.2.2.2.2.1

theorem rs_fits_sha (h : R.Valid) :
    R.sha.params.row.openings + R.sha.params.q + R.sha.params.row.n
      ≤ R.sha.params.row.fieldSize := h.2.2.2.2.2.2.2.2.1

theorem mac_pos (h : R.Valid) : 0 < R.macFieldSize := h.2.2.2.2.2.2.2.2.2.1

theorem target (h : R.Valid) : R.bound ≤ (1 : ℚ) / 2 ^ R.lam := h.2.2.2.2.2.2.2.2.2.2.1

theorem size (h : R.Valid) :
    R.ecdsa.params.proofBytes + R.sha.params.proofBytes ≤ R.sizeBound :=
  h.2.2.2.2.2.2.2.2.2.2.2

theorem valid_of_validBool (h : R.validBool = true) : R.Valid := of_decide_eq_true h

/-! ### Non-vacuity, at every valid row -/

/--
**The fuel premises are jointly satisfiable.**  On the shared tape `tlen = sha.tape`, at Ligero's
`n` leaves per side, both sides' `ht₁`, `hT`, `hT1` hold at once, with the tape's spare room handed
to the SHA side's adversary as opening fuel — and both sides' leaves and fuels fit together.  Neither
side records `commitFuel = tape`, the V3 rows' failure (`TwoFieldLongfellow.twoFieldRow_fuel_unsat`).
-/
theorem fuel_satisfiable (h : R.Valid) :
    R.ecdsa.tape = R.sha.tape ∧
      R.ecdsa.commitFuel ≤ R.sha.tape ∧ R.sha.commitFuel ≤ R.sha.tape ∧ 1 ≤ R.sha.tape ∧
      2 * R.ecdsa.params.row.n + (0 + 0) + R.ecdsa.commitFuel ≤ R.sha.tape ∧
      2 * R.sha.params.row.n
          + (0 + (R.sha.tape - ((2 * R.ecdsa.params.row.n + R.ecdsa.commitFuel)
            + (2 * R.sha.params.row.n + R.sha.commitFuel))))
          + R.sha.commitFuel ≤ R.sha.tape ∧
      (2 * R.ecdsa.params.row.n + (0 + 0) + R.ecdsa.commitFuel)
          + (2 * R.sha.params.row.n
            + (0 + (R.sha.tape - ((2 * R.ecdsa.params.row.n + R.ecdsa.commitFuel)
              + (2 * R.sha.params.row.n + R.sha.commitFuel))))
            + R.sha.commitFuel) ≤ R.sha.tape ∧
      R.ecdsa.commitFuel < R.ecdsa.tape ∧ R.sha.commitFuel < R.sha.tape := by
  have hr := room h
  have ht := tape_eq h
  refine ⟨ht, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- **Both Reed–Solomon domains exist**, at any fields of the rows' cardinalities. -/
theorem domain_exists_ecdsa (h : R.Valid) {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = R.ecdsa.params.row.fieldSize) :
    Nonempty (LigeroFamily.ReedSolomon.Domain F R.ecdsa.params.row.openings R.ecdsa.params.q
      R.ecdsa.params.row.n) :=
  ⟨LigeroFamily.ReedSolomon.Domain.ofCardLE (by rw [hF]; exact rs_fits_ecdsa h)⟩

theorem domain_exists_sha (h : R.Valid) {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = R.sha.params.row.fieldSize) :
    Nonempty (LigeroFamily.ReedSolomon.Domain F R.sha.params.row.openings R.sha.params.q
      R.sha.params.row.n) :=
  ⟨LigeroFamily.ReedSolomon.Domain.ofCardLE (by rw [hF]; exact rs_fits_sha h)⟩

/-! ### Profile monotonicity -/

/-- The row at narrower profiles on both sides. -/
def withProfiles (R : TwoFieldRowV1) (P₁ P₂ : CostV1.Params) : TwoFieldRowV1 :=
  { R with ecdsa := { R.ecdsa with params := P₁ }, sha := { R.sha with params := P₂ } }

/--
**A valid two-field row covers every narrower pair of profiles.**  Each side by
`ProfileMonoV1.Row.valid_of_profile_le`; the shared-tape, two-field, room and domain conjuncts read
only fields `ProfileLe` holds fixed; the composed bound and size are sums of monotone terms.
-/
theorem valid_of_profile_le (h : R.Valid) {P₁ P₂ : CostV1.Params}
    (hle₁ : ProfileMonoV1.ProfileLe P₁ R.ecdsa.params) (hle₂ : ProfileMonoV1.ProfileLe P₂ R.sha.params)
    (hnl₁ : 0 < R.ecdsa.params.nl) (hnl₂ : 0 < R.sha.params.nl) :
    (R.withProfiles P₁ P₂).Valid := by
  obtain ⟨he, hs, ht, hd, ho₁, ho₂, hroom, hrs₁, hrs₂, hmac, hbound, hsize⟩ := h
  refine ⟨ProfileMonoV1.Row.valid_of_profile_le he hle₁ hnl₁,
    ProfileMonoV1.Row.valid_of_profile_le hs hle₂ hnl₂, ht, ?_, ?_, ?_, ?_, ?_, ?_, hmac, ?_, ?_⟩
  · show P₁.digestBits = P₂.digestBits
    rw [hle₁.digestBits, hle₂.digestBits]; exact hd
  · show P₁.row.fieldOrder ≠ 0
    rw [hle₁.row]; exact ho₁
  · show P₂.row.fieldOrder = 0
    rw [hle₂.row]; exact ho₂
  · show (2 * P₁.row.n + R.ecdsa.commitFuel) + (2 * P₂.row.n + R.sha.commitFuel) < R.sha.tape
    rw [hle₁.row, hle₂.row]; exact hroom
  · show P₁.row.openings + P₁.q + P₁.row.n ≤ P₁.row.fieldSize
    rw [hle₁.row, hle₁.q]; exact hrs₁
  · show P₂.row.openings + P₂.q + P₂.row.n ≤ P₂.row.fieldSize
    rw [hle₂.row, hle₂.q]; exact hrs₂
  · show ({ R.ecdsa with params := P₁ } : CertifiedV1.Row).bound
        + ({ R.sha with params := P₂ } : CertifiedV1.Row).bound + 1 / (R.macFieldSize : ℚ)
      ≤ 1 / 2 ^ R.lam
    have h₁ := ProfileMonoV1.Row.bound_le (R := R.ecdsa) hle₁
    have h₂ := ProfileMonoV1.Row.bound_le (R := R.sha) hle₂
    have : R.ecdsa.bound + R.sha.bound + 1 / (R.macFieldSize : ℚ) ≤ 1 / 2 ^ R.lam := hbound
    linarith
  · show P₁.proofBytes + P₂.proofBytes ≤ R.sizeBound
    have := ProfileMonoV1.proofBytes_le hle₁
    have := ProfileMonoV1.proofBytes_le hle₂
    omega

end TwoFieldRowV1

/-! ## The composed theorem at a valid row -/

section Compose

open Bcs Merkle Merkle.MH Merkle.RandomOracle
open scoped Classical
open Lfzk.Mac Lfzk.TwoField Lfzk.TwoFieldBridge Lfzk.TwoFieldV1

variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {D : Type} [Fintype D] [DecidableEq D] [Inhabited D]
variable {Fmac : Type} [Field Fmac] [Fintype Fmac] {nblk tlen T : ℕ}
variable {Cand₁ F₁ Equations₁ Witness₁ : Type} [Fintype Cand₁] [Nonempty Cand₁] [Field F₁]
  [Fintype F₁] [DecidableEq F₁] [SumcheckInterp F₁] [Fintype Equations₁] [DecidableEq Equations₁]
variable {nc₁ nv₁ logw₁ logc₁ : ℕ}
variable {Statement₁ Oracle₁ Challenge₁ Response₁ Query₁ : Type} {Opening₁ : Query₁ → Type}
variable {Enc₁ Salt₁ M₁ : Type} [DecidableEq Enc₁] [Inhabited Salt₁] [Inhabited M₁]
variable {Aux₁ Aux₁' : Type} {n₁ respondFuel₁ revealFuel₁ : ℕ}
variable {codec₁ : Codec Salt₁ M₁ D Enc₁} {dec₁ : RoleDecoders codec₁}
variable {K₁ : Compiler Statement₁ Oracle₁ Challenge₁ Response₁ Query₁ Opening₁ M₁ n₁}
variable {Cand₂ F₂ Equations₂ Witness₂ : Type} [Fintype Cand₂] [Nonempty Cand₂] [Field F₂]
  [Fintype F₂] [DecidableEq F₂] [SumcheckInterp F₂] [Fintype Equations₂] [DecidableEq Equations₂]
variable {nc₂ nv₂ logw₂ logc₂ : ℕ}
variable {Statement₂ Oracle₂ Challenge₂ Response₂ Query₂ : Type} {Opening₂ : Query₂ → Type}
variable {Enc₂ Salt₂ M₂ : Type} [DecidableEq Enc₂] [Inhabited Salt₂] [Inhabited M₂]
variable {Aux₂ Aux₂' : Type} {n₂ respondFuel₂ revealFuel₂ : ℕ}
variable {codec₂ : Codec Salt₂ M₂ D Enc₂} {dec₂ : RoleDecoders codec₂}
variable {K₂ : Compiler Statement₂ Oracle₂ Challenge₂ Response₂ Query₂ Opening₂ M₂ n₂}

/--
**A valid two-field V1 row certifies the composed protocol at `2^-lam`.**

`TwoFieldV1.twofield_v1_ratio_le_exact` at the row's two sides, with the MAC field of the row's size,
followed by the row's `target`.  The premises are the composed theorem's: per side a `V1Family` (see
`Lfzk.TwoFieldV1` for exactly what it assumes), the MAC slot's data, and the MAC rows `hrow₁`,
`hrow₂`.
-/
theorem TwoFieldRowV1.nizk_ratio_le {R : TwoFieldRowV1} (h : R.Valid)
    (hFmac : Fintype.card Fmac = R.macFieldSize)
    (sch : Schedule (Rounds.Role.length R.ecdsa.params.nl R.ecdsa.params.rounds)
      (Rounds.Role.length R.sha.params.nl R.sha.params.rounds) T)
    {challengeOf₁ :
      (Fin (Rounds.Role.length R.ecdsa.params.nl R.ecdsa.params.rounds) → C) → Challenge₁}
    {queryOf₁ : (Fin (Rounds.Role.length R.ecdsa.params.nl R.ecdsa.params.rounds) → C) → Query₁}
    {dom₁ : LigeroFamily.ReedSolomon.Domain F₁ R.ecdsa.params.row.openings R.ecdsa.params.q
      R.ecdsa.params.row.n}
    {challengeOf₂ :
      (Fin (Rounds.Role.length R.sha.params.nl R.sha.params.rounds) → C) → Challenge₂}
    {queryOf₂ : (Fin (Rounds.Role.length R.sha.params.nl R.sha.params.rounds) → C) → Query₂}
    {dom₂ : LigeroFamily.ReedSolomon.Domain F₂ R.sha.params.row.openings R.sha.params.q
      R.sha.params.row.n}
    (L₁ : V1Family R.ecdsa (TwoFieldRowV1.ecdsa_valid h) (Rest sch.ι₁ → C) C Cand₁ F₁
      Equations₁ Witness₁ nc₁ nv₁ logw₁ logc₁ Aux₁ Aux₁' tlen n₁ respondFuel₁ revealFuel₁ dec₁ K₁
      challengeOf₁ queryOf₁ dom₁)
    (L₂ : V1Family R.sha (TwoFieldRowV1.sha_valid h) (Rest sch.ι₂ → C) C Cand₂ F₂
      Equations₂ Witness₂ nc₂ nv₂ logw₂ logc₂ Aux₂ Aux₂' tlen n₂ respondFuel₂ revealFuel₂ dec₂ K₂
      challengeOf₂ queryOf₂ dom₂)
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
      ≤ (1 : ℚ) / 2 ^ R.lam := by
  refine le_trans (twofield_v1_ratio_le_exact sch L₁ L₂ decode aP kmac hbal hmac common₁ hrow₁
    common₂ hrow₂ hT) ?_
  have ht := TwoFieldRowV1.target h
  unfold TwoFieldRowV1.bound at ht
  rw [hFmac]
  exact ht

end Compose

/-! ## The row

`rows_valid` re-checks the literal by `native_decide`. -/

-- Recheck after any change to `Lfzk.CostV1.Params`; `rows_valid` re-checks it.
def rows : List TwoFieldRowV1 := [
  -- the deployed v8 circuits on both sides, V1 at 132 openings on both fields
  { ecdsa :=
      { params :=
          { row := Lfzk.LigeroV1Rows.v8Sig
            q := 362, nl := 21,
            logw := fun ly => [7, 8, 9, 10, 11, 11, 12, 12, 12, 13, 13, 13, 14, 14, 15, 15, 15, 15, 15, 14, 12].getD ly 0,
            logc := 0, digestBits := 256, ninp := 3941,
            colBytes := 32, nfullWit := 1 }
        lam := 121, cardCand := 2,
        commitFuel := 2 ^ 60, tape := 2 ^ 62,
        sizeBound := 141568 }
    sha :=
      { params :=
          { row := Lfzk.LigeroV1Rows.v8Hash
            q := 452, nl := 20,
            logw := fun ly => [7, 7, 8, 13, 13, 14, 15, 16, 15, 15, 15, 16, 17, 18, 20, 20, 20, 20, 19, 17].getD ly 0,
            logc := 0, digestBits := 256, ninp := 85733,
            colBytes := 2, nfullWit := 1 }
        lam := 114, cardCand := 2,
        commitFuel := 2 ^ 60, tape := 2 ^ 62,
        sizeBound := 145952 }
    macFieldSize := 2 ^ 128, lam := 114, sizeBound := 287520 }
]

/-- The row, by name: ECDSA over `P-256`'s base field and SHA over `GF(2^128)`, each at its deployed
v8 circuit profile and V1 at 132 openings, one shared hash tape of `2^62` slots. -/
def p256sha : TwoFieldRowV1 :=
  { ecdsa :=
      { params :=
          { row := Lfzk.LigeroV1Rows.v8Sig
            q := 362, nl := 21,
            logw := fun ly => [7, 8, 9, 10, 11, 11, 12, 12, 12, 13, 13, 13, 14, 14, 15, 15, 15, 15, 15, 14, 12].getD ly 0,
            logc := 0, digestBits := 256, ninp := 3941,
            colBytes := 32, nfullWit := 1 }
        lam := 121, cardCand := 2,
        commitFuel := 2 ^ 60, tape := 2 ^ 62,
        sizeBound := 141568 }
    sha :=
      { params :=
          { row := Lfzk.LigeroV1Rows.v8Hash
            q := 452, nl := 20,
            logw := fun ly => [7, 7, 8, 13, 13, 14, 15, 16, 15, 15, 15, 16, 17, 18, 20, 20, 20, 20, 19, 17].getD ly 0,
            logc := 0, digestBits := 256, ninp := 85733,
            colBytes := 2, nfullWit := 1 }
        lam := 114, cardCand := 2,
        commitFuel := 2 ^ 60, tape := 2 ^ 62,
        sizeBound := 145952 }
    macFieldSize := 2 ^ 128, lam := 114, sizeBound := 287520 }

theorem rows_eq : rows = [p256sha] := rfl

/-- **The row checks**, both sides included. -/
theorem rows_valid : rows.all TwoFieldRowV1.validBool = true := by native_decide

/-- The recorded `lam` is the composed bound's exact integer bit level. -/
theorem rows_sharp : rows.all TwoFieldRowV1.sharpBool = true := by native_decide

theorem p256sha_valid : p256sha.Valid := of_decide_eq_true (by native_decide)

theorem p256sha_sharp : p256sha.Sharp := of_decide_eq_true (by native_decide)

/-! ## Non-vacuity at `p256sha`, before any `lam` is used -/

/-- The two sides' fields: `p` and `2^128`. -/
theorem p256sha_fieldSizes :
    p256sha.ecdsa.params.row.fieldSize = Lfzk.LigeroV1Rows.p256Order ∧
      p256sha.sha.params.row.fieldSize = 2 ^ 128 ∧ p256sha.macFieldSize = 2 ^ 128 := by
  refine ⟨?_, ?_, rfl⟩ <;> decide

/-- **The V3 fuel failure does not occur**: neither side records `commitFuel = tape`. -/
theorem p256sha_commitFuel_lt_tape :
    p256sha.ecdsa.commitFuel < p256sha.ecdsa.tape ∧ p256sha.sha.commitFuel < p256sha.sha.tape :=
  ⟨(TwoFieldRowV1.fuel_satisfiable p256sha_valid).2.2.2.2.2.2.2.1,
    (TwoFieldRowV1.fuel_satisfiable p256sha_valid).2.2.2.2.2.2.2.2⟩

/--
**The fuel premises hold at `p256sha` with real fuel on both sides.**  At the two sides' column
counts (`3458` and `4088`) and `2^59 - 4088` opening fuel for each of the four reveal/respond stages,
both sides' `ht₁`, `hT`, `hT1` hold on the shared `2^62`-slot tape, and so does the joint budget.
-/
theorem p256sha_fuel :
    let n₁ := 3458
    let n₂ := 4088
    let f := 2 ^ 59 - 4088
    p256sha.ecdsa.params.row.n = n₁ ∧ p256sha.sha.params.row.n = n₂ ∧
      p256sha.ecdsa.tape = p256sha.sha.tape ∧
      p256sha.ecdsa.commitFuel ≤ p256sha.sha.tape ∧ p256sha.sha.commitFuel ≤ p256sha.sha.tape ∧
      1 ≤ p256sha.sha.tape ∧
      2 * n₁ + (f + f) + p256sha.ecdsa.commitFuel ≤ p256sha.sha.tape ∧
      2 * n₂ + (f + f) + p256sha.sha.commitFuel ≤ p256sha.sha.tape ∧
      (2 * n₁ + (f + f) + p256sha.ecdsa.commitFuel)
        + (2 * n₂ + (f + f) + p256sha.sha.commitFuel) ≤ p256sha.sha.tape ∧ 0 < f := by
  intro n₁ n₂ f
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [n₁, n₂, f, p256sha] <;> norm_num

open Lfzk.TwoFieldV1Fields in
/--
**Every numeric and type-level premise of the composed theorem is satisfiable at `p256sha`.**

* fields: `ZMod p` and `GaloisField 2 128` have the two sides' cardinalities, with
  `SumcheckInterp` instances (`TwoFieldV1Fields`; `p` prime by Pratt certificate), and the MAC field
  `GaloisField 2 128` has `macFieldSize`;
* both Reed–Solomon domains exist over them;
* the candidate types and the digest type exist at `cardCand = 2` and `2^256`;
* on the shared coin alphabet `TwoFieldCoins` (with the two sides' V1 challenge and query spaces at
  the row's `nw`, `nq`, `openings`), the MAC key decoder has `kmac · |Fmac| ≤ |C|`, and the pair
  budget has room for the layer-0 decoder on both fields.

At the same alphabet `twoField_coins_exact` re-decodes every field half of either side to an `Exact`
one; it is stated for all types, so it applies here verbatim.
-/
theorem p256sha_premises_satisfiable :
    Fintype.card FP256 = p256sha.ecdsa.params.row.fieldSize ∧
      Fintype.card GF128 = p256sha.sha.params.row.fieldSize ∧
      Fintype.card GF128 = p256sha.macFieldSize ∧
      Nonempty (LigeroFamily.ReedSolomon.Domain FP256 p256sha.ecdsa.params.row.openings
        p256sha.ecdsa.params.q p256sha.ecdsa.params.row.n) ∧
      Nonempty (LigeroFamily.ReedSolomon.Domain GF128 p256sha.sha.params.row.openings
        p256sha.sha.params.q p256sha.sha.params.row.n) ∧
      Fintype.card (Fin 2) = p256sha.ecdsa.cardCand ∧
      Fintype.card (Fin 2) = p256sha.sha.cardCand ∧
      Fintype.card (Fin (2 ^ 256)) = 2 ^ p256sha.ecdsa.params.digestBits ∧
      Fintype.card (Fin (2 ^ 256)) = 2 ^ p256sha.sha.params.digestBits ∧
      (macD FP256 (LigeroV1LayerStep.Chal FP256 Unit p256sha.ecdsa.params.nw p256sha.ecdsa.params.nq)
          (LigeroV1LayerStep.Qry p256sha.ecdsa.params.row) GF128
          (LigeroV1LayerStep.Chal GF128 Unit p256sha.sha.params.nw p256sha.sha.params.nq)
          (LigeroV1LayerStep.Qry p256sha.sha.params.row) GF128).k * Fintype.card GF128
        ≤ Fintype.card (TwoFieldCoins FP256
            (LigeroV1LayerStep.Chal FP256 Unit p256sha.ecdsa.params.nw p256sha.ecdsa.params.nq)
            (LigeroV1LayerStep.Qry p256sha.ecdsa.params.row) GF128
            (LigeroV1LayerStep.Chal GF128 Unit p256sha.sha.params.nw p256sha.sha.params.nq)
            (LigeroV1LayerStep.Qry p256sha.sha.params.row) GF128) ∧
      2 * Fintype.card FP256 ≤ CertifiedV1.pairBudget
        (Fintype.card (TwoFieldCoins FP256
            (LigeroV1LayerStep.Chal FP256 Unit p256sha.ecdsa.params.nw p256sha.ecdsa.params.nq)
            (LigeroV1LayerStep.Qry p256sha.ecdsa.params.row) GF128
            (LigeroV1LayerStep.Chal GF128 Unit p256sha.sha.params.nw p256sha.sha.params.nq)
            (LigeroV1LayerStep.Qry p256sha.sha.params.row) GF128))
        (Fintype.card FP256) ∧
      2 * Fintype.card GF128 ≤ CertifiedV1.pairBudget
        (Fintype.card (TwoFieldCoins FP256
            (LigeroV1LayerStep.Chal FP256 Unit p256sha.ecdsa.params.nw p256sha.ecdsa.params.nq)
            (LigeroV1LayerStep.Qry p256sha.ecdsa.params.row) GF128
            (LigeroV1LayerStep.Chal GF128 Unit p256sha.sha.params.nw p256sha.sha.params.nq)
            (LigeroV1LayerStep.Qry p256sha.sha.params.row) GF128))
        (Fintype.card GF128) := by
  have hF₁ : Fintype.card FP256 = p256sha.ecdsa.params.row.fieldSize := by
    rw [p256_card]; exact p256sha_fieldSizes.1.symm
  have hF₂ : Fintype.card GF128 = p256sha.sha.params.row.fieldSize := by
    rw [gf128_card]; exact p256sha_fieldSizes.2.1.symm
  haveI : Nonempty (LigeroV1LayerStep.Qry p256sha.ecdsa.params.row) :=
    LigeroFamily.QuerySet.nonempty (by decide)
  haveI : Nonempty (LigeroV1LayerStep.Qry p256sha.sha.params.row) :=
    LigeroFamily.QuerySet.nonempty (by decide)
  refine ⟨hF₁, hF₂, by rw [gf128_card]; rfl,
    TwoFieldRowV1.domain_exists_ecdsa p256sha_valid hF₁,
    TwoFieldRowV1.domain_exists_sha p256sha_valid hF₂,
    by simp [p256sha], by simp [p256sha], by simp [p256sha], by simp [p256sha],
    (macD _ _ _ _ _ _ _).hexact, pair_room (side₁ _ _ _ _ _ _ _).1,
    pair_room (side₂ _ _ _ _ _ _ _).1⟩

/-! ## The two-field statement at `p256sha`: `2^-114`

Every numeral above is checked; `fuel_satisfiable`, `p256sha_fuel`, `twoField_coins_exact` and
`p256sha_premises_satisfiable` show the row escapes the known vacuity modes. -/

section Headline

open Bcs Merkle Merkle.MH Merkle.RandomOracle
open scoped Classical
open Lfzk.Mac Lfzk.TwoField Lfzk.TwoFieldBridge Lfzk.TwoFieldV1

variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {D : Type} [Fintype D] [DecidableEq D] [Inhabited D]
variable {Fmac : Type} [Field Fmac] [Fintype Fmac] {nblk tlen : ℕ}
variable {Cand₁ F₁ Equations₁ Witness₁ : Type} [Fintype Cand₁] [Nonempty Cand₁] [Field F₁]
  [Fintype F₁] [DecidableEq F₁] [SumcheckInterp F₁] [Fintype Equations₁] [DecidableEq Equations₁]
variable {nc₁ nv₁ logw₁ logc₁ : ℕ}
variable {Statement₁ Oracle₁ Challenge₁ Response₁ Query₁ : Type} {Opening₁ : Query₁ → Type}
variable {Enc₁ Salt₁ M₁ : Type} [DecidableEq Enc₁] [Inhabited Salt₁] [Inhabited M₁]
variable {Aux₁ Aux₁' : Type} {n₁ respondFuel₁ revealFuel₁ : ℕ}
variable {codec₁ : Codec Salt₁ M₁ D Enc₁} {dec₁ : RoleDecoders codec₁}
variable {K₁ : Compiler Statement₁ Oracle₁ Challenge₁ Response₁ Query₁ Opening₁ M₁ n₁}
variable {Cand₂ F₂ Equations₂ Witness₂ : Type} [Fintype Cand₂] [Nonempty Cand₂] [Field F₂]
  [Fintype F₂] [DecidableEq F₂] [SumcheckInterp F₂] [Fintype Equations₂] [DecidableEq Equations₂]
variable {nc₂ nv₂ logw₂ logc₂ : ℕ}
variable {Statement₂ Oracle₂ Challenge₂ Response₂ Query₂ : Type} {Opening₂ : Query₂ → Type}
variable {Enc₂ Salt₂ M₂ : Type} [DecidableEq Enc₂] [Inhabited Salt₂] [Inhabited M₂]
variable {Aux₂ Aux₂' : Type} {n₂ respondFuel₂ revealFuel₂ : ℕ}
variable {codec₂ : Codec Salt₂ M₂ D Enc₂} {dec₂ : RoleDecoders codec₂}
variable {K₂ : Compiler Statement₂ Oracle₂ Challenge₂ Response₂ Query₂ Opening₂ M₂ n₂}

/-- The tape length of Protocol 3.8's schedule at `p256sha`: the key slot, then both sides. -/
abbrev keyFirstLen : ℕ :=
  1 + Rounds.Role.length p256sha.ecdsa.params.nl p256sha.ecdsa.params.rounds
    + Rounds.Role.length p256sha.sha.params.nl p256sha.sha.params.rounds

/--
**Two-field Longfellow at `p256sha`, end to end: `2^-114`.**

ECDSA over `P-256`'s base field and SHA-256 over `GF(2^128)`, each at its deployed v8 circuit profile
proved with Ligero V1 at 132 openings, composed through the MAC over a field of `2^128` elements, at
Protocol 3.8's schedule (`k_v`, then the ECDSA side's coins, then the SHA side's):

```text
Pr over (pre, tape) [ both compiled verifiers accept  ∧  the composed extractor fails ]  ≤  2^-114
```

The premises are `TwoFieldRowV1.nizk_ratio_le`'s at `p256sha` and `Schedule.keyFirst`: per side a
`TwoFieldV1.V1Family` (`hfalse`, `hright`, `hexact`, the field half of LayerStep, the numeric
premises), the MAC slot's `decode`, `hbal`, `hmac`, `|Fmac| = 2^128`, and the MAC rows `hrow₁`,
`hrow₂`.  Their numeric and type-level parts are jointly satisfiable
(`p256sha_premises_satisfiable`, `p256sha_fuel`).
-/
theorem p256sha_nizk_ratio_le_keyFirst
    (hFmac : Fintype.card Fmac = 2 ^ 128)
    {challengeOf₁ :
      (Fin (Rounds.Role.length p256sha.ecdsa.params.nl p256sha.ecdsa.params.rounds) → C) →
        Challenge₁}
    {queryOf₁ :
      (Fin (Rounds.Role.length p256sha.ecdsa.params.nl p256sha.ecdsa.params.rounds) → C) → Query₁}
    {dom₁ : LigeroFamily.ReedSolomon.Domain F₁ p256sha.ecdsa.params.row.openings
      p256sha.ecdsa.params.q p256sha.ecdsa.params.row.n}
    {challengeOf₂ :
      (Fin (Rounds.Role.length p256sha.sha.params.nl p256sha.sha.params.rounds) → C) → Challenge₂}
    {queryOf₂ :
      (Fin (Rounds.Role.length p256sha.sha.params.nl p256sha.sha.params.rounds) → C) → Query₂}
    {dom₂ : LigeroFamily.ReedSolomon.Domain F₂ p256sha.sha.params.row.openings
      p256sha.sha.params.q p256sha.sha.params.row.n}
    (L₁ : V1Family p256sha.ecdsa (TwoFieldRowV1.ecdsa_valid p256sha_valid)
      (Rest (Schedule.keyFirst
        (Rounds.Role.length p256sha.ecdsa.params.nl p256sha.ecdsa.params.rounds)
        (Rounds.Role.length p256sha.sha.params.nl p256sha.sha.params.rounds)).ι₁ → C)
      C Cand₁ F₁ Equations₁ Witness₁ nc₁ nv₁ logw₁ logc₁ Aux₁ Aux₁' tlen n₁ respondFuel₁
      revealFuel₁ dec₁ K₁ challengeOf₁ queryOf₁ dom₁)
    (L₂ : V1Family p256sha.sha (TwoFieldRowV1.sha_valid p256sha_valid)
      (Rest (Schedule.keyFirst
        (Rounds.Role.length p256sha.ecdsa.params.nl p256sha.ecdsa.params.rounds)
        (Rounds.Role.length p256sha.sha.params.nl p256sha.sha.params.rounds)).ι₂ → C)
      C Cand₂ F₂ Equations₂ Witness₂ nc₂ nv₂ logw₂ logc₂ Aux₂ Aux₂' tlen n₂ respondFuel₂
      revealFuel₂ dec₂ K₂ challengeOf₂ queryOf₂ dom₂)
    (decode : C → Fmac) (aP : (Fin tlen → D) → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    {keyB tag : (Fin tlen → D) × (Fin keyFirstLen → C) → Fin nblk → Fmac}
    (common₁ : Witness₁ → Fin nblk → Fmac)
    (hrow₁ : ∀ (ω : (Fin tlen → D) × (Fin keyFirstLen → C)) (cand : Cand₁),
      L₁.accepts (restOf (Schedule.keyFirst _ _).ι₁ ω.2) (ω.1, ω.2 ∘ (Schedule.keyFirst _ _).ι₁) →
      L₁.Sat (restOf (Schedule.keyFirst _ _).ι₁ ω.2) ω.1 cand →
      macTag (aP ω.1 + decode (ω.2 (Schedule.keyFirst _ _).s)) (keyB ω)
        (common₁ ((L₁.field (restOf (Schedule.keyFirst _ _).ι₁ ω.2) ω.1).wOf cand)) = tag ω)
    (common₂ : Witness₂ → Fin nblk → Fmac)
    (hrow₂ : ∀ (ω : (Fin tlen → D) × (Fin keyFirstLen → C)) (cand : Cand₂),
      L₂.accepts (restOf (Schedule.keyFirst _ _).ι₂ ω.2) (ω.1, ω.2 ∘ (Schedule.keyFirst _ _).ι₂) →
      L₂.Sat (restOf (Schedule.keyFirst _ _).ι₂ ω.2) ω.1 cand →
      macTag (aP ω.1 + decode (ω.2 (Schedule.keyFirst _ _).s)) (keyB ω)
        (common₂ ((L₂.field (restOf (Schedule.keyFirst _ _).ι₂ ω.2) ω.1).wOf cand)) = tag ω) :
    ((univ.filter fun ω : (Fin tlen → D) × (Fin keyFirstLen → C) =>
        (L₁.macSide common₁ hrow₁).accepts ω ∧ (L₂.macSide common₂ hrow₂).accepts ω ∧
          composedE (L₁.macSide common₁ hrow₁) (L₂.macSide common₂ hrow₂) ω = none).card : ℚ)
        / (Fintype.card (Fin tlen → D) * (Fintype.card C : ℚ) ^ keyFirstLen)
      ≤ (1 : ℚ) / 2 ^ 114 :=
  TwoFieldRowV1.nizk_ratio_le p256sha_valid hFmac (Schedule.keyFirst _ _) L₁ L₂ decode aP kmac hbal
    hmac common₁ hrow₁ common₂ hrow₂ (by omega)

end Headline

/-! ## Covering narrower circuits -/

/-- **`p256sha` covers every pair of circuits no wider than the deployed profiles**: the
row at any pair of narrower profiles is valid at the same `lam = 114`, with no new `native_decide`;
`TwoFieldRowV1.nizk_ratio_le` then applies to it. -/
theorem p256sha_valid_of_profile_le {P₁ P₂ : CostV1.Params}
    (hle₁ : ProfileMonoV1.ProfileLe P₁ p256sha.ecdsa.params)
    (hle₂ : ProfileMonoV1.ProfileLe P₂ p256sha.sha.params) :
    (p256sha.withProfiles P₁ P₂).Valid ∧ (p256sha.withProfiles P₁ P₂).lam = 114 :=
  ⟨TwoFieldRowV1.valid_of_profile_le p256sha_valid hle₁ hle₂ (by decide) (by decide), rfl⟩

end Lfzk.TwoFieldV1Rows
