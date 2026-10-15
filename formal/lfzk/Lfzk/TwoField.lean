import Lfzk.Mac
import Lfzk.LigeroSystem

/-!
# Two-field consistency: knowledge soundness

Theorem 9 of the paper, soundness half.  Two arguments over two *different* fields prove two halves
of one statement; they share a witness, and a cheating prover could use different values for it in
the two instances.  Each circuit is augmented to assert `MAC_k(w) = m` at a jointly sampled key,
and this file is the bound that buys.

```
Pr[ both accept  ∧  the composed extractor fails ]
      ≤  eps₁/|Ω|  +  eps₂/|Ω|  +  1/|Fmac|
```

exactly — not `O(η + λ_s)`.  The third term is `Lfzk.Mac`'s collision count and at the deployed
parameters it is `2^-128`.

## Why the two sides are opaque

`MacBound.W` is a plain `Type`: no `Field` instance, no `LigeroSystem`, no dependent fields.  All
the MAC algebra happens in one field `Fmac`, and each side's only contribution is a *decoder*
`common : W → Fin nblk → Fmac`, which is where its own field's encoding lives — bit-sliced
`Gf2_128Mul` over `F_p256` on the ECDSA side, `as_eltw_field` over `GF(2^128)` on the SHA side.

So this file never mentions `F₁` or `F₂`, and the composition is genuinely field-agnostic — which is
what the paper claims when it says "two or more proof fields, or more generally, two or more proof
systems".  `macBound_of_ligeroSound` is the only place a `LigeroSystem` appears, and it is the
*instantiation*, one side at a time.

## The key and the tag are parameters, not fields

Both circuits verify the MAC at the **same** key and the **same** tag; that is the whole point of the
construction.  So `keyA`, `keyB` and `tag` are parameters of `MacBound` rather than fields of it, and
two sides over the same parameters share them *by typing*.  There is no `s₁.tag = s₂.tag` hypothesis
to supply or to get wrong.

This includes sharing the **private blind** `keyB`, not just the public multiplier and tags.
Rust v8 supplies the same public tags and multiplier to both circuits, but each circuit has its own
private blind witness (v7 instead has separate private multiplier shares). Equal honest-prover
private values do not establish the shared-`keyB` premise for
malicious proofs. Applying this theorem to those circuits remains an open obligation. A composition
using `Mac.macTag_collision_card_le_one` instead must track the pre-challenge candidate lists,
including the blinds, rather than use the message-independent zero-multiplier event below.

## No binding hypothesis on either extractor

This is the one place the argument here is simpler than the paper's sketch, and it is worth stating
because it determines the whole file.  The bad event is

```
keyA ω = 0
```

and **it does not mention the extracted values**.  `composed_fail_subset` derives it: if both sides
accept, both extract, and their decoded common values differ, then `Mac.macTag_collision` applied to
the two `mac_row`s at the shared key and tag forces the multiplier to vanish.  So `E₁` and `E₂` may
be arbitrarily adaptive — full functions of `Ω`, challenges included — and no "the commitment binds
the witness before `k_v`" hypothesis is needed.

The only causality requirement is on the **key**: the prover's share is a function of the prefix and
the verifier's coin is free.  That is the `Ω = D × Fmac` splitting of `twofield_soundness`, and it is
`Lfzk.Types.alpha_bad_card`'s shape.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset Sumcheck
open scoped Classical

namespace Lfzk.TwoField

open Lfzk.Mac

variable {Fmac : Type} [Field Fmac] {nblk : ℕ} {Ω : Type} [Fintype Ω]

/--
**One side of a two-field composition.**

An extractor with a knowledge error, whose output is pinned to the MAC equation at the shared key
and tag.  `W` is opaque; `common` is the side's decoder into `Fmac`.

`mac_row` is the interface to the circuit design — it says that satisfying this side's constraints
implies the MAC equation holds of the decoded values.  It is a statement about the
*arithmetization*, of the same kind as `ArithmetizedCircuit.arith`, and it is not discharged here;
`macBound_of_ligeroSound` reduces it to a statement about one Ligero system.
-/
structure MacBound (Fmac : Type) [Field Fmac] (nblk : ℕ) (Ω : Type) [Fintype Ω]
    (keyA : Ω → Fmac) (keyB tag : Ω → Fin nblk → Fmac) (W : Type) where
  /-- this side's verifier accepts -/
  accepts : Ω → Prop
  /-- this side's extractor -/
  E : Ω → Option W
  /-- this side's knowledge error, as a count over `Ω` -/
  eps : ℕ
  extraction : event_card (univ.filter fun ω => accepts ω ∧ E ω = none) ≤ eps
  /-- the common value this side committed, decoded into `nblk` elements of `Fmac` -/
  common : W → Fin nblk → Fmac
  /-- **the interface fact**: an accepted, extracted run satisfies the MAC equation -/
  mac_row : ∀ (ω : Ω) (a : W), accepts ω → E ω = some a →
    macTag (keyA ω) (keyB ω) (common a) = tag ω

variable {keyA : Ω → Fmac} {keyB tag : Ω → Fin nblk → Fmac} {W₁ W₂ : Type}

/--
**The composed extractor.**  Run both, and succeed only if both succeed *and* they agree on the
common value.  This is the paper's "if `w ≠ w'`, then the composed extractor fails".
-/
noncomputable def composedE (s₁ : MacBound Fmac nblk Ω keyA keyB tag W₁)
    (s₂ : MacBound Fmac nblk Ω keyA keyB tag W₂) : Ω → Option (W₁ × W₂) := fun ω =>
  match s₁.E ω, s₂.E ω with
  | some a₁, some a₂ => if s₁.common a₁ = s₂.common a₂ then some (a₁, a₂) else none
  | _, _ => none

/--
**When the composed extractor fails**, exactly three things can have gone wrong.  Everything
downstream is this characterisation plus `Mac.macTag_collision`.
-/
theorem composedE_eq_none_iff (s₁ : MacBound Fmac nblk Ω keyA keyB tag W₁)
    (s₂ : MacBound Fmac nblk Ω keyA keyB tag W₂) (ω : Ω) :
    composedE s₁ s₂ ω = none ↔
      (s₁.E ω = none ∨ s₂.E ω = none ∨
        ∃ a₁ a₂, s₁.E ω = some a₁ ∧ s₂.E ω = some a₂ ∧ s₁.common a₁ ≠ s₂.common a₂) := by
  unfold composedE
  cases hE1 : s₁.E ω <;> cases hE2 : s₂.E ω <;> simp_all

/-- When the composed extractor succeeds, the two sides really do agree — so its output is a joint
witness and not merely a pair. -/
theorem composedE_common_eq {s₁ : MacBound Fmac nblk Ω keyA keyB tag W₁}
    {s₂ : MacBound Fmac nblk Ω keyA keyB tag W₂} {ω : Ω} {p : W₁ × W₂}
    (h : composedE s₁ s₂ ω = some p) :
    s₁.E ω = some p.1 ∧ s₂.E ω = some p.2 ∧ s₁.common p.1 = s₂.common p.2 := by
  unfold composedE at h
  rcases hE1 : s₁.E ω with _ | a₁
  · rw [hE1] at h; exact absurd h (by simp)
  rcases hE2 : s₂.E ω with _ | a₂
  · rw [hE1, hE2] at h; exact absurd h (by simp)
  by_cases hc : s₁.common a₁ = s₂.common a₂
  · simp only [hE1, hE2, if_pos hc] at h
    obtain rfl : (a₁, a₂) = p := by simpa using h
    exact ⟨rfl, rfl, hc⟩
  · simp only [hE1, hE2, if_neg hc] at h
    exact absurd h (by simp)

/--
**The three-way decomposition.**

The composed extractor fails on an accepted run only if one of the two individual extractors fails,
or the multiplier is zero.  The third set is where the MAC does its work, and note again that it
does not mention the extracted values.
-/
theorem composed_fail_subset (s₁ : MacBound Fmac nblk Ω keyA keyB tag W₁)
    (s₂ : MacBound Fmac nblk Ω keyA keyB tag W₂) :
    (univ.filter fun ω => s₁.accepts ω ∧ s₂.accepts ω ∧ composedE s₁ s₂ ω = none)
      ⊆ (univ.filter fun ω => s₁.accepts ω ∧ s₁.E ω = none)
        ∪ (univ.filter fun ω => s₂.accepts ω ∧ s₂.E ω = none)
        ∪ (univ.filter fun ω => keyA ω = 0) := by
  intro ω hω
  simp only [mem_filter, mem_univ, true_and] at hω
  obtain ⟨ha₁, ha₂, hfail⟩ := hω
  simp only [mem_union, mem_filter, mem_univ, true_and]
  rcases (composedE_eq_none_iff s₁ s₂ ω).mp hfail with h | h | ⟨a₁, a₂, h1, h2, hne⟩
  · exact Or.inl (Or.inl ⟨ha₁, h⟩)
  · exact Or.inl (Or.inr ⟨ha₂, h⟩)
  · -- both extract but disagree: the two MAC rows at the shared key and tag kill the multiplier
    exact Or.inr (macTag_collision hne
      ((s₁.mac_row ω a₁ ha₁ h1).trans (s₂.mac_row ω a₂ ha₂ h2).symm))

/--
**The decomposition as a bare count.**

`composed_fail_subset` with the union discharged, so no `∪` appears in the statement.  That is not
cosmetic: a caller in another file synthesises its own `DecidableEq Ω`, which need not be the
classical one this file's unions carry, and the two do not unify.  Everything downstream — the
`eps`-form below and `Lfzk.TwoFieldNizk`'s ratio-level union bound — consumes this instead.
-/
theorem composed_fail_card_le (s₁ : MacBound Fmac nblk Ω keyA keyB tag W₁)
    (s₂ : MacBound Fmac nblk Ω keyA keyB tag W₂) :
    (univ.filter fun ω => s₁.accepts ω ∧ s₂.accepts ω ∧ composedE s₁ s₂ ω = none).card
      ≤ (univ.filter fun ω => s₁.accepts ω ∧ s₁.E ω = none).card
        + (univ.filter fun ω => s₂.accepts ω ∧ s₂.E ω = none).card
        + (univ.filter fun ω => keyA ω = 0).card := by
  refine le_trans (card_le_card (composed_fail_subset s₁ s₂)) ?_
  refine le_trans (card_union_le _ _) (Nat.add_le_add_right ?_ _)
  exact card_union_le _ _

/--
**The composed knowledge error, as a count.**

`nmac` is a bound on the multiplier-zero event; `twofield_soundness` supplies `|D|` for it from
`Mac.macKeyBad_split_card`.
-/
theorem twofield_extraction_card (s₁ : MacBound Fmac nblk Ω keyA keyB tag W₁)
    (s₂ : MacBound Fmac nblk Ω keyA keyB tag W₂) {nmac : ℕ}
    (hmac : (univ.filter fun ω => keyA ω = 0).card ≤ nmac) :
    event_card (univ.filter fun ω =>
        s₁.accepts ω ∧ s₂.accepts ω ∧ composedE s₁ s₂ ω = none)
      ≤ s₁.eps + s₂.eps + nmac := by
  dsimp only [event_card]
  refine le_trans (composed_fail_card_le s₁ s₂) ?_
  exact Nat.add_le_add (Nat.add_le_add s₁.extraction s₂.extraction) hmac

/--
**Theorem 9, soundness half.**

The sample space splits as `D × Fmac`: everything the prover decided before the key challenge, times
the challenge.  The prover's share `aP` of the multiplier is a function of the prefix — that is the
one causality requirement, and it is what "jointly sampled by the Prover and Verifier" means.

The MAC term is exactly `1/|Fmac|`, and `Mac.macKeyBad_card` says it is tight.
-/
theorem twofield_soundness {D : Type} [Fintype D] [Fintype Fmac] [DecidableEq Fmac]
    (aP : D → Fmac) {keyB tag : D × Fmac → Fin nblk → Fmac}
    (s₁ : MacBound Fmac nblk (D × Fmac) (fun p => aP p.1 + p.2) keyB tag W₁)
    (s₂ : MacBound Fmac nblk (D × Fmac) (fun p => aP p.1 + p.2) keyB tag W₂)
    (hD : 0 < Fintype.card D) (hF : 0 < Fintype.card Fmac) :
    (event_card (univ.filter fun ω : D × Fmac =>
          s₁.accepts ω ∧ s₂.accepts ω ∧ composedE s₁ s₂ ω = none) : ℚ)
        / Fintype.card (D × Fmac)
      ≤ (s₁.eps : ℚ) / Fintype.card (D × Fmac)
        + (s₂.eps : ℚ) / Fintype.card (D × Fmac)
        + 1 / Fintype.card Fmac := by
  have hDq : (0 : ℚ) < Fintype.card D := by exact_mod_cast hD
  have hFq : (0 : ℚ) < Fintype.card Fmac := by exact_mod_cast hF
  have hprod : (Fintype.card (D × Fmac) : ℚ) = Fintype.card D * Fintype.card Fmac := by
    rw [Fintype.card_prod]; push_cast; ring
  have hcount := twofield_extraction_card s₁ s₂ (nmac := Fintype.card D)
    (macKeyBad_split_card (Fmac := Fmac) aP)
  have hstep : (event_card (univ.filter fun ω : D × Fmac =>
        s₁.accepts ω ∧ s₂.accepts ω ∧ composedE s₁ s₂ ω = none) : ℚ)
      ≤ ((s₁.eps + s₂.eps + Fintype.card D : ℕ) : ℚ) := by exact_mod_cast hcount
  have hlast : ((Fintype.card D : ℕ) : ℚ) / Fintype.card (D × Fmac) = 1 / Fintype.card Fmac := by
    rw [hprod]; field_simp
  calc (event_card (univ.filter fun ω : D × Fmac =>
          s₁.accepts ω ∧ s₂.accepts ω ∧ composedE s₁ s₂ ω = none) : ℚ)
        / Fintype.card (D × Fmac)
      ≤ ((s₁.eps + s₂.eps + Fintype.card D : ℕ) : ℚ) / Fintype.card (D × Fmac) := by
        gcongr
    _ = (s₁.eps : ℚ) / Fintype.card (D × Fmac) + (s₂.eps : ℚ) / Fintype.card (D × Fmac)
          + ((Fintype.card D : ℕ) : ℚ) / Fintype.card (D × Fmac) := by push_cast; ring
    _ = (s₁.eps : ℚ) / Fintype.card (D × Fmac) + (s₂.eps : ℚ) / Fintype.card (D × Fmac)
          + 1 / Fintype.card Fmac := by rw [hlast]


/-! ## More than two sides

The paper's prose claims the technique for "two or more proof fields, or more generally, two or more
proof systems", and the theorem is stated for two.  The `n`-ary version is free here, because the
sides are opaque types: `W : Fin n → Type` needs no instances.

The headline is that **the MAC term does not scale with the number of sides.**  A disagreement
between *any* two sides forces the same single event `keyA ω = 0`, so the bound is
`∑ i, eps i + 1/|Fmac|` rather than one MAC term per pair. -/

section Family

variable {n : ℕ} {W : Fin n → Type}

/-- The `n`-ary failure event: some side fails to extract, or two sides disagree on the common
value. -/
def FamilyFails (s : ∀ i, MacBound Fmac nblk Ω keyA keyB tag (W i)) (ω : Ω) : Prop :=
  (∃ i, (s i).accepts ω ∧ (s i).E ω = none) ∨
  (∃ (i j : Fin n) (a : W i) (b : W j), (s i).accepts ω ∧ (s j).accepts ω ∧
    (s i).E ω = some a ∧ (s j).E ω = some b ∧ (s i).common a ≠ (s j).common b)

theorem family_fail_subset (s : ∀ i, MacBound Fmac nblk Ω keyA keyB tag (W i)) :
    (univ.filter fun ω => FamilyFails s ω)
      ⊆ (univ.biUnion fun i : Fin n => univ.filter fun ω => (s i).accepts ω ∧ (s i).E ω = none)
        ∪ (univ.filter fun ω => keyA ω = 0) := by
  intro ω hω
  simp only [mem_filter, mem_univ, true_and] at hω
  simp only [mem_union, mem_biUnion, mem_filter, mem_univ, true_and]
  rcases hω with ⟨i, hacc, hnone⟩ | ⟨i, j, a, b, hai, haj, hEi, hEj, hne⟩
  · exact Or.inl ⟨i, hacc, hnone⟩
  · exact Or.inr (macTag_collision hne
      (((s i).mac_row ω a hai hEi).trans ((s j).mac_row ω b haj hEj).symm))

/-- The `n`-ary decomposition as a bare count, union-free for the same reason as
`composed_fail_card_le`. -/
theorem family_fail_card_le (s : ∀ i, MacBound Fmac nblk Ω keyA keyB tag (W i)) :
    (univ.filter fun ω => FamilyFails s ω).card
      ≤ (∑ i : Fin n, (univ.filter fun ω => (s i).accepts ω ∧ (s i).E ω = none).card)
        + (univ.filter fun ω => keyA ω = 0).card := by
  refine le_trans (card_le_card (family_fail_subset s)) ?_
  exact le_trans (card_union_le _ _) (Nat.add_le_add_right card_biUnion_le _)

/-- **The `n`-ary bound.**  One MAC term, however many sides. -/
theorem family_extraction_card (s : ∀ i, MacBound Fmac nblk Ω keyA keyB tag (W i)) {nmac : ℕ}
    (hmac : (univ.filter fun ω => keyA ω = 0).card ≤ nmac) :
    event_card (univ.filter fun ω => FamilyFails s ω) ≤ (∑ i, (s i).eps) + nmac := by
  dsimp only [event_card]
  refine le_trans (family_fail_card_le s) ?_
  exact Nat.add_le_add (Finset.sum_le_sum (fun i _ => (s i).extraction)) hmac

end Family

/-! ## Instantiation: one side, from Ligero

The only place a `LigeroSystem` — and hence a per-side field — appears.  `IsLigeroSound.sound` says
an accepted, extracted run satisfies the public system; `hrow` says satisfying the system implies the
MAC equation.  Composing them is `MacBound.mac_row`.

`hrow` is the two-field step's share of README gap 2: it is the refinement statement for
`assert_mac`, which over `F_p256` is `Gf2_128Mul`'s bit-sliced multiplier (`mac/src/circuit.rs:46`)
and over `GF(2^128)` is a native `mul` (`mac_gf128/src/circuit.rs:47`).  Proving it means
constructing the arithmetization, which this development does not do for any circuit. -/

/-- Build a `MacBound` for one side out of that side's Ligero soundness and its MAC row. -/
def macBound_of_ligeroSound {ninp M : ℕ} {F : Type} [Field F]
    {accepts : Ω → Prop} {system : Ω → LigeroSystem ninp M F}
    {E : Ω → Option (LigeroAssignment ninp M F)} {eps : ℕ}
    (hs : IsLigeroSound accepts system E eps)
    (common : LigeroAssignment ninp M F → Fin nblk → Fmac)
    (hrow : ∀ (ω : Ω) (a : LigeroAssignment ninp M F), (system ω).Sat a.1 a.2 →
      macTag (keyA ω) (keyB ω) (common a) = tag ω) :
    MacBound Fmac nblk Ω keyA keyB tag (LigeroAssignment ninp M F) where
  accepts := accepts
  E := E
  eps := eps
  extraction := hs.extraction
  common := common
  mac_row := fun ω a hacc hE => hrow ω a (hs.sound ω a hacc hE)

end Lfzk.TwoField
