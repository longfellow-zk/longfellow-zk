import Lfzk.TwoField
import Lfzk.Nizk

/-!
# The two-field bound, non-interactively

Phase 5 of `../two-field-plan.md`: carrying `Lfzk.TwoField`'s composition into the round-by-round
setting, where the verifier's key share is not sampled but *hashed* — one more slot on the
Fiat–Shamir tape.

```
Pr over (commitment, tape) [ both verifiers accept  ∧  the composed extractor fails ]
      ≤  b₁  +  b₂  +  kmac / |C|
```

`b₁` and `b₂` are the two sides' own non-interactive bounds — each is a whole Longfellow argument,
and `Lfzk.Certified.Row.nizk_ratio_le_longfellow` is what supplies one.  `kmac` is the balance of the
decoder that reads the key challenge off an oracle answer: `1` for a bijective decoder at `|C| =
|Fmac|`, which is the deployed case.

**So the two-field step costs one tape slot with escape budget `kmac`, and nothing else.**  Not one
per layer, not one per side, not one per pair of sides — one, for the whole composition.

## The MAC key slot *is* a round-by-round argument

That is the content of this file, and `macRbr` is where it lives.  The event the two-field soundness
proof has to charge for is `keyA ω = 0`, and over a tape that reads

```
doomed j pref  :=  ∀ h : s < j, ¬ (a_p + decode (pref s) = 0)
```

— vacuous before the key slot is read, and afterwards the assertion that the key survived.  Every
slot but `s` has escape budget `0`, because the state is a function of one already-fixed answer;
slot `s` has budget `kmac`, because escaping means landing in `decode⁻¹(-a_p)`.  `Bcs.Rbr` then does
the counting, and `Bcs.rbr_ratio_le_prod` sums over commitments.

This is not a re-derivation of `Lfzk.Mac.macKeyBad_split_card` in another idiom: that lemma splits
the sample space as `D × Fmac`, which is the *interactive* model where the verifier samples the key.
Here the key is a hash output at a designated slot of a shared tape, alongside every other
challenge, and what has to be shown is that no other round can move the event — which is what a
per-slot budget of `0` says.

## What the composition needs, and what it does not

The three-way decomposition is `Lfzk.TwoField.composed_fail_subset`, unchanged: the composed
extractor fails only if one of the two individual extractors fails, or the multiplier vanishes.  So
this file is a union bound over three ratios, and the two side bounds are *inputs* — the composition
does not care how they were obtained, only that they are over the same sample space.

**No ordering hypothesis between the sides.**  Protocol 3.8 runs `Ĉ₁`'s transcript and then `Ĉ₂`'s,
but nothing here needs that: each side's bound is over the whole tape, so each side is analysed
against an adversary that already sees the other side's coins.  That makes the model *stronger*
than the protocol rather than weaker, which is the same trade `Lfzk.TwoFieldAPI` records for the
key share.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset Sumcheck
open scoped Classical

namespace Lfzk.TwoFieldNizk

open Lfzk.Mac Lfzk.TwoField

variable {Pre C Fmac : Type} [Fintype Pre] [Fintype C] [DecidableEq C]
-- **No `[DecidableEq Fmac]` here, deliberately.**  `Lfzk.TwoField` states `composed_fail_card_le`
-- with only `[Field Fmac]` in scope, so its `keyA ω = 0` filter carries the classical
-- `DecidablePred`.  Declaring `DecidableEq Fmac` here would make the same filter carry a *different*
-- instance, and the two statements would print identically and refuse to unify.
variable [Field Fmac]
variable {T : ℕ}

/-! ## The key slot -/

/--
**The MAC key challenge, as a one-slot round-by-round argument.**

`s` is the slot the key challenge is read from, `decode` turns an oracle answer into a field
element, `ap` is the prover's committed share and `kmac` the decoder's balance.

The state is "the multiplier has not been killed", which is vacuous until slot `s` is read and a
fixed fact afterwards.  So every slot but `s` has escape budget `0` — nothing else in the protocol
can move this event — and slot `s` has budget `kmac`.
-/
noncomputable def macRbr (s : Fin T) (decode : C → Fmac) (ap : Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac) :
    Bcs.Rbr C T (fun tape => ap + decode (tape s) = 0) True where
  doomed j pref := ∀ h : s.val < j, ¬ (ap + decode (pref ⟨s.val, h⟩) = 0)
  beta i := if i = s then kmac else 0
  doomed_start := by
    intro _ _ h
    exact absurd h (by omega)
  doom_preserved := by
    intro i pref hdoom
    by_cases hi : i = s
    · -- the key slot: escaping means the answer decodes to `-ap`
      subst hi
      simp only
      refine le_trans (Finset.card_le_card ?_) (hbal (-ap))
      intro c hc
      simp only [mem_filter, mem_univ, true_and, not_forall, not_not] at hc ⊢
      obtain ⟨_, hzero⟩ := hc
      have hval : (Bcs.extend pref c) ⟨i.val, by omega⟩ = c := by
        simp [Bcs.extend]
      rw [hval] at hzero
      linear_combination hzero
    · -- any other slot: the state cannot change, so nothing escapes
      simp only [if_neg hi]
      refine le_trans (Finset.card_le_card ?_) (le_of_eq (Finset.card_empty (α := C)))
      intro c hc
      simp only [mem_filter, mem_univ, true_and, not_forall, not_not] at hc
      obtain ⟨hlt, hzero⟩ := hc
      exfalso
      rcases Nat.lt_or_ge s.val i.val with hs | hs
      · -- slot `s` is already in the prefix, so the state is unchanged
        have hval : (Bcs.extend pref c) ⟨s.val, hlt⟩ = pref ⟨s.val, hs⟩ := by
          simp [Bcs.extend, hs]
        rw [hval] at hzero
        exact hdoom hs hzero
      · -- slot `s` has not been read yet, so the state is still vacuous
        have : s.val = i.val := by omega
        exact hi (Fin.ext this).symm
  accepts_undoomed := by
    intro tape hacc hdoom
    exact hdoom s.isLt (by simpa [Bcs.trunc] using hacc)

omit [DecidableEq C] in
/-- The key slot is the only one with a budget, so LayerStep's total is `kmac`. -/
theorem macRbr_budget (s : Fin T) (decode : C → Fmac) (ap : Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac) :
    (∑ i, (macRbr s decode ap kmac hbal).beta i) = kmac := by
  simp [macRbr]

/--
**The key slot costs `kmac / |C|`.**

`Bcs.rbr_ratio_le_prod` at `macRbr`, one per commitment.  At a bijective decoder — `|C| = |Fmac|`,
the deployed case — this is `1/|Fmac| = 2^-128`, the same number
`Lfzk.Mac.macKeyBad_split_card` gives in the interactive model.
-/
theorem mac_slot_ratio [Nonempty Pre] [Nonempty C]
    (s : Fin T) (decode : C → Fmac) (aP : Pre → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hT : 1 ≤ T) :
    ((univ.filter fun ω : Pre × (Fin T → C) => aP ω.1 + decode (ω.2 s) = 0).card : ℚ)
        / (Fintype.card Pre * (Fintype.card C : ℚ) ^ T)
      ≤ (kmac : ℚ) / (Fintype.card C : ℚ) := by
  have h := Bcs.rbr_ratio_le_prod
    (Accepts := fun ω : Pre × (Fin T → C) => aP ω.1 + decode (ω.2 s) = 0)
    (Fails := fun _ : Pre => True)
    (fun pre => macRbr s decode (aP pre) kmac hbal) kmac
    (fun pre => le_of_eq (macRbr_budget s decode (aP pre) kmac hbal)) hT
  simpa using h

/-! ## The composition -/

variable {nblk : ℕ} {W₁ W₂ : Type}

/--
**The two-field bound, non-interactively.**

`b₁` and `b₂` are the two sides' own bounds over the shared sample space; the composition adds
exactly `kmac / |C|`, the cost of the one tape slot that carries the key challenge.

The key is `aP pre + decode (tape s)`: the prover's share is fixed by the commitment stage and the
verifier's share is the hash output at slot `s`.  That is the only causality this needs — and note
what it does *not* need: neither extractor is required to be a function of the commitment alone, and
the two sides' slots are not required to be disjoint, because `Lfzk.TwoField.composed_fail_subset`
puts the whole burden on the event `keyA ω = 0`, which mentions no extracted value.
-/
theorem twofield_nizk_ratio_le [Nonempty Pre] [Nonempty C]
    (s : Fin T) (decode : C → Fmac) (aP : Pre → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    {keyB tag : Pre × (Fin T → C) → Fin nblk → Fmac}
    (side₁ : MacBound Fmac nblk (Pre × (Fin T → C))
      (fun ω => aP ω.1 + decode (ω.2 s)) keyB tag W₁)
    (side₂ : MacBound Fmac nblk (Pre × (Fin T → C))
      (fun ω => aP ω.1 + decode (ω.2 s)) keyB tag W₂)
    {b₁ b₂ : ℚ}
    (h₁ : ((univ.filter fun ω : Pre × (Fin T → C) =>
          side₁.accepts ω ∧ side₁.E ω = none).card : ℚ)
        / (Fintype.card Pre * (Fintype.card C : ℚ) ^ T) ≤ b₁)
    (h₂ : ((univ.filter fun ω : Pre × (Fin T → C) =>
          side₂.accepts ω ∧ side₂.E ω = none).card : ℚ)
        / (Fintype.card Pre * (Fintype.card C : ℚ) ^ T) ≤ b₂)
    (hT : 1 ≤ T) :
    ((univ.filter fun ω : Pre × (Fin T → C) =>
        side₁.accepts ω ∧ side₂.accepts ω ∧ composedE side₁ side₂ ω = none).card : ℚ)
        / (Fintype.card Pre * (Fintype.card C : ℚ) ^ T)
      ≤ b₁ + b₂ + (kmac : ℚ) / (Fintype.card C : ℚ) := by
  have hmac := mac_slot_ratio (Pre := Pre) s decode aP kmac hbal hT
  -- the three-way decomposition, as a count.  `composed_fail_card_le` states it with no `∪`, so no
  -- `DecidableEq` instance has to cross the file boundary
  have hcard : (univ.filter fun ω : Pre × (Fin T → C) =>
        side₁.accepts ω ∧ side₂.accepts ω ∧ composedE side₁ side₂ ω = none).card
      ≤ (univ.filter fun ω : Pre × (Fin T → C) => side₁.accepts ω ∧ side₁.E ω = none).card
        + (univ.filter fun ω : Pre × (Fin T → C) => side₂.accepts ω ∧ side₂.E ω = none).card
        + (univ.filter fun ω : Pre × (Fin T → C) => aP ω.1 + decode (ω.2 s) = 0).card := composed_fail_card_le side₁ side₂
  -- and as a ratio
  have hDpos : (0 : ℚ) < Fintype.card Pre * (Fintype.card C : ℚ) ^ T := by
    have hP : (0 : ℚ) < Fintype.card Pre := by exact_mod_cast Fintype.card_pos (α := Pre)
    have hC : (0 : ℚ) < Fintype.card C := by exact_mod_cast Fintype.card_pos (α := C)
    positivity
  have hq : ((univ.filter fun ω : Pre × (Fin T → C) =>
        side₁.accepts ω ∧ side₂.accepts ω ∧ composedE side₁ side₂ ω = none).card : ℚ)
      ≤ ((univ.filter fun ω : Pre × (Fin T → C) => side₁.accepts ω ∧ side₁.E ω = none).card : ℚ)
        + ((univ.filter fun ω : Pre × (Fin T → C) => side₂.accepts ω ∧ side₂.E ω = none).card : ℚ)
        + ((univ.filter fun ω : Pre × (Fin T → C) => aP ω.1 + decode (ω.2 s) = 0).card : ℚ) := by exact_mod_cast hcard
  calc ((univ.filter fun ω : Pre × (Fin T → C) =>
        side₁.accepts ω ∧ side₂.accepts ω ∧ composedE side₁ side₂ ω = none).card : ℚ)
        / (Fintype.card Pre * (Fintype.card C : ℚ) ^ T)
      ≤ (((univ.filter fun ω : Pre × (Fin T → C) => side₁.accepts ω ∧ side₁.E ω = none).card : ℚ)
          + ((univ.filter fun ω : Pre × (Fin T → C) => side₂.accepts ω ∧ side₂.E ω = none).card : ℚ)
          + ((univ.filter fun ω : Pre × (Fin T → C) => aP ω.1 + decode (ω.2 s) = 0).card : ℚ))
          / (Fintype.card Pre * (Fintype.card C : ℚ) ^ T) := by gcongr
    _ = ((univ.filter fun ω : Pre × (Fin T → C) => side₁.accepts ω ∧ side₁.E ω = none).card : ℚ) / (Fintype.card Pre * (Fintype.card C : ℚ) ^ T)
          + ((univ.filter fun ω : Pre × (Fin T → C) => side₂.accepts ω ∧ side₂.E ω = none).card : ℚ) / (Fintype.card Pre * (Fintype.card C : ℚ) ^ T)
          + ((univ.filter fun ω : Pre × (Fin T → C) => aP ω.1 + decode (ω.2 s) = 0).card : ℚ) / (Fintype.card Pre * (Fintype.card C : ℚ) ^ T) := by ring
    _ ≤ b₁ + b₂ + (kmac : ℚ) / (Fintype.card C : ℚ) := by gcongr

/--
**At a bijective decoder the extra slot costs `1/|C|`.**

The deployed case: the key challenge is one full hash output read as one `GF(2^128)` element, so
`kmac = 1` and the composition pays `2^-128`.  This is the same numeral
`Lfzk.TwoFieldAPI.mac_term_costs_no_bit` shows does not cost a security bit.
-/
theorem twofield_nizk_ratio_le_bijective [Nonempty Pre] [Nonempty C]
    (s : Fin T) (decode : C → Fmac) (aP : Pre → Fmac)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ 1)
    {keyB tag : Pre × (Fin T → C) → Fin nblk → Fmac}
    (side₁ : MacBound Fmac nblk (Pre × (Fin T → C))
      (fun ω => aP ω.1 + decode (ω.2 s)) keyB tag W₁)
    (side₂ : MacBound Fmac nblk (Pre × (Fin T → C))
      (fun ω => aP ω.1 + decode (ω.2 s)) keyB tag W₂)
    {b₁ b₂ : ℚ}
    (h₁ : ((univ.filter fun ω : Pre × (Fin T → C) =>
          side₁.accepts ω ∧ side₁.E ω = none).card : ℚ)
        / (Fintype.card Pre * (Fintype.card C : ℚ) ^ T) ≤ b₁)
    (h₂ : ((univ.filter fun ω : Pre × (Fin T → C) =>
          side₂.accepts ω ∧ side₂.E ω = none).card : ℚ)
        / (Fintype.card Pre * (Fintype.card C : ℚ) ^ T) ≤ b₂)
    (hT : 1 ≤ T) :
    ((univ.filter fun ω : Pre × (Fin T → C) =>
        side₁.accepts ω ∧ side₂.accepts ω ∧ composedE side₁ side₂ ω = none).card : ℚ)
        / (Fintype.card Pre * (Fintype.card C : ℚ) ^ T)
      ≤ b₁ + b₂ + 1 / (Fintype.card C : ℚ) := by
  have h := twofield_nizk_ratio_le s decode aP 1 hbal side₁ side₂ h₁ h₂ hT
  simpa using h

/--
**At a security target.**  The form a parameter row is quoted in: two certified side bounds and one
slot, against `2^-lam`.
-/
theorem twofield_nizk_ratio_le_target [Nonempty Pre] [Nonempty C] (lam : ℕ)
    (s : Fin T) (decode : C → Fmac) (aP : Pre → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    {keyB tag : Pre × (Fin T → C) → Fin nblk → Fmac}
    (side₁ : MacBound Fmac nblk (Pre × (Fin T → C))
      (fun ω => aP ω.1 + decode (ω.2 s)) keyB tag W₁)
    (side₂ : MacBound Fmac nblk (Pre × (Fin T → C))
      (fun ω => aP ω.1 + decode (ω.2 s)) keyB tag W₂)
    {b₁ b₂ : ℚ}
    (h₁ : ((univ.filter fun ω : Pre × (Fin T → C) =>
          side₁.accepts ω ∧ side₁.E ω = none).card : ℚ)
        / (Fintype.card Pre * (Fintype.card C : ℚ) ^ T) ≤ b₁)
    (h₂ : ((univ.filter fun ω : Pre × (Fin T → C) =>
          side₂.accepts ω ∧ side₂.E ω = none).card : ℚ)
        / (Fintype.card Pre * (Fintype.card C : ℚ) ^ T) ≤ b₂)
    (hT : 1 ≤ T)
    (htarget : b₁ + b₂ + (kmac : ℚ) / (Fintype.card C : ℚ) ≤ (1 : ℚ) / 2 ^ lam) :
    ((univ.filter fun ω : Pre × (Fin T → C) =>
        side₁.accepts ω ∧ side₂.accepts ω ∧ composedE side₁ side₂ ω = none).card : ℚ)
        / (Fintype.card Pre * (Fintype.card C : ℚ) ^ T)
      ≤ (1 : ℚ) / 2 ^ lam :=
  le_trans (twofield_nizk_ratio_le s decode aP kmac hbal side₁ side₂ h₁ h₂ hT) htarget

/-! ## More than two sides

The MAC term does not scale with the number of sides: a disagreement between *any* two forces the
same single event `keyA ω = 0`, which is the same single tape slot.  So `n` arguments over `n`
fields cost `∑ᵢ bᵢ + kmac/|C|`. -/

/-- **The `n`-ary non-interactive bound.**  One extra tape slot, however many sides. -/
theorem twofield_nizk_family_ratio_le [Nonempty Pre] [Nonempty C] {n : ℕ} {W : Fin n → Type}
    (s : Fin T) (decode : C → Fmac) (aP : Pre → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    {keyB tag : Pre × (Fin T → C) → Fin nblk → Fmac}
    (sides : ∀ i, MacBound Fmac nblk (Pre × (Fin T → C))
      (fun ω => aP ω.1 + decode (ω.2 s)) keyB tag (W i))
    (b : Fin n → ℚ)
    (hb : ∀ i, ((univ.filter fun ω : Pre × (Fin T → C) =>
          (sides i).accepts ω ∧ (sides i).E ω = none).card : ℚ)
        / (Fintype.card Pre * (Fintype.card C : ℚ) ^ T) ≤ b i)
    (hT : 1 ≤ T) :
    ((univ.filter fun ω : Pre × (Fin T → C) => FamilyFails sides ω).card : ℚ)
        / (Fintype.card Pre * (Fintype.card C : ℚ) ^ T)
      ≤ (∑ i, b i) + (kmac : ℚ) / (Fintype.card C : ℚ) := by
  have hmac := mac_slot_ratio (Pre := Pre) s decode aP kmac hbal hT
  have hcard := family_fail_card_le sides
  have hDpos : (0 : ℚ) < Fintype.card Pre * (Fintype.card C : ℚ) ^ T := by
    have hP : (0 : ℚ) < Fintype.card Pre := by exact_mod_cast Fintype.card_pos (α := Pre)
    have hC : (0 : ℚ) < Fintype.card C := by exact_mod_cast Fintype.card_pos (α := C)
    positivity
  have hq : ((univ.filter fun ω : Pre × (Fin T → C) => FamilyFails sides ω).card : ℚ)
      ≤ (∑ i : Fin n, ((univ.filter fun ω : Pre × (Fin T → C) =>
            (sides i).accepts ω ∧ (sides i).E ω = none).card : ℚ))
        + ((univ.filter fun ω : Pre × (Fin T → C) =>
            aP ω.1 + decode (ω.2 s) = 0).card : ℚ) := by exact_mod_cast hcard
  calc ((univ.filter fun ω : Pre × (Fin T → C) => FamilyFails sides ω).card : ℚ)
        / (Fintype.card Pre * (Fintype.card C : ℚ) ^ T)
      ≤ ((∑ i : Fin n, ((univ.filter fun ω : Pre × (Fin T → C) =>
              (sides i).accepts ω ∧ (sides i).E ω = none).card : ℚ))
          + ((univ.filter fun ω : Pre × (Fin T → C) =>
              aP ω.1 + decode (ω.2 s) = 0).card : ℚ))
          / (Fintype.card Pre * (Fintype.card C : ℚ) ^ T) := by gcongr
    _ = (∑ i : Fin n, ((univ.filter fun ω : Pre × (Fin T → C) =>
              (sides i).accepts ω ∧ (sides i).E ω = none).card : ℚ)
            / (Fintype.card Pre * (Fintype.card C : ℚ) ^ T))
          + ((univ.filter fun ω : Pre × (Fin T → C) =>
              aP ω.1 + decode (ω.2 s) = 0).card : ℚ)
            / (Fintype.card Pre * (Fintype.card C : ℚ) ^ T) := by
        rw [add_div, Finset.sum_div]
    _ ≤ (∑ i, b i) + (kmac : ℚ) / (Fintype.card C : ℚ) :=
        add_le_add (Finset.sum_le_sum (fun i _ => hb i)) hmac

end Lfzk.TwoFieldNizk
