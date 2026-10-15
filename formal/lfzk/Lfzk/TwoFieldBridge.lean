import Lfzk.TwoFieldNizk

/-!
# The two-field composition, with the side bounds proved rather than assumed

`Lfzk.TwoFieldNizk.twofield_nizk_ratio_le` takes each side's knowledge-error ratio **over the
shared tape** as a hypothesis (`h₁`, `h₂`), and `Lfzk.Certified.TwoFieldRow.twofield_nizk_ratio_le`
inherits them as `hE`, `hS`.  A single-field theorem — `Lfzk.Nizk.nizk_ratio_le_merkle`, or
`Lfzk.Certified.Row.nizk_ratio_le_longfellow` — proves a bound over *that side's own* sample space
`Pre × (Fin Tᵢ → C)`.  This file is the step between the two, and it is a theorem.

```
∀ z, Pr over (pre, tapeᵢ) [ accᵢ z ∧ no good witness ]  ≤  bᵢ          (the single-field theorem)
─────────────────────────────────────────────────────────────────────    ratio_transfer
     Pr over (pre, tape)  [ sideᵢ accepts ∧ sideᵢ.E = none ]  ≤  bᵢ        (TwoFieldNizk's hᵢ)
```

where `z` is the merged tape restricted to the slots side `i` does **not** read.

## Three pieces

1. **The extractor** (`chooseE`, `MacBound.ofGood`).  A single-field theorem bounds
   `accepts ∧ (no candidate is good)`.  The extractor that outputs a good candidate when one exists
   has `E = none` *exactly* on that event (`chooseE_eq_none_iff`), so the side's `MacBound` knowledge
   error is the single-field event, with no slack and no new hypothesis.
2. **The merged schedule** (`Schedule`).  Side 1's slots, side 2's slots and the MAC key slot, as two
   injections `Fin T₁ → Fin T`, `Fin T₂ → Fin T` and a slot `s` in neither image.  `Schedule.keyFirst`
   is Protocol 3.8's order — `k_v`, then side 1, then side 2 — and covers the tape exactly.
3. **The transfer** (`tapeSplit`, `sideView`, `ratio_transfer`).  Injectivity of `ιᵢ` splits the merged
   tape as `(side i's coins) × (the rest)`; the rest is absorbed into a free coordinate `z`, and a bound
   that holds at *every* `z` survives averaging over `z`.  `ratio_transfer_equiv` is the same along any
   bijection `Ω' ≃ Z × Ω`, and `ratio_transfer_prefix` the case of a separated merged prefix `Y × Pre`
   (say, one hash tape per side), where `Y` joins the absorbed coordinate.

## The causality the proof needs, and nothing more

The counting in `ratio_transfer` uses only the product structure of the tape and `Injective ιᵢ`.
What the argument needs of the *protocol* is:

* **(C1) side `i`'s verifier reads its challenges only from its own slots.**  This is built into the
  merged acceptance `accᵢ (restOf ιᵢ ω.2) (ω.1, ω.2 ∘ ιᵢ)`: the tape enters side `i`'s verifier only
  through `ω.2 ∘ ιᵢ`;
* **(C2) everything else side `i` depends on is a function of `(z, pre)`.**  `z` contains the other
  side's coins and the key coin, so the side-`i` adversary — its commitment included — may depend on
  the other side's challenges, *including ones the real protocol draws later*, and the other side may
  depend on side `i`'s coins in turn.  That is foresight the real prover does not have, so the model
  is stronger than the protocol; it is sound because the single-field theorem is quantified over
  **all** adversaries and is applied once per `z`;
* **(C3) the prover's key share `aP` is a function of the prefix alone** — `TwoFieldNizk.macRbr`'s
  requirement, unchanged.  Protocol 3.8 commits `a_p` before `k_v` is drawn.

`Schedule.s_not₁`, `s_not₂` are **not** consumed by the counting.  What they buy is that the key coin
is one of the absorbed coordinates of *both* sides (`Schedule.key_rest₁`, `key_rest₂`), so each side's
statement — which takes the MAC key as a public input — is fixed by `(z, pre)` before that side's LayerStep
starts.  A single-field theorem whose doom-at-start is "the statement is false" needs exactly that,
and it is what "Protocol 3.8 draws `k_v` before the Ligero coins" provides.  No disjointness of the two
sides' slots is needed, and none is assumed; `Schedule.keyFirst` has it anyway (`keyFirst_disjoint`).

## What is still a hypothesis

`twofield_merged_ratio_le` has no ratio hypothesis on the shared tape.  Its inputs are, per side,
a `SideBound` — the single-field theorem's *conclusion*, at every absorbed `z` — and `hrow`, the
arithmetization fact that a good witness satisfies the MAC equation (`MacBound.mac_row`'s content,
kept named).  `Lfzk.TwoFieldLongfellow` builds a `SideBound` from Longfellow LayerStep data, so there the
first input is a theorem too.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset Sumcheck
open scoped Classical

namespace Lfzk.TwoFieldBridge

open Lfzk.Mac Lfzk.TwoField Lfzk.TwoFieldNizk

/-! ## 1. The extractor: output a good candidate when one exists -/

section Extractor

variable {Ω W : Type}

/-- **The choosing extractor.**  Output some `a` with `good ω a`, if there is one. -/
noncomputable def chooseE (good : Ω → W → Prop) : Ω → Option W := fun ω =>
  if h : ∃ a, good ω a then some h.choose else none

/-- `chooseE` fails exactly when there is no good candidate.  This is what makes the side's knowledge
error *equal* to the single-field theorem's failure event, rather than bounded by it. -/
theorem chooseE_eq_none_iff (good : Ω → W → Prop) (ω : Ω) :
    chooseE good ω = none ↔ ∀ a, ¬ good ω a := by
  unfold chooseE
  by_cases h : ∃ a, good ω a
  · simp only [dif_pos h, reduceCtorEq, false_iff, not_forall, not_not]
    exact h
  · simp only [dif_neg h, true_iff]
    exact fun a ha => h ⟨a, ha⟩

/-- What `chooseE` outputs is good. -/
theorem chooseE_spec {good : Ω → W → Prop} {ω : Ω} {a : W} (h : chooseE good ω = some a) :
    good ω a := by
  unfold chooseE at h
  by_cases hex : ∃ a, good ω a
  · rw [dif_pos hex, Option.some.injEq] at h
    exact h ▸ hex.choose_spec
  · rw [dif_neg hex] at h
    exact absurd h (by simp)

end Extractor

section MacSide

variable {Fmac : Type} [Field Fmac] {nblk : ℕ} {Ω : Type} [Fintype Ω]
variable {keyA : Ω → Fmac} {keyB tag : Ω → Fin nblk → Fmac} {W : Type}

/--
**A `MacBound` from a goodness relation.**

`good ω a` says `a` is a valid witness for this side's statement at `ω`; the extractor is `chooseE
good`, and the knowledge error `eps` is the count of the failure event itself, so `extraction` is
`le_rfl`.  `hrow` is the arithmetization fact — a good witness satisfies the MAC equation at the
shared key and tag — and it is the *only* thing this construction asks for beyond the relation.
-/
noncomputable def MacBound.ofGood (accepts : Ω → Prop) (good : Ω → W → Prop)
    (common : W → Fin nblk → Fmac)
    (hrow : ∀ (ω : Ω) (a : W), accepts ω → good ω a →
      macTag (keyA ω) (keyB ω) (common a) = tag ω) :
    MacBound Fmac nblk Ω keyA keyB tag W where
  accepts := accepts
  E := chooseE good
  eps := (univ.filter fun ω => accepts ω ∧ chooseE good ω = none).card
  extraction := le_rfl
  common := common
  mac_row := fun ω a hacc hE => hrow ω a hacc (chooseE_spec hE)

/-- **The knowledge-error event of `ofGood` is the "accepts, but nothing good" event**, as a count. -/
theorem MacBound.ofGood_fail_card (accepts : Ω → Prop) (good : Ω → W → Prop)
    (common : W → Fin nblk → Fmac)
    (hrow : ∀ (ω : Ω) (a : W), accepts ω → good ω a →
      macTag (keyA ω) (keyB ω) (common a) = tag ω) :
    (univ.filter fun ω => (MacBound.ofGood accepts good common hrow).accepts ω ∧
        (MacBound.ofGood accepts good common hrow).E ω = none).card
      = (univ.filter fun ω => accepts ω ∧ ∀ a, ¬ good ω a).card := by
  congr 1
  refine Finset.filter_congr (fun ω _ => ?_)
  exact and_congr_right fun _ => chooseE_eq_none_iff good ω

end MacSide

/-! ## 2. The merged schedule -/

/--
**One tape for the whole two-field argument.**

`ι₁`, `ι₂` place side 1's and side 2's challenge slots on the merged tape and `s` is the MAC key slot.
The injections are what make each side's coins a *coordinate* of the merged tape; `s_not₁`, `s_not₂`
put the key coin outside both sides' own coins — see the module docstring for what that buys and that
the counting does not consume it.
-/
structure Schedule (T₁ T₂ T : ℕ) where
  ι₁ : Fin T₁ → Fin T
  ι₂ : Fin T₂ → Fin T
  inj₁ : Function.Injective ι₁
  inj₂ : Function.Injective ι₂
  /-- The MAC key slot. -/
  s : Fin T
  s_not₁ : s ∉ Set.range ι₁
  s_not₂ : s ∉ Set.range ι₂

/-- The slots a side does not read. -/
abbrev Rest {Tᵢ T : ℕ} (ι : Fin Tᵢ → Fin T) : Type := {j : Fin T // j ∉ Set.range ι}

/-- The merged tape restricted to the slots a side does not read: the coordinate that is absorbed. -/
def restOf {C : Type} {Tᵢ T : ℕ} (ι : Fin Tᵢ → Fin T) (t : Fin T → C) : Rest ι → C :=
  fun j => t j.1

namespace Schedule

variable {T₁ T₂ T : ℕ} (sch : Schedule T₁ T₂ T) {C : Type}

/-- **The key coin is absorbed into side 1's free coordinate.**  So side 1's statement, which takes
the key as a public input, is a function of `(restOf ι₁ tape, pre)`. -/
theorem key_rest₁ (t : Fin T → C) : t sch.s = restOf sch.ι₁ t ⟨sch.s, sch.s_not₁⟩ := rfl

/-- The same for side 2. -/
theorem key_rest₂ (t : Fin T → C) : t sch.s = restOf sch.ι₂ t ⟨sch.s, sch.s_not₂⟩ := rfl

/--
**Protocol 3.8's order.**  The key challenge `k_v` at slot `0`, then side 1's `T₁` coins, then side
2's `T₂`.
-/
def keyFirst (T₁ T₂ : ℕ) : Schedule T₁ T₂ (1 + T₁ + T₂) where
  ι₁ j := ⟨1 + j.val, by omega⟩
  ι₂ j := ⟨1 + T₁ + j.val, by omega⟩
  inj₁ := by
    intro a b h
    have := congrArg Fin.val h
    exact Fin.ext (by simp only at this; omega)
  inj₂ := by
    intro a b h
    have := congrArg Fin.val h
    exact Fin.ext (by simp only at this; omega)
  s := ⟨0, by omega⟩
  s_not₁ := by
    rintro ⟨j, hj⟩
    have := congrArg Fin.val hj
    simp only at this
    omega
  s_not₂ := by
    rintro ⟨j, hj⟩
    have := congrArg Fin.val hj
    simp only at this
    omega

/-- In `keyFirst` the two sides read disjoint slots.  Not needed by any bound here. -/
theorem keyFirst_disjoint (T₁ T₂ : ℕ) (j₁ : Fin T₁) (j₂ : Fin T₂) :
    (keyFirst T₁ T₂).ι₁ j₁ ≠ (keyFirst T₁ T₂).ι₂ j₂ := by
  intro h
  have := congrArg Fin.val h
  simp only [keyFirst] at this
  omega

/-- **`keyFirst` is the whole tape**: every slot is the key slot, one of side 1's, or one of
side 2's.  So the merged tape carries nothing beyond the three parts. -/
theorem keyFirst_cover (T₁ T₂ : ℕ) (j : Fin (1 + T₁ + T₂)) :
    j = (keyFirst T₁ T₂).s ∨ j ∈ Set.range (keyFirst T₁ T₂).ι₁ ∨
      j ∈ Set.range (keyFirst T₁ T₂).ι₂ := by
  rcases Nat.eq_zero_or_pos j.val with h0 | hpos
  · exact Or.inl (Fin.ext (by simp [keyFirst, h0]))
  · by_cases h1 : j.val < 1 + T₁
    · refine Or.inr (Or.inl ⟨⟨j.val - 1, by omega⟩, Fin.ext ?_⟩)
      simp only [keyFirst]
      omega
    · refine Or.inr (Or.inr ⟨⟨j.val - (1 + T₁), by omega⟩, Fin.ext ?_⟩)
      simp only [keyFirst]
      omega

end Schedule

/-! ## 3. The transfer -/

section Transfer

variable {C : Type} {Tᵢ T : ℕ}

/--
**Split a merged tape into one side's coins and the rest.**  `Injective ι` is all it needs.
-/
noncomputable def tapeSplit (ι : Fin Tᵢ → Fin T) (hι : Function.Injective ι) :
    (Fin T → C) ≃ (Fin Tᵢ → C) × (Rest ι → C) :=
  (Equiv.piEquivPiSubtypeProd (fun j => j ∈ Set.range ι) (fun _ => C)).trans
    (Equiv.prodCongr ((Equiv.ofInjective ι hι).arrowCongr (Equiv.refl C)).symm (Equiv.refl _))

@[simp] theorem tapeSplit_fst (ι : Fin Tᵢ → Fin T) (hι : Function.Injective ι) (t : Fin T → C) :
    (tapeSplit ι hι t).1 = t ∘ ι := by
  funext i
  simp [tapeSplit, Equiv.arrowCongr]

@[simp] theorem tapeSplit_snd (ι : Fin Tᵢ → Fin T) (hι : Function.Injective ι) (t : Fin T → C) :
    (tapeSplit ι hι t).2 = restOf ι t := rfl

/--
**A side's view of the merged sample space**: the absorbed coordinate, then the side's own sample
space.  An equivalence, so counting through it loses nothing.
-/
noncomputable def sideView {Pre : Type} (ι : Fin Tᵢ → Fin T) (hι : Function.Injective ι) :
    Pre × (Fin T → C) ≃ (Rest ι → C) × (Pre × (Fin Tᵢ → C)) where
  toFun ω := ((tapeSplit ι hι ω.2).2, (ω.1, (tapeSplit ι hι ω.2).1))
  invFun p := (p.2.1, (tapeSplit ι hι).symm (p.2.2, p.1))
  left_inv ω := by
    rcases ω with ⟨pre, t⟩
    simp only [Prod.mk.eta, Equiv.symm_apply_apply]
  right_inv p := by
    rcases p with ⟨z, pre, t⟩
    simp only [Equiv.apply_symm_apply]

@[simp] theorem sideView_apply {Pre : Type} (ι : Fin Tᵢ → Fin T) (hι : Function.Injective ι)
    (ω : Pre × (Fin T → C)) :
    sideView ι hι ω = (restOf ι ω.2, (ω.1, ω.2 ∘ ι)) := by
  simp [sideView]

/--
**Averaging a fibrewise bound.**  If every fibre `{x | P z x}` has density at most `b`, so does the
whole event over `Z × Ω`.
-/
theorem fiber_ratio_le {Z Ω : Type} [Fintype Z] [Fintype Ω] [Nonempty Z] [Nonempty Ω]
    (P : Z → Ω → Prop) {b : ℚ}
    (h : ∀ z, ((univ.filter fun x => P z x).card : ℚ) / Fintype.card Ω ≤ b) :
    ((univ.filter fun p : Z × Ω => P p.1 p.2).card : ℚ)
        / ((Fintype.card Z : ℚ) * Fintype.card Ω) ≤ b := by
  have hZ : (0 : ℚ) < Fintype.card Z := by exact_mod_cast Fintype.card_pos
  have hΩ : (0 : ℚ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hsum : (univ.filter fun p : Z × Ω => P p.1 p.2).card
      = ∑ z : Z, (univ.filter fun x => P z x).card := by
    simp only [Finset.card_filter, Fintype.sum_prod_type]
  rw [hsum, div_le_iff₀ (mul_pos hZ hΩ)]
  push_cast
  calc (∑ z : Z, ((univ.filter fun x => P z x).card : ℚ))
      ≤ ∑ _z : Z, b * Fintype.card Ω :=
        Finset.sum_le_sum fun z _ => (div_le_iff₀ hΩ).mp (h z)
    _ = b * ((Fintype.card Z : ℚ) * Fintype.card Ω) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

/--
**The transfer: "put the other side's coins in the prefix".**

A family of side events `P z`, one per value `z` of the coordinates the side does not read, each of
density at most `b` over the side's own space `Pre × (Fin Tᵢ → C)`.  Then the event read off the
merged tape — `z := restOf ι ω.2`, the side's coins `ω.2 ∘ ι` — has density at most `b` over the
merged `Pre × (Fin T → C)`.

The proof is `sideView` (a bijection, from `Injective ι`) followed by `fiber_ratio_le`.  The family
`P` is arbitrary in `z`: that is the sense in which the other side's coins — and the key coin — are
handed to the side's adversary in advance.
-/
theorem ratio_transfer {Pre : Type} [Fintype Pre] [Nonempty Pre] [Fintype C] [Nonempty C]
    (ι : Fin Tᵢ → Fin T) (hι : Function.Injective ι)
    (P : (Rest ι → C) → Pre × (Fin Tᵢ → C) → Prop) {b : ℚ}
    (h : ∀ z, ((univ.filter fun x : Pre × (Fin Tᵢ → C) => P z x).card : ℚ)
        / (Fintype.card Pre * (Fintype.card C : ℚ) ^ Tᵢ) ≤ b) :
    ((univ.filter fun ω : Pre × (Fin T → C) => P (restOf ι ω.2) (ω.1, ω.2 ∘ ι)).card : ℚ)
        / (Fintype.card Pre * (Fintype.card C : ℚ) ^ T) ≤ b := by
  -- the count, through the bijection
  have hcard : (univ.filter fun ω : Pre × (Fin T → C) => P (restOf ι ω.2) (ω.1, ω.2 ∘ ι)).card
      = (univ.filter fun p : (Rest ι → C) × (Pre × (Fin Tᵢ → C)) => P p.1 p.2).card :=
    Finset.card_equiv (sideView ι hι) (fun ω => by simp)
  -- the denominator, through the same bijection
  have hden : (Fintype.card Pre * (Fintype.card C : ℚ) ^ T)
      = (Fintype.card (Rest ι → C) : ℚ) * Fintype.card (Pre × (Fin Tᵢ → C)) := by
    have hn := Fintype.card_congr (sideView (Pre := Pre) (C := C) ι hι)
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin] at hn
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
    exact_mod_cast hn
  have hside : ∀ z, ((univ.filter fun x : Pre × (Fin Tᵢ → C) => P z x).card : ℚ)
      / Fintype.card (Pre × (Fin Tᵢ → C)) ≤ b := by
    intro z
    simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Nat.cast_mul,
      Nat.cast_pow] using h z
  rw [hcard, hden]
  exact fiber_ratio_le P hside

/-- **The transfer along any bijection** `Ω' ≃ Z × Ω`: the counting core of `ratio_transfer`, for
callers whose merged sample space is shaped differently. -/
theorem ratio_transfer_equiv {Ω' Z Ω : Type} [Fintype Ω'] [Fintype Z] [Fintype Ω]
    [Nonempty Z] [Nonempty Ω] (e : Ω' ≃ Z × Ω) (P : Z → Ω → Prop) {b : ℚ}
    (h : ∀ z, ((univ.filter fun x => P z x).card : ℚ) / Fintype.card Ω ≤ b) :
    ((univ.filter fun ω' => P (e ω').1 (e ω').2).card : ℚ) / Fintype.card Ω' ≤ b := by
  have hcard : (univ.filter fun ω' => P (e ω').1 (e ω').2).card
      = (univ.filter fun p : Z × Ω => P p.1 p.2).card :=
    Finset.card_equiv e (fun _ => by simp)
  have hden : (Fintype.card Ω' : ℚ) = (Fintype.card Z : ℚ) * Fintype.card Ω := by
    rw [Fintype.card_congr e, Fintype.card_prod]
    push_cast
    ring
  rw [hcard, hden]
  exact fiber_ratio_le P h

/-- A side's view when the merged prefix is `Y × Pre`: `Y` (say, the other side's own hash tape)
joins the absorbed coordinate. -/
noncomputable def sideViewPrefix {Y Pre : Type} (ι : Fin Tᵢ → Fin T) (hι : Function.Injective ι) :
    (Y × Pre) × (Fin T → C) ≃ (Y × (Rest ι → C)) × (Pre × (Fin Tᵢ → C)) where
  toFun ω := ((ω.1.1, restOf ι ω.2), (ω.1.2, ω.2 ∘ ι))
  invFun p := ((p.1.1, p.2.1), (tapeSplit ι hι).symm (p.2.2, p.1.2))
  left_inv ω := by
    rcases ω with ⟨⟨y, pre⟩, t⟩
    have ht : (t ∘ ι, restOf ι t) = tapeSplit ι hι t :=
      Prod.ext (tapeSplit_fst ι hι t).symm (tapeSplit_snd ι hι t).symm
    simp only [ht, Equiv.symm_apply_apply]
  right_inv p := by
    rcases p with ⟨⟨y, z⟩, pre, x⟩
    have h := (tapeSplit ι hι).apply_symm_apply (x, z)
    have h1 : (tapeSplit ι hι).symm (x, z) ∘ ι = x := by
      rw [← tapeSplit_fst ι hι, h]
    have h2 : restOf ι ((tapeSplit ι hι).symm (x, z)) = z := by
      rw [← tapeSplit_snd ι hι, h]
    simp only [h1, h2]

/--
**The transfer with a separated prefix.**  The merged prefix is `Y × Pre` and the side reads only
`Pre`; `Y` is absorbed together with the other slots.  `ratio_transfer` is the case `Y = Unit` up to
relabelling; the composed theorems below use a shared prefix, which is the one-random-oracle case.
-/
theorem ratio_transfer_prefix {Y Pre : Type} [Fintype Y] [Nonempty Y] [Fintype Pre] [Nonempty Pre]
    [Fintype C] [Nonempty C] (ι : Fin Tᵢ → Fin T) (hι : Function.Injective ι)
    (P : Y × (Rest ι → C) → Pre × (Fin Tᵢ → C) → Prop) {b : ℚ}
    (h : ∀ z, ((univ.filter fun x : Pre × (Fin Tᵢ → C) => P z x).card : ℚ)
        / (Fintype.card Pre * (Fintype.card C : ℚ) ^ Tᵢ) ≤ b) :
    ((univ.filter fun ω : (Y × Pre) × (Fin T → C) =>
        P (ω.1.1, restOf ι ω.2) (ω.1.2, ω.2 ∘ ι)).card : ℚ)
        / (Fintype.card (Y × Pre) * (Fintype.card C : ℚ) ^ T) ≤ b := by
  have hside : ∀ z, ((univ.filter fun x : Pre × (Fin Tᵢ → C) => P z x).card : ℚ)
      / Fintype.card (Pre × (Fin Tᵢ → C)) ≤ b := by
    intro z
    simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Nat.cast_mul,
      Nat.cast_pow] using h z
  have hT := ratio_transfer_equiv (sideViewPrefix (Y := Y) (Pre := Pre) (C := C) ι hι) P hside
  simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Nat.cast_mul,
    Nat.cast_pow, sideViewPrefix, Equiv.coe_fn_mk] using hT

end Transfer

/-! ## 4. One side, on the merged tape -/

section Side

variable {Fmac : Type} [Field Fmac] {nblk : ℕ}

/--
**A side's single-field bound, at every absorbed coordinate.**

`accepts z x` is the side's verifier on its own sample space `x : Pre × (Fin L → C)`, with the
coordinates it does not read fixed to `z`; `good z x a` says `a` is a valid witness for the side's
statement there.  `sound` is the single-field theorem's *conclusion* — `accepts ∧ nothing good` has
density at most `bound` — at **every** `z`.  `Lfzk.TwoFieldLongfellow.LongfellowFamily.sideBound`
proves it for a Longfellow side; any other single-field theorem of the same shape plugs in here.
-/
structure SideBound (Z Pre C : Type) [Fintype Pre] [Fintype C] (L : ℕ) (W : Type) where
  accepts : Z → Pre × (Fin L → C) → Prop
  good : Z → Pre × (Fin L → C) → W → Prop
  bound : ℚ
  sound : ∀ z, ((univ.filter fun x : Pre × (Fin L → C) =>
      accepts z x ∧ ∀ a, ¬ good z x a).card : ℚ)
    / (Fintype.card Pre * (Fintype.card C : ℚ) ^ L) ≤ bound

variable {Pre C : Type} [Fintype Pre] [Fintype C] {Tᵢ T : ℕ} {W : Type}

/-- A side's acceptance, read off the merged sample space. -/
abbrev SideBound.mergedAccepts {ι : Fin Tᵢ → Fin T} (S : SideBound (Rest ι → C) Pre C Tᵢ W) :
    Pre × (Fin T → C) → Prop :=
  fun ω => S.accepts (restOf ι ω.2) (ω.1, ω.2 ∘ ι)

/-- A side's goodness relation, read off the merged sample space. -/
abbrev SideBound.mergedGood {ι : Fin Tᵢ → Fin T} (S : SideBound (Rest ι → C) Pre C Tᵢ W) :
    Pre × (Fin T → C) → W → Prop :=
  fun ω a => S.good (restOf ι ω.2) (ω.1, ω.2 ∘ ι) a

/--
**The side, as a `MacBound` on the merged tape.**  `MacBound.ofGood` at the merged acceptance and
goodness; `hrow` is the side's MAC row, stated on the merged sample space where the key and tag live.
-/
noncomputable def SideBound.toMacBound {ι : Fin Tᵢ → Fin T}
    (S : SideBound (Rest ι → C) Pre C Tᵢ W)
    {keyA : Pre × (Fin T → C) → Fmac} {keyB tag : Pre × (Fin T → C) → Fin nblk → Fmac}
    (common : W → Fin nblk → Fmac)
    (hrow : ∀ (ω : Pre × (Fin T → C)) (a : W), S.mergedAccepts ω → S.mergedGood ω a →
      macTag (keyA ω) (keyB ω) (common a) = tag ω) :
    MacBound Fmac nblk (Pre × (Fin T → C)) keyA keyB tag W :=
  MacBound.ofGood S.mergedAccepts S.mergedGood common hrow

/--
**The transferred bound — `TwoFieldNizk`'s `hᵢ`, as a theorem.**

The side's knowledge-error event on the merged tape has density at most the side's single-field
bound.  `MacBound.ofGood_fail_card` turns the event into "accepts, but nothing good"; `ratio_transfer`
moves it from the side's space to the merged one.
-/
theorem SideBound.merged_ratio_le [Nonempty Pre] [Nonempty C]
    {ι : Fin Tᵢ → Fin T} (hι : Function.Injective ι)
    (S : SideBound (Rest ι → C) Pre C Tᵢ W)
    {keyA : Pre × (Fin T → C) → Fmac} {keyB tag : Pre × (Fin T → C) → Fin nblk → Fmac}
    (common : W → Fin nblk → Fmac)
    (hrow : ∀ (ω : Pre × (Fin T → C)) (a : W), S.mergedAccepts ω → S.mergedGood ω a →
      macTag (keyA ω) (keyB ω) (common a) = tag ω) :
    ((univ.filter fun ω : Pre × (Fin T → C) =>
        (S.toMacBound common hrow).accepts ω ∧ (S.toMacBound common hrow).E ω = none).card : ℚ)
        / (Fintype.card Pre * (Fintype.card C : ℚ) ^ T) ≤ S.bound := by
  have hcard := MacBound.ofGood_fail_card S.mergedAccepts S.mergedGood common hrow
  unfold SideBound.toMacBound
  rw [hcard]
  -- `S.sound`'s filter carries the structure's `DecidablePred`, which need not be the one
  -- elaborated here; `convert` closes the instance gap and nothing else
  have h := ratio_transfer ι hι (fun z x => S.accepts z x ∧ ∀ a, ¬ S.good z x a)
    (fun z => by convert S.sound z)
  -- the two filters differ only by unfolding `mergedAccepts`/`mergedGood` and by instance
  convert h

end Side

/-! ## 5. The composed theorem -/

section Compose

variable {Pre C Fmac : Type} [Fintype Pre] [Fintype C] [DecidableEq C]
-- no `[DecidableEq Fmac]`: see the comment at `Lfzk.TwoFieldNizk`'s variable block
variable [Field Fmac]
variable {nblk T₁ T₂ T : ℕ} {W₁ W₂ : Type}

/--
**The two-field bound on one merged tape, with both side bounds proved.**

Two sides, each given by its single-field bound at every absorbed coordinate (`S₁`, `S₂`) and its
MAC row (`hrow₁`, `hrow₂`); one MAC key slot `sch.s`, read through `decode` with balance `kmac`, keyed
by the prover share `aP`, which is a function of the prefix (causality (C3)).  Then

```
Pr over (pre, tape) [ both verifiers accept  ∧  the composed extractor fails ]
      ≤  S₁.bound  +  S₂.bound  +  kmac / |C|
```

`TwoFieldNizk.twofield_nizk_ratio_le` with its `h₁`, `h₂` discharged by `SideBound.merged_ratio_le`.
There is no ratio hypothesis over the shared tape left.
-/
theorem twofield_merged_ratio_le [Nonempty Pre] [Nonempty C]
    (sch : Schedule T₁ T₂ T) (decode : C → Fmac) (aP : Pre → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    {keyB tag : Pre × (Fin T → C) → Fin nblk → Fmac}
    (S₁ : SideBound (Rest sch.ι₁ → C) Pre C T₁ W₁) (common₁ : W₁ → Fin nblk → Fmac)
    (hrow₁ : ∀ (ω : Pre × (Fin T → C)) (a : W₁), S₁.mergedAccepts ω → S₁.mergedGood ω a →
      macTag (aP ω.1 + decode (ω.2 sch.s)) (keyB ω) (common₁ a) = tag ω)
    (S₂ : SideBound (Rest sch.ι₂ → C) Pre C T₂ W₂) (common₂ : W₂ → Fin nblk → Fmac)
    (hrow₂ : ∀ (ω : Pre × (Fin T → C)) (a : W₂), S₂.mergedAccepts ω → S₂.mergedGood ω a →
      macTag (aP ω.1 + decode (ω.2 sch.s)) (keyB ω) (common₂ a) = tag ω)
    (hT : 1 ≤ T) :
    ((univ.filter fun ω : Pre × (Fin T → C) =>
        (S₁.toMacBound common₁ hrow₁).accepts ω ∧ (S₂.toMacBound common₂ hrow₂).accepts ω ∧
          composedE (S₁.toMacBound common₁ hrow₁) (S₂.toMacBound common₂ hrow₂) ω = none).card
          : ℚ)
        / (Fintype.card Pre * (Fintype.card C : ℚ) ^ T)
      ≤ S₁.bound + S₂.bound + (kmac : ℚ) / (Fintype.card C : ℚ) :=
  twofield_nizk_ratio_le sch.s decode aP kmac hbal
    (S₁.toMacBound common₁ hrow₁) (S₂.toMacBound common₂ hrow₂)
    (S₁.merged_ratio_le sch.inj₁ common₁ hrow₁) (S₂.merged_ratio_le sch.inj₂ common₂ hrow₂) hT

/-- **At a security target.** -/
theorem twofield_merged_ratio_le_target [Nonempty Pre] [Nonempty C] (lam : ℕ)
    (sch : Schedule T₁ T₂ T) (decode : C → Fmac) (aP : Pre → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    {keyB tag : Pre × (Fin T → C) → Fin nblk → Fmac}
    (S₁ : SideBound (Rest sch.ι₁ → C) Pre C T₁ W₁) (common₁ : W₁ → Fin nblk → Fmac)
    (hrow₁ : ∀ (ω : Pre × (Fin T → C)) (a : W₁), S₁.mergedAccepts ω → S₁.mergedGood ω a →
      macTag (aP ω.1 + decode (ω.2 sch.s)) (keyB ω) (common₁ a) = tag ω)
    (S₂ : SideBound (Rest sch.ι₂ → C) Pre C T₂ W₂) (common₂ : W₂ → Fin nblk → Fmac)
    (hrow₂ : ∀ (ω : Pre × (Fin T → C)) (a : W₂), S₂.mergedAccepts ω → S₂.mergedGood ω a →
      macTag (aP ω.1 + decode (ω.2 sch.s)) (keyB ω) (common₂ a) = tag ω)
    (hT : 1 ≤ T)
    (htarget : S₁.bound + S₂.bound + (kmac : ℚ) / (Fintype.card C : ℚ) ≤ (1 : ℚ) / 2 ^ lam) :
    ((univ.filter fun ω : Pre × (Fin T → C) =>
        (S₁.toMacBound common₁ hrow₁).accepts ω ∧ (S₂.toMacBound common₂ hrow₂).accepts ω ∧
          composedE (S₁.toMacBound common₁ hrow₁) (S₂.toMacBound common₂ hrow₂) ω = none).card
          : ℚ)
        / (Fintype.card Pre * (Fintype.card C : ℚ) ^ T)
      ≤ (1 : ℚ) / 2 ^ lam :=
  le_trans (twofield_merged_ratio_le sch decode aP kmac hbal S₁ common₁ hrow₁ S₂ common₂ hrow₂ hT)
    htarget

end Compose

end Lfzk.TwoFieldBridge
