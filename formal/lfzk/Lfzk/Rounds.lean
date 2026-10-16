import Mathlib
import Sumcheck.Grinding

/-!
# Longfellow's round schedule

Which tape slot carries which challenge.  `Bcs.RoundByRound` counts over a tape of oracle answers
indexed by `Fin L` in protocol order; this file says what Longfellow's `L` is and what each slot is
for, so that Phase 5's state function can be written as a function of a prefix.

## The schedule

At `logc = 0` — the ZK path asserts it (`zk_common.h:L72`), which is why the derived degree `d = 2`
is stated there — a layer runs `nrnd = 2 * logw` sumcheck rounds, and the run is

```
  P: the Merkle root of the Ligero oracle (witness ‖ pad)      -- not a challenge slot
  for ly = 0 … nl-1:
     V: (beta_ly, alpha_ly)                                    -- begin_layer, one slot
     for j = 0 … nrnd-1:
        P: (tr0, tr2)                                          -- RoundData
        V: r_{ly,j}                                            -- one slot
     P: (wc0, wc1)
  V: alpha_in                                                  -- elt_field, one slot
  V: the Ligero linear-combination challenge                    -- one slot
  P: the Ligero response
  V: the query set                                             -- one slot
  P: the openings ‖ Merkle paths
```

so `L = nl * (1 + nrnd) + 3`.  `(beta, alpha)` is **one** slot, not two: `begin_layer` draws them
back to back before any of the layer's messages (`transcript.rs:L106`,
`transcript_sumcheck.h:L54`), so they are decoded from one oracle answer.

## Why a `Role` type and not just arithmetic

`slot` is injective and hits every element of `Fin L` exactly once (`slotEquiv`), which is the
statement that the schedule accounts for the whole tape — no slot unused, none double-booked.  That
is worth having as a theorem rather than a comment: an off-by-one in the layer stride would make
two rounds share a slot, and a shared slot is exactly what breaks the counting, since the two rounds'
bad sets would then be over the same answer.

`PadLayout.blindSlot_inj` (`ZkHiding.lean`) is the same discipline for the pad's blinding slots, and
for the same reason.

## What is deliberately not here

The challenge *types*.  A slot carries an oracle answer in some type `C` and each round decodes it —
`Bcs.card_preimage_le_of_balanced` is what charges for the decoding — so the schedule does not need
to know that a layer pair lands in `F × F` and a query set in an `r`-subset of `n` columns.  Keeping
those out means this file imports no Ligero, which is what lets Phase 5 pick the decoders.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.Rounds

/-! ## Roles -/

/--
**What a tape slot is for.**  `nl` layers, layer `ly` carrying `w ly` sumcheck rounds, plus the three
challenges drawn after LayerStep closes.

`w` is a **width profile**, not a single padded width.  The number of sumcheck rounds a layer needs is
set by that layer's width, and taking the profile rather than its maximum is what makes the bound
`(∑ ly, w ly) · bround` instead of `nl · (max ly, w ly) · bround`.  For an uneven circuit that is the
dominant saving; `uniform` recovers the padded case.
-/
inductive Role (nl : ℕ) (w : ℕ → ℕ) where
  /-- `begin_layer`'s pair `(beta_ly, alpha_ly)` — one slot, decoded into two field elements. -/
  | layerPair (ly : Fin nl)
  /-- Sumcheck round `j` of layer `ly`, of which there are `w ly`. -/
  | sumcheck (ly : Fin nl) (j : Fin (w ly.val))
  /-- `elt_field`'s `alpha_in`, combining the input-layer claims. -/
  | inputBind
  /-- Ligero's linear-combination challenge. -/
  | ligeroChallenge
  /-- Ligero's query set: which `r` of the `n` columns are opened. -/
  | ligeroQuery
  deriving DecidableEq

namespace Role

variable {nl : ℕ} {w : ℕ → ℕ}

/-- The padded profile: every layer takes the same number of rounds. -/
abbrev uniform (nrnd : ℕ) : ℕ → ℕ := fun _ => nrnd

/-- The first slot of layer `ly`: a prefix sum over the profile.  At a uniform profile this is
`ly * (1 + nrnd)`, which is `layerBase_uniform`. -/
abbrev layerBase (w : ℕ → ℕ) (ly : ℕ) : ℕ := ∑ i ∈ Finset.range ly, (1 + w i)

/-- The tape length: one slot per layer pair, `w ly` per layer, and three at the end. -/
abbrev length (nl : ℕ) (w : ℕ → ℕ) : ℕ := layerBase w nl + 3

theorem layerBase_succ (ly : ℕ) :
    layerBase w (ly + 1) = layerBase w ly + (1 + w ly) :=
  Finset.sum_range_succ _ _

theorem layerBase_mono {ly ly' : ℕ} (h : ly ≤ ly') :
    layerBase w ly ≤ layerBase w ly' := by
  apply Finset.sum_le_sum_of_subset
  intro x hx
  simp only [Finset.mem_range] at hx ⊢
  omega

theorem layerBase_uniform (nrnd ly : ℕ) :
    layerBase (uniform nrnd) ly = ly * (1 + nrnd) := by
  induction ly with
  | zero => simp
  | succ n ih => rw [layerBase_succ, ih]; ring

theorem length_uniform (nl nrnd : ℕ) :
    length nl (uniform nrnd) = nl * (1 + nrnd) + 3 := by
  rw [length, layerBase_uniform]

/-- Which slot a role occupies. -/
def slot : Role nl w → ℕ
  | .layerPair ly => layerBase w ly.val
  | .sumcheck ly j => layerBase w ly.val + 1 + j.val
  | .inputBind => layerBase w nl
  | .ligeroChallenge => layerBase w nl + 1
  | .ligeroQuery => layerBase w nl + 2

/-! ### The schedule fits, and it fits exactly -/

/-- **Layers occupy disjoint blocks.**  Every role of layer `ly` sits in `[layerBase ly,
layerBase (ly+1))`.  With `layerBase_mono` this replaces the uniform version's base-`n` block
decomposition: separation between layers is monotonicity of a prefix sum, not divisibility. -/
theorem layer_block (ly : Fin nl) {k : ℕ} (hk : k < 1 + w ly.val) :
    layerBase w ly.val + k < layerBase w (ly.val + 1) := by
  rw [layerBase_succ]
  omega

/-- **Layer roles come first**: all of them are below `layerBase w nl`, where the tail begins. -/
theorem layer_slot_lt (ly : Fin nl) {k : ℕ} (hk : k < 1 + w ly.val) :
    layerBase w ly.val + k < layerBase w nl :=
  lt_of_lt_of_le (layer_block ly hk) (layerBase_mono ly.isLt)

theorem slot_lt (rl : Role nl w) : rl.slot < length nl w := by
  cases rl with
  | layerPair ly =>
      have h := layer_slot_lt (w := w) ly (k := 0) (by omega)
      simp only [slot, length]; omega
  | sumcheck ly j =>
      have h := layer_slot_lt (w := w) ly (k := 1 + j.val) (by omega)
      simp only [slot, length] at h ⊢; omega
  | inputBind => exact Nat.lt_add_of_pos_right (by omega)
  | ligeroChallenge => exact Nat.add_lt_add_left (show 1 < 3 by omega) _
  | ligeroQuery => exact Nat.add_lt_add_left (show 2 < 3 by omega) _

/-- The layer a role belongs to, together with its offset inside that layer's block.  Stated as the
two bounds `slot_inj` needs, so that the case analysis below is about blocks rather than arithmetic. -/
private theorem layer_bounds (ly : Fin nl) {k : ℕ} (hk : k < 1 + w ly.val) :
    layerBase w ly.val ≤ layerBase w ly.val + k ∧
      layerBase w ly.val + k < layerBase w (ly.val + 1) :=
  ⟨Nat.le_add_right _ _, layer_block ly hk⟩

/-- Two roles in *different* layers cannot share a slot: the earlier layer's block ends before the
later layer's begins. -/
private theorem block_ne {lya lyb : Fin nl} {ka kb : ℕ}
    (hka : ka < 1 + w lya.val) (hkb : kb < 1 + w lyb.val) (hne : lya.val ≠ lyb.val) :
    layerBase w lya.val + ka ≠ layerBase w lyb.val + kb := by
  rcases Nat.lt_or_ge lya.val lyb.val with h | h
  · -- the earlier block ends strictly before the later one starts; pure order, no arithmetic
    exact Nat.ne_of_lt (lt_of_lt_of_le (layer_bounds lya hka).2
      (le_trans (layerBase_mono (w := w) (Nat.succ_le_of_lt h)) (Nat.le_add_right _ _)))
  · have hlt : lyb.val < lya.val := lt_of_le_of_ne h (Ne.symm hne)
    exact Ne.symm (Nat.ne_of_lt (lt_of_lt_of_le (layer_bounds lyb hkb).2
      (le_trans (layerBase_mono (w := w) (Nat.succ_le_of_lt hlt)) (Nat.le_add_right _ _))))

/-- Slots of layer roles, in the `layerBase + offset` form `block_ne` consumes. -/
private theorem slot_layerPair (ly : Fin nl) :
    (layerPair ly : Role nl w).slot = layerBase w ly.val + 0 := by
  simp [slot]

private theorem slot_sumcheck (ly : Fin nl) (j : Fin (w ly.val)) :
    (sumcheck ly j : Role nl w).slot = layerBase w ly.val + (1 + j.val) := by
  simp [slot, Nat.add_assoc]

/-- **The schedule is injective**: no two rounds share a slot.  A shared slot would put two rounds'
bad sets over the *same* oracle answer, which is exactly what a per-slot count may not have — so
this is a soundness-relevant fact and not bookkeeping.

Layers are separated by `block_ne` — monotonicity of the prefix sum — layer roles from the tail by
`layer_slot_lt`, and the tail roles from each other by their offsets. -/
theorem slot_inj : Function.Injective (slot : Role nl w → ℕ) := by
  intro a b hab
  cases a with
  | layerPair lya =>
      have hla := layer_slot_lt (w := w) lya (k := 0) (by omega)
      cases b with
      | layerPair lyb =>
          by_cases hly : lya.val = lyb.val
          · simp [Fin.ext hly]
          · exact absurd (by rw [slot_layerPair, slot_layerPair] at hab; exact hab)
              (block_ne (w := w) (ka := 0) (kb := 0) (by omega) (by omega) hly)
      | sumcheck lyb jb =>
          exfalso
          by_cases hly : lya.val = lyb.val
          · have hfin : lya = lyb := Fin.ext hly
            subst hfin
            rw [slot_layerPair, slot_sumcheck] at hab
            omega
          · exact block_ne (w := w) (ka := 0) (kb := 1 + jb.val) (by omega) (by omega) hly
              (by rw [slot_layerPair, slot_sumcheck] at hab; exact hab)
      | inputBind => exact absurd hab (by simp only [slot] at hla ⊢; omega)
      | ligeroChallenge => exact absurd hab (by simp only [slot] at hla ⊢; omega)
      | ligeroQuery => exact absurd hab (by simp only [slot] at hla ⊢; omega)
  | sumcheck lya ja =>
      have hla := layer_slot_lt (w := w) lya (k := 1 + ja.val) (by omega)
      cases b with
      | layerPair lyb =>
          exfalso
          by_cases hly : lya.val = lyb.val
          · have hfin : lya = lyb := Fin.ext hly
            subst hfin
            rw [slot_sumcheck, slot_layerPair] at hab
            omega
          · exact block_ne (w := w) (ka := 1 + ja.val) (kb := 0) (by omega) (by omega) hly
              (by rw [slot_sumcheck, slot_layerPair] at hab; exact hab)
      | sumcheck lyb jb =>
          by_cases hly : lya.val = lyb.val
          · have hfin : lya = lyb := Fin.ext hly
            subst hfin
            rw [slot_sumcheck, slot_sumcheck] at hab
            have hj : ja.val = jb.val := by omega
            simp [Fin.ext hj]
          · exact absurd (by rw [slot_sumcheck, slot_sumcheck] at hab; exact hab)
              (block_ne (w := w) (ka := 1 + ja.val) (kb := 1 + jb.val)
                (by omega) (by omega) hly)
      | inputBind => exact absurd hab (by simp only [slot] at hla ⊢; omega)
      | ligeroChallenge => exact absurd hab (by simp only [slot] at hla ⊢; omega)
      | ligeroQuery => exact absurd hab (by simp only [slot] at hla ⊢; omega)
  | inputBind =>
      cases b with
      | layerPair lyb =>
          have hlb := layer_slot_lt (w := w) lyb (k := 0) (by omega)
          exact absurd hab (by simp only [slot] at hlb ⊢; omega)
      | sumcheck lyb jb =>
          have hlb := layer_slot_lt (w := w) lyb (k := 1 + jb.val) (by omega)
          exact absurd hab (by simp only [slot] at hlb ⊢; omega)
      | inputBind => rfl
      | ligeroChallenge => exact absurd hab (by simp only [slot]; omega)
      | ligeroQuery => exact absurd hab (by simp only [slot]; omega)
  | ligeroChallenge =>
      cases b with
      | layerPair lyb =>
          have hlb := layer_slot_lt (w := w) lyb (k := 0) (by omega)
          exact absurd hab (by simp only [slot] at hlb ⊢; omega)
      | sumcheck lyb jb =>
          have hlb := layer_slot_lt (w := w) lyb (k := 1 + jb.val) (by omega)
          exact absurd hab (by simp only [slot] at hlb ⊢; omega)
      | inputBind => exact absurd hab (by simp only [slot]; omega)
      | ligeroChallenge => rfl
      | ligeroQuery => exact absurd hab (by simp only [slot]; omega)
  | ligeroQuery =>
      cases b with
      | layerPair lyb =>
          have hlb := layer_slot_lt (w := w) lyb (k := 0) (by omega)
          exact absurd hab (by simp only [slot] at hlb ⊢; omega)
      | sumcheck lyb jb =>
          have hlb := layer_slot_lt (w := w) lyb (k := 1 + jb.val) (by omega)
          exact absurd hab (by simp only [slot] at hlb ⊢; omega)
      | inputBind => exact absurd hab (by simp only [slot]; omega)
      | ligeroChallenge => exact absurd hab (by simp only [slot]; omega)
      | ligeroQuery => rfl

/-! ### Protocol order

The facts Phase 5's state function turns on.  It must be written as a function of a tape *prefix*,
so for every round it needs to know which other rounds are strictly earlier — that is the whole
content of this section, and it is what makes "LayerStep so far" a legitimate argument of
`doomed`.
-/

/-- A layer's pair is drawn before that layer's sumcheck rounds. -/
theorem layerPair_lt_sumcheck (ly : Fin nl) (j : Fin (w ly.val)) :
    (layerPair ly : Role nl w).slot < (sumcheck ly j : Role nl w).slot := by
  simp only [slot]; omega

/-- Within a layer, the sumcheck rounds are in order. -/
theorem sumcheck_lt_sumcheck (ly : Fin nl) {j j' : Fin (w ly.val)} (h : j.val < j'.val) :
    (sumcheck ly j : Role nl w).slot < (sumcheck ly j' : Role nl w).slot := by
  simp only [slot]; omega

/-- A layer finishes before the next one starts.  With a profile this is monotonicity of the prefix
sum rather than a multiple of a fixed stride. -/
theorem sumcheck_lt_layerPair {ly ly' : Fin nl} (j : Fin (w ly.val)) (h : ly.val < ly'.val) :
    (sumcheck ly j : Role nl w).slot < (layerPair ly' : Role nl w).slot := by
  rw [slot_sumcheck, slot_layerPair]
  exact lt_of_lt_of_le (layer_block (w := w) ly (k := 1 + j.val) (by omega))
    (le_trans (layerBase_mono (w := w) (Nat.succ_le_of_lt h)) (Nat.le_add_right _ _))

/-- Every layer round precedes the input binding. -/
theorem sumcheck_lt_inputBind (ly : Fin nl) (j : Fin (w ly.val)) :
    (sumcheck ly j : Role nl w).slot < (inputBind : Role nl w).slot := by
  have h := layer_slot_lt (w := w) ly (k := 1 + j.val) (by omega)
  rw [slot_sumcheck]
  simpa only [slot] using h

/-- Every layer pair precedes the input binding. -/
theorem layerPair_lt_inputBind (ly : Fin nl) :
    (layerPair ly : Role nl w).slot < (inputBind : Role nl w).slot := by
  have h := layer_slot_lt (w := w) ly (k := 0) (by omega)
  rw [slot_layerPair]
  simpa only [slot] using h

/-- The three tail challenges are drawn in the order `alpha_in`, Ligero challenge, query set. -/
theorem inputBind_lt_ligeroChallenge :
    (inputBind : Role nl w).slot < (ligeroChallenge : Role nl w).slot := by
  simp only [slot]; omega

theorem ligeroChallenge_lt_ligeroQuery :
    (ligeroChallenge : Role nl w).slot < (ligeroQuery : Role nl w).slot := by
  simp only [slot]; omega

/-! ### The schedule uses every slot exactly once -/

/-- The roles, enumerated: `nl` layer pairs, `w ly` sumcheck rounds at layer `ly`, three tail
challenges.  The sumcheck part is a *sigma* rather than a product, which is the whole difference
between a profile and a padded width. -/
def roleEquiv :
    Role nl w ≃ (Fin nl ⊕ (ly : Fin nl) × Fin (w ly.val)) ⊕ (Unit ⊕ Unit ⊕ Unit) where
  toFun
    | .layerPair ly => .inl (.inl ly)
    | .sumcheck ly j => .inl (.inr ⟨ly, j⟩)
    | .inputBind => .inr (.inl ())
    | .ligeroChallenge => .inr (.inr (.inl ()))
    | .ligeroQuery => .inr (.inr (.inr ()))
  invFun
    | .inl (.inl ly) => .layerPair ly
    | .inl (.inr ⟨ly, j⟩) => .sumcheck ly j
    | .inr (.inl ()) => .inputBind
    | .inr (.inr (.inl ())) => .ligeroChallenge
    | .inr (.inr (.inr ())) => .ligeroQuery
  left_inv rl := by cases rl <;> rfl
  right_inv x := by
    rcases x with (ly | ⟨ly, j⟩) | (u | (u | u)) <;> rfl

instance : Fintype (Role nl w) := Fintype.ofEquiv _ roleEquiv.symm

/-- The profile's total round count, in the two forms the proofs need. -/
theorem sum_w_range : ∑ ly : Fin nl, w ly.val = ∑ i ∈ Finset.range nl, w i := by
  simpa using (Finset.sum_range (n := nl) (f := w)).symm

/-- **The schedule accounts for the whole tape.**  There are exactly `L` roles, so with `index_inj`
the schedule is a bijection onto `Fin L`: every slot is used, and none is shared. -/
theorem card_role : Fintype.card (Role nl w) = length nl w := by
  rw [Fintype.card_congr roleEquiv]
  simp only [Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin, Fintype.card_unit,
    length, layerBase, sum_w_range]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
  ring

/-- The slot as an element of the tape's index type. -/
def index (rl : Role nl w) : Fin (length nl w) := ⟨rl.slot, rl.slot_lt⟩

theorem index_inj : Function.Injective (index : Role nl w → Fin (length nl w)) :=
  fun _ _ h => slot_inj (Fin.val_eq_of_eq h)

/-- **`index` is a bijection.** -/
theorem index_bijective : Function.Bijective (index : Role nl w → Fin (length nl w)) := by
  refine (Fintype.bijective_iff_injective_and_card index).mpr ⟨index_inj, ?_⟩
  simpa using card_role (nl := nl) (w := w)

/-- The schedule, as an equivalence between roles and tape slots. -/
noncomputable def indexEquiv : Role nl w ≃ Fin (length nl w) :=
  Equiv.ofBijective index index_bijective

/-! ### Collecting a budget over the schedule -/

section Budget

variable {M : Type} [AddCommMonoid M]

/-- A budget indexed by slots sums to the same thing as one indexed by roles. -/
theorem sum_slot_eq_sum_role (b : Role nl w → M) :
    ∑ i : Fin (length nl w), b (indexEquiv.symm i) = ∑ rl : Role nl w, b rl :=
  Equiv.sum_comp indexEquiv.symm b

/-- **The budget, collected by role class.**  One term per constructor of `Role`; the sumcheck term
is a sum over the profile. -/
theorem sum_role (b : Role nl w → M) :
    ∑ rl : Role nl w, b rl
      = (∑ ly : Fin nl, b (layerPair ly))
        + (∑ ly : Fin nl, ∑ j : Fin (w ly.val), b (sumcheck ly j))
        + b inputBind + b ligeroChallenge + b ligeroQuery := by
  have h : ∑ rl : Role nl w, b rl
      = ∑ x : (Fin nl ⊕ (ly : Fin nl) × Fin (w ly.val)) ⊕ (Unit ⊕ Unit ⊕ Unit),
          b (roleEquiv.symm x) :=
    Fintype.sum_equiv roleEquiv b (fun x => b (roleEquiv.symm x)) (fun rl => by simp)
  rw [h]
  simp only [Fintype.sum_sum_type, Fintype.sum_unique, roleEquiv, Equiv.coe_fn_symm_mk]
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  abel

end Budget

/--
**The closed form at constant budgets.**  `nl` layer pairs, `∑ ly, w ly` sumcheck rounds, and the
three tail challenges.

This is the whole point of the profile: the sumcheck term is `(∑ ly, w ly) · bround`, not
`nl · (max ly, w ly) · bround`.  At `w = uniform nrnd` the two agree (`sum_role_const_uniform`).
-/
theorem sum_role_const (b : Role nl w → ℕ) (bpair bround bin blig bquery : ℕ)
    (hpair : ∀ ly, b (layerPair ly) = bpair)
    (hround : ∀ ly j, b (sumcheck ly j) = bround)
    (hin : b inputBind = bin) (hlig : b ligeroChallenge = blig)
    (hquery : b ligeroQuery = bquery) :
    ∑ rl : Role nl w, b rl
      = nl * bpair + (∑ i ∈ Finset.range nl, w i) * bround + bin + blig + bquery := by
  rw [sum_role b]
  have h1 : (∑ ly : Fin nl, b (layerPair ly)) = nl * bpair := by
    simp [hpair, Finset.sum_const, Finset.card_univ]
  have h2 : (∑ ly : Fin nl, ∑ j : Fin (w ly.val), b (sumcheck ly j))
      = (∑ i ∈ Finset.range nl, w i) * bround := by
    rw [← sum_w_range, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ly _ => ?_
    simp [hround, Finset.sum_const, Finset.card_univ, mul_comm]
  rw [h1, h2, hin, hlig, hquery]

/-- The same exact role count for rational budgets.  The two terminal
potential charges need not be integer-valued. -/
theorem sum_role_const_rat (b : Role nl w → ℚ)
    (bpair bround bin blig bquery : ℚ)
    (hpair : ∀ ly, b (layerPair ly) = bpair)
    (hround : ∀ ly j, b (sumcheck ly j) = bround)
    (hin : b inputBind = bin) (hlig : b ligeroChallenge = blig)
    (hquery : b ligeroQuery = bquery) :
    ∑ rl : Role nl w, b rl =
      (nl : ℚ) * bpair +
        (∑ ly : Fin nl, (w ly.val : ℚ)) * bround +
        bin + blig + bquery := by
  rw [sum_role b]
  simp_rw [hpair, hround]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, hin, hlig, hquery]
  rw [← Finset.sum_mul]

/-- At the padded profile the closed form is the old one, `nl * nrnd * bround`. -/
theorem sum_role_const_uniform {nrnd : ℕ} (b : Role nl (uniform nrnd) → ℕ)
    (bpair bround bin blig bquery : ℕ)
    (hpair : ∀ ly, b (layerPair ly) = bpair)
    (hround : ∀ ly j, b (sumcheck ly j) = bround)
    (hin : b inputBind = bin) (hlig : b ligeroChallenge = blig)
    (hquery : b ligeroQuery = bquery) :
    ∑ rl : Role nl (uniform nrnd), b rl
      = nl * bpair + nl * nrnd * bround + bin + blig + bquery := by
  rw [sum_role_const b bpair bround bin blig bquery hpair hround hin hlig hquery]
  simp [uniform, Finset.sum_const, Finset.card_range, mul_comm]

/-! ### Reading the tape -/

section Read

variable {C : Type}

/-- The oracle answer a round consumes. -/
def readAt (tape : Fin (length nl w) → C) (rl : Role nl w) : C := tape rl.index

/-- **Earlier rounds are visible in the prefix.** -/
theorem readAt_eq_prefix (tape : Fin (length nl w) → C) (rl rl' : Role nl w)
    (h : rl.slot < rl'.slot) :
    readAt tape rl = Sumcheck.extract_prefix tape rl'.index ⟨rl.slot, h⟩ := rfl

end Read


end Role

end Lfzk.Rounds
