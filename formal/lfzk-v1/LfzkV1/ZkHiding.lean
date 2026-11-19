import LfzkV1.Builder

open SumcheckV1

open BigOperators
open Classical Polynomial Finset

set_option autoImplicit true
set_option relaxedAutoImplicit true

/-!
# Perfect hiding of the blinded transcript

The soundness development uses the pad only as *data*: `RoundData` carries two pad indices
`pp0`, `pp2` and nothing constrains them.  That is enough for soundness — a colliding pad
only ever helps the verifier — but it is not enough for zero-knowledge.  If `pp0 = pp2` then
`tr[0] - tr[2]` is unblinded and leaks `p(0) - p(2)`.

This file supplies what ZK needs:

* `PadLayout`, transliterated from `zk_common.h:L193-L247`;
* `blindIdx_injective` — the slots a layer actually blinds with are *contiguous*, hence
  pairwise distinct, and `layer_blind_disjoint` — consecutive layers blind with disjoint
  slots, even though their `ConstraintBuilder` windows overlap by the claim-pad triple;
* `blindSlot_inj` and `quadSlot_ne_blindSlot` — the same two facts for a *whole run*: a pad
  index belongs to at most one layer's blinder, and no layer's quadratic slot is any layer's
  blinder.  Together they are what lets a run's pad be computed from its blinder vector
  (`stdRunPad`) rather than supplied as data;
* `blindEquiv` — the one-time pad as an explicit bijection, and `blind_witness_indep`: for
  *any* two witnesses and any transmission there is exactly one blinder assignment producing
  it in each case.

That last statement is perfect hiding of the transmitted round polynomials, with no
probability and no distinguisher.  The Merkle commitment inside Ligero is only
*statistically* hiding, so the protocol's ZK is statistical overall; this file is the part
that is perfect.
-/

namespace PadLayout

/-- `poly_pad(r, point)` (`zk_common.h:L223`): the pair `[dP(0), dP(2)]` of round `r`. -/
def polyPad (r point : ℕ) : ℕ := if point = 0 then 2 * r else 2 * r + 1

/-- `claim_pad(n)` (`zk_common.h:L233`): the triple `[dWC[0], dWC[1], dWC[0]*dWC[1]]`. -/
def claimPad (logw n : ℕ) : ℕ := polyPad (2 * logw) 0 + n

/-- `layer_size()` — the stride between consecutive layers' pad windows. -/
def layerSize (logw : ℕ) : ℕ := claimPad logw 3

/-- `ovp_claim_pad_m1(n)`: the *previous* layer's claim pad, which `ConstraintBuilder::first`
reads. -/
def ovpClaimPadM1 (n : ℕ) : ℕ := n

/-- `ovp_poly_pad(r, point)` (`zk_common.h:L243`). -/
def ovpPolyPad (r point : ℕ) : ℕ := 3 + polyPad r point

/-- `ovp_claim_pad(n)` (`zk_common.h:L246`). -/
def ovpClaimPad (logw n : ℕ) : ℕ := 3 + claimPad logw n

/-- `ovp_layer_size()` — the length of one layer's window.  Note this exceeds `layerSize`
by `3`: adjacent windows overlap by exactly the claim-pad triple. -/
def ovpLayerSize (logw : ℕ) : ℕ := ovpClaimPad logw 3

@[simp] lemma polyPad_zero (r : ℕ) : polyPad r 0 = 2 * r := by simp [polyPad]
@[simp] lemma polyPad_two (r : ℕ) : polyPad r 2 = 2 * r + 1 := by simp [polyPad]
@[simp] lemma claimPad_eq (logw n : ℕ) : claimPad logw n = 4 * logw + n := by
  simp [claimPad, polyPad]; ring
@[simp] lemma layerSize_eq (logw : ℕ) : layerSize logw = 4 * logw + 3 := by simp [layerSize]
@[simp] lemma ovpLayerSize_eq (logw : ℕ) : ovpLayerSize logw = 4 * logw + 6 := by
  simp [ovpLayerSize, ovpClaimPad]; ring

/--
**The slots a layer blinds with, in order.**

A layer transmits `4 * logw` values (`tr[0]`, `tr[2]` for each of the `2 * logw` rounds) and
then the two masked hand evaluations `wc[0]`, `wc[1]`.  Their blinders are
`ovp_poly_pad(r, ·)` and `ovp_claim_pad(0)`, `ovp_claim_pad(1)` — which is exactly the
contiguous block `3, 4, …, 4*logw + 4`.
-/
def blindIdx (k : ℕ) : ℕ := 3 + k

@[simp] lemma blindIdx_polyPad (r : ℕ) :
    ovpPolyPad r 0 = blindIdx (2 * r) ∧ ovpPolyPad r 2 = blindIdx (2 * r + 1) := by
  constructor <;> simp [ovpPolyPad, blindIdx, polyPad]

@[simp] lemma blindIdx_claimPad (logw : ℕ) :
    ovpClaimPad logw 0 = blindIdx (4 * logw) ∧ ovpClaimPad logw 1 = blindIdx (4 * logw + 1) := by
  constructor <;> simp [ovpClaimPad, blindIdx, claimPad, polyPad] <;> ring

/-- **The blinding slots of one layer are pairwise distinct.**  Without this the one-time pad
argument is false: two transmitted values sharing a blinder leak their difference. -/
lemma blindIdx_injective : Function.Injective blindIdx := by
  intro a b h; simpa [blindIdx] using h

/-- The claim-pad triple of layer `ly` *is* the "previous layer" triple that layer `ly+1`
reads.  This is the overlap `zk_common.h:L207-L213` documents. -/
lemma claim_pad_overlap (logw ly n : ℕ) :
    ly * layerSize logw + ovpClaimPad logw n
      = (ly + 1) * layerSize logw + ovpClaimPadM1 n := by
  simp [ovpClaimPad, ovpClaimPadM1, layerSize, claimPad, polyPad]
  ring

/--
**Consecutive layers blind with disjoint slots**, even though their windows overlap.

The shared claim-pad triple is used *once* as blinder — at layer `ly`, masking `wc[0]` and
`wc[1]` — and only *read* at layer `ly+1`, where `ConstraintBuilder::first` needs it to
reconstruct the incoming claim.  So the blinders really are independent across layers, which
is what the one-time pad argument needs.
-/
lemma layer_blind_disjoint (logw ly j k : ℕ) (hj : j < 4 * logw + 2) (_hk : k < 4 * logw + 2) :
    ly * layerSize logw + blindIdx j ≠ (ly + 1) * layerSize logw + blindIdx k := by
  simp only [layerSize_eq, blindIdx]
  have h : (ly + 1) * (4 * logw + 3) = ly * (4 * logw + 3) + (4 * logw + 3) := by ring
  rw [h]
  set S := ly * (4 * logw + 3)
  omega

/-!
### The whole layout, not just consecutive layers

`layer_blind_disjoint` is the local statement.  A run's pad needs the global one: the map
`(layer, blinder) ↦ pad index` is *injective across the whole run*, and no layer's quadratic
slot is any layer's blinding slot.  Together those say a pad index determines at most one
`(layer, blinder)` pair, which is what lets the run's pad be **computed** from the run's
blinder vector rather than supplied as data.

The obstacle is that the stride `layerSize logw = 4·logw + 3` is symbolic, so `omega` cannot
divide by it.  It does not have to: `blindSlot_lt_of_lt` replaces division by the one
multiplication fact `ly < ly' → ly·S + S ≤ ly'·S`, after which every index comparison is
linear in the opaque products and `omega` finishes.
-/

/-- Layer `ly`'s pad base: `ly · layer_size()` (`zk_common.h:L207`). -/
def layerBase (logw ly : ℕ) : ℕ := ly * layerSize logw

/-- Where layer `ly`'s blinder `k` lives in the run's pad. -/
def blindSlot (logw ly k : ℕ) : ℕ := layerBase logw ly + blindIdx k

/-- Layer `ly`'s quadratic slot, holding `dWC[0]·dWC[1]`.  It sits one past the layer's
blinding block — `claimTriple_not_blinding` locally, `quadSlot_ne_blindSlot` globally. -/
def quadSlot (logw ly : ℕ) : ℕ := layerBase logw ly + blindIdx (4 * logw + 2)

@[simp] lemma blindSlot_eq (logw ly k : ℕ) :
    blindSlot logw ly k = ly * (4 * logw + 3) + (3 + k) := by
  simp [blindSlot, layerBase, blindIdx]

@[simp] lemma quadSlot_eq (logw ly : ℕ) :
    quadSlot logw ly = ly * (4 * logw + 3) + (4 * logw + 5) := by
  simp [quadSlot, layerBase, blindIdx]; ring

/-- The one multiplication fact the layout arithmetic needs: a later layer's base is at least
a full stride further along. -/
lemma base_le_of_lt {logw ly ly' : ℕ} (h : ly < ly') :
    ly * (4 * logw + 3) + (4 * logw + 3) ≤ ly' * (4 * logw + 3) := by
  have h1 : (ly + 1) * (4 * logw + 3) ≤ ly' * (4 * logw + 3) :=
    Nat.mul_le_mul_right _ h
  have h2 : (ly + 1) * (4 * logw + 3) = ly * (4 * logw + 3) + (4 * logw + 3) := by ring
  omega

/-- **Blinding slots of a strictly earlier layer come strictly first.**  This is what makes the
layout injective: layer `ly`'s block ends at `ly·S + 4·logw + 4`, and layer `ly'`'s starts no
earlier than `ly·S + S + 3 = ly·S + 4·logw + 6`. -/
lemma blindSlot_lt_of_lt (logw ly ly' j k : ℕ) (hlt : ly < ly') (hj : j < 4 * logw + 2) :
    blindSlot logw ly j < blindSlot logw ly' k := by
  have hb := base_le_of_lt (logw := logw) hlt
  simp only [blindSlot_eq]
  set A := ly * (4 * logw + 3)
  set B := ly' * (4 * logw + 3)
  omega

/-- **The run's blinding slots are pairwise distinct.**  Injectivity across the *whole* run,
not merely between neighbours — a pad index belongs to at most one layer's blinder. -/
lemma blindSlot_inj {logw ly ly' j k : ℕ} (hj : j < 4 * logw + 2) (hk : k < 4 * logw + 2)
    (h : blindSlot logw ly j = blindSlot logw ly' k) : ly = ly' ∧ j = k := by
  rcases lt_trichotomy ly ly' with hc | hc | hc
  · exact absurd h (Nat.ne_of_lt (blindSlot_lt_of_lt logw ly ly' j k hc hj))
  · subst hc
    refine ⟨rfl, ?_⟩
    simp only [blindSlot_eq] at h
    omega
  · exact absurd h.symm (Nat.ne_of_lt (blindSlot_lt_of_lt logw ly' ly k j hc hk))

/-- **No layer's quadratic slot is any layer's blinding slot.**  Within a layer this is
`claimTriple_not_blinding`; across layers it is the stride argument again.  Without it the
run's pad would be over-determined at `ivLR`. -/
lemma quadSlot_ne_blindSlot (logw ly ly' k : ℕ) (hk : k < 4 * logw + 2) :
    quadSlot logw ly ≠ blindSlot logw ly' k := by
  rcases lt_trichotomy ly ly' with hc | hc | hc
  · have hb := base_le_of_lt (logw := logw) hc
    simp only [quadSlot_eq, blindSlot_eq]
    set A := ly * (4 * logw + 3)
    set B := ly' * (4 * logw + 3)
    omega
  · subst hc; simp only [quadSlot_eq, blindSlot_eq]; omega
  · have hb := base_le_of_lt (logw := logw) hc
    simp only [quadSlot_eq, blindSlot_eq]
    set A := ly' * (4 * logw + 3)
    set B := ly * (4 * logw + 3)
    omega

/-- Distinct layers have distinct quadratic slots. -/
lemma quadSlot_inj {logw ly ly' : ℕ} (h : quadSlot logw ly = quadSlot logw ly') : ly = ly' := by
  simp only [quadSlot_eq] at h
  have hm : ly * (4 * logw + 3) = ly' * (4 * logw + 3) := by omega
  exact Nat.eq_of_mul_eq_mul_right (by omega) hm

/-- Every slot layer `ly < nl` touches fits in a pad of size `nl · layerSize logw + 3` — the
size `zk_common.h` allocates, the stride times the layer count plus the trailing overlap. -/
lemma blindSlot_lt_pad (logw nl ly k : ℕ) (hly : ly < nl) (hk : k < 4 * logw + 2) :
    blindSlot logw ly k < nl * layerSize logw + 3 := by
  have hb := base_le_of_lt (logw := logw) hly
  simp only [blindSlot_eq, layerSize_eq]
  set A := ly * (4 * logw + 3)
  set B := nl * (4 * logw + 3)
  omega

lemma quadSlot_lt_pad (logw nl ly : ℕ) (hly : ly < nl) :
    quadSlot logw ly < nl * layerSize logw + 3 := by
  have hb := base_le_of_lt (logw := logw) hly
  simp only [quadSlot_eq, layerSize_eq]
  set A := ly * (4 * logw + 3)
  set B := nl * (4 * logw + 3)
  omega

end PadLayout

/-!
## The one-time pad, as a bijection

`RoundData.unpad` says the honest value is the transmitted one plus its blinder:
`p(0) = tr[0] + dP(r,0)`.  So for a *fixed* honest polynomial, the map
`blinder ↦ transmitted` is `t = p - d`, a translation — a bijection, uniformly in `p`.

That uniformity is the whole content: since the bijection exists for every honest value, and
`PadLayout` gives each transmitted value its own blinder (`blindIdx_injective`), every
transmission is explained by exactly one blinder assignment **no matter which witness the
prover used**.
-/

variable {F : Type} [Field F]

/-- The blinders of one layer: a pair per round, plus the two claim blinders. -/
abbrev Blinders (n : ℕ) (F : Type) := Fin n → F

/-- What the prover puts on the wire for those slots. -/
abbrev Transmission (n : ℕ) (F : Type) := Fin n → F

/--
**The one-time pad.**  For a fixed honest value at each slot, blinding is a bijection from
blinder assignments onto transmissions.

`toFun` is the prover (`transmitted = honest - blinder`) and `invFun` is the solve
(`blinder = honest - transmitted`), which is exactly "for every transcript there are coins
that explain it".
-/
def blindEquiv {n : ℕ} (honest : Fin n → F) : Blinders n F ≃ Transmission n F where
  toFun b := fun k => honest k - b k
  invFun t := fun k => honest k - t k
  left_inv b := by funext k; ring
  right_inv t := by funext k; ring

@[simp] lemma blindEquiv_apply {n : ℕ} (honest b : Fin n → F) (k : Fin n) :
    blindEquiv honest b k = honest k - b k := rfl

@[simp] lemma blindEquiv_symm_apply {n : ℕ} (honest t : Fin n → F) (k : Fin n) :
    (blindEquiv honest).symm t k = honest k - t k := rfl

/--
**Perfect hiding: the transmission does not depend on the witness.**

For any two witnesses — that is, any two honest value assignments `h₁`, `h₂` — there is a
bijection on blinder assignments carrying one prover's transmissions to the other's.  So the
two transmission distributions are equal, not merely close: the wire carries no information
about which witness was used.
-/
def blindReindex {n : ℕ} (h₁ h₂ : Fin n → F) : Blinders n F ≃ Blinders n F :=
  (blindEquiv h₁).trans (blindEquiv h₂).symm

lemma blindReindex_spec {n : ℕ} (h₁ h₂ : Fin n → F) (b : Blinders n F) :
    blindEquiv h₂ (blindReindex h₁ h₂ b) = blindEquiv h₁ b := by
  simp [blindReindex]

/--
**Every transmission is explained, for every witness.**  The surjectivity half, stated the
way the protocol argument uses it: given any wire content and any witness, there exist pad
coins producing exactly that content.
-/
theorem exists_blinders {n : ℕ} (honest : Fin n → F) (t : Transmission n F) :
    ∃! b : Blinders n F, blindEquiv honest b = t :=
  ⟨(blindEquiv honest).symm t, (blindEquiv honest).apply_symm_apply t,
   fun b hb => by rw [← hb, Equiv.symm_apply_apply]⟩

/-!
## The model's pad really has that shape

The abstract bijection above is easy.  The content is that the model's `RoundData` satisfies
its hypotheses — which is exactly what `RoundData` does *not* currently say, since `pp0` and
`pp2` are unconstrained `Fin M`.  `PadIndicesOK` supplies the missing constraint, and
`exists_pad_explaining` is the payoff.
-/

/-- A layer's rounds use the `PadLayout` blinding slots at pad base `pi`.  Soundness never
needed this; hiding is false without it. -/
def PadIndicesOK {M : ℕ} {F : Type} (pi : ℕ) (rounds : List (RoundData M F)) : Prop :=
  ∀ (r : ℕ) (h : r < rounds.length),
    ((rounds.get ⟨r, h⟩).pp0 : ℕ) = pi + PadLayout.blindIdx (2 * r) ∧
    ((rounds.get ⟨r, h⟩).pp2 : ℕ) = pi + PadLayout.blindIdx (2 * r + 1)

/-- Under `PadIndicesOK` every one of a layer's `2 * k` blinding slots is distinct — the
hypothesis the one-time pad argument needs, and the one that fails if `pp0 = pp2`. -/
lemma padIndices_distinct {M : ℕ} {F : Type} (pi : ℕ) (rounds : List (RoundData M F))
    (hidx : PadIndicesOK pi rounds) (r r' : ℕ) (h : r < rounds.length) (h' : r' < rounds.length) :
    ((rounds.get ⟨r, h⟩).pp0 = (rounds.get ⟨r', h'⟩).pp0 ↔ r = r') ∧
    (rounds.get ⟨r, h⟩).pp0 ≠ (rounds.get ⟨r', h'⟩).pp2 := by
  obtain ⟨e0, e2⟩ := hidx r h
  obtain ⟨e0', e2'⟩ := hidx r' h'
  constructor
  · constructor
    · intro he
      have : ((rounds.get ⟨r, h⟩).pp0 : ℕ) = ((rounds.get ⟨r', h'⟩).pp0 : ℕ) := by rw [he]
      rw [e0, e0'] at this
      simp only [PadLayout.blindIdx] at this
      omega
    · intro he; subst he; rfl
  · intro he
    have : ((rounds.get ⟨r, h⟩).pp0 : ℕ) = ((rounds.get ⟨r', h'⟩).pp2 : ℕ) := by rw [he]
    rw [e0, e2'] at this
    simp only [PadLayout.blindIdx] at this
    omega

/--
**Perfect hiding, in the model.**

Fix a layer at pad base `pi` with `nb` blinding slots.  For *any* honest values `h` — that is,
for any witness — and *any* transmitted values `t`, there is a pad making the blinding
relation `t j + pad (slot j) = h j` hold at every slot, and agreeing with `base` outside the
layer's own block.

Because `PadLayout`'s blinding slots are **contiguous** (`blindIdx j = 3 + j`), one
construction covers them all: the `4·logw` round slots masking `tr[0]`, `tr[2]` and the two
claim slots masking `wc[0]`, `wc[1]`.  Membership in the block is an inequality, so the pad is
*constructed* rather than chosen.

Read the other way round: the wire content is compatible with every witness, so it carries no
information about which one the prover holds.  `exists_blinders` gives the matching
uniqueness, so the two are in bijection rather than merely both non-empty.
-/
theorem exists_pad_explaining {M : ℕ} (pi nb : ℕ) (h t : ℕ → F) (base : Pad M F) :
    ∃ pad : Pad M F,
      (∀ (j : ℕ) (i : Fin M), j < nb → (i : ℕ) = pi + PadLayout.blindIdx j →
        t j + pad i = h j)
      ∧ (∀ i : Fin M, ((i : ℕ) < pi + 3 ∨ pi + 3 + nb ≤ (i : ℕ)) → pad i = base i) := by
  classical
  refine ⟨fun i =>
    if pi + 3 ≤ (i : ℕ) ∧ (i : ℕ) < pi + 3 + nb
      then h ((i : ℕ) - (pi + 3)) - t ((i : ℕ) - (pi + 3))
      else base i, ?_, ?_⟩
  · intro j i hj e
    simp only [PadLayout.blindIdx] at e
    show t j + (if pi + 3 ≤ (i : ℕ) ∧ (i : ℕ) < pi + 3 + nb then _ else _) = _
    rw [if_pos (by omega), show (i : ℕ) - (pi + 3) = j by omega]
    ring
  · intro i hi
    show (if pi + 3 ≤ (i : ℕ) ∧ (i : ℕ) < pi + 3 + nb then _ else _) = _
    rw [if_neg (by omega)]

/--
**The pad a run's blinders determine — `exists_pad_explaining`'s construction, as a function.**

`exists_pad_explaining` says a pad exists; `ZkSetup.padOf` needs one.  This is the same
formula, with the blinders read directly out of the layer's contiguous block.  Outside the
block it falls back to `base`, which is how a layer sits inside a whole run's pad.
-/
noncomputable def padOfBlinders {M : ℕ} (pi nb : ℕ) (base : Pad M F) (b : Fin nb → F) :
    Pad M F :=
  fun i =>
    if h : pi + 3 ≤ (i : ℕ) ∧ (i : ℕ) < pi + 3 + nb
      then b ⟨(i : ℕ) - (pi + 3), by omega⟩
      else base i

/--
**The blinding relation holds slot by slot.**

At blinding slot `j` the transmitted value plus the pad entry is the honest value — the
one-time pad, now with both sides written down rather than one of them existentially
quantified.
-/
lemma padOfBlinders_blind {M : ℕ} (pi nb : ℕ) (base : Pad M F) (b h : Fin nb → F)
    (j : Fin nb) (i : Fin M) (e : (i : ℕ) = pi + PadLayout.blindIdx j.val) :
    blindEquiv h b j + padOfBlinders pi nb base b i = h j := by
  simp only [PadLayout.blindIdx] at e
  have hj : j.val < nb := j.isLt
  have hb : pi + 3 ≤ (i : ℕ) ∧ (i : ℕ) < pi + 3 + nb := by omega
  have hlt : (i : ℕ) - (pi + 3) < nb := by omega
  have hidx : (⟨(i : ℕ) - (pi + 3), hlt⟩ : Fin nb) = j := Fin.ext (by simp; omega)
  show (h j - b j) + (if _ : pi + 3 ≤ (i : ℕ) ∧ (i : ℕ) < pi + 3 + nb then _ else _) = _
  rw [dif_pos hb]
  rw [show (⟨(i : ℕ) - (pi + 3), by omega⟩ : Fin nb) = j from hidx]
  ring

omit [Field F] in
/-- At a blinding slot the pad entry *is* the blinder.  `padOfBlinders_blind` is this plus the
transmission; this bare form is what the quadratic slot needs. -/
lemma padOfBlinders_at {M : ℕ} (pi nb : ℕ) (base : Pad M F) (b : Fin nb → F)
    (j : Fin nb) (i : Fin M) (e : (i : ℕ) = pi + PadLayout.blindIdx j.val) :
    padOfBlinders pi nb base b i = b j := by
  simp only [PadLayout.blindIdx] at e
  have hj : j.val < nb := j.isLt
  have hb : pi + 3 ≤ (i : ℕ) ∧ (i : ℕ) < pi + 3 + nb := by omega
  have hlt : (i : ℕ) - (pi + 3) < nb := by omega
  have hidx : (⟨(i : ℕ) - (pi + 3), hlt⟩ : Fin nb) = j := Fin.ext (by simp; omega)
  show (if _ : pi + 3 ≤ (i : ℕ) ∧ (i : ℕ) < pi + 3 + nb then _ else _) = _
  rw [dif_pos hb]
  exact congrArg b hidx

omit [Field F] in
/-- Outside its own block the pad is whatever the surrounding run put there. -/
lemma padOfBlinders_outside {M : ℕ} (pi nb : ℕ) (base : Pad M F) (b : Fin nb → F) (i : Fin M)
    (hi : (i : ℕ) < pi + 3 ∨ pi + 3 + nb ≤ (i : ℕ)) :
    padOfBlinders pi nb base b i = base i := by
  show (if _ : pi + 3 ≤ (i : ℕ) ∧ (i : ℕ) < pi + 3 + nb then _ else _) = _
  rw [dif_neg (by omega)]

/--
The round and claim slots of a layer, named.  Slot `2r` and `2r+1` blind round `r`'s
`tr[0]` and `tr[2]`; slots `4·logw` and `4·logw+1` blind `wc[0]` and `wc[1]`.
-/
lemma PadLayout.blind_slots (logw r : ℕ) (hr : r < 2 * logw) :
    2 * r < 4 * logw + 2 ∧ 2 * r + 1 < 4 * logw + 2
      ∧ 4 * logw < 4 * logw + 2 ∧ 4 * logw + 1 < 4 * logw + 2 := by
  refine ⟨by omega, by omega, by omega, by omega⟩

/-!
## Closeness of transcript families

The Merkle commitment inside Ligero is only *statistically* hiding, so the composed statement
cannot be a plain bijection.  `ZkClose` is the **coupling** form of statistical distance: a
bijection on coins that agrees outside a bounded exceptional set.  For uniform coins that is
exactly `Δ ≤ eps / |R|`, and it is the same shape as every soundness bound here —
`event_card (bad set) ≤ eps`.

`eps = 0` is perfect indistinguishability, which is what the pad blinding gives.
-/

/-- The determined coordinate of a claim triple, `dWC[0]*dWC[1]`, is **not** a blinding slot.
So imposing the quadratic pad relation leaves the one-time pad untouched: the pad is a
variety rather than a cube, but the constrained coordinate never masks anything. -/
lemma PadLayout.claimTriple_not_blinding (logw k : ℕ) (hk : k < 4 * logw + 2) :
    PadLayout.ovpClaimPad logw 2 ≠ PadLayout.blindIdx k := by
  simp only [PadLayout.ovpClaimPad, PadLayout.blindIdx, PadLayout.claimPad_eq]
  omega


/- Generic coupling and statistical-distance results are imported from Bcs.StatisticalDistance. -/
