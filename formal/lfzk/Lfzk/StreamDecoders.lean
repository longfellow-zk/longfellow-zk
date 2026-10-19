import Lfzk.StreamSampler
import Lfzk.RbrZkLongfellow

/-!
# Challenge decoders on a stream of AES blocks

`Lfzk.StreamSampler` proves the deployed samplers exactly balanced as functions of a finite byte
list.  This file reads them on the raw challenge alphabet the deployed transcript actually has: a
**stream of `B` 16-byte blocks** (`Stream B := Fin B → Block`), the AES-CTR output
`E_k(0‖0), E_k(1‖0), …` of one key, read byte by byte in block order (`flatten`; Rust's `FsPrf`
refills its 16-byte buffer from the next counter block and hands out its bytes in order).  Rust's
`refill` asserts `block_counter < MAX_PRF_BLOCKS = 2^40`, so with `B = 2^40` a sampler that runs out
of stream is exactly a run on which the deployed verifier **panics** (and so does not accept).

## What is proved

* `card_filter_flatten` — counting streams is counting byte strings of length `16 B`;
* `exact_balance_dvd`, `no_exact_decoder_odd` — **exact balance over streams alone is impossible**
  whenever the target's size has an odd factor (the P-256 base field, every query-set family with
  `C(n, r)` not a power of two): an exactly balanced decoder `C → Y` (the `CircuitSide` fields
  `hbal…`, `hk…`) forces `|Y| ∣ |C| = 2^(128 B)`;
* `decode` — the decoder: the deployed sampler where it succeeds, a **round-robin fallback**
  (`spread`) over the streams where it runs out.  `decode_count_le`, `kOf_mul_le`: every value has
  at most `kOf` preimages, and `kOf · |Y| ≤ |Stream B| + |Y|` — the best possible for any decoder,
  and the **virtual card** `K = |C| + |Y|` the counting layer `Lfzk.ZkVirtualCard` consumes;
* `decodeBk`, `decodeBk_count` — with an independent ideal backup coordinate used only where the
  stream runs out, the decoder is **exactly** balanced over `Stream B × Bk` (`count · |Y| = |C|`);
* the deployed slots (§4): `initS` (`begin_circuit`'s `cc, hc` then layer 0's `begin_layer`
  `alpha, beta`, decoded as `(G, β, α)` with `G` the first `logv` coordinates of `hc`), `pairS`
  (`begin_layer`, decoded `(β, α)`), `eltS` (a round challenge, `alpha_in`), `chalS` (the Ligero
  combination: one stream, `m` field elements, read into the model's challenge by any map with equal
  fibres — a surjective additive map such as a coordinate selection, or an equivalence), `queryS`
  (`choose(n, r)` as the query set), `macS` (`bytes(16)`, little-endian).  Each is local and
  balanced; the joint outputs (`initS`, `pairS`, `chalS`) are jointly balanced, not merely per
  coordinate.

## What is a modelling choice

The block-to-byte order and the samplers are Rust's.  The bijection from a sampler's integer to the
field element (`to_montgomery`, `Gf2_128::from`) is a parameter (any bijection), as is the layout
map from Rust's Ligero combination vector (`u_ldt ‖ alphal ‖ alphaq ‖ u_quad`) to the model's
challenge type; the latter only needs equal fibres.  Which stream feeds which slot is
`Lfzk.NizkDeployedHash`'s point layout.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.StreamDecoders

open Finset Lfzk.StreamSampler
open scoped Classical

/-! ## 1. Streams of blocks -/

/-- An AES block: 16 bytes. -/
abbrev Block := Fin 16 → Byte

/-- **One key's stream**: `B` counter blocks. -/
abbrev Stream (B : ℕ) := Fin B → Block

/-- Blocks in counter order, bytes in buffer order: byte `t` of block `i` is stream byte
`16 i + t`. -/
def streamEquiv (B : ℕ) : Stream B ≃ (Fin (B * 16) → Byte) :=
  (Equiv.curry (Fin B) (Fin 16) Byte).symm.trans
    (Equiv.arrowCongr finProdFinEquiv (Equiv.refl Byte))

/-- **The stream as the byte sequence `bytes(len)` hands out.** -/
def flatten {B : ℕ} (c : Stream B) : List Byte := List.ofFn (streamEquiv B c)

theorem flatten_length {B : ℕ} (c : Stream B) : (flatten c).length = B * 16 := List.length_ofFn

/-- Byte `t` of block `i` sits at position `16 i + t`. -/
theorem streamEquiv_apply {B : ℕ} (c : Stream B) (i : Fin B) (t : Fin 16) :
    streamEquiv B c (finProdFinEquiv (i, t)) = c i t := by
  simp [streamEquiv, Equiv.arrowCongr_apply]

theorem finProdFinEquiv_val {B : ℕ} (i : Fin B) (t : Fin 16) :
    ((finProdFinEquiv (i, t) : Fin (B * 16)) : ℕ) = t + 16 * i := by
  simp [finProdFinEquiv_apply_val]

theorem card_stream (B : ℕ) : Fintype.card (Stream B) = 256 ^ (B * 16) := by
  rw [Fintype.card_congr (streamEquiv B)]
  simp

/-- **Counting streams is counting byte strings of length `16 B`.** -/
theorem card_filter_flatten {B : ℕ} (P : List Byte → Prop) [DecidablePred P] :
    (univ.filter fun c : Stream B => P (flatten c)).card = ((words (B * 16)).filter P).card := by
  rw [card_filter_words]
  exact card_equiv (streamEquiv B) fun c => by simp [flatten]

/-! ## 2. Exact balance over streams alone is impossible -/

/-- **An exactly balanced decoder forces divisibility**: if every value has at most `k` preimages
and `k · |Y| ≤ |C|`, then every value has exactly `k`, so `|Y| ∣ |C|`. -/
theorem exact_balance_dvd {C Y : Type} [Fintype C] [Fintype Y] (d : C → Y) (k : ℕ)
    (hb : ∀ y, (univ.filter fun c => d c = y).card ≤ k)
    (hk : k * Fintype.card Y ≤ Fintype.card C) : Fintype.card Y ∣ Fintype.card C := by
  have hsum : ∑ y : Y, (univ.filter fun c => d c = y).card = Fintype.card C := by
    rw [← Finset.card_univ, ← card_biUnion]
    · congr 1
      ext c
      simp
    · intro y _ y' _ hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro c hc hc'
      simp only [mem_filter] at hc hc'
      exact hne (hc.2.symm.trans hc'.2)
  have hle : ∑ y : Y, (univ.filter fun c => d c = y).card ≤ ∑ _y : Y, k := sum_le_sum fun y _ => hb y
  have heq : ∀ y, (univ.filter fun c => d c = y).card = k := by
    intro y
    by_contra hne
    have hlt : (univ.filter fun c => d c = y).card < k := lt_of_le_of_ne (hb y) hne
    have : ∑ y' : Y, (univ.filter fun c => d c = y').card < ∑ _y : Y, k :=
      sum_lt_sum (fun y _ => hb y) ⟨y, mem_univ _, hlt⟩
    rw [sum_const, card_univ, smul_eq_mul] at this
    have := mul_comm k (Fintype.card Y)
    omega
  refine ⟨k, ?_⟩
  rw [← hsum, sum_congr rfl fun y _ => heq y, sum_const, card_univ, smul_eq_mul]

/-- **No exactly balanced decoder from streams onto a set of odd size `> 1`** — the P-256 base
field, `|F| = p` odd, in particular: `|Stream B| = 2^(128 B)`. -/
theorem no_exact_decoder_odd {B : ℕ} {Y : Type} [Fintype Y] (hodd : Fintype.card Y % 2 = 1)
    (hY : 1 < Fintype.card Y) (d : Stream B → Y) (k : ℕ)
    (hb : ∀ y, (univ.filter fun c => d c = y).card ≤ k) :
    ¬ k * Fintype.card Y ≤ Fintype.card (Stream B) := by
  intro hk
  have hdvd := exact_balance_dvd d k hb hk
  rw [card_stream, show (256 : ℕ) ^ (B * 16) = 2 ^ (8 * (B * 16)) by rw [pow_mul 2 8]; norm_num]
    at hdvd
  have hcop : Nat.Coprime (Fintype.card Y) (2 ^ (8 * (B * 16))) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr (Nat.odd_iff.mpr hodd))
  have := Nat.Coprime.eq_one_of_dvd hcop hdvd
  omega

/-! ## 3. The decoders -/

section Decode

variable {α : Type} {B : ℕ}

/-- The streams on which the sampler runs out (the deployed verifier panics). -/
def Fails (p : Sampler α) (c : Stream B) : Prop := p (flatten c) = none

/-- **Round-robin fallback** over the streams on which `p` runs out: the `i`-th such stream (in a
fixed enumeration) is sent to value number `i mod |α|`. -/
noncomputable def spread [Fintype α] [Nonempty α] (p : Sampler α) (B : ℕ) (c : Stream B) : α :=
  if h : Fails p c then
    (Fintype.equivFin α).symm
      ⟨(Fintype.equivFin {c : Stream B // Fails p c} ⟨c, h⟩ : ℕ) % Fintype.card α,
        Nat.mod_lt _ Fintype.card_pos⟩
  else Classical.arbitrary α

/-- **The stream decoder**: the sampler's value where it succeeds, `fb` where it runs out. -/
noncomputable def decodeWith (p : Sampler α) (fb : Stream B → α) (c : Stream B) : α :=
  match p (flatten c) with
  | some ar => ar.1
  | none => fb c

/-- **The deployed decoder with the round-robin fallback.** -/
noncomputable def decode [Fintype α] [Nonempty α] (p : Sampler α) (B : ℕ) : Stream B → α :=
  decodeWith p (spread p B)

theorem decodeWith_of_some {p : Sampler α} {fb : Stream B → α} {c : Stream B} {a : α}
    {r : List Byte} (h : p (flatten c) = some (a, r)) : decodeWith p fb c = a := by
  simp [decodeWith, h]

theorem decodeWith_of_fails {p : Sampler α} {fb : Stream B → α} {c : Stream B}
    (h : Fails p c) : decodeWith p fb c = fb c := by
  unfold Fails at h
  simp [decodeWith, h]

/-- The streams on which the sampler succeeds with `a` are its success count at length `16 B`. -/
theorem card_success (p : Sampler α) (a : α) :
    (univ.filter fun c : Stream B => ∃ r, p (flatten c) = some (a, r)).card
      = Sampler.succ p (B * 16) a := by
  unfold Sampler.succ
  exact card_filter_flatten (fun w => ∃ r, p w = some (a, r))

/-- `#{i < M | i mod d = r} ≤ M / d + 1`. -/
theorem card_fin_mod_le {M d r : ℕ} :
    (univ.filter fun i : Fin M => (i : ℕ) % d = r).card ≤ M / d + 1 := by
  rw [← Finset.card_range (M / d + 1)]
  refine card_le_card_of_injOn (fun i => (i : ℕ) / d) ?_ ?_
  · intro i _
    simp only [coe_range, Set.mem_Iio]
    have := Nat.div_le_div_right (c := d) i.isLt.le
    omega
  · intro i hi i' hi' h
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hi hi'
    simp only at h
    apply Fin.ext
    rw [← Nat.div_add_mod (i : ℕ) d, ← Nat.div_add_mod (i' : ℕ) d, h, hi, hi']

/-- **The fallback is spread evenly**: at most `#Fail / |α| + 1` failing streams per value. -/
theorem card_spread_le [Fintype α] [Nonempty α] (p : Sampler α) (a : α) :
    (univ.filter fun c : Stream B => Fails p c ∧ spread p B c = a).card
      ≤ (univ.filter fun c : Stream B => Fails p c).card / Fintype.card α + 1 := by
  set e := Fintype.equivFin {c : Stream B // Fails p c}
  have hcard : Fintype.card {c : Stream B // Fails p c}
      = (univ.filter fun c : Stream B => Fails p c).card := Fintype.card_subtype _
  calc (univ.filter fun c : Stream B => Fails p c ∧ spread p B c = a).card
      = (univ.filter fun x : {c : Stream B // Fails p c} => spread p B x.1 = a).card := by
        refine card_bij' (fun c hc => (⟨c, (mem_filter.mp hc).2.1⟩ : {c : Stream B // Fails p c}))
          (fun x _ => x.1) ?_ ?_ ?_ ?_
        · intro c hc
          simp only [mem_filter, mem_univ, true_and] at hc ⊢
          exact hc.2
        · intro x hx
          simp only [mem_filter, mem_univ, true_and] at hx ⊢
          exact ⟨x.2, hx⟩
        · intro c _; rfl
        · intro x _; rfl
    _ = (univ.filter fun i : Fin (Fintype.card {c : Stream B // Fails p c}) =>
          (i : ℕ) % Fintype.card α = (Fintype.equivFin α a : ℕ)).card := by
        refine card_equiv e fun x => ?_
        simp only [mem_filter, mem_univ, true_and]
        have hs : spread p B x.1 = (Fintype.equivFin α).symm
            ⟨(e x : ℕ) % Fintype.card α, Nat.mod_lt _ Fintype.card_pos⟩ := by
          unfold spread
          rw [dif_pos x.2]
        rw [hs, Equiv.symm_apply_eq, Fin.ext_iff]
    _ ≤ (univ.filter fun c : Stream B => Fails p c).card / Fintype.card α + 1 := by
        rw [← hcard]
        exact card_fin_mod_le

/-- **Every value of the decoder has at most `succ + #Fail / |α| + 1` preimages.** -/
theorem decode_count_le [Fintype α] [Nonempty α] (p : Sampler α) (a : α) :
    (univ.filter fun c : Stream B => decode p B c = a).card
      ≤ Sampler.succ p (B * 16) a
        + (univ.filter fun c : Stream B => Fails p c).card / Fintype.card α + 1 := by
  calc (univ.filter fun c : Stream B => decode p B c = a).card
      ≤ ((univ.filter fun c : Stream B => ∃ r, p (flatten c) = some (a, r))
          ∪ (univ.filter fun c : Stream B => Fails p c ∧ spread p B c = a)).card := by
        refine card_le_card fun c hc => ?_
        simp only [mem_filter, mem_univ, true_and, mem_union] at hc ⊢
        rcases h : p (flatten c) with _ | ⟨a', r⟩
        · right
          have hf : Fails p c := h
          exact ⟨hf, by rw [← hc]; exact (decodeWith_of_fails hf).symm⟩
        · left
          unfold decode at hc
          rw [decodeWith_of_some h] at hc
          subst hc
          exact ⟨r, rfl⟩
    _ ≤ _ := card_union_le _ _
    _ ≤ _ := by
        rw [card_success, add_assoc]
        exact Nat.add_le_add_left (card_spread_le p a) _

/-- **The successes and the failures partition the streams.** -/
theorem sum_succ_add_fail [Fintype α] (p : Sampler α) :
    ∑ a, Sampler.succ p (B * 16) a + (univ.filter fun c : Stream B => Fails p c).card
      = Fintype.card (Stream B) := by
  have h1 : ∑ a, Sampler.succ p (B * 16) a
      = (univ.filter fun c : Stream B => ¬ Fails p c).card := by
    rw [← sum_congr rfl fun a _ => card_success (B := B) p a, ← card_biUnion]
    · congr 1
      ext c
      simp only [mem_biUnion, mem_univ, true_and, mem_filter, Fails]
      constructor
      · rintro ⟨a, r, h⟩
        rw [h]; simp
      · intro h
        rcases h' : p (flatten c) with _ | ⟨a, r⟩
        · exact absurd h' h
        · exact ⟨a, r, rfl⟩
    · intro a _ a' _ hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro c hc hc'
      simp only [mem_filter] at hc hc'
      obtain ⟨r, hr⟩ := hc.2
      obtain ⟨r', hr'⟩ := hc'.2
      rw [hr] at hr'
      simp only [Option.some.injEq, Prod.mk.injEq] at hr'
      exact hne hr'.1
  rw [h1, add_comm, Finset.card_filter_add_card_filter_not, card_univ]

/-- **The decoder's preimage bound** `kOf`: the common success count (balance) plus the fallback's
share. -/
noncomputable def kOf [Fintype α] [Nonempty α] (p : Sampler α) (B : ℕ) : ℕ :=
  Sampler.succ p (B * 16) (Classical.arbitrary α)
    + (univ.filter fun c : Stream B => Fails p c).card / Fintype.card α + 1

theorem decode_le_kOf [Fintype α] [Nonempty α] {p : Sampler α} (hp : p.Local)
    (hb : p.Balanced) (a : α) :
    (univ.filter fun c : Stream B => decode p B c = a).card ≤ kOf p B := by
  unfold kOf
  rw [← Sampler.succ_balanced hp hb (B * 16) a (Classical.arbitrary α)]
  exact decode_count_le p a

/-- **The virtual card**: `kOf · |α| ≤ |Stream B| + |α|`. -/
theorem kOf_mul_le [Fintype α] [Nonempty α] {p : Sampler α} (hp : p.Local) (hb : p.Balanced) :
    kOf p B * Fintype.card α ≤ Fintype.card (Stream B) + Fintype.card α := by
  have hs := sum_succ_add_fail (B := B) p
  rw [sum_congr rfl fun a _ => Sampler.succ_balanced hp hb (B * 16) a (Classical.arbitrary α),
    sum_const, card_univ, smul_eq_mul] at hs
  unfold kOf
  have := Nat.div_mul_le_self (univ.filter fun c : Stream B => Fails p c).card (Fintype.card α)
  nlinarith

/-! ### With an ideal backup coordinate: exact balance -/

/-- **The deployed decoder, with an ideal backup coordinate used only where the stream runs out.** -/
noncomputable def decodeBk {Bk : Type} (p : Sampler α) (bk : Bk → α) (c : Stream B × Bk) : α :=
  decodeWith p (fun _ => bk c.2) c.1

theorem decodeBk_count {Bk : Type} [Fintype α] [Fintype Bk] {p : Sampler α} (hp : p.Local)
    (hb : p.Balanced) {bk : Bk → α} {f : ℕ} (hf : ∀ a, (univ.filter fun b => bk b = a).card = f)
    (hfα : f * Fintype.card α = Fintype.card Bk) (a : α) :
    (univ.filter fun c : Stream B × Bk => decodeBk p bk c = a).card * Fintype.card α
      = Fintype.card (Stream B × Bk) := by
  have hsplit : (univ.filter fun c : Stream B × Bk => decodeBk p bk c = a).card
      = (univ.filter fun c : Stream B => ∃ r, p (flatten c) = some (a, r)).card * Fintype.card Bk
        + (univ.filter fun c : Stream B => Fails p c).card * f := by
    rw [← hf a, ← card_univ, ← card_product, ← card_product, ← card_union_of_disjoint]
    · congr 1
      ext ⟨s, b⟩
      simp only [mem_filter, mem_univ, true_and, and_true, mem_union, mem_product]
      constructor
      · intro h
        unfold decodeBk at h
        rcases hs : p (flatten s) with _ | ⟨a', r⟩
        · right
          exact ⟨hs, by rw [decodeWith_of_fails hs] at h; exact h⟩
        · left
          rw [decodeWith_of_some hs] at h
          subst h
          exact ⟨r, rfl⟩
      · rintro (⟨r, hr⟩ | ⟨hfl, hb'⟩)
        · exact decodeWith_of_some hr
        · unfold decodeBk
          rw [decodeWith_of_fails hfl]
          exact hb'
    · rw [Finset.disjoint_left]
      rintro ⟨s, b⟩ h1 h2
      simp only [mem_product, mem_filter, mem_univ, true_and] at h1 h2
      obtain ⟨r, hr⟩ := h1.1
      have hfl : p (flatten s) = none := h2.1
      rw [hr] at hfl
      simp at hfl
  have hs := sum_succ_add_fail (B := B) p
  rw [sum_congr rfl fun a' _ => Sampler.succ_balanced hp hb (B * 16) a' a,
    sum_const, card_univ, smul_eq_mul] at hs
  rw [hsplit, card_success, Fintype.card_prod, ← hs, ← hfα]
  ring

end Decode

/-- **Exact balance over streams**: a local balanced sampler succeeds with every value on the
same number of streams of `B` blocks (Part A's "balanced over the streams on which it
succeeds"). -/
theorem success_balanced {α : Type} {B : ℕ} {p : Sampler α} (hp : p.Local) (hb : p.Balanced)
    (a a' : α) :
    (univ.filter fun c : Stream B => ∃ r, p (flatten c) = some (a, r)).card
      = (univ.filter fun c : Stream B => ∃ r, p (flatten c) = some (a', r)).card := by
  rw [card_success, card_success, Sampler.succ_balanced hp hb]

/-! ## 4. The deployed slots -/

/-- **Equal fibres of a surjective additive map**: translation by a preimage of `b' − b`. -/
theorem fiber_card_eq_of_surj {A Y : Type} [AddCommGroup A] [AddCommGroup Y] [Fintype A]
    (g : A →+ Y) (hg : Function.Surjective g) (b b' : Y) :
    (univ.filter fun a => g a = b).card = (univ.filter fun a => g a = b').card := by
  obtain ⟨t, ht⟩ := hg (-b + b')
  refine card_equiv (Equiv.addRight t) fun a => ?_
  simp only [mem_filter, mem_univ, true_and, Equiv.coe_addRight, map_add, ht]
  constructor
  · rintro rfl; abel
  · intro h
    rw [eq_sub_of_add_eq h]
    abel

/-- **A field's deployed sampler**: Rust's raw integer sampler, local and balanced, and the
representation bijection onto the field. -/
structure FieldSampler (F : Type) where
  q : ℕ
  raw : Sampler (Fin q)
  e : Fin q ≃ F
  hlocal : raw.Local
  hbal : raw.Balanced

/-- `GF(2^128)` (`gf2_128.rs`): 16 bytes, little-endian `u128`, through the representation
`e`. -/
def gfSampler {F : Type} (e : Fin (2 ^ 128) ≃ F) : FieldSampler F :=
  ⟨2 ^ 128, gfRaw, e, rejNat_local _ _ _ _, gfRaw_balanced⟩

/-- The P-256 base field (`fp_generic.rs`), modulus `p ≤ 2^256`: 32 bytes, little-endian, rejected
when `≥ p`, through the representation `e`. -/
def p256Sampler {F : Type} (p : ℕ) (hp : p ≤ 2 ^ 256) (e : Fin p ≃ F) : FieldSampler F :=
  ⟨p, p256Raw p, e, rejNat_local _ _ _ _, p256Raw_balanced hp⟩

namespace FieldSampler

variable {F : Type} (fs : FieldSampler F)

/-- `elt_field`. -/
def elt : Sampler F := StreamSampler.elt fs.e fs.raw

theorem elt_local : fs.elt.Local := StreamSampler.elt_local fs.e fs.hlocal

theorem elt_balanced : fs.elt.Balanced := StreamSampler.elt_balanced fs.e fs.hbal

end FieldSampler

section Slots

variable {F : Type}

/-- The decoded initial slot: `G` the first `logv` coordinates of `hc`, then `beta`, `alpha`. -/
def initOf [Field F] {maxLogw logv : ℕ} (h : logv ≤ maxLogw) :
    ((Fin maxLogw → F) × (Fin maxLogw → F) × F × F) →+ ((Fin logv → F) × F × F) where
  toFun x := (fun i => x.2.1 (Fin.castLE h i), x.2.2.2, x.2.2.1)
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

theorem initOf_surjective [Field F] {maxLogw logv : ℕ} (h : logv ≤ maxLogw) :
    Function.Surjective (initOf (F := F) h) := by
  rintro ⟨G, b, a⟩
  refine ⟨(0, fun t => if ht : (t : ℕ) < logv then G ⟨t, ht⟩ else 0, a, b), ?_⟩
  simp only [initOf, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.mk.injEq, and_true]
  funext i
  simp [Fin.castLE, i.isLt]

/-- **`begin_circuit` then layer 0's `begin_layer`** (`symbolic_sumcheck_verifier.rs`): on one
stream, `cc ← elt_field_slice(maxLogw)`, `hc ← elt_field_slice(maxLogw)`, `alpha ← elt_field`,
`beta ← elt_field`; decoded as `(G, β, α)`, `G` the first `logv` coordinates of `hc`. -/
def initS [Field F] (fs : FieldSampler F) (maxLogw logv : ℕ) (h : logv ≤ maxLogw) :
    Sampler ((Fin logv → F) × F × F) :=
  Sampler.map (initOf h)
    (Sampler.seq (Sampler.vec maxLogw fs.elt)
      (Sampler.seq (Sampler.vec maxLogw fs.elt) (Sampler.seq fs.elt fs.elt)))

theorem initS_local [Field F] (fs : FieldSampler F) (maxLogw logv : ℕ) (h : logv ≤ maxLogw) :
    (initS fs maxLogw logv h).Local :=
  Sampler.map_local (Sampler.seq_local (Sampler.vec_local _ fs.elt_local)
    (Sampler.seq_local (Sampler.vec_local _ fs.elt_local)
      (Sampler.seq_local fs.elt_local fs.elt_local)))

/-- **The initial slot is jointly balanced**: every `(G, β, α)` is decoded, by consuming exactly
`j` bytes, from the same number of byte strings. -/
theorem initS_balanced [Field F] [Fintype F] (fs : FieldSampler F) (maxLogw logv : ℕ)
    (h : logv ≤ maxLogw) :
    (initS fs maxLogw logv h).Balanced :=
  Sampler.Balanced.map
    (Sampler.Balanced.seq (Sampler.vec_local _ fs.elt_local)
      (Sampler.vec_balanced _ fs.elt_local fs.elt_balanced)
      (Sampler.Balanced.seq (Sampler.vec_local _ fs.elt_local)
        (Sampler.vec_balanced _ fs.elt_local fs.elt_balanced)
        (Sampler.Balanced.seq fs.elt_local fs.elt_balanced fs.elt_balanced)))
    fun b b' => by
      have := fiber_card_eq_of_surj (initOf (F := F) h) (initOf_surjective h) b b'
      convert this using 3

/-- **`begin_layer`**: `alpha ← elt_field`, `beta ← elt_field`, decoded as `(β, α)`. -/
def pairS (fs : FieldSampler F) : Sampler (F × F) :=
  Sampler.map Prod.swap (Sampler.seq fs.elt fs.elt)

theorem pairS_local (fs : FieldSampler F) : (pairS fs).Local :=
  Sampler.map_local (Sampler.seq_local fs.elt_local fs.elt_local)

theorem pairS_balanced [Fintype F] (fs : FieldSampler F) : (pairS fs).Balanced :=
  Sampler.Balanced.map_bijective (Sampler.Balanced.seq fs.elt_local fs.elt_balanced fs.elt_balanced)
    Prod.swap_bijective

/-- **The Ligero combination** (`ligero/src/transcript.rs`): on one stream,
`u_ldt ‖ alphal ‖ alphaq ‖ u_quad`, `m` field elements in all, read into the model's challenge by
`chalOf`. -/
def chalS {X : Type} (fs : FieldSampler F) (m : ℕ) (chalOf : (Fin m → F) → X) : Sampler X :=
  Sampler.map chalOf (Sampler.vec m fs.elt)

theorem chalS_local {X : Type} (fs : FieldSampler F) (m : ℕ) (chalOf : (Fin m → F) → X) :
    (chalS fs m chalOf).Local :=
  Sampler.map_local (Sampler.vec_local _ fs.elt_local)

/-- **The Ligero combination is jointly balanced** for any layout map with equal fibres. -/
theorem chalS_balanced {X : Type} [DecidableEq X] [Fintype F] (fs : FieldSampler F) (m : ℕ)
    (chalOf : (Fin m → F) → X)
    (hchal : ∀ x x', (univ.filter fun v => chalOf v = x).card
      = (univ.filter fun v => chalOf v = x').card) :
    (chalS fs m chalOf).Balanced :=
  Sampler.Balanced.map (Sampler.vec_balanced _ fs.elt_local fs.elt_balanced) hchal

/-- Any equivalence is a layout map with equal fibres. -/
theorem equiv_fibers {X : Type} [DecidableEq X] [Fintype F] {m : ℕ} (e : (Fin m → F) ≃ X)
    (x x' : X) :
    (univ.filter fun v => e v = x).card = (univ.filter fun v => e v = x').card := by
  rw [Sampler.fiber_card_of_bijective e.bijective, Sampler.fiber_card_of_bijective e.bijective]

end Slots

/-- **The Ligero query set**: `choose(n, r)` (`gen_idx`, `n = block_enc − dblock`). -/
def queryS (n r : ℕ) (h : r ≤ n) : Sampler (QSet n r) := chooseRust n r h

/-- **The MAC-key share** (`mdoc_zk/runtime/src/verifier.rs`): `bytes(16)`, `u128::from_le_bytes`,
through the representation `e`. -/
def macS {Fmac : Type} (e : Fin (2 ^ 128) ≃ Fmac) : Sampler Fmac := StreamSampler.elt e gfRaw

theorem macS_local {Fmac : Type} (e : Fin (2 ^ 128) ≃ Fmac) : (macS e).Local :=
  StreamSampler.elt_local e (rejNat_local _ _ _ _)

theorem macS_balanced {Fmac : Type} (e : Fin (2 ^ 128) ≃ Fmac) : (macS e).Balanced :=
  StreamSampler.elt_balanced e gfRaw_balanced

/-! ## 5. A side's decoders -/

/-- **One side's five deployed slot samplers**, each local and balanced. -/
structure SlotSamplers (F X Q Gpt : Type) where
  init : Sampler (Gpt × F × F)
  pair : Sampler (F × F)
  f : Sampler F
  chal : Sampler X
  query : Sampler Q
  init_local : init.Local
  pair_local : pair.Local
  f_local : f.Local
  chal_local : chal.Local
  query_local : query.Local
  init_bal : init.Balanced
  pair_bal : pair.Balanced
  f_bal : f.Balanced
  chal_bal : chal.Balanced
  query_bal : query.Balanced

/-- **The deployed slot samplers of a side** over a field with sampler `fs`: `initS`, `pairS`,
`elt`, `chalS` at a layout map with equal fibres, `queryS`. -/
def deployedSlots {F X : Type} [Field F] [Fintype F] [DecidableEq X] (fs : FieldSampler F)
    (maxLogw logv : ℕ)
    (hlog : logv ≤ maxLogw) (m : ℕ) (chalOf : (Fin m → F) → X)
    (hchal : ∀ x x', (univ.filter fun v => chalOf v = x).card
      = (univ.filter fun v => chalOf v = x').card) (n r : ℕ) (hnr : r ≤ n) :
    SlotSamplers F X (QSet n r) (Fin logv → F) where
  init := initS fs maxLogw logv hlog
  pair := pairS fs
  f := fs.elt
  chal := chalS fs m chalOf
  query := queryS n r hnr
  init_local := initS_local fs maxLogw logv hlog
  pair_local := pairS_local fs
  f_local := fs.elt_local
  chal_local := chalS_local fs m chalOf
  query_local := chooseRust_local n r hnr
  init_bal := initS_balanced fs maxLogw logv hlog
  pair_bal := pairS_balanced fs
  f_bal := fs.elt_balanced
  chal_bal := chalS_balanced fs m chalOf hchal
  query_bal := chooseRust_balanced n r hnr

/-- **A zero-knowledge code read on streams**: `V`'s computation, its five coin decoders replaced by
the stream decoders (`decode`, round-robin fallback), read through `proj : C → Stream B` (the
identity on streams; the inclusion of the injective block tuples for the ideal cipher). -/
noncomputable def withStreams {C' C F X Q Msg Gpt : Type} [Fintype F] [Fintype X] [Fintype Q]
    [Fintype Gpt] [Nonempty F] [Nonempty X] [Nonempty Q] [Nonempty Gpt]
    {M ninp logw logc : ℕ} (V : RbrZkLongfellow.ZkCode C' F X Q Msg Gpt M ninp logw logc)
    (B : ℕ) (ss : SlotSamplers F X Q Gpt) (proj : C → Stream B) :
    RbrZkLongfellow.ZkCode C F X Q Msg Gpt M ninp logw logc where
  st0 := V.st0
  stNext := V.stNext
  eqqOf := V.eqqOf
  npub := V.npub
  inCoeffs := V.inCoeffs
  pubBinding := V.pubBinding
  nlin := V.nlin
  nt := V.nt
  roundOf := V.roundOf
  closeOf := V.closeOf
  decodeInit c := decode ss.init B (proj c)
  decodePair c := decode ss.pair B (proj c)
  decodeF c := decode ss.f B (proj c)
  decodeChal c := decode ss.chal B (proj c)
  decodeQuery c := decode ss.query B (proj c)

/-- Reading through an injection does not raise preimage counts. -/
theorem card_comp_le {C α : Type} [Fintype C] {B : ℕ} {proj : C → Stream B}
    (hproj : Function.Injective proj) (f : Stream B → α) (a : α) :
    (univ.filter fun c : C => f (proj c) = a).card
      ≤ (univ.filter fun s : Stream B => f s = a).card :=
  card_le_card_of_injOn proj (fun c hc => by simpa using hc) (fun _ _ _ _ h => hproj h)

/-- **Each stream decoder through an injection has at most `kOf` preimages per value.** -/
theorem decode_comp_le_kOf {C α : Type} [Fintype C] [Fintype α] [Nonempty α] {B : ℕ}
    {proj : C → Stream B} (hproj : Function.Injective proj) {p : Sampler α} (hp : p.Local)
    (hb : p.Balanced) (a : α) :
    (univ.filter fun c : C => decode p B (proj c) = a).card ≤ kOf p B :=
  (card_comp_le hproj (decode p B) a).trans (decode_le_kOf hp hb a)

end Lfzk.StreamDecoders
