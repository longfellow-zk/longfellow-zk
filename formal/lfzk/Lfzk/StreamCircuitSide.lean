import Lfzk.CompiledZkProfileK
import Lfzk.IdealCipherStream

/-!
# The v7 pairs with Rust's samplers on AES-CTR streams

`Lfzk.CompiledZkProfileK.v7P256Sha{1..4}_zk_circuit_tsecK` needs, per side, decoders balanced up
to a virtual card `K` with `K / |C| ≤ 1 + 2^-40`.  This file constructs them: a `StreamSide` is
a side's circuit and verifier data **without** decoders, plus the deployed samplers
(`Lfzk.StreamDecoders.deployedSlots`: `begin_circuit`+`begin_layer`, `begin_layer`, `elt_field`,
the Ligero combination, `choose`), and `StreamSide.toK` is the `CircuitSideK` whose five decoders are
those samplers on the stream (`StreamDecoders.withStreams`), with the round-robin fallback where Rust
would panic, and

* `kinit … kq` the samplers' preimage bounds (`StreamDecoders.kOf`), `hbal…` theorems
  (`decode_comp_le_kOf`, from `StreamSampler`'s exact balance);
* `hk…` theorems at `K = |Stream B| + 2^(256 W)` (`kOf_mul_le`), `W` a common width with
  `logv + 2 ≤ W`, `m ≤ W` (the Ligero combination's length in field elements) and `n ≤ 256 W`.

The decoder-balance premise is a theorem, **relative to a uniform stream per slot** (Part A), and
relative to a uniform *injective* block tuple per slot (Part B, the ideal cipher):

* `v7P256Sha{1..4}_zk_stream_tsec` — the raw challenge alphabet is `Stream B` (`B` blocks of 16
  bytes): `(1 + tA + N) · 2^-115`, under the room condition `256 W + 40 ≤ 128 B`;
* `v7P256Sha{1..4}_zk_icstream_tsec` — the raw challenge alphabet is `InjStream B` (injective
  `B`-tuples of blocks), the stream of a fresh key under an ideal cipher
  (`IdealCipherStream.ctrFn_fiber_card`): `(1 + tA + N) · 2^-115`, under `256 W + 41 ≤ 128 B` and
  `B(B−1)/2^129 ≤ 2^-49` (Rust's `B = 2^40`).  The factor `K / |InjStream B|` absorbs both the
  fallback (`+ 2^(256 W)`) and the injectivity inflation (`IdealCipherStream.lam_inj_le`).

At Rust's `B = MAX_PRF_BLOCKS = 2^40` the room conditions hold for every `W ≤ 2^38`; the deployed
widths are a few thousand at most.  Rust panics exactly where a sampler runs out, so the deployed
verifier accepts only on streams where the decoders agree with Rust's samplers; the fallback never
helps the deployed prover.

## What is still a hypothesis

* As in `CompiledZkProfileRows`: the circuits and verifier code (`WellFormedP`, `Isolated`,
  `DeadEnd`, `CodeAgreesP`, …), the MAC rows; the representation bijections of the fields
  (`FieldSampler.e`) and the layout map `chalOf` from Rust's combination vector to the model's
  challenge (equal fibres only);
* the **oracle model**: in `_stream_tsec` a uniformly random function from hash inputs to streams;
  in `_icstream_tsec` a uniformly random function to injective tuples.  The latter is the
  composite `prefix ↦ AES-CTR_{SHA256(prefix)}` under SHA-256 as a random oracle and AES-256 as an
  ideal cipher **up to the collision events** — two relevant prefixes sharing a key
  (`IdealCipherStream.card_collide_le`, `(N + L)² / 2^257`) and a relevant key queried to the cipher
  before it was hashed (`IdealCipherStream.card_key_mem`, `Q_E (N + L) / 2^256`).  That adaptive
  game hop is not formalised (`IdealCipherStream`'s docstring); its non-adaptive form is
  `IdealCipherStream.composite_le`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.StreamCircuitSide

open Finset Bcs Bcs.AdaptiveCommit Merkle Merkle.MH Merkle.RandomOracle
  Merkle.RandomOracle.TwoOracleTree RbrLongfellow Lfzk.RbrZkLongfellow Lfzk.RbrZkSplit Lfzk.NizkZk
  Lfzk.ZkLigeroV1 Lfzk.CompiledZk Lfzk.CertifiedV1 Lfzk.Arith Lfzk.ZkArithProfile
  Lfzk.ZkArithInit Lfzk.ZkVirtualCard Lfzk.CompiledZkDeployedHash Lfzk.CompiledZkProfileK
  Lfzk.StreamSampler Lfzk.StreamDecoders Lfzk.IdealCipherStream Lfzk.Mac
open Lfzk.CompiledLongfellow (Col guarded v1K)
open Lfzk.CompiledLongfellowAdaptive (Sig slice1 slice2)
open Lfzk.NizkAdaptiveTwoField (check2 len2)
open Lfzk.NizkDeployedHashTwoField (Pt2 setup2 sideCtx)
open scoped Classical

/-! ## 1. Sizes -/

section Sizes

variable {F : Type} [Fintype F]

theorem pow_le_two_pow {a b W : ℕ} (ha : a ≤ 2 ^ 256) (hb : b ≤ W) : a ^ b ≤ 2 ^ (256 * W) :=
  calc a ^ b ≤ (2 ^ 256) ^ b := Nat.pow_le_pow_left ha b
    _ = 2 ^ (256 * b) := by rw [← pow_mul]
    _ ≤ 2 ^ (256 * W) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem card_init {logv : ℕ} :
    Fintype.card ((Fin logv → F) × F × F) = Fintype.card F ^ (logv + 2) := by
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  ring

/-- **A layout map with equal fibres is onto**, so the model's challenge has at most `|F|^m`
values. -/
theorem card_le_of_fibers {X : Type} [Fintype X] [DecidableEq X] [Nonempty F] {m : ℕ}
    (chalOf : (Fin m → F) → X)
    (hchal : ∀ x x', (univ.filter fun v => chalOf v = x).card
      = (univ.filter fun v => chalOf v = x').card) :
    Fintype.card X ≤ Fintype.card F ^ m := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · simp [Fintype.card_eq_zero]
  · have hsum : ∑ x : X, (univ.filter fun v => chalOf v = x).card = Fintype.card (Fin m → F) := by
      rw [← Finset.card_univ (α := Fin m → F), ← card_biUnion]
      · congr 1; ext v; simp
      · intro x _ x' _ hne
        simp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro v h h'
        simp only [mem_filter] at h h'
        exact hne (h.2.symm.trans h'.2)
    rw [sum_congr rfl fun x _ => hchal x x₀, sum_const, card_univ, smul_eq_mul] at hsum
    have hf : 0 < (univ.filter fun v => chalOf v = x₀).card := by
      by_contra h0
      push Not at h0
      have : (univ.filter fun v => chalOf v = x₀).card = 0 := by omega
      rw [this, mul_zero] at hsum
      have : 0 < Fintype.card (Fin m → F) := Fintype.card_pos
      omega
    rw [Fintype.card_fun, Fintype.card_fin] at hsum
    calc Fintype.card X ≤ Fintype.card X * (univ.filter fun v => chalOf v = x₀).card :=
          Nat.le_mul_of_pos_right _ hf
      _ = Fintype.card F ^ m := hsum

end Sizes

/-- **The `CircuitSide` decoder fields cannot be met on streams at the P-256 base field**: no
decoder `Stream B → F` with `|F| = p256` (odd) has every value hit at most `k` times with
`k · |F| ≤ |Stream B|` (`StreamDecoders.no_exact_decoder_odd`).  This is why the stream decoders
are packaged as a `CircuitSideK`. -/
theorem no_exact_stream_decoder_p256 {B : ℕ} {F : Type} [Fintype F]
    (hF : Fintype.card F = Lfzk.LigeroV1Rows.p256Order) (d : StreamDecoders.Stream B → F) (k : ℕ)
    (hb : ∀ y, (univ.filter fun c => d c = y).card ≤ k) :
    ¬ k * Fintype.card F ≤ Fintype.card (StreamDecoders.Stream B) :=
  no_exact_decoder_odd (by rw [hF]; decide) (by rw [hF]; decide) d k hb

/-! ## 2. A side read on streams -/

/--
**A side's data apart from its decoders, with the deployed samplers.**  The verifier's computation
`V₀` (its own coin decoders are discarded), the circuit facts, and: the field's sampler `fs`,
`begin_circuit`'s slice length `maxLogw`, the Ligero combination's length `m` and layout map
`chalOf` (equal fibres), and how the raw challenge alphabet reads as a stream (`proj`, injective).
-/
structure StreamSide (R : Row) (hR : R.Valid) (hr : 0 < R.params.row.openings) (logv : ℕ)
    (C : Type) [Fintype C] (F Msg : Type) [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    (M nt nlin : ℕ) {Enc D Salt : Type} [Inhabited D] [DecidableEq D] [DecidableEq Enc]
    [Inhabited Salt] (X : Type) {codec : Codec Salt (Col F R.params.nw R.params.nq) D Enc}
    (dec : RoleDecoders codec) (rootOfKey : D × D → D) (B : ℕ) where
  /-- The circuit, in the deployed format. -/
  c : QuadCircuit F
  hnl : c.nl = R.params.nl
  /-- The container dimension. -/
  L : ℕ
  hwf : WellFormedP c logv R.params.logw L
  hiso : c.Isolated
  hde : c.DeadEnd
  /-- The public input at the MAC-key share and the public data. -/
  pubIn : C → X → Fin c.ninp → F
  /-- The placement of the built system into the tableau. -/
  pl : Encode.Placement c.ninp M R.params.q R.params.nw R.params.nq nt
  /-- The code's evaluation domain. -/
  dom : LigeroFamily.ReedSolomon.Domain F R.params.row.openings R.params.q R.params.row.n
  /-- The verifier's computation at the MAC-key share and the public data (its decoders are
  replaced by the stream decoders). -/
  V₀ : C → X → ZkCode C F (ZkLigeroV1.Chal F R.params.nw R.params.nq nlin nt)
    (LigeroV1LayerStep.Qry R.params.row) Msg (Fin logv → F) M c.ninp L 0
  hnlin : ∀ a x, (V₀ a x).nlin = nlin
  hnt : ∀ a x, (V₀ a x).nt = nt
  hV : ∀ a x, CodeAgreesP c (pubIn a x) L (V₀ a x)
  hst0 : ∀ a x G, ((V₀ a x).st0 G).g0 = padG L G ∧ ((V₀ a x).st0 G).g1 = padG L G
  /-- How a message carries the side's Ligero response. -/
  respOf : Msg → LigeroFamily.Response F R.params.row.openings R.params.q R.params.row.n 1
  hF : Fintype.card F = R.params.row.fieldSize
  hF256 : Fintype.card F ≤ 2 ^ 256
  /-- The field's deployed sampler. -/
  fs : FieldSampler F
  /-- `begin_circuit`'s slice length (`MAX_LOGW`). -/
  maxLogw : ℕ
  hlog : logv ≤ maxLogw
  /-- The Ligero combination's length in field elements, and its layout in the model's
  challenge. -/
  m : ℕ
  chalOf : (Fin m → F) → ZkLigeroV1.Chal F R.params.nw R.params.nq nlin nt
  hchal : ∀ x x', (univ.filter fun v => chalOf v = x).card
    = (univ.filter fun v => chalOf v = x').card
  hnr : R.params.row.openings ≤ R.params.row.n
  /-- How the raw challenge alphabet reads as one key's stream. -/
  proj : C → Stream B
  hproj : Function.Injective proj

theorem qset_nonempty {n r : ℕ} (h : r ≤ n) : Nonempty (QSet n r) :=
  LigeroFamily.QuerySet.nonempty h

namespace StreamSide

variable {R : Row} {hR : R.Valid} {hr : 0 < R.params.row.openings} {logv : ℕ}
variable {C : Type} [Fintype C] {F Msg : Type} [Field F] [Fintype F] [DecidableEq F]
  [SumcheckInterp F] {M nt nlin : ℕ}
variable {Enc D Salt : Type} [Inhabited D] [DecidableEq D] [DecidableEq Enc] [Inhabited Salt]
variable {X : Type} {codec : Codec Salt (Col F R.params.nw R.params.nq) D Enc}
  {dec : RoleDecoders codec} {rootOfKey : D × D → D} {B : ℕ}
variable (S : StreamSide R hR hr logv C F Msg M nt nlin X dec rootOfKey B)

/-- The side's five deployed slot samplers. -/
noncomputable def slots : SlotSamplers F (ZkLigeroV1.Chal F R.params.nw R.params.nq nlin nt)
    (QSet R.params.row.n R.params.row.openings) (Fin logv → F) :=
  deployedSlots S.fs S.maxLogw logv S.hlog S.m S.chalOf S.hchal R.params.row.n
    R.params.row.openings S.hnr


/-- **The side's verifier code with the stream decoders.** -/
noncomputable def Vc (a : C) (x : X) : ZkCode C F (ZkLigeroV1.Chal F R.params.nw R.params.nq nlin nt)
    (LigeroV1LayerStep.Qry R.params.row) Msg (Fin logv → F) M S.c.ninp S.L 0 :=
  haveI := qset_nonempty S.hnr
  withStreams (S.V₀ a x) B S.slots S.proj

/-- The width condition of a side at a common width `W`. -/
def Room (W : ℕ) : Prop := logv + 2 ≤ W ∧ S.m ≤ W ∧ R.params.row.n ≤ 256 * W

/-- **The `CircuitSideK` a stream side is**, at the virtual card `|Stream B| + 2^(256 W)`. -/
noncomputable def toK (W : ℕ) (hW : S.Room W) :
    CircuitSideK R hR hr logv C F Msg M nt nlin X dec rootOfKey
      (Fintype.card (Stream B) + 2 ^ (256 * W)) := by
  haveI := qset_nonempty S.hnr
  exact
  { c := S.c
    hnl := S.hnl
    L := S.L
    hwf := S.hwf
    hiso := S.hiso
    hde := S.hde
    pubIn := S.pubIn
    pl := S.pl
    dom := S.dom
    Vc := S.Vc
    hnlin := S.hnlin
    hnt := S.hnt
    hV := fun a x => ⟨(S.hV a x).hst, (S.hV a x).heqq, (S.hV a x).hnpub, (S.hV a x).hinC,
      (S.hV a x).hpubB⟩
    hst0 := S.hst0
    respOf := S.respOf
    kinit := kOf S.slots.init B
    kpair := kOf S.slots.pair B
    k := kOf S.slots.f B
    kchal := kOf S.slots.chal B
    kq := kOf S.slots.query B
    hbalInit := fun _ _ y => by
      convert decode_comp_le_kOf S.hproj S.slots.init_local S.slots.init_bal y using 3
      exact Iff.rfl
    hbalPair := fun _ _ y => by
      convert decode_comp_le_kOf S.hproj S.slots.pair_local S.slots.pair_bal y using 3
      exact Iff.rfl
    hbalF := fun _ _ y => by
      convert decode_comp_le_kOf S.hproj S.slots.f_local S.slots.f_bal y using 3
      exact Iff.rfl
    hbalChal := fun _ _ y => by
      convert decode_comp_le_kOf S.hproj S.slots.chal_local S.slots.chal_bal y using 3
      exact Iff.rfl
    hbalQuery := fun _ _ y => by
      convert decode_comp_le_kOf S.hproj S.slots.query_local S.slots.query_bal y using 3
      exact Iff.rfl
    hkinit := by
      have h := kOf_mul_le (B := B) S.slots.init_local S.slots.init_bal
      rw [card_init] at h
      exact h.trans (Nat.add_le_add_left (pow_le_two_pow S.hF256 hW.1) _)
    hkpair := by
      have h := kOf_mul_le (B := B) S.slots.pair_local S.slots.pair_bal
      rw [Fintype.card_prod] at h
      refine h.trans (Nat.add_le_add_left ?_ _)
      have hW2 : 2 ≤ W := by have := hW.1; omega
      have := pow_le_two_pow (a := Fintype.card F) (b := 2) (W := W) S.hF256 hW2
      rw [pow_two] at this
      exact this
    hk := by
      have h := kOf_mul_le (B := B) S.slots.f_local S.slots.f_bal
      refine h.trans (Nat.add_le_add_left ?_ _)
      have hW1 : 1 ≤ W := by have := hW.1; omega
      have := pow_le_two_pow (a := Fintype.card F) (b := 1) (W := W) S.hF256 hW1
      rw [pow_one] at this
      exact this
    hkchal := by
      have h := kOf_mul_le (B := B) S.slots.chal_local S.slots.chal_bal
      refine h.trans (Nat.add_le_add_left ?_ _)
      exact (card_le_of_fibers S.chalOf S.hchal).trans (pow_le_two_pow S.hF256 hW.2.1)
    hkq := by
      have h := kOf_mul_le (B := B) S.slots.query_local S.slots.query_bal
      refine h.trans (Nat.add_le_add_left ?_ _)
      show Fintype.card (QSet R.params.row.n R.params.row.openings) ≤ _
      rw [Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
      exact (Nat.choose_le_two_pow _ _).trans
        (Nat.pow_le_pow_right (by norm_num) (by have := hW.2.2; omega))
    hF := S.hF }

end StreamSide

/-! ## 3. The MAC-key share and the virtual card -/

/-- **The MAC-key share decoder** (`bytes(16)`, little-endian), through `proj`. -/
noncomputable def macDecode {C Fmac : Type} [Fintype Fmac] [Nonempty Fmac] {B : ℕ}
    (e : Fin (2 ^ 128) ≃ Fmac) (proj : C → Stream B) : C → Fmac :=
  fun c => decode (macS e) B (proj c)

theorem macDecode_le {C Fmac : Type} [Fintype C] [Fintype Fmac] [Nonempty Fmac] [DecidableEq Fmac]
    {B : ℕ} (e : Fin (2 ^ 128) ≃ Fmac) {proj : C → Stream B} (hproj : Function.Injective proj)
    (x : Fmac) :
    (univ.filter fun c : C => macDecode e proj c = x).card ≤ kOf (macS e) B := by
  convert decode_comp_le_kOf hproj (macS_local e) (macS_balanced e) x using 3
  exact Iff.rfl

theorem macK_le {Fmac : Type} [Fintype Fmac] [Nonempty Fmac] {B W : ℕ} (e : Fin (2 ^ 128) ≃ Fmac)
    (hW : 1 ≤ W) :
    kOf (macS e) B * Fintype.card Fmac ≤ Fintype.card (Stream B) + 2 ^ (256 * W) := by
  refine (kOf_mul_le (macS_local e) (macS_balanced e)).trans (Nat.add_le_add_left ?_ _)
  rw [← Fintype.card_congr e, Fintype.card_fin]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **On streams**: `(|Stream B| + 2^(256 W)) / |Stream B| ≤ 1 + 2^-40` when `256 W + 40 ≤ 128 B`. -/
theorem lam_stream_le {B W : ℕ} (hroom : 256 * W + 40 ≤ 128 * B) :
    ((Fintype.card (Stream B) + 2 ^ (256 * W) : ℕ) : ℚ) / (Fintype.card (Stream B) : ℚ) ≤ lam₀ := by
  have hA := card_all B
  have hApos : (0 : ℚ) < Fintype.card (Stream B) := by exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hApos, lam₀]
  push_cast
  have h2 : (2 : ℚ) ^ (256 * W) * 2 ^ 40 ≤ Fintype.card (Stream B) := by
    rw [hA, ← pow_mul, ← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have : (2 : ℚ) ^ (256 * W) ≤ Fintype.card (Stream B) * (1 / 2 ^ 40) := by
    rw [mul_one_div, le_div_iff₀ (by positivity)]; exact h2
  linarith

/-- **On injective block tuples** (the ideal-cipher stream):
`(|Stream B| + 2^(256 W)) / |InjStream B| ≤ 1 + 2^-40` when `256 W + 41 ≤ 128 B` and
`B(B−1)/2^129 ≤ 2^-49`. -/
theorem lam_icstream_le {B W : ℕ} (hroom : 256 * W + 41 ≤ 128 * B) (hB : B ≤ 2 ^ 128 + 1)
    (hδ : ((B * (B - 1) : ℕ) : ℚ) / 2 ^ 129 ≤ 1 / 2 ^ 49) :
    ((Fintype.card (Stream B) + 2 ^ (256 * W) : ℕ) : ℚ) / (Fintype.card (InjStream B) : ℚ)
      ≤ lam₀ := by
  refine lam_inj_le B _ hB hδ ?_
  have hA := card_stream B
  rw [hA, show (256 : ℕ) ^ (B * 16) = 2 ^ (128 * B) by rw [mul_comm B 16, pow_mul, pow_mul]; norm_num,
    ← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- At Rust's `MAX_PRF_BLOCKS = 2^40`. -/
theorem B40_facts : (2 ^ 40 : ℕ) ≤ 2 ^ 128 + 1 ∧
    ((((2 ^ 40 : ℕ) * ((2 ^ 40 : ℕ) - 1) : ℕ) : ℚ)) / 2 ^ 129 ≤ 1 / 2 ^ 49 := by
  refine ⟨by norm_num, ?_⟩
  norm_num

open Lfzk.TwoFieldV1Rows

/-! ## 4. The deployed v7 pairs, decoders the deployed samplers -/

section V7Streams

open Lfzk.TSec

variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {D : Type} [Fintype D] [DecidableEq D] [Inhabited D]
variable {Enc X Out : Type} [DecidableEq Enc] [Fintype X]
variable {Fmac : Type} [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {nblk : ℕ}
variable {F₁ Msg₁ : Type} [Field F₁] [Fintype F₁] [DecidableEq F₁] [SumcheckInterp F₁]
  [DecidableEq Msg₁] [Inhabited Msg₁] [Fintype Msg₁] {M₁ nt₁ nlin₁ : ℕ}
variable {F₂ Msg₂ : Type} [Field F₂] [Fintype F₂] [DecidableEq F₂] [SumcheckInterp F₂]
  [DecidableEq Msg₂] [Inhabited Msg₂] [Fintype Msg₂] {M₂ nt₂ nlin₂ : ℕ}
variable {Salt₁ Salt₂ : Type} [Inhabited Salt₁] [Inhabited Salt₂]

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**Two-field Longfellow at `v7P256Sha1`, the decoders Rust's samplers on a uniform stream of `B` AES blocks per slot, T-secure at `λ = 115`.**
Both sides' coin decoders are the deployed ones (`StreamSide.toK`: `begin_circuit`+`begin_layer`,
`begin_layer`, `elt_field`, the Ligero combination, `choose`, and `bytes(16)` for the MAC-key share),
so `CompiledZkProfileK.v7P256Sha1_zk_circuit_tsecK`'s decoder premises are discharged:

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧
    no hash-side and signature-side good witnesses agree on the MAC'd common value ]
    ≤  (1 + tA + N) · 2^-115
```
-/
theorem v7P256Sha1_zk_stream_tsec {tA N TM B W : ℕ} (hC : Fintype.card C = Fintype.card (StreamDecoders.Stream B))
    (hroom : 256 * W + 40 ≤ 128 * B)
    (hFmac : Fintype.card Fmac = 2 ^ 128) (eMac : Fin (2 ^ 128) ≃ Fmac)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha1.sha.params.nw v7P256Sha1.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha1.ecdsa.params.nw v7P256Sha1.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : StreamSide v7P256Sha1.sha (TwoFieldRowV1.sha_valid v7P256Sha1_valid) v7P256Sha1_sha_openings_pos 3
      (C) F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst B)
    (S₂ : StreamSide v7P256Sha1.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha1_valid) v7P256Sha1_ecdsa_openings_pos 8
      (C) F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd B)
    (hW₁ : S₁.Room W) (hW₂ : S₂.Room W)
    (body : TwoOracleTree Enc D (Pt2 D (C) X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds) (C) Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7P256Sha1.sha.params.row.n Salt₁
      (Col F₁ v7P256Sha1.sha.params.nw v7P256Sha1.sha.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7P256Sha1.ecdsa.params.row.n Salt₂
      (Col F₂ v7P256Sha1.ecdsa.params.nw v7P256Sha1.ecdsa.params.nq) D)
    (hD : Fintype.card D = 2 ^ v7P256Sha1.ecdsa.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D (C) X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds → C) (a : Fin S₁.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      (S₁.toK W hW₁).acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf
        pubOf (slice1 v7P256Sha1.sha v7P256Sha1.ecdsa) mt ro →
      (S₁.toK W hW₁).Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + macDecode eMac S₁.proj (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D (C) X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds → C) (a : Fin S₂.c.ninp → F₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      (S₂.toK W hW₂).acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf
        pubOf (slice2 v7P256Sha1.sha v7P256Sha1.ecdsa) mt ro →
      (S₂.toK W hW₂).Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + macDecode eMac S₁.proj (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₂ a) = tagOf (S.proof mt ro))
    (htape : 2 * v7P256Sha1.ecdsa.params.row.n + 2 * v7P256Sha1.sha.params.row.n + tA ≤ TM)
    (hTM : 0 < TM) :
    ((univ.filter fun ω : (Fin TM → D) ×
          (Pt2 D (C) X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds → C) =>
        (S₁.toK W hW₁).acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 v7P256Sha1.sha v7P256Sha1.ecdsa) ω.1 ω.2 ∧
          (S₂.toK W hW₂).acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 v7P256Sha1.sha v7P256Sha1.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            (S₁.toK W hW₁).Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₁ ∧
            (S₂.toK W hW₂).Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card (C) : ℚ) ^ Fintype.card
            (Pt2 D (C) X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds))
      ≤ (1 + N + tA : ℚ) / 2 ^ 115 := by
  exact v7P256Sha1_zk_circuit_tsecK (Nat.add_pos_right _ (Nat.two_pow_pos _)) (by rw [hC]; exact lam_stream_le hroom) hFmac (S₁.toK W hW₁) (S₂.toK W hW₂) body rootOf₁ rootOf₂
    avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂ hD aP (macDecode eMac S₁.proj) (kOf (macS eMac) B)
    (macDecode_le eMac S₁.hproj) (macK_le eMac (by have := hW₁.1; omega)) keyB tagOf common₁
    common₂ hrow₁ hrow₂ htape hTM

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**Two-field Longfellow at `v7P256Sha2`, the decoders Rust's samplers on a uniform stream of `B` AES blocks per slot, T-secure at `λ = 115`.**
Both sides' coin decoders are the deployed ones (`StreamSide.toK`: `begin_circuit`+`begin_layer`,
`begin_layer`, `elt_field`, the Ligero combination, `choose`, and `bytes(16)` for the MAC-key share),
so `CompiledZkProfileK.v7P256Sha2_zk_circuit_tsecK`'s decoder premises are discharged:

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧
    no hash-side and signature-side good witnesses agree on the MAC'd common value ]
    ≤  (1 + tA + N) · 2^-115
```
-/
theorem v7P256Sha2_zk_stream_tsec {tA N TM B W : ℕ} (hC : Fintype.card C = Fintype.card (StreamDecoders.Stream B))
    (hroom : 256 * W + 40 ≤ 128 * B)
    (hFmac : Fintype.card Fmac = 2 ^ 128) (eMac : Fin (2 ^ 128) ≃ Fmac)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha2.sha.params.nw v7P256Sha2.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha2.ecdsa.params.nw v7P256Sha2.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : StreamSide v7P256Sha2.sha (TwoFieldRowV1.sha_valid v7P256Sha2_valid) v7P256Sha2_sha_openings_pos 4
      (C) F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst B)
    (S₂ : StreamSide v7P256Sha2.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha2_valid) v7P256Sha2_ecdsa_openings_pos 8
      (C) F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd B)
    (hW₁ : S₁.Room W) (hW₂ : S₂.Room W)
    (body : TwoOracleTree Enc D (Pt2 D (C) X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds) (C) Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7P256Sha2.sha.params.row.n Salt₁
      (Col F₁ v7P256Sha2.sha.params.nw v7P256Sha2.sha.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7P256Sha2.ecdsa.params.row.n Salt₂
      (Col F₂ v7P256Sha2.ecdsa.params.nw v7P256Sha2.ecdsa.params.nq) D)
    (hD : Fintype.card D = 2 ^ v7P256Sha2.ecdsa.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D (C) X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds → C) (a : Fin S₁.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      (S₁.toK W hW₁).acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf
        pubOf (slice1 v7P256Sha2.sha v7P256Sha2.ecdsa) mt ro →
      (S₁.toK W hW₁).Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + macDecode eMac S₁.proj (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D (C) X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds → C) (a : Fin S₂.c.ninp → F₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      (S₂.toK W hW₂).acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf
        pubOf (slice2 v7P256Sha2.sha v7P256Sha2.ecdsa) mt ro →
      (S₂.toK W hW₂).Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + macDecode eMac S₁.proj (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₂ a) = tagOf (S.proof mt ro))
    (htape : 2 * v7P256Sha2.ecdsa.params.row.n + 2 * v7P256Sha2.sha.params.row.n + tA ≤ TM)
    (hTM : 0 < TM) :
    ((univ.filter fun ω : (Fin TM → D) ×
          (Pt2 D (C) X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds → C) =>
        (S₁.toK W hW₁).acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 v7P256Sha2.sha v7P256Sha2.ecdsa) ω.1 ω.2 ∧
          (S₂.toK W hW₂).acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 v7P256Sha2.sha v7P256Sha2.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            (S₁.toK W hW₁).Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₁ ∧
            (S₂.toK W hW₂).Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card (C) : ℚ) ^ Fintype.card
            (Pt2 D (C) X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds))
      ≤ (1 + N + tA : ℚ) / 2 ^ 115 := by
  exact v7P256Sha2_zk_circuit_tsecK (Nat.add_pos_right _ (Nat.two_pow_pos _)) (by rw [hC]; exact lam_stream_le hroom) hFmac (S₁.toK W hW₁) (S₂.toK W hW₂) body rootOf₁ rootOf₂
    avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂ hD aP (macDecode eMac S₁.proj) (kOf (macS eMac) B)
    (macDecode_le eMac S₁.hproj) (macK_le eMac (by have := hW₁.1; omega)) keyB tagOf common₁
    common₂ hrow₁ hrow₂ htape hTM

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**Two-field Longfellow at `v7P256Sha3`, the decoders Rust's samplers on a uniform stream of `B` AES blocks per slot, T-secure at `λ = 115`.**
Both sides' coin decoders are the deployed ones (`StreamSide.toK`: `begin_circuit`+`begin_layer`,
`begin_layer`, `elt_field`, the Ligero combination, `choose`, and `bytes(16)` for the MAC-key share),
so `CompiledZkProfileK.v7P256Sha3_zk_circuit_tsecK`'s decoder premises are discharged:

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧
    no hash-side and signature-side good witnesses agree on the MAC'd common value ]
    ≤  (1 + tA + N) · 2^-115
```
-/
theorem v7P256Sha3_zk_stream_tsec {tA N TM B W : ℕ} (hC : Fintype.card C = Fintype.card (StreamDecoders.Stream B))
    (hroom : 256 * W + 40 ≤ 128 * B)
    (hFmac : Fintype.card Fmac = 2 ^ 128) (eMac : Fin (2 ^ 128) ≃ Fmac)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha3.sha.params.nw v7P256Sha3.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha3.ecdsa.params.nw v7P256Sha3.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : StreamSide v7P256Sha3.sha (TwoFieldRowV1.sha_valid v7P256Sha3_valid) v7P256Sha3_sha_openings_pos 4
      (C) F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst B)
    (S₂ : StreamSide v7P256Sha3.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha3_valid) v7P256Sha3_ecdsa_openings_pos 8
      (C) F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd B)
    (hW₁ : S₁.Room W) (hW₂ : S₂.Room W)
    (body : TwoOracleTree Enc D (Pt2 D (C) X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds) (C) Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7P256Sha3.sha.params.row.n Salt₁
      (Col F₁ v7P256Sha3.sha.params.nw v7P256Sha3.sha.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7P256Sha3.ecdsa.params.row.n Salt₂
      (Col F₂ v7P256Sha3.ecdsa.params.nw v7P256Sha3.ecdsa.params.nq) D)
    (hD : Fintype.card D = 2 ^ v7P256Sha3.ecdsa.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D (C) X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds → C) (a : Fin S₁.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      (S₁.toK W hW₁).acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf
        pubOf (slice1 v7P256Sha3.sha v7P256Sha3.ecdsa) mt ro →
      (S₁.toK W hW₁).Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + macDecode eMac S₁.proj (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D (C) X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds → C) (a : Fin S₂.c.ninp → F₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      (S₂.toK W hW₂).acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf
        pubOf (slice2 v7P256Sha3.sha v7P256Sha3.ecdsa) mt ro →
      (S₂.toK W hW₂).Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + macDecode eMac S₁.proj (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₂ a) = tagOf (S.proof mt ro))
    (htape : 2 * v7P256Sha3.ecdsa.params.row.n + 2 * v7P256Sha3.sha.params.row.n + tA ≤ TM)
    (hTM : 0 < TM) :
    ((univ.filter fun ω : (Fin TM → D) ×
          (Pt2 D (C) X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds → C) =>
        (S₁.toK W hW₁).acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 v7P256Sha3.sha v7P256Sha3.ecdsa) ω.1 ω.2 ∧
          (S₂.toK W hW₂).acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 v7P256Sha3.sha v7P256Sha3.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            (S₁.toK W hW₁).Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₁ ∧
            (S₂.toK W hW₂).Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card (C) : ℚ) ^ Fintype.card
            (Pt2 D (C) X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds))
      ≤ (1 + N + tA : ℚ) / 2 ^ 115 := by
  exact v7P256Sha3_zk_circuit_tsecK (Nat.add_pos_right _ (Nat.two_pow_pos _)) (by rw [hC]; exact lam_stream_le hroom) hFmac (S₁.toK W hW₁) (S₂.toK W hW₂) body rootOf₁ rootOf₂
    avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂ hD aP (macDecode eMac S₁.proj) (kOf (macS eMac) B)
    (macDecode_le eMac S₁.hproj) (macK_le eMac (by have := hW₁.1; omega)) keyB tagOf common₁
    common₂ hrow₁ hrow₂ htape hTM

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**Two-field Longfellow at `v7P256Sha4`, the decoders Rust's samplers on a uniform stream of `B` AES blocks per slot, T-secure at `λ = 115`.**
Both sides' coin decoders are the deployed ones (`StreamSide.toK`: `begin_circuit`+`begin_layer`,
`begin_layer`, `elt_field`, the Ligero combination, `choose`, and `bytes(16)` for the MAC-key share),
so `CompiledZkProfileK.v7P256Sha4_zk_circuit_tsecK`'s decoder premises are discharged:

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧
    no hash-side and signature-side good witnesses agree on the MAC'd common value ]
    ≤  (1 + tA + N) · 2^-115
```
-/
theorem v7P256Sha4_zk_stream_tsec {tA N TM B W : ℕ} (hC : Fintype.card C = Fintype.card (StreamDecoders.Stream B))
    (hroom : 256 * W + 40 ≤ 128 * B)
    (hFmac : Fintype.card Fmac = 2 ^ 128) (eMac : Fin (2 ^ 128) ≃ Fmac)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha4.sha.params.nw v7P256Sha4.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha4.ecdsa.params.nw v7P256Sha4.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : StreamSide v7P256Sha4.sha (TwoFieldRowV1.sha_valid v7P256Sha4_valid) v7P256Sha4_sha_openings_pos 5
      (C) F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst B)
    (S₂ : StreamSide v7P256Sha4.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha4_valid) v7P256Sha4_ecdsa_openings_pos 8
      (C) F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd B)
    (hW₁ : S₁.Room W) (hW₂ : S₂.Room W)
    (body : TwoOracleTree Enc D (Pt2 D (C) X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds) (C) Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7P256Sha4.sha.params.row.n Salt₁
      (Col F₁ v7P256Sha4.sha.params.nw v7P256Sha4.sha.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7P256Sha4.ecdsa.params.row.n Salt₂
      (Col F₂ v7P256Sha4.ecdsa.params.nw v7P256Sha4.ecdsa.params.nq) D)
    (hD : Fintype.card D = 2 ^ v7P256Sha4.ecdsa.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D (C) X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds → C) (a : Fin S₁.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      (S₁.toK W hW₁).acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf
        pubOf (slice1 v7P256Sha4.sha v7P256Sha4.ecdsa) mt ro →
      (S₁.toK W hW₁).Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + macDecode eMac S₁.proj (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D (C) X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds → C) (a : Fin S₂.c.ninp → F₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      (S₂.toK W hW₂).acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf
        pubOf (slice2 v7P256Sha4.sha v7P256Sha4.ecdsa) mt ro →
      (S₂.toK W hW₂).Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + macDecode eMac S₁.proj (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₂ a) = tagOf (S.proof mt ro))
    (htape : 2 * v7P256Sha4.ecdsa.params.row.n + 2 * v7P256Sha4.sha.params.row.n + tA ≤ TM)
    (hTM : 0 < TM) :
    ((univ.filter fun ω : (Fin TM → D) ×
          (Pt2 D (C) X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds → C) =>
        (S₁.toK W hW₁).acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 v7P256Sha4.sha v7P256Sha4.ecdsa) ω.1 ω.2 ∧
          (S₂.toK W hW₂).acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 v7P256Sha4.sha v7P256Sha4.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            (S₁.toK W hW₁).Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₁ ∧
            (S₂.toK W hW₂).Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card (C) : ℚ) ^ Fintype.card
            (Pt2 D (C) X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds))
      ≤ (1 + N + tA : ℚ) / 2 ^ 115 := by
  exact v7P256Sha4_zk_circuit_tsecK (Nat.add_pos_right _ (Nat.two_pow_pos _)) (by rw [hC]; exact lam_stream_le hroom) hFmac (S₁.toK W hW₁) (S₂.toK W hW₂) body rootOf₁ rootOf₂
    avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂ hD aP (macDecode eMac S₁.proj) (kOf (macS eMac) B)
    (macDecode_le eMac S₁.hproj) (macK_le eMac (by have := hW₁.1; omega)) keyB tagOf common₁
    common₂ hrow₁ hrow₂ htape hTM

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**Two-field Longfellow at `v7P256Sha1`, the decoders Rust's samplers on the ideal-cipher stream of `B` AES blocks per slot (a uniform injective block tuple), T-secure at `λ = 115`.**
Both sides' coin decoders are the deployed ones (`StreamSide.toK`: `begin_circuit`+`begin_layer`,
`begin_layer`, `elt_field`, the Ligero combination, `choose`, and `bytes(16)` for the MAC-key share),
so `CompiledZkProfileK.v7P256Sha1_zk_circuit_tsecK`'s decoder premises are discharged:

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧
    no hash-side and signature-side good witnesses agree on the MAC'd common value ]
    ≤  (1 + tA + N) · 2^-115
```
-/
theorem v7P256Sha1_zk_icstream_tsec {tA N TM B W : ℕ} (hC : Fintype.card C = Fintype.card (InjStream B))
    (hroom : 256 * W + 41 ≤ 128 * B) (hB : B ≤ 2 ^ 128)
    (hδ : ((B * (B - 1) : ℕ) : ℚ) / 2 ^ 129 ≤ 1 / 2 ^ 49)
    (hFmac : Fintype.card Fmac = 2 ^ 128) (eMac : Fin (2 ^ 128) ≃ Fmac)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha1.sha.params.nw v7P256Sha1.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha1.ecdsa.params.nw v7P256Sha1.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : StreamSide v7P256Sha1.sha (TwoFieldRowV1.sha_valid v7P256Sha1_valid) v7P256Sha1_sha_openings_pos 3
      (C) F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst B)
    (S₂ : StreamSide v7P256Sha1.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha1_valid) v7P256Sha1_ecdsa_openings_pos 8
      (C) F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd B)
    (hW₁ : S₁.Room W) (hW₂ : S₂.Room W)
    (body : TwoOracleTree Enc D (Pt2 D (C) X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds) (C) Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7P256Sha1.sha.params.row.n Salt₁
      (Col F₁ v7P256Sha1.sha.params.nw v7P256Sha1.sha.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7P256Sha1.ecdsa.params.row.n Salt₂
      (Col F₂ v7P256Sha1.ecdsa.params.nw v7P256Sha1.ecdsa.params.nq) D)
    (hD : Fintype.card D = 2 ^ v7P256Sha1.ecdsa.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D (C) X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds → C) (a : Fin S₁.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      (S₁.toK W hW₁).acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf
        pubOf (slice1 v7P256Sha1.sha v7P256Sha1.ecdsa) mt ro →
      (S₁.toK W hW₁).Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + macDecode eMac S₁.proj (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D (C) X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds → C) (a : Fin S₂.c.ninp → F₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      (S₂.toK W hW₂).acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf
        pubOf (slice2 v7P256Sha1.sha v7P256Sha1.ecdsa) mt ro →
      (S₂.toK W hW₂).Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + macDecode eMac S₁.proj (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₂ a) = tagOf (S.proof mt ro))
    (htape : 2 * v7P256Sha1.ecdsa.params.row.n + 2 * v7P256Sha1.sha.params.row.n + tA ≤ TM)
    (hTM : 0 < TM) :
    ((univ.filter fun ω : (Fin TM → D) ×
          (Pt2 D (C) X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds → C) =>
        (S₁.toK W hW₁).acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 v7P256Sha1.sha v7P256Sha1.ecdsa) ω.1 ω.2 ∧
          (S₂.toK W hW₂).acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 v7P256Sha1.sha v7P256Sha1.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            (S₁.toK W hW₁).Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₁ ∧
            (S₂.toK W hW₂).Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card (C) : ℚ) ^ Fintype.card
            (Pt2 D (C) X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds))
      ≤ (1 + N + tA : ℚ) / 2 ^ 115 := by
  exact v7P256Sha1_zk_circuit_tsecK (Nat.add_pos_right _ (Nat.two_pow_pos _)) (by rw [hC]; exact lam_icstream_le hroom (by omega) hδ) hFmac (S₁.toK W hW₁) (S₂.toK W hW₂) body rootOf₁ rootOf₂
    avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂ hD aP (macDecode eMac S₁.proj) (kOf (macS eMac) B)
    (macDecode_le eMac S₁.hproj) (macK_le eMac (by have := hW₁.1; omega)) keyB tagOf common₁
    common₂ hrow₁ hrow₂ htape hTM

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**Two-field Longfellow at `v7P256Sha2`, the decoders Rust's samplers on the ideal-cipher stream of `B` AES blocks per slot (a uniform injective block tuple), T-secure at `λ = 115`.**
Both sides' coin decoders are the deployed ones (`StreamSide.toK`: `begin_circuit`+`begin_layer`,
`begin_layer`, `elt_field`, the Ligero combination, `choose`, and `bytes(16)` for the MAC-key share),
so `CompiledZkProfileK.v7P256Sha2_zk_circuit_tsecK`'s decoder premises are discharged:

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧
    no hash-side and signature-side good witnesses agree on the MAC'd common value ]
    ≤  (1 + tA + N) · 2^-115
```
-/
theorem v7P256Sha2_zk_icstream_tsec {tA N TM B W : ℕ} (hC : Fintype.card C = Fintype.card (InjStream B))
    (hroom : 256 * W + 41 ≤ 128 * B) (hB : B ≤ 2 ^ 128)
    (hδ : ((B * (B - 1) : ℕ) : ℚ) / 2 ^ 129 ≤ 1 / 2 ^ 49)
    (hFmac : Fintype.card Fmac = 2 ^ 128) (eMac : Fin (2 ^ 128) ≃ Fmac)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha2.sha.params.nw v7P256Sha2.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha2.ecdsa.params.nw v7P256Sha2.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : StreamSide v7P256Sha2.sha (TwoFieldRowV1.sha_valid v7P256Sha2_valid) v7P256Sha2_sha_openings_pos 4
      (C) F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst B)
    (S₂ : StreamSide v7P256Sha2.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha2_valid) v7P256Sha2_ecdsa_openings_pos 8
      (C) F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd B)
    (hW₁ : S₁.Room W) (hW₂ : S₂.Room W)
    (body : TwoOracleTree Enc D (Pt2 D (C) X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds) (C) Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7P256Sha2.sha.params.row.n Salt₁
      (Col F₁ v7P256Sha2.sha.params.nw v7P256Sha2.sha.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7P256Sha2.ecdsa.params.row.n Salt₂
      (Col F₂ v7P256Sha2.ecdsa.params.nw v7P256Sha2.ecdsa.params.nq) D)
    (hD : Fintype.card D = 2 ^ v7P256Sha2.ecdsa.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D (C) X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds → C) (a : Fin S₁.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      (S₁.toK W hW₁).acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf
        pubOf (slice1 v7P256Sha2.sha v7P256Sha2.ecdsa) mt ro →
      (S₁.toK W hW₁).Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + macDecode eMac S₁.proj (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D (C) X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds → C) (a : Fin S₂.c.ninp → F₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      (S₂.toK W hW₂).acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf
        pubOf (slice2 v7P256Sha2.sha v7P256Sha2.ecdsa) mt ro →
      (S₂.toK W hW₂).Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + macDecode eMac S₁.proj (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₂ a) = tagOf (S.proof mt ro))
    (htape : 2 * v7P256Sha2.ecdsa.params.row.n + 2 * v7P256Sha2.sha.params.row.n + tA ≤ TM)
    (hTM : 0 < TM) :
    ((univ.filter fun ω : (Fin TM → D) ×
          (Pt2 D (C) X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds → C) =>
        (S₁.toK W hW₁).acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 v7P256Sha2.sha v7P256Sha2.ecdsa) ω.1 ω.2 ∧
          (S₂.toK W hW₂).acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 v7P256Sha2.sha v7P256Sha2.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            (S₁.toK W hW₁).Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₁ ∧
            (S₂.toK W hW₂).Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card (C) : ℚ) ^ Fintype.card
            (Pt2 D (C) X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds))
      ≤ (1 + N + tA : ℚ) / 2 ^ 115 := by
  exact v7P256Sha2_zk_circuit_tsecK (Nat.add_pos_right _ (Nat.two_pow_pos _)) (by rw [hC]; exact lam_icstream_le hroom (by omega) hδ) hFmac (S₁.toK W hW₁) (S₂.toK W hW₂) body rootOf₁ rootOf₂
    avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂ hD aP (macDecode eMac S₁.proj) (kOf (macS eMac) B)
    (macDecode_le eMac S₁.hproj) (macK_le eMac (by have := hW₁.1; omega)) keyB tagOf common₁
    common₂ hrow₁ hrow₂ htape hTM

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**Two-field Longfellow at `v7P256Sha3`, the decoders Rust's samplers on the ideal-cipher stream of `B` AES blocks per slot (a uniform injective block tuple), T-secure at `λ = 115`.**
Both sides' coin decoders are the deployed ones (`StreamSide.toK`: `begin_circuit`+`begin_layer`,
`begin_layer`, `elt_field`, the Ligero combination, `choose`, and `bytes(16)` for the MAC-key share),
so `CompiledZkProfileK.v7P256Sha3_zk_circuit_tsecK`'s decoder premises are discharged:

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧
    no hash-side and signature-side good witnesses agree on the MAC'd common value ]
    ≤  (1 + tA + N) · 2^-115
```
-/
theorem v7P256Sha3_zk_icstream_tsec {tA N TM B W : ℕ} (hC : Fintype.card C = Fintype.card (InjStream B))
    (hroom : 256 * W + 41 ≤ 128 * B) (hB : B ≤ 2 ^ 128)
    (hδ : ((B * (B - 1) : ℕ) : ℚ) / 2 ^ 129 ≤ 1 / 2 ^ 49)
    (hFmac : Fintype.card Fmac = 2 ^ 128) (eMac : Fin (2 ^ 128) ≃ Fmac)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha3.sha.params.nw v7P256Sha3.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha3.ecdsa.params.nw v7P256Sha3.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : StreamSide v7P256Sha3.sha (TwoFieldRowV1.sha_valid v7P256Sha3_valid) v7P256Sha3_sha_openings_pos 4
      (C) F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst B)
    (S₂ : StreamSide v7P256Sha3.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha3_valid) v7P256Sha3_ecdsa_openings_pos 8
      (C) F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd B)
    (hW₁ : S₁.Room W) (hW₂ : S₂.Room W)
    (body : TwoOracleTree Enc D (Pt2 D (C) X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds) (C) Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7P256Sha3.sha.params.row.n Salt₁
      (Col F₁ v7P256Sha3.sha.params.nw v7P256Sha3.sha.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7P256Sha3.ecdsa.params.row.n Salt₂
      (Col F₂ v7P256Sha3.ecdsa.params.nw v7P256Sha3.ecdsa.params.nq) D)
    (hD : Fintype.card D = 2 ^ v7P256Sha3.ecdsa.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D (C) X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds → C) (a : Fin S₁.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      (S₁.toK W hW₁).acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf
        pubOf (slice1 v7P256Sha3.sha v7P256Sha3.ecdsa) mt ro →
      (S₁.toK W hW₁).Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + macDecode eMac S₁.proj (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D (C) X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds → C) (a : Fin S₂.c.ninp → F₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      (S₂.toK W hW₂).acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf
        pubOf (slice2 v7P256Sha3.sha v7P256Sha3.ecdsa) mt ro →
      (S₂.toK W hW₂).Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + macDecode eMac S₁.proj (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₂ a) = tagOf (S.proof mt ro))
    (htape : 2 * v7P256Sha3.ecdsa.params.row.n + 2 * v7P256Sha3.sha.params.row.n + tA ≤ TM)
    (hTM : 0 < TM) :
    ((univ.filter fun ω : (Fin TM → D) ×
          (Pt2 D (C) X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds → C) =>
        (S₁.toK W hW₁).acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 v7P256Sha3.sha v7P256Sha3.ecdsa) ω.1 ω.2 ∧
          (S₂.toK W hW₂).acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 v7P256Sha3.sha v7P256Sha3.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            (S₁.toK W hW₁).Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₁ ∧
            (S₂.toK W hW₂).Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card (C) : ℚ) ^ Fintype.card
            (Pt2 D (C) X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds))
      ≤ (1 + N + tA : ℚ) / 2 ^ 115 := by
  exact v7P256Sha3_zk_circuit_tsecK (Nat.add_pos_right _ (Nat.two_pow_pos _)) (by rw [hC]; exact lam_icstream_le hroom (by omega) hδ) hFmac (S₁.toK W hW₁) (S₂.toK W hW₂) body rootOf₁ rootOf₂
    avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂ hD aP (macDecode eMac S₁.proj) (kOf (macS eMac) B)
    (macDecode_le eMac S₁.hproj) (macK_le eMac (by have := hW₁.1; omega)) keyB tagOf common₁
    common₂ hrow₁ hrow₂ htape hTM

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**Two-field Longfellow at `v7P256Sha4`, the decoders Rust's samplers on the ideal-cipher stream of `B` AES blocks per slot (a uniform injective block tuple), T-secure at `λ = 115`.**
Both sides' coin decoders are the deployed ones (`StreamSide.toK`: `begin_circuit`+`begin_layer`,
`begin_layer`, `elt_field`, the Ligero combination, `choose`, and `bytes(16)` for the MAC-key share),
so `CompiledZkProfileK.v7P256Sha4_zk_circuit_tsecK`'s decoder premises are discharged:

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧
    no hash-side and signature-side good witnesses agree on the MAC'd common value ]
    ≤  (1 + tA + N) · 2^-115
```
-/
theorem v7P256Sha4_zk_icstream_tsec {tA N TM B W : ℕ} (hC : Fintype.card C = Fintype.card (InjStream B))
    (hroom : 256 * W + 41 ≤ 128 * B) (hB : B ≤ 2 ^ 128)
    (hδ : ((B * (B - 1) : ℕ) : ℚ) / 2 ^ 129 ≤ 1 / 2 ^ 49)
    (hFmac : Fintype.card Fmac = 2 ^ 128) (eMac : Fin (2 ^ 128) ≃ Fmac)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha4.sha.params.nw v7P256Sha4.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha4.ecdsa.params.nw v7P256Sha4.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : StreamSide v7P256Sha4.sha (TwoFieldRowV1.sha_valid v7P256Sha4_valid) v7P256Sha4_sha_openings_pos 5
      (C) F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst B)
    (S₂ : StreamSide v7P256Sha4.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha4_valid) v7P256Sha4_ecdsa_openings_pos 8
      (C) F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd B)
    (hW₁ : S₁.Room W) (hW₂ : S₂.Room W)
    (body : TwoOracleTree Enc D (Pt2 D (C) X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds) (C) Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7P256Sha4.sha.params.row.n Salt₁
      (Col F₁ v7P256Sha4.sha.params.nw v7P256Sha4.sha.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7P256Sha4.ecdsa.params.row.n Salt₂
      (Col F₂ v7P256Sha4.ecdsa.params.nw v7P256Sha4.ecdsa.params.nq) D)
    (hD : Fintype.card D = 2 ^ v7P256Sha4.ecdsa.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D (C) X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds → C) (a : Fin S₁.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      (S₁.toK W hW₁).acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf
        pubOf (slice1 v7P256Sha4.sha v7P256Sha4.ecdsa) mt ro →
      (S₁.toK W hW₁).Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + macDecode eMac S₁.proj (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D (C) X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds → C) (a : Fin S₂.c.ninp → F₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      (S₂.toK W hW₂).acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf
        pubOf (slice2 v7P256Sha4.sha v7P256Sha4.ecdsa) mt ro →
      (S₂.toK W hW₂).Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + macDecode eMac S₁.proj (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₂ a) = tagOf (S.proof mt ro))
    (htape : 2 * v7P256Sha4.ecdsa.params.row.n + 2 * v7P256Sha4.sha.params.row.n + tA ≤ TM)
    (hTM : 0 < TM) :
    ((univ.filter fun ω : (Fin TM → D) ×
          (Pt2 D (C) X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds → C) =>
        (S₁.toK W hW₁).acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 v7P256Sha4.sha v7P256Sha4.ecdsa) ω.1 ω.2 ∧
          (S₂.toK W hW₂).acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 v7P256Sha4.sha v7P256Sha4.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            (S₁.toK W hW₁).Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₁ ∧
            (S₂.toK W hW₂).Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf
              pubOf ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ TM * (Fintype.card (C) : ℚ) ^ Fintype.card
            (Pt2 D (C) X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds))
      ≤ (1 + N + tA : ℚ) / 2 ^ 115 := by
  exact v7P256Sha4_zk_circuit_tsecK (Nat.add_pos_right _ (Nat.two_pow_pos _)) (by rw [hC]; exact lam_icstream_le hroom (by omega) hδ) hFmac (S₁.toK W hW₁) (S₂.toK W hW₂) body rootOf₁ rootOf₂
    avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂ hD aP (macDecode eMac S₁.proj) (kOf (macS eMac) B)
    (macDecode_le eMac S₁.hproj) (macK_le eMac (by have := hW₁.1; omega)) keyB tagOf common₁
    common₂ hrow₁ hrow₂ htape hTM

end V7Streams

end Lfzk.StreamCircuitSide
