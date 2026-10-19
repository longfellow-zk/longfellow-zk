import Lfzk.StreamDecoders

/-!
# The AES-CTR expansion as an explicit idealisation: ideal cipher, injective streams, collisions

The deployed challenge stream of one transcript state is `AES-256_k(0‖0), AES-256_k(1‖0), …` with
key `k = SHA-256(transcript state)` (`rust/runtime/random/src/transcript.rs`).  The key is a
**public** digest, so secret-key PRF security of AES says nothing here.  This file states the
idealisation that replaces it and proves its consequences for the counting layer.

## The model

* SHA-256 of the running state at each prefix is a random oracle to 256-bit keys;
* AES-256 is an **ideal cipher**: for each key an independent uniformly random permutation of the
  128-bit blocks, which the adversary may query in both directions `Q_E` times.

## What is proved

* **The stream of a fresh key is a uniform injective block tuple** (`ctr_fiber_card`,
  `ctrFn_fiber_card`): for distinct counter blocks, every injective `B`-tuple is the counter-mode
  output of the same number of permutations, and (over all keys at once) every function from keys to
  injective tuples is hit by the same number of ideal ciphers.  So `k ↦ stream(k)` under an ideal
  cipher is exactly a uniformly random function into `Fin B ↪ Block`.
* **The inflation** (`card_inj_ge`, `inflation`): `|injective| ≥ |all| · (1 − B(B−1)/2^129)`, so for
  every decoder and every bad set, the bad density over injective tuples is at most the density over
  all tuples times `1 / (1 − B(B−1)/2^129)` — at `B = 2^40`, at most `1 + 2^-48`
  (`inflation_2_40`).  `lam_inj_le` turns this into the virtual-card factor the counting layer
  (`Lfzk.ZkVirtualCard`) consumes: `(|all| + Y) / |injective| ≤ 1 + 2^-40` when `2^41 · Y ≤ |all|`.
* **The cross-slot terms, as counting facts about a random key function** `key : P → Key`,
  `|Key| = 2^256`:
  * `card_collide_le`: on any set of `m` points, two of them share a key with probability at most
    `m(m−1)/2 / 2^256` — at `m = N + L` the birthday term `(N + L)² / 2^257`;
  * `card_key_mem`: a given point's key lies in a fixed set of `Q_E` keys (those the adversary queried
    the cipher at) with probability exactly `Q_E / 2^256`.
* `restrict_fiber_card`, `composite_fiber_card`: on any fixed set of points on which the keys are
  distinct, the ideal cipher's streams at those points are jointly uniform injective tuples;
  `composite_le`: for any event on a fixed set `S` of points, its probability under (random keys,
  ideal cipher) is at most its probability under uniform injective tuples plus the probability that
  two points of `S` share a key — the non-adaptive form of "the composite
  `prefix ↦ AES-CTR_{SHA256(prefix)}` is a random function into injective tuples".

## What is idealised, and what is not proved here

SHA-256 as a random oracle and AES-256 as an ideal cipher are assumptions.  The reduction from the
adaptive RO + ideal-cipher experiment to the total random function into injective tuples is proved
here only in its non-adaptive, per-point-set form; the adaptive game hop (the adversary chooses
which prefixes to hash and may query the cipher, so the collision events are about its own queries)
is argued, not formalised: on the event that the `N + L` relevant keys are pairwise distinct and none
was queried to the cipher before it was output by the random oracle, every relevant stream is a
fresh uniform injective tuple independent of the adversary's view, which is the random function into
injective tuples.  The two excluded events cost `(N + L)² / 2^257` and `Q_E · (N + L) / 2^256`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.IdealCipherStream

open Finset Lfzk.StreamSampler Lfzk.StreamDecoders
open scoped Classical

/-! ## 1. Counter mode under an ideal cipher -/

section CTR

variable {Blk : Type} [Fintype Blk] [DecidableEq Blk] {B : ℕ}

/-- The counter-mode output of a permutation at the counter blocks `ctr`. -/
def ctrOut (ctr : Fin B ↪ Blk) (π : Equiv.Perm Blk) : Fin B ↪ Blk := ctr.trans π.toEmbedding

/-- A permutation carrying one injective tuple onto another. -/
theorem exists_perm_trans (t t' : Fin B ↪ Blk) :
    ∃ τ : Equiv.Perm Blk, ∀ i, τ (t i) = t' i := by
  let e : {x // x ∈ Set.range t} ≃ {x // x ∈ Set.range t'} :=
    (Equiv.ofInjective t t.injective).symm.trans (Equiv.ofInjective t' t'.injective)
  refine ⟨e.extendSubtype, fun i => ?_⟩
  rw [Equiv.extendSubtype_apply_of_mem e (t i) ⟨i, rfl⟩]
  simp only [e, Equiv.trans_apply]
  have : (Equiv.ofInjective t t.injective).symm ⟨t i, ⟨i, rfl⟩⟩ = i :=
    (Equiv.ofInjective t t.injective).symm_apply_eq.mpr rfl
  rw [this]
  rfl

/-- **The stream of an ideal-cipher key is a uniform injective tuple**: every injective `B`-tuple is
the counter-mode output of the same number of permutations. -/
theorem ctr_fiber_card (ctr : Fin B ↪ Blk) (t t' : Fin B ↪ Blk) :
    (univ.filter fun π : Equiv.Perm Blk => ctrOut ctr π = t).card
      = (univ.filter fun π : Equiv.Perm Blk => ctrOut ctr π = t').card := by
  have key : ∀ t t' : Fin B ↪ Blk,
      (univ.filter fun π : Equiv.Perm Blk => ctrOut ctr π = t).card
        ≤ (univ.filter fun π : Equiv.Perm Blk => ctrOut ctr π = t').card := by
    intro t t'
    -- move `t` to `ctr`'s output of the identity first, then to `t'`
    obtain ⟨τ, hτ⟩ := exists_perm_trans t t'
    refine card_le_card_of_injOn (fun π => τ * π) ?_ ?_
    · intro π hπ
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hπ ⊢
      refine Function.Embedding.ext fun i => ?_
      have := congrArg (fun x : Fin B ↪ Blk => x i) hπ
      simp only [ctrOut, Function.Embedding.trans_apply, Equiv.toEmbedding_apply] at this ⊢
      rw [Equiv.Perm.mul_apply, this, hτ]
    · intro π _ π' _ h
      exact mul_left_cancel h
  exact le_antisymm (key t t') (key t' t)

/-- **Over all keys at once**: the map from ideal ciphers (a permutation per key) to stream functions
(an injective tuple per key) has equal fibres, so the stream function of a uniformly random ideal
cipher is a uniformly random function into injective tuples. -/
theorem ctrFn_fiber_card {Key : Type} [Fintype Key] [DecidableEq Key] (ctr : Fin B ↪ Blk)
    (σ σ' : Key → (Fin B ↪ Blk)) :
    (univ.filter fun π : Key → Equiv.Perm Blk => (fun k => ctrOut ctr (π k)) = σ).card
      = (univ.filter fun π : Key → Equiv.Perm Blk => (fun k => ctrOut ctr (π k)) = σ').card := by
  have hcard : ∀ σ : Key → (Fin B ↪ Blk),
      (univ.filter fun π : Key → Equiv.Perm Blk => (fun k => ctrOut ctr (π k)) = σ).card
        = ∏ k, (univ.filter fun p : Equiv.Perm Blk => ctrOut ctr p = σ k).card := by
    intro σ
    rw [← Fintype.card_subtype]
    have e : {π : Key → Equiv.Perm Blk // (fun k => ctrOut ctr (π k)) = σ}
        ≃ ∀ k, {p : Equiv.Perm Blk // ctrOut ctr p = σ k} :=
      (Equiv.subtypeEquivRight fun π => funext_iff).trans
        (Equiv.subtypePiEquivPi (β := fun _ => Equiv.Perm Blk)
          (p := fun k p => ctrOut ctr p = σ k))
    rw [Fintype.card_congr e, Fintype.card_pi]
    exact prod_congr rfl fun k _ => Fintype.card_subtype _
  rw [hcard, hcard]
  exact Finset.prod_congr rfl fun k _ => ctr_fiber_card ctr (σ k) (σ' k)

end CTR

/-! ## 2. Injective block tuples: the inflation -/

section Inflation

/-- `∏ i < B, (1 − i/q) ≥ 1 − Σ i < B, i/q` while `B ≤ q + 1`. -/
theorem prod_one_sub_ge (q : ℚ) (hq : 0 < q) :
    ∀ B : ℕ, (B : ℚ) ≤ q + 1 →
      1 - ((B * (B - 1) : ℕ) : ℚ) / (2 * q) ≤ ∏ i ∈ range B, (1 - (i : ℚ) / q) := by
  intro B
  induction B with
  | zero => intro _; simp
  | succ B ih =>
    intro hB
    rw [prod_range_succ]
    have hB' : (B : ℚ) ≤ q + 1 := by push_cast at hB; linarith
    have h1 := ih hB'
    have hfac : 0 ≤ 1 - (B : ℚ) / q := by
      rw [sub_nonneg, div_le_one hq]; push_cast at hB; linarith
    have hsum : ((B * (B - 1) : ℕ) : ℚ) / (2 * q) + (B : ℚ) / q
        = (((B + 1) * (B + 1 - 1) : ℕ) : ℚ) / (2 * q) := by
      rcases B with _ | B
      · simp
      · push_cast
        field_simp
        ring
    have hS0 : 0 ≤ ((B * (B - 1) : ℕ) : ℚ) / (2 * q) := by positivity
    have hBq0 : 0 ≤ (B : ℚ) / q := by positivity
    calc 1 - (((B + 1) * (B + 1 - 1) : ℕ) : ℚ) / (2 * q)
        = (1 - ((B * (B - 1) : ℕ) : ℚ) / (2 * q)) * (1 - (B : ℚ) / q)
          - ((B * (B - 1) : ℕ) : ℚ) / (2 * q) * ((B : ℚ) / q) := by rw [← hsum]; ring
      _ ≤ (1 - ((B * (B - 1) : ℕ) : ℚ) / (2 * q)) * (1 - (B : ℚ) / q) := by
          have := mul_nonneg hS0 hBq0; linarith
      _ ≤ (∏ i ∈ range B, (1 - (i : ℚ) / q)) * (1 - (B : ℚ) / q) :=
          mul_le_mul_of_nonneg_right h1 hfac

/-- **The injective tuples are almost all**: `q.descFactorial B ≥ q^B · (1 − B(B−1)/(2q))`. -/
theorem descFactorial_ge (q B : ℕ) (hq : 0 < q) (hB : B ≤ q + 1) :
    (q : ℚ) ^ B * (1 - ((B * (B - 1) : ℕ) : ℚ) / (2 * q)) ≤ (q.descFactorial B : ℚ) := by
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq
  have hprod : (q.descFactorial B : ℚ) = (q : ℚ) ^ B * ∏ i ∈ range B, (1 - (i : ℚ) / q) := by
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    have hq_pow : (q : ℚ) ^ B = ∏ _i ∈ range B, (q : ℚ) := by rw [prod_const, card_range]
    rw [hq_pow, ← prod_mul_distrib]
    refine prod_congr rfl fun i hi => ?_
    have hi' : i ≤ q := by have := Finset.mem_range.mp hi; omega
    rw [Nat.cast_sub hi']
    field_simp
  rw [hprod]
  exact mul_le_mul_of_nonneg_left (prod_one_sub_ge (q : ℚ) hq' B (by exact_mod_cast hB))
    (by positivity)

/-- The injective block tuples. -/
abbrev InjStream (B : ℕ) := Fin B ↪ Block

theorem card_block : Fintype.card Block = 2 ^ 128 := by
  simp [Block]

theorem card_all (B : ℕ) : (Fintype.card (Stream B) : ℚ) = (2 ^ 128 : ℚ) ^ B := by
  rw [card_stream]
  push_cast
  rw [mul_comm B 16, pow_mul]
  norm_num

theorem card_inj (B : ℕ) : Fintype.card (InjStream B) = (2 ^ 128).descFactorial B := by
  rw [Fintype.card_embedding_eq, card_block, Fintype.card_fin]

/-- **`|injective| ≥ |all| · (1 − B(B−1)/2^129)`.** -/
theorem card_inj_ge (B : ℕ) (hB : B ≤ 2 ^ 128 + 1) :
    (Fintype.card (Stream B) : ℚ) * (1 - ((B * (B - 1) : ℕ) : ℚ) / 2 ^ 129)
      ≤ (Fintype.card (InjStream B) : ℚ) := by
  rw [card_all, card_inj]
  have := descFactorial_ge (2 ^ 128) B (by positivity) hB
  have e1 : ((2 ^ 128 : ℕ) : ℚ) = (2 : ℚ) ^ 128 := by push_cast; ring
  have e2 : (2 : ℚ) * 2 ^ 128 = 2 ^ 129 := by norm_num
  rw [e1, e2] at this
  exact this

/-- **The inflation, for any event on streams**: its density over injective tuples is at most its
density over all tuples divided by `1 − B(B−1)/2^129`. -/
theorem inflation (B : ℕ) (hB : B ≤ 2 ^ 128 + 1)
    (hδ : ((B * (B - 1) : ℕ) : ℚ) / 2 ^ 129 < 1) (P : Stream B → Prop) :
    ((univ.filter fun t : InjStream B => P t).card : ℚ) / Fintype.card (InjStream B)
      ≤ (((univ.filter fun s : Stream B => P s).card : ℚ) / Fintype.card (Stream B))
        / (1 - ((B * (B - 1) : ℕ) : ℚ) / 2 ^ 129) := by
  have hle : (univ.filter fun t : InjStream B => P t).card
      ≤ (univ.filter fun s : Stream B => P s).card :=
    card_le_card_of_injOn (fun t => (t : Fin B → Block)) (fun t ht => by simpa using ht)
      (fun _ _ _ _ h => DFunLike.coe_injective h)
  have hA : (0 : ℚ) < Fintype.card (Stream B) := by exact_mod_cast Fintype.card_pos
  have h1 : (0 : ℚ) < 1 - ((B * (B - 1) : ℕ) : ℚ) / 2 ^ 129 := by linarith
  have hI := card_inj_ge B hB
  have hIpos : (0 : ℚ) < Fintype.card (InjStream B) := lt_of_lt_of_le (by positivity) hI
  rw [div_div, div_le_div_iff₀ hIpos (by positivity)]
  have hn : (0 : ℚ) ≤ (univ.filter fun s : Stream B => P s).card := Nat.cast_nonneg _
  calc ((univ.filter fun t : InjStream B => P t).card : ℚ)
        * (Fintype.card (Stream B) * (1 - ((B * (B - 1) : ℕ) : ℚ) / 2 ^ 129))
      ≤ ((univ.filter fun s : Stream B => P s).card : ℚ)
        * (Fintype.card (Stream B) * (1 - ((B * (B - 1) : ℕ) : ℚ) / 2 ^ 129)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hle) (by positivity)
    _ ≤ ((univ.filter fun s : Stream B => P s).card : ℚ) * Fintype.card (InjStream B) :=
        mul_le_mul_of_nonneg_left hI hn

/-- At Rust's `MAX_PRF_BLOCKS = 2^40`: `B(B−1)/2^129 ≤ 2^-49`. -/
theorem delta_2_40 : (((2 ^ 40 * (2 ^ 40 - 1) : ℕ) : ℚ)) / 2 ^ 129 ≤ 1 / 2 ^ 49 := by
  norm_num

/-- **At `B = 2^40` the inflation is at most `1 + 2^-48`.** -/
theorem inflation_2_40 : 1 / (1 - (((2 ^ 40 * (2 ^ 40 - 1) : ℕ) : ℚ)) / 2 ^ 129) ≤ 1 + 1 / 2 ^ 48 := by
  rw [div_le_iff₀ (by norm_num)]
  norm_num

/-- **The virtual-card factor over injective tuples**: with room `2^41 · Y ≤ |all|` and
`B(B−1)/2^129 ≤ 2^-49`, `(|all| + Y) / |injective| ≤ 1 + 2^-40`. -/
theorem lam_inj_le (B Y : ℕ) (hB : B ≤ 2 ^ 128 + 1)
    (hδ : ((B * (B - 1) : ℕ) : ℚ) / 2 ^ 129 ≤ 1 / 2 ^ 49)
    (hY : 2 ^ 41 * Y ≤ Fintype.card (Stream B)) :
    ((Fintype.card (Stream B) + Y : ℕ) : ℚ) / Fintype.card (InjStream B) ≤ 1 + 1 / 2 ^ 40 := by
  have hI := card_inj_ge B hB
  have hA : (0 : ℚ) < Fintype.card (Stream B) := by exact_mod_cast Fintype.card_pos
  set δ := ((B * (B - 1) : ℕ) : ℚ) / 2 ^ 129 with hδdef
  have hδ0 : 0 ≤ δ := by positivity
  have hIpos : (0 : ℚ) < Fintype.card (InjStream B) :=
    lt_of_lt_of_le (mul_pos hA (by linarith [show (1 : ℚ) / 2 ^ 49 < 1 by norm_num])) hI
  rw [div_le_iff₀ hIpos]
  have hYq : (2 : ℚ) ^ 41 * Y ≤ Fintype.card (Stream B) := by exact_mod_cast hY
  push_cast
  have hAδ : (Fintype.card (Stream B) : ℚ) * δ ≤ Fintype.card (Stream B) * (1 / 2 ^ 49) :=
    mul_le_mul_of_nonneg_left hδ hA.le
  nlinarith

end Inflation

/-! ## 3. The cross-slot terms: a random key function -/

section Keys

variable {P K : Type} [Fintype P] [DecidableEq P] [Fintype K] [DecidableEq K]

/-- A given point's key is uniform: `#{key | key x = k} = |K|^(|P| − 1)`. -/
theorem card_key_eq (x : P) (k : K) :
    (univ.filter fun f : P → K => f x = k).card = Fintype.card K ^ (Fintype.card P - 1) := by
  have h := Fintype.card_filter_piFinset_const_eq_of_mem (ι := P) (univ : Finset K) x
    (mem_univ k)
  rw [Fintype.piFinset_univ, Finset.card_univ] at h
  convert h using 3

/-- **A given point's key falls in a fixed set of `Q_E` keys with probability `Q_E / |K|`**:
`#{key | key x ∈ Q} = |Q| · |K|^(|P| − 1)`. -/
theorem card_key_mem (x : P) (Q : Finset K) :
    (univ.filter fun f : P → K => f x ∈ Q).card = Q.card * Fintype.card K ^ (Fintype.card P - 1) := by
  rw [← sum_const_nat fun k _ => card_key_eq x k, ← card_biUnion]
  · congr 1
    ext f
    simp
  · intro k _ k' _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro f hf hf'
    simp only [mem_filter] at hf hf'
    exact hne (hf.2.symm.trans hf'.2)

/-- Two distinct points share their key with probability `1 / |K|`:
`#{key | key a = key b} · |K| = |K|^|P|`. -/
theorem card_key_pair_mul {a b : P} (hab : a ≠ b) :
    (univ.filter fun f : P → K => f a = f b).card * Fintype.card K = Fintype.card K ^ Fintype.card P := by
  rw [← Fintype.card_subtype, ← Fintype.card_prod, ← Fintype.card_fun]
  refine Fintype.card_congr
    { toFun := fun fc => Function.update fc.1.1 b fc.2
      invFun := fun g => (⟨Function.update g b (g a), by simp [Function.update_of_ne hab]⟩, g b)
      left_inv := ?_
      right_inv := ?_ }
  · rintro ⟨⟨f, hf⟩, c⟩
    refine Prod.ext (Subtype.ext ?_) ?_
    · show Function.update (Function.update f b c) b (Function.update f b c a) = f
      rw [Function.update_of_ne hab, Function.update_idem, hf, Function.update_eq_self]
    · show Function.update f b c b = c
      exact Function.update_self b c f
  · intro g
    simp

/-- **The birthday term**: on a set `S` of `m` points, `2 · #{key | two points of S share a key}
≤ m (m − 1) · |K|^(|P| − 1)`, i.e. probability at most `m(m−1)/2 / |K|`. -/
theorem card_collide_le [Nonempty K] (S : Finset P) :
    2 * (univ.filter fun f : P → K => ¬ Set.InjOn f S).card
      ≤ S.card * (S.card - 1) * Fintype.card K ^ (Fintype.card P - 1) := by
  have hK : 0 < Fintype.card K := Fintype.card_pos
  have hpair : ∀ p ∈ S.offDiag,
      (univ.filter fun f : P → K => f p.1 = f p.2).card = Fintype.card K ^ (Fintype.card P - 1) := by
    intro p hp
    have hne : p.1 ≠ p.2 := (Finset.mem_offDiag.mp hp).2.2
    have h := card_key_pair_mul (K := K) hne
    have hP : 0 < Fintype.card P := Fintype.card_pos_iff.mpr ⟨p.1⟩
    have : Fintype.card K ^ Fintype.card P = Fintype.card K ^ (Fintype.card P - 1) * Fintype.card K := by
      rw [← pow_succ]; congr 1; omega
    rw [this] at h
    exact Nat.eq_of_mul_eq_mul_right hK h
  have hsum : ∑ p ∈ S.offDiag, (univ.filter fun f : P → K => f p.1 = f p.2).card
      = S.card * (S.card - 1) * Fintype.card K ^ (Fintype.card P - 1) := by
    rw [sum_congr rfl hpair, sum_const, Finset.offDiag_card, smul_eq_mul]
    congr 1
    rw [Nat.mul_sub_one]
  rw [← hsum]
  have hswap : ∑ p ∈ S.offDiag, (univ.filter fun f : P → K => f p.1 = f p.2).card
      = ∑ f : P → K, (S.offDiag.filter fun p => f p.1 = f p.2).card := by
    simp only [card_filter]
    exact Finset.sum_comm
  rw [hswap, mul_comm, card_eq_sum_ones, sum_mul, one_mul]
  calc ∑ _f ∈ univ.filter fun f : P → K => ¬ Set.InjOn f S, 2
      ≤ ∑ f ∈ univ.filter fun f : P → K => ¬ Set.InjOn f S,
          (S.offDiag.filter fun p => f p.1 = f p.2).card := by
        refine sum_le_sum fun f hf => ?_
        simp only [mem_filter, mem_univ, true_and, Set.InjOn, not_forall] at hf
        obtain ⟨a, ha, b, hb, hfab, hne⟩ := hf
        have hsub : ({(a, b), (b, a)} : Finset (P × P)) ⊆ S.offDiag.filter fun p => f p.1 = f p.2 := by
          intro p hp
          simp only [mem_insert, mem_singleton] at hp
          rcases hp with rfl | rfl
          · simp [Finset.mem_offDiag, Finset.mem_coe.mp ha, Finset.mem_coe.mp hb, hne, hfab]
          · simp [Finset.mem_offDiag, Finset.mem_coe.mp ha, Finset.mem_coe.mp hb, Ne.symm hne,
              hfab.symm]
        have h2 : ({(a, b), (b, a)} : Finset (P × P)).card = 2 := by
          rw [Finset.card_pair]
          intro h
          simp only [Prod.mk.injEq] at h
          exact hne h.1
        rw [← h2]
        exact card_le_card hsub
    _ ≤ ∑ f : P → K, (S.offDiag.filter fun p => f p.1 = f p.2).card :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)

end Keys

/-! ## 4. The composite on a fixed set of points (non-adaptive) -/

section Composite

variable {Blk : Type} [Fintype Blk] [DecidableEq Blk] {B : ℕ}
variable {P Key : Type} [Fintype P] [DecidableEq P] [Fintype Key] [DecidableEq Key]

omit [Fintype P] [DecidableEq P] in
/-- **On points with distinct keys, a uniform stream function is jointly uniform**: for `key`
injective on `S`, every assignment of injective tuples to the points of `S` is the restriction of the
same number of stream functions. -/
theorem restrict_fiber_le (key : P → Key) (S : Finset P) (hinj : Set.InjOn key S)
    (τ τ' : S → (Fin B ↪ Blk)) :
    (univ.filter fun σ : Key → (Fin B ↪ Blk) => (fun x : S => σ (key x)) = τ).card
      ≤ (univ.filter fun σ : Key → (Fin B ↪ Blk) => (fun x : S => σ (key x)) = τ').card := by
  choose g hg using fun x : S => exists_perm_trans (τ x) (τ' x)
  let G : Key → Equiv.Perm Blk := fun k =>
    if h : ∃ x : S, key x = k then g (Classical.choose h) else 1
  have hG : ∀ x : S, G (key x) = g x := by
    intro x
    have h : ∃ x' : S, key x' = key x := ⟨x, rfl⟩
    simp only [G, dif_pos h]
    congr 1
    have hc := Classical.choose_spec h
    exact Subtype.ext (hinj (Classical.choose h).2 x.2 hc)
  refine card_le_card_of_injOn (fun σ k => (σ k).trans (G k).toEmbedding) ?_ ?_
  · intro σ hσ
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hσ ⊢
    funext x
    refine Function.Embedding.ext fun i => ?_
    have := congrArg (fun f => (f x : Fin B ↪ Blk) i) hσ
    simp only at this
    simp only [Function.Embedding.trans_apply, Equiv.toEmbedding_apply, hG, this, hg]
  · intro σ _ σ' _ h
    funext k
    refine Function.Embedding.ext fun i => ?_
    have := congrArg (fun f => (f k : Fin B ↪ Blk) i) h
    simp only [Function.Embedding.trans_apply, Equiv.toEmbedding_apply] at this
    exact (G k).injective this

omit [Fintype P] [DecidableEq P] in
theorem restrict_fiber_card (key : P → Key) (S : Finset P) (hinj : Set.InjOn key S)
    (τ τ' : S → (Fin B ↪ Blk)) :
    (univ.filter fun σ : Key → (Fin B ↪ Blk) => (fun x : S => σ (key x)) = τ).card
      = (univ.filter fun σ : Key → (Fin B ↪ Blk) => (fun x : S => σ (key x)) = τ').card :=
  le_antisymm (restrict_fiber_le key S hinj τ τ') (restrict_fiber_le key S hinj τ' τ)

omit [Fintype P] [DecidableEq P] in
/-- **The composite `x ↦ AES-CTR_{key x}` at a fixed set of points with distinct keys is jointly
uniform over injective tuples**: every assignment `τ : S → (Fin B ↪ Blk)` is produced by the same
number of ideal ciphers. -/
theorem composite_fiber_card (ctr : Fin B ↪ Blk) (key : P → Key) (S : Finset P)
    (hinj : Set.InjOn key S) (τ τ' : S → (Fin B ↪ Blk)) :
    (univ.filter fun π : Key → Equiv.Perm Blk =>
        (fun x : S => ctrOut ctr (π (key x))) = τ).card
      = (univ.filter fun π : Key → Equiv.Perm Blk =>
        (fun x : S => ctrOut ctr (π (key x))) = τ').card := by
  have hsplit : ∀ τ : S → (Fin B ↪ Blk),
      (univ.filter fun π : Key → Equiv.Perm Blk =>
          (fun x : S => ctrOut ctr (π (key x))) = τ).card
        = ∑ σ ∈ univ.filter fun σ : Key → (Fin B ↪ Blk) => (fun x : S => σ (key x)) = τ,
            (univ.filter fun π : Key → Equiv.Perm Blk => (fun k => ctrOut ctr (π k)) = σ).card := by
    intro τ
    rw [← card_biUnion]
    · congr 1
      ext π
      simp only [mem_filter, mem_univ, true_and, mem_biUnion]
      constructor
      · intro h; exact ⟨_, h, rfl⟩
      · rintro ⟨σ, hσ, rfl⟩; exact hσ
    · intro σ _ σ' _ hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro π h h'
      simp only [mem_filter] at h h'
      exact hne (h.2.symm.trans h'.2)
  rw [hsplit τ, hsplit τ']
  rcases isEmpty_or_nonempty (Key → (Fin B ↪ Blk)) with he | ⟨⟨σ₀⟩⟩
  · simp [Finset.univ_eq_empty]
  · rw [sum_congr rfl fun σ _ => ctrFn_fiber_card ctr σ σ₀,
      sum_congr rfl fun σ _ => ctrFn_fiber_card ctr σ σ₀, sum_const, sum_const,
      restrict_fiber_card key S hinj τ τ']

/-- Pushing an event forward along a map with equal fibres:
`#{a | E (r a)} · |T| = #{τ | E τ} · |A|`. -/
theorem card_comp_mul {A T : Type} [Fintype A] [Fintype T] [DecidableEq T] (r : A → T)
    (hr : ∀ τ τ', (univ.filter fun a => r a = τ).card = (univ.filter fun a => r a = τ').card)
    (E : T → Prop) :
    (univ.filter fun a => E (r a)).card * Fintype.card T
      = (univ.filter fun τ => E τ).card * Fintype.card A := by
  have hsum : ∀ U : Finset T, (univ.filter fun a => r a ∈ U).card
      = ∑ τ ∈ U, (univ.filter fun a => r a = τ).card := by
    intro U
    rw [← card_biUnion]
    · congr 1
      ext a
      simp
    · intro τ _ τ' _ hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro a h h'
      simp only [mem_filter] at h h'
      exact hne (h.2.symm.trans h'.2)
  rcases isEmpty_or_nonempty T with hT | ⟨⟨τ₀⟩⟩
  · have hA : IsEmpty A := ⟨fun a => hT.false (r a)⟩
    simp [Fintype.card_eq_zero]
  · have h1 := hsum (univ.filter fun τ => E τ)
    have h2 := hsum univ
    rw [sum_congr rfl fun τ _ => hr τ τ₀, sum_const, smul_eq_mul] at h1 h2
    have e1 : (univ.filter fun a => E (r a)) = (univ.filter fun a => r a ∈ univ.filter fun τ => E τ) := by
      ext a; simp
    have e2 : (univ.filter fun a => r a ∈ (univ : Finset T)) = univ := by ext a; simp
    have hA : Fintype.card A = Fintype.card T * (univ.filter fun a => r a = τ₀).card := by
      have h := h2
      rw [e2, Finset.card_univ, Finset.card_univ] at h
      exact h
    rw [e1, h1, hA]
    ring

/-- **The non-adaptive switching bound**: for any event `E` on the composite's values at a fixed set
`S` of points, its probability under the random oracle to keys and the ideal cipher is at most its
probability under a uniformly random assignment of injective tuples, plus the probability that two
points of `S` share a key:

```text
#{(key, π) | E (x ↦ AES-CTR_{key x}, x ∈ S)} / |keys · ciphers|
    ≤  #{τ | E τ} / |S → injective|  +  #{key | key not injective on S} / |keys|
```
-/
theorem composite_le [Nonempty Key] (ctr : Fin B ↪ Blk) (S : Finset P)
    (E : (S → (Fin B ↪ Blk)) → Prop) [Nonempty (Fin B ↪ Blk)] :
    ((univ.filter fun ω : (P → Key) × (Key → Equiv.Perm Blk) =>
        E (fun x : S => ctrOut ctr (ω.2 (ω.1 x)))).card : ℚ)
        / Fintype.card ((P → Key) × (Key → Equiv.Perm Blk))
      ≤ ((univ.filter fun τ : S → (Fin B ↪ Blk) => E τ).card : ℚ)
          / Fintype.card (S → (Fin B ↪ Blk))
        + ((univ.filter fun key : P → Key => ¬ Set.InjOn key S).card : ℚ)
          / Fintype.card (P → Key) := by
  obtain ⟨nP, hnP⟩ : ∃ n, Fintype.card (Key → Equiv.Perm Blk) = n := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ n, Fintype.card (S → (Fin B ↪ Blk)) = n := ⟨_, rfl⟩
  obtain ⟨nE, hnE⟩ : ∃ n, (univ.filter fun τ : S → (Fin B ↪ Blk) => E τ).card = n := ⟨_, rfl⟩
  obtain ⟨nK, hnK⟩ : ∃ n, Fintype.card (P → Key) = n := ⟨_, rfl⟩
  obtain ⟨nB, hnB⟩ : ∃ n, (univ.filter fun key : P → Key => ¬ Set.InjOn key S).card = n :=
    ⟨_, rfl⟩
  have hTpos : 0 < T := hT ▸ Fintype.card_pos
  have hPpos : 0 < nP := hnP ▸ Fintype.card_pos
  have hKpos : 0 < nK := hnK ▸ Fintype.card_pos
  -- per key
  have hkey : ∀ key : P → Key,
      ((univ.filter fun π : Key → Equiv.Perm Blk =>
          E (fun x : S => ctrOut ctr (π (key x)))).card : ℚ)
        ≤ (if Set.InjOn key S then (nE : ℚ) * nP / T else (nP : ℚ)) := by
    intro key
    by_cases hinj : Set.InjOn key S
    · rw [if_pos hinj, le_div_iff₀ (by exact_mod_cast hTpos)]
      have h := card_comp_mul (fun π : Key → Equiv.Perm Blk => fun x : S => ctrOut ctr (π (key x)))
        (composite_fiber_card ctr key S hinj) E
      rw [hT, hnE, hnP] at h
      rw [← Nat.cast_mul, ← Nat.cast_mul, h]
    · rw [if_neg hinj, ← hnP]
      exact Nat.cast_le.mpr (card_le_univ _)
  have htotal : ((univ.filter fun ω : (P → Key) × (Key → Equiv.Perm Blk) =>
        E (fun x : S => ctrOut ctr (ω.2 (ω.1 x)))).card : ℚ)
      = ∑ key : P → Key, ((univ.filter fun π : Key → Equiv.Perm Blk =>
          E (fun x : S => ctrOut ctr (π (key x)))).card : ℚ) := by
    rw [card_filter, Fintype.sum_prod_type]
    push_cast
    refine sum_congr rfl fun key _ => ?_
    rw [card_filter]
    push_cast
    rfl
  have hsplit : ∑ key : P → Key, (if Set.InjOn key S then (nE : ℚ) * nP / T else (nP : ℚ))
      ≤ (nK : ℚ) * ((nE : ℚ) * nP / T) + (nB : ℚ) * nP := by
    rw [Finset.sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul, hnB]
    have h1 : ((univ.filter fun key : P → Key => Set.InjOn key S).card : ℚ) ≤ nK := by
      rw [← hnK]; exact Nat.cast_le.mpr (card_le_univ _)
    have h2 : (0 : ℚ) ≤ (nE : ℚ) * nP / T := by positivity
    have := mul_le_mul_of_nonneg_right h1 h2
    linarith
  rw [htotal, Fintype.card_prod, hnK, hnP, hT, hnE, hnB, Nat.cast_mul,
    div_le_iff₀ (by positivity)]
  calc ∑ key : P → Key, ((univ.filter fun π : Key → Equiv.Perm Blk =>
          E (fun x : S => ctrOut ctr (π (key x)))).card : ℚ)
      ≤ ∑ key : P → Key, (if Set.InjOn key S then (nE : ℚ) * nP / T else (nP : ℚ)) :=
        sum_le_sum fun key _ => hkey key
    _ ≤ (nK : ℚ) * ((nE : ℚ) * nP / T) + (nB : ℚ) * nP := hsplit
    _ = ((nE : ℚ) / T + (nB : ℚ) / nK) * ((nK : ℚ) * nP) := by
        have : (T : ℚ) ≠ 0 := by exact_mod_cast hTpos.ne'
        have : (nK : ℚ) ≠ 0 := by exact_mod_cast hKpos.ne'
        field_simp

end Composite

end Lfzk.IdealCipherStream
