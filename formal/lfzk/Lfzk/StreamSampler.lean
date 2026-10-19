import Mathlib

/-!
# Rust's challenge samplers, as functions of a finite byte stream, and their exact balance

The deployed verifier (`rust/runtime/random/src/lib.rs`, `transcript.rs`) turns each Fiat–Shamir
challenge into protocol values by reading bytes from one AES-CTR stream: `bytes(len)` hands out the
next `len` bytes of the stream, and

* `nat(n)` reads `l = ⌈bits(n)/8⌉` bytes, forms the little-endian integer, keeps its low `bits(n)`
  bits (`& msk`, `msk = 2^bits(n) − 1`) and rejects (reads again) when the result is `≥ n`;
* `choose(n, k)` is a partial Fisher–Yates shuffle: `j = i + nat(n − i)`, `swap(a[i], a[j])`,
  `res[i] = a[i]`, for `i = 0, …, k − 1`;
* the P-256 base-field sampler (`fp_generic.rs`, `W = 4`) reads 32 bytes as four little-endian
  64-bit words, i.e. one little-endian 256-bit integer, and rejects when it is `≥ p` (no masking);
* the GF(2^128) sampler (`gf2_128.rs`) reads 16 bytes as a little-endian `u128`, never rejecting.

This file formalises those samplers as functions of a **finite** byte list that *fail* (`none`) when
the list runs out, and proves that they are **exactly balanced**: for every length `j`, every output
value is produced, by consuming exactly `j` bytes, by the same number of byte strings.  Balance is
closed under sequential composition (`seq`, the joint output of two successive draws — joint
uniformity is *not* implied by per-coordinate uniformity, and is proved here) and under maps with
constant fibres, and it gives the statement about a whole stream (`succ_balanced`): over byte
streams of any fixed length `N`, every output value has the same number of streams on which the
sampler succeeds with that value.

## The counting framework

* `Sampler α := List Byte → Option (α × List Byte)`: read from the front, return the value and the
  rest.  `Local p`: a successful run is determined by the bytes it consumed (it reads a prefix and
  does not look past it) — every sampler here is local.
* `exact p j a`: the byte strings of length `j` that `p` consumes **exactly**, with output `a`;
  `Balanced p`: `exact p j a` does not depend on `a`.
* `exact_seq`: `exact (seq p q) j (a, b) = ∑ i ≤ j, exact p i a · exact q (j − i) b` (for local
  `p`), so `seq` of balanced samplers is balanced; `exact_map`: a map sums `exact` over its fibre.
* `succ p N a`: streams of length `N` on which `p` succeeds with `a`;
  `succ_eq : succ p N a = ∑ i ≤ N, exact p i a · 256^(N − i)`, so balance gives `succ_balanced`.

## The samplers (§3–§6)

`rej`: rejection sampling with an attempt of fixed length; balanced when each accepted value has
the same number of attempts (`rej_balanced`).  `rejNat l m n` is Rust's attempt "`l` bytes,
little-endian, low `m` bits, accept if `< n`", balanced whenever `n ≤ 2^m` and `m ≤ 8l`
(`rejNat_balanced`; each accepted value has `256^l / 2^m` attempts, `natAttempt_accCount`).
`natRust n` (with Rust's byte count `byteLen` and mask loop `rustMask`, `and_rustMask`),
`p256Raw` and `gfRaw` are the three deployed samplers (`natRust_balanced`, `p256Raw_balanced`,
`gfRaw_balanced`; `p256_attempt` and `gfRaw_eq` show the unmasked P-256 attempt and the
never-rejecting GF(2^128) read).  `Sampler.vec` / `dvec` draw tuples (`elt_field_slice`,
`dvec_balanced`).  `chooseRust n k` is `choose` read as the deployed query **set**: every
`k`-subset is produced by the same number of byte strings (`chooseRust_balanced`), because the
draws → ordered-tuple map is a bijection onto the injective tuples (`fyEmb_bijective`; as an
ordered tuple of distinct indices `chooseTuple_balanced`).

## What is modelled, exactly

Byte order (little-endian, both for `nat`'s `r = (r << 8) | buf[i]` loop over `i` descending and for
`u64::from_le_bytes`), masking (`r & msk = r mod 2^bits(n)`, `and_rustMask`, with Rust's own mask
loop `rustMask`), the rejection loop, the Fisher–Yates index arithmetic (`j = i + nat(n − i)`;
Rust's `% n` is the identity there, `fyJ_mod`) and the swap are as in the Rust source.  The field samplers' final step (`to_montgomery`, `Gf2_128::from`)
is a bijection onto the field; which bijection is immaterial for balance and is taken as a
parameter.  `bytes(len)` is `List.take`/`List.drop` on the stream.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.StreamSampler

open Finset
open scoped Classical

/-- A byte. -/
abbrev Byte := Fin 256

/-- **A byte-stream sampler**: reads from the front of the stream and returns its value and the
rest of the stream, or `none` when the stream runs out before it finishes. -/
abbrev Sampler (α : Type) := List Byte → Option (α × List Byte)

/-! ## 1. Byte strings of a fixed length -/

/-- The byte strings of length `j`. -/
noncomputable def words (j : ℕ) : Finset (List Byte) :=
  (univ : Finset (Fin j → Byte)).image List.ofFn

theorem mem_words {j : ℕ} {w : List Byte} : w ∈ words j ↔ w.length = j := by
  unfold words
  constructor
  · intro h
    obtain ⟨f, -, rfl⟩ := Finset.mem_image.mp h
    exact List.length_ofFn
  · intro h
    subst h
    exact Finset.mem_image.mpr ⟨w.get, Finset.mem_univ _, List.ofFn_get w⟩

theorem card_words (j : ℕ) : (words j).card = 256 ^ j := by
  unfold words
  rw [Finset.card_image_of_injective _ List.ofFn_injective, Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- `List.ofFn` is a bijection from `Fin j → Byte` onto `words j`: counting over either is the
same. -/
theorem card_filter_words {j : ℕ} (P : List Byte → Prop) [DecidablePred P] :
    ((words j).filter P).card = (univ.filter fun f : Fin j → Byte => P (List.ofFn f)).card := by
  unfold words
  rw [Finset.filter_image, Finset.card_image_of_injective _ List.ofFn_injective]

namespace Sampler

variable {α β : Type}

/-- **A local sampler**: a successful run consumed a prefix `w` of the stream, and on any stream
starting with `w` it consumes exactly `w` with the same value. -/
def Local (p : Sampler α) : Prop :=
  ∀ s a r, p s = some (a, r) → ∃ w, s = w ++ r ∧ ∀ r', p (w ++ r') = some (a, r')

/-- **Exact consumption counts**: the byte strings of length `j` that `p` consumes exactly, with
output `a`. -/
noncomputable def exact (p : Sampler α) (j : ℕ) (a : α) : ℕ :=
  ((words j).filter fun w => p w = some (a, [])).card

/-- **Balance**: at every length, every output has the same exact-consumption count. -/
def Balanced (p : Sampler α) : Prop := ∀ (j : ℕ) (a b : α), exact p j a = exact p j b

/-- **Success counts on streams of length `N`**. -/
noncomputable def succ (p : Sampler α) (N : ℕ) (a : α) : ℕ :=
  ((words N).filter fun s => ∃ r, p s = some (a, r)).card

/-! ## 2. Composition -/

/-- **Two successive draws**: run `p`, then `q` on the rest. -/
def seq (p : Sampler α) (q : Sampler β) : Sampler (α × β) := fun s =>
  (p s).bind fun ar => (q ar.2).map fun br => ((ar.1, br.1), br.2)

/-- Post-process the value. -/
def map (g : α → β) (p : Sampler α) : Sampler β := fun s =>
  (p s).map fun ar => (g ar.1, ar.2)

/-- Return a value without reading. -/
def pure (a : α) : Sampler α := fun s => some (a, s)

theorem seq_eq_some {p : Sampler α} {q : Sampler β} {s : List Byte} {a : α} {b : β}
    {r' : List Byte} :
    seq p q s = some ((a, b), r') ↔ ∃ r, p s = some (a, r) ∧ q r = some (b, r') := by
  unfold seq
  constructor
  · intro h
    rcases hp : p s with _ | ⟨a', r⟩
    · rw [hp] at h; simp at h
    · rw [hp] at h
      rcases hq : q r with _ | ⟨b', r''⟩
      · simp [hq] at h
      · simp only [hq, Option.bind_some, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
        exact ⟨r, rfl, hq⟩
  · rintro ⟨r, hp, hq⟩
    simp [hp, hq]

theorem map_eq_some {g : α → β} {p : Sampler α} {s : List Byte} {b : β} {r : List Byte} :
    map g p s = some (b, r) ↔ ∃ a, g a = b ∧ p s = some (a, r) := by
  unfold map
  constructor
  · intro h
    rcases hp : p s with _ | ⟨a, r'⟩
    · rw [hp] at h; simp at h
    · rw [hp] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨a, rfl, rfl⟩
  · rintro ⟨a, rfl, hp⟩
    simp [hp]

theorem pure_local (a : α) : (pure a).Local := by
  intro s a' r h
  simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨[], by simp, fun r' => by simp [pure]⟩

theorem seq_local {p : Sampler α} {q : Sampler β} (hp : p.Local) (hq : q.Local) :
    (seq p q).Local := by
  rintro s ⟨a, b⟩ r' h
  obtain ⟨r, h1, h2⟩ := seq_eq_some.mp h
  obtain ⟨w, rfl, hw⟩ := hp s a r h1
  obtain ⟨v, rfl, hv⟩ := hq r b r' h2
  refine ⟨w ++ v, by simp, fun y => ?_⟩
  rw [seq_eq_some]
  exact ⟨v ++ y, by rw [List.append_assoc]; exact hw _, hv y⟩

theorem map_local {g : α → β} {p : Sampler α} (hp : p.Local) : (map g p).Local := by
  intro s b r h
  obtain ⟨a, rfl, h1⟩ := map_eq_some.mp h
  obtain ⟨w, rfl, hw⟩ := hp _ a r h1
  exact ⟨w, rfl, fun r' => map_eq_some.mpr ⟨a, rfl, hw r'⟩⟩

/-- On a local sampler, an exact parse of a prefix extends to the whole stream. -/
theorem Local.extend {p : Sampler α} (hp : p.Local) {w : List Byte} {a : α}
    (h : p w = some (a, [])) (r : List Byte) : p (w ++ r) = some (a, r) := by
  obtain ⟨w', hw', hext⟩ := hp w a [] h
  rw [List.append_nil] at hw'
  subst hw'
  exact hext r

/-- **A local sampler consumes at most one prefix exactly.** -/
theorem Local.prefix_unique {p : Sampler α} (hp : p.Local) {w : List Byte} {i i' : ℕ}
    (hi : i ≤ w.length) (hi' : i' ≤ w.length) {a a' : α}
    (h : p (w.take i) = some (a, [])) (h' : p (w.take i') = some (a', [])) : i = i' := by
  have key : ∀ {i i' : ℕ} {a a' : α}, i < i' → i' ≤ w.length →
      p (w.take i) = some (a, []) → p (w.take i') = some (a', []) → False := by
    intro i i' a a' hlt hi' h h'
    have e : w.take i' = w.take i ++ (w.take i').drop i := by
      conv_lhs => rw [← List.take_append_drop i (w.take i')]
      rw [List.take_take, min_eq_left hlt.le]
    have hx := hp.extend h ((w.take i').drop i)
    rw [← e, h'] at hx
    have hnil : (w.take i').drop i = [] := by
      simp only [Option.some.injEq, Prod.mk.injEq] at hx
      exact hx.2.symm
    have hl := congrArg List.length hnil
    simp only [List.length_drop, List.length_take, List.length_nil] at hl
    omega
  rcases lt_trichotomy i i' with hlt | heq | hgt
  · exact (key hlt hi' h h').elim
  · exact heq
  · exact (key hgt hi h' h).elim

/-- **Splitting a run of `seq`**: `seq p q` consumes `w` exactly with `(a, b)` iff some prefix of
`w` is consumed exactly by `p` with `a` and the rest exactly by `q` with `b`. -/
theorem seq_nil_iff {p : Sampler α} (hp : p.Local) (q : Sampler β) (w : List Byte) (a : α)
    (b : β) :
    seq p q w = some ((a, b), []) ↔
      ∃ i, i ≤ w.length ∧ p (w.take i) = some (a, []) ∧ q (w.drop i) = some (b, []) := by
  constructor
  · intro h
    obtain ⟨r, h1, h2⟩ := seq_eq_some.mp h
    obtain ⟨u, rfl, hu⟩ := hp w a r h1
    refine ⟨u.length, by simp, ?_, ?_⟩
    · rw [List.take_left' rfl]
      simpa using hu []
    · rw [List.drop_left' rfl]
      exact h2
  · rintro ⟨i, -, h1, h2⟩
    have := hp.extend h1 (w.drop i)
    rw [List.take_append_drop] at this
    exact seq_eq_some.mpr ⟨w.drop i, this, h2⟩

/-- The strings of length `j` split at `i ≤ j` into a length-`i` prefix with one property and the
rest with another: their number is the product. -/
theorem card_split {j i : ℕ} (hij : i ≤ j) (P Q : List Byte → Prop) :
    ((words j).filter fun w => P (w.take i) ∧ Q (w.drop i)).card
      = ((words i).filter P).card * ((words (j - i)).filter Q).card := by
  rw [← card_product]
  refine card_bij' (fun w _ => (w.take i, w.drop i)) (fun uv _ => uv.1 ++ uv.2) ?_ ?_ ?_ ?_
  · intro w hw
    simp only [mem_filter, mem_words, mem_product] at hw ⊢
    refine ⟨⟨?_, hw.2.1⟩, ?_, hw.2.2⟩
    · simp [List.length_take, hw.1, hij]
    · simp [List.length_drop, hw.1]
  · intro uv huv
    simp only [mem_filter, mem_words, mem_product] at huv ⊢
    obtain ⟨⟨hu, hP⟩, hv, hQ⟩ := huv
    refine ⟨by simp [hu, hv]; omega, ?_, ?_⟩
    · rwa [List.take_left' hu]
    · rwa [List.drop_left' hu]
  · intro w _
    simp
  · intro uv huv
    simp only [mem_filter, mem_words, mem_product] at huv
    obtain ⟨⟨hu, -⟩, -, -⟩ := huv
    simp [List.take_left' hu, List.drop_left' hu]

/-- **Exact counts of two successive draws** (for local `p`). -/
theorem exact_seq {p : Sampler α} (hp : p.Local) (q : Sampler β) (j : ℕ) (a : α) (b : β) :
    exact (seq p q) j (a, b) = ∑ i ∈ range (j + 1), exact p i a * exact q (j - i) b := by
  calc exact (seq p q) j (a, b)
      = ((range (j + 1)).biUnion (fun i => (words j).filter
          (fun w => p (w.take i) = some (a, []) ∧ q (w.drop i) = some (b, [])))).card := by
        unfold exact
        congr 1
        ext w
        simp only [mem_filter, mem_biUnion, mem_range, mem_words, seq_nil_iff hp]
        constructor
        · rintro ⟨hw, i, hi, h1, h2⟩
          exact ⟨i, by omega, hw, h1, h2⟩
        · rintro ⟨i, hi, hw, h1, h2⟩
          exact ⟨hw, i, by omega, h1, h2⟩
    _ = ∑ i ∈ range (j + 1), exact p i a * exact q (j - i) b := by
        rw [card_biUnion]
        · refine sum_congr rfl fun i hi => ?_
          unfold exact
          convert card_split (by simpa [Nat.lt_succ_iff] using hi)
            (fun u => p u = some (a, [])) (fun v => q v = some (b, [])) using 5
        · intro i hi i' hi' hne
          simp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro w hw hw'
          simp only [mem_filter, mem_words] at hw hw'
          simp only [coe_range, Set.mem_Iio] at hi hi'
          exact hne (hp.prefix_unique (by omega) (by omega) hw.2.1 hw'.2.1)

/-- **Exact counts of a map**: the sum over the fibre. -/
theorem exact_map [Fintype α] [DecidableEq β] (g : α → β) (p : Sampler α) (j : ℕ) (b : β) :
    exact (map g p) j b = ∑ a ∈ univ.filter (fun a => g a = b), exact p j a := by
  calc exact (map g p) j b
      = ((univ.filter fun a => g a = b).biUnion
          (fun a => (words j).filter (fun w => p w = some (a, [])))).card := by
        unfold exact
        congr 1
        ext w
        simp only [mem_filter, mem_biUnion, mem_univ, true_and, map_eq_some]
        constructor
        · rintro ⟨hw, a, rfl, h⟩
          exact ⟨a, rfl, hw, h⟩
        · rintro ⟨a, rfl, hw, h⟩
          exact ⟨hw, a, rfl, h⟩
    _ = ∑ a ∈ univ.filter (fun a => g a = b), exact p j a := by
        rw [card_biUnion]
        · rfl
        intro a _ a' _ hne
        simp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro w hw hw'
        simp only [mem_filter] at hw hw'
        rw [hw.2] at hw'
        simp only [Option.some.injEq, Prod.mk.injEq] at hw'
        exact hne hw'.2.1

/-- **Balance is closed under `seq`.** -/
theorem Balanced.seq {p : Sampler α} {q : Sampler β} (hp : p.Local) (hbp : p.Balanced)
    (hbq : q.Balanced) : (seq p q).Balanced := by
  rintro j ⟨a, b⟩ ⟨a', b'⟩
  rw [exact_seq hp, exact_seq hp]
  exact sum_congr rfl fun i _ => by rw [hbp i a a', hbq (j - i) b b']

/-- **Balance is closed under maps with constant fibres.** -/
theorem Balanced.map [Fintype α] [DecidableEq β] {p : Sampler α} (hbp : p.Balanced) {g : α → β}
    (hg : ∀ b b', (univ.filter fun a => g a = b).card = (univ.filter fun a => g a = b').card) :
    (Sampler.map g p).Balanced := by
  intro j b b'
  rw [exact_map, exact_map]
  rcases isEmpty_or_nonempty α with hα | ⟨⟨a₀⟩⟩
  · simp [Finset.univ_eq_empty]
  · rw [sum_congr rfl (fun a _ => hbp j a a₀), sum_congr rfl (fun a _ => hbp j a a₀), sum_const,
      sum_const, hg b b']

/-- A bijection has fibres of size one. -/
theorem fiber_card_of_bijective [Fintype α] [DecidableEq β] {g : α → β}
    (hg : Function.Bijective g) (b : β) :
    (univ.filter fun a => g a = b).card = 1 := by
  obtain ⟨a, rfl⟩ := hg.2 b
  rw [Finset.card_eq_one]
  refine ⟨a, ?_⟩
  ext a'
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  exact ⟨fun h => hg.1 h, fun h => h ▸ rfl⟩

theorem Balanced.map_bijective [Fintype α] [DecidableEq β] {p : Sampler α} (hbp : p.Balanced)
    {g : α → β}
    (hg : Function.Bijective g) : (Sampler.map g p).Balanced :=
  Balanced.map hbp fun b b' => by rw [fiber_card_of_bijective hg, fiber_card_of_bijective hg]

theorem pure_balanced [Subsingleton α] (a : α) : (pure a).Balanced :=
  fun j b b' => by rw [Subsingleton.elim b b']

/-! ### Whole streams -/

/-- Read the whole rest of the stream (a device for counting streams, not a deployed sampler). -/
def rest : Sampler Unit := fun _ => some ((), [])

theorem exact_rest (m : ℕ) : exact rest m () = 256 ^ m := by
  unfold exact
  rw [← card_words m]
  congr 1
  ext w
  simp [rest]

/-- **Success counts are a convolution of exact counts with the free tail.** -/
theorem succ_eq {p : Sampler α} (hp : p.Local) (N : ℕ) (a : α) :
    succ p N a = ∑ i ∈ range (N + 1), exact p i a * 256 ^ (N - i) := by
  have h : succ p N a = exact (seq p rest) N (a, ()) := by
    unfold succ exact
    congr 1
    ext s
    simp only [mem_filter, seq_eq_some, rest, and_true]
  rw [h, exact_seq hp]
  exact sum_congr rfl fun i _ => by rw [exact_rest]

/-- **A balanced local sampler succeeds on equally many streams of every length with every
value.** -/
theorem succ_balanced {p : Sampler α} (hp : p.Local) (hb : p.Balanced) (N : ℕ) (a b : α) :
    succ p N a = succ p N b := by
  rw [succ_eq hp, succ_eq hp]
  exact sum_congr rfl fun i _ => by rw [hb i a b]

/-- The successful streams, over all values, are at most all the streams. -/
theorem sum_succ_le [Fintype α] (p : Sampler α) (N : ℕ) : ∑ a, succ p N a ≤ 256 ^ N := by
  unfold succ
  rw [← card_biUnion]
  · rw [← card_words N]
    refine card_le_card fun s hs => ?_
    simp only [mem_biUnion, mem_univ, true_and, mem_filter] at hs
    exact hs.choose_spec.1
  · intro a _ a' _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro s hs hs'
    simp only [mem_filter] at hs hs'
    obtain ⟨r, hr⟩ := hs.2
    obtain ⟨r', hr'⟩ := hs'.2
    rw [hr] at hr'
    simp only [Option.some.injEq, Prod.mk.injEq] at hr'
    exact hne hr'.1

/-! ## 3. Rejection sampling -/

/-- **Rejection sampling**: read `l` bytes; if the attempt accepts them return its value,
otherwise try again on the rest; fail when fewer than `l` bytes remain. -/
def rej (l : ℕ) (hl : 0 < l) (att : List Byte → Option α) : Sampler α := fun s =>
  if _h : l ≤ s.length then
    match att (s.take l) with
    | some a => some (a, s.drop l)
    | none => rej l hl att (s.drop l)
  else none
termination_by s => s.length
decreasing_by simp only [List.length_drop]; omega

theorem rej_eq (l : ℕ) (hl : 0 < l) (att : List Byte → Option α) (s : List Byte) :
    rej l hl att s =
      if l ≤ s.length then
        (match att (s.take l) with
          | some a => some (a, s.drop l)
          | none => rej l hl att (s.drop l))
      else none := by
  rw [rej]
  simp only [dite_eq_ite]

theorem rej_local (l : ℕ) (hl : 0 < l) (att : List Byte → Option α) :
    (rej l hl att).Local := by
  suffices H : ∀ n, ∀ s : List Byte, s.length = n → ∀ a r, rej l hl att s = some (a, r) →
      ∃ w, s = w ++ r ∧ ∀ r', rej l hl att (w ++ r') = some (a, r') from
    fun s a r h => H _ s rfl a r h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s hs a r h
  rw [rej_eq] at h
  split_ifs at h with hls
  · rcases ha : att (s.take l) with _ | a'
    · rw [ha] at h
      obtain ⟨w, hw, hext⟩ := ih _ (by simp only [List.length_drop]; omega) (s.drop l) rfl a r h
      refine ⟨s.take l ++ w, ?_, fun r' => ?_⟩
      · rw [List.append_assoc, ← hw, List.take_append_drop]
      · have hlen : (s.take l).length = l := by simp; omega
        rw [rej_eq, if_pos (by simp; omega), List.append_assoc, List.take_left' hlen,
          List.drop_left' hlen, ha]
        exact hext r'
    · rw [ha] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨s.take l, (List.take_append_drop l s).symm, fun r' => ?_⟩
      have hlen : (s.take l).length = l := by simp; omega
      rw [rej_eq, if_pos (by simp; omega), List.take_left' hlen, List.drop_left' hlen, ha]

/-- The attempt's acceptance counts. -/
noncomputable def accCount (l : ℕ) (att : List Byte → Option α) (a : α) : ℕ :=
  ((words l).filter fun u => att u = some a).card

/-- The attempt's rejection count. -/
noncomputable def rejCount (l : ℕ) (att : List Byte → Option α) : ℕ :=
  ((words l).filter fun u => att u = none).card

theorem rej_exact_lt (l : ℕ) (hl : 0 < l) (att : List Byte → Option α) {j : ℕ} (hj : j < l)
    (a : α) : exact (rej l hl att) j a = 0 := by
  unfold exact
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro w hw
  rw [mem_words] at hw
  rw [rej_eq, if_neg (by omega)]
  simp

theorem card_words_nil (m : ℕ) : ((words m).filter fun v => v = []).card = if m = 0 then 1 else 0 := by
  rcases m with _ | m
  · rw [if_pos rfl, Finset.card_eq_one]
    refine ⟨[], ?_⟩
    ext v
    simp only [mem_filter, mem_words, mem_singleton]
    constructor
    · exact fun h => h.2
    · rintro rfl; exact ⟨rfl, rfl⟩
  · rw [if_neg (by omega), Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro v hv hv'
    rw [mem_words, hv'] at hv
    simp at hv

/-- **The first-attempt recursion of exact counts.** -/
theorem rej_exact_ge (l : ℕ) (hl : 0 < l) (att : List Byte → Option α) {j : ℕ} (hj : l ≤ j)
    (a : α) : exact (rej l hl att) j a
      = accCount l att a * (if j - l = 0 then 1 else 0)
        + rejCount l att * exact (rej l hl att) (j - l) a := by
  have hset : ((words j).filter fun w => rej l hl att w = some (a, [])).card
      = (((words j).filter fun w => att (w.take l) = some a ∧ w.drop l = [])
        ∪ ((words j).filter fun w => att (w.take l) = none
            ∧ rej l hl att (w.drop l) = some (a, []))).card := by
    congr 1
    ext w
    simp only [mem_filter, mem_union, mem_words]
    constructor
    · rintro ⟨hw, h⟩
      rw [rej_eq, if_pos (by omega)] at h
      rcases ha : att (w.take l) with _ | a'
      · rw [ha] at h
        exact Or.inr ⟨hw, rfl, h⟩
      · rw [ha] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, h⟩ := h
        exact Or.inl ⟨hw, rfl, h⟩
    · rintro (⟨hw, ha, hd⟩ | ⟨hw, ha, h⟩)
      · refine ⟨hw, ?_⟩
        rw [rej_eq, if_pos (by omega), ha, hd]
      · refine ⟨hw, ?_⟩
        rw [rej_eq, if_pos (by omega), ha]
        exact h
  unfold exact
  rw [hset, card_union_of_disjoint]
  · congr 1
    · unfold accCount
      rw [← card_words_nil]
      convert card_split hj (fun u => att u = some a) (fun v => v = []) using 5
    · unfold rejCount
      convert card_split hj (fun u => att u = none)
        (fun v => rej l hl att v = some (a, [])) using 5
  · rw [Finset.disjoint_left]
    intro w hw hw'
    simp only [mem_filter] at hw hw'
    rw [hw.2.1] at hw'
    simp at hw'

/-- **Rejection sampling is balanced when its attempt is**: every accepted value has the same
number of accepting attempts. -/
theorem rej_balanced (l : ℕ) (hl : 0 < l) (att : List Byte → Option α)
    (hacc : ∀ a b, accCount l att a = accCount l att b) : (rej l hl att).Balanced := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro a b
  by_cases hj : j < l
  · rw [rej_exact_lt l hl att hj, rej_exact_lt l hl att hj]
  · rw [rej_exact_ge l hl att (j := j) (by omega) a, rej_exact_ge l hl att (j := j) (by omega) b,
      hacc a b, ih (j - l) (by omega) a b]

end Sampler

/-! ## 4. Little-endian integers and the deployed rejection samplers -/

/-- **The little-endian value of a byte string**: `Σ bᵢ · 256^i`.  Rust's `nat` builds it as
`r = (r << 8) | buf[i]` over `i` descending, `fp_generic`'s sampler as `u64::from_le_bytes` words
in little-endian word order, `gf2_128`'s as `u128::from_le_bytes`. -/
def leNat : List Byte → ℕ
  | [] => 0
  | b :: bs => b.val + 256 * leNat bs

theorem leNat_ofFn {l : ℕ} (f : Fin l → Byte) :
    leNat (List.ofFn f) = ∑ i, (f i : ℕ) * 256 ^ (i : ℕ) := by
  induction l with
  | zero => simp [leNat]
  | succ l ih =>
    rw [List.ofFn_succ, leNat, ih, Fin.sum_univ_succ, Finset.mul_sum]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
    congr 1
    exact sum_congr rfl fun i _ => by ring

theorem leNat_ofFn_eq {l : ℕ} (f : Fin l → Byte) :
    leNat (List.ofFn f) = (finFunctionFinEquiv f : ℕ) := by
  rw [finFunctionFinEquiv_apply, leNat_ofFn]

theorem leNat_lt (u : List Byte) : leNat u < 256 ^ u.length := by
  induction u with
  | nil => simp [leNat]
  | cons b bs ih =>
    rw [leNat, List.length_cons, pow_succ]
    have := b.isLt
    nlinarith

/-- `#{x < N | x mod d = y} = N / d` when `d ∣ N` and `y < d`. -/
theorem card_fin_mod {N d y : ℕ} (hd : d ∣ N) (hy : y < d) :
    (univ.filter fun x : Fin N => (x : ℕ) % d = y).card = N / d := by
  have hd0 : 0 < d := by omega
  obtain ⟨Q, rfl⟩ := hd
  rw [Nat.mul_div_cancel_left Q hd0]
  conv_rhs => rw [← Fintype.card_fin Q, ← Finset.card_univ]
  refine card_bij' (fun x _ => (⟨(x : ℕ) / d, ?_⟩ : Fin Q)) (fun q _ => ⟨(q : ℕ) * d + y, ?_⟩)
    ?_ ?_ ?_ ?_
  · exact Nat.div_lt_of_lt_mul (by simp)
  · have := q.isLt
    nlinarith
  · intro x _; exact mem_univ _
  · intro q _
    simp only [mem_filter, mem_univ, true_and]
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hy]
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    ext
    simp only
    rw [← hx, Nat.div_add_mod']
  · intro q _
    ext
    simp only
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd0, Nat.div_eq_of_lt hy, zero_add]

/-- **One attempt of Rust's integer sampler**: the little-endian value, its low `m` bits, accepted
when `< n`. -/
def natAttempt (m n : ℕ) (u : List Byte) : Option (Fin n) :=
  if h : leNat u % 2 ^ m < n then some ⟨leNat u % 2 ^ m, h⟩ else none

theorem natAttempt_eq_some {m n : ℕ} {u : List Byte} {y : Fin n} :
    natAttempt m n u = some y ↔ leNat u % 2 ^ m = y := by
  unfold natAttempt
  split_ifs with h
  · simp [Fin.ext_iff]
  · simp only [false_iff]
    intro he
    exact h (he ▸ y.isLt)

/-- **Each accepted value has `256^l / 2^m` accepting attempts.** -/
theorem natAttempt_accCount {l m n : ℕ} (hm : m ≤ 8 * l) (hn : n ≤ 2 ^ m) (y : Fin n) :
    Sampler.accCount l (natAttempt m n) y = 256 ^ l / 2 ^ m := by
  unfold Sampler.accCount
  rw [card_filter_words]
  refine Eq.trans (card_equiv (t := univ.filter fun x : Fin (256 ^ l) => (x : ℕ) % 2 ^ m = y)
    finFunctionFinEquiv fun f => ?_) ?_
  · simp only [mem_filter, mem_univ, true_and, natAttempt_eq_some, leNat_ofFn_eq]
  · refine card_fin_mod ?_ (lt_of_lt_of_le y.isLt hn)
    rw [show (256 : ℕ) ^ l = 2 ^ (8 * l) by rw [pow_mul]; norm_num]
    exact pow_dvd_pow 2 hm

/-- **Rust's rejection sampler on `l`-byte attempts, low `m` bits, range `n`.** -/
def rejNat (l m n : ℕ) (hl : 0 < l) : Sampler (Fin n) := Sampler.rej l hl (natAttempt m n)

theorem rejNat_local (l m n : ℕ) (hl : 0 < l) : (rejNat l m n hl).Local :=
  Sampler.rej_local l hl _

theorem rejNat_balanced {l m n : ℕ} (hl : 0 < l) (hm : m ≤ 8 * l) (hn : n ≤ 2 ^ m) :
    (rejNat l m n hl).Balanced :=
  Sampler.rej_balanced l hl _ fun a b => by
    rw [natAttempt_accCount hm hn, natAttempt_accCount hm hn]

/-! ### `nat(n)`: the byte length and the mask, as Rust computes them -/

/-- **Rust's byte count** `l`: `while nn != 0 { nn >>= 8; l += 1 }`. -/
def byteLen : ℕ → ℕ
  | 0 => 0
  | n + 1 => 1 + byteLen ((n + 1) / 256)
decreasing_by exact Nat.div_lt_self (Nat.succ_pos n) (by norm_num)

theorem lt_pow_byteLen (n : ℕ) : n < 256 ^ byteLen n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases n with _ | n
  · simp [byteLen]
  · rw [byteLen, pow_add, pow_one]
    have := ih ((n + 1) / 256) (Nat.div_lt_self (Nat.succ_pos n) (by norm_num))
    omega

theorem byteLen_pos {n : ℕ} (hn : 0 < n) : 0 < byteLen n := by
  rcases n with _ | n
  · omega
  · rw [byteLen]; omega

/-- **Rust's mask loop**: `msk = 0; while (n & msk) != n { msk = (msk << 1) | 1 }`, run with
enough fuel. -/
def maskLoop (n : ℕ) : ℕ → ℕ → ℕ
  | 0, msk => msk
  | fuel + 1, msk => if n &&& msk = n then msk else maskLoop n fuel (2 * msk + 1)

/-- Rust's `mask(n)`. -/
def rustMask (n : ℕ) : ℕ := maskLoop n (n + 1) 0

theorem maskLoop_eq (n : ℕ) :
    ∀ fuel k, k ≤ Nat.size n → Nat.size n ≤ k + fuel →
      maskLoop n fuel (2 ^ k - 1) = 2 ^ Nat.size n - 1 := by
  intro fuel
  induction fuel with
  | zero => intro k hk hk'; rw [maskLoop]; congr; omega
  | succ fuel ih =>
    intro k hk hk'
    rw [maskLoop, Nat.and_two_pow_sub_one_eq_mod]
    by_cases hlt : n < 2 ^ k
    · rw [if_pos (Nat.mod_eq_of_lt hlt)]
      have := Nat.size_le.mpr hlt
      congr; omega
    · have hmod : n % 2 ^ k ≠ n := fun h => hlt (h ▸ Nat.mod_lt _ (by positivity))
      rw [if_neg hmod]
      have hk2 : k < Nat.size n := Nat.lt_size.mpr (by omega)
      have e : 2 * (2 ^ k - 1) + 1 = 2 ^ (k + 1) - 1 := by
        have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        rw [pow_succ]; omega
      rw [e]
      exact ih (k + 1) hk2 (by omega)

/-- **Rust's mask is `2^bits(n) − 1`**, so `r & msk = r mod 2^bits(n)`. -/
theorem rustMask_eq (n : ℕ) : rustMask n = 2 ^ Nat.size n - 1 := by
  have h := maskLoop_eq n (n + 1) 0 (Nat.zero_le _)
    (by have := Nat.size_le.mpr (Nat.lt_two_pow_self (n := n)); omega)
  unfold rustMask
  simpa using h

theorem and_rustMask (r n : ℕ) : r &&& rustMask n = r % 2 ^ Nat.size n := by
  rw [rustMask_eq, Nat.and_two_pow_sub_one_eq_mod]

theorem size_le_byteLen (n : ℕ) : Nat.size n ≤ 8 * byteLen n :=
  Nat.size_le.mpr (by have := lt_pow_byteLen n; rw [pow_mul]; norm_num; exact this)

/-- **Rust's `nat(n)`** (`lib.rs`), `n > 0`: `l = byteLen n` bytes per attempt, value
`r & mask(n) = r mod 2^bits(n)`, rejected when `≥ n`. -/
def natRust (n : ℕ) (hn : 0 < n) : Sampler (Fin n) := rejNat (byteLen n) (Nat.size n) n (byteLen_pos hn)

theorem natRust_local (n : ℕ) (hn : 0 < n) : (natRust n hn).Local := rejNat_local _ _ _ _

theorem natRust_balanced (n : ℕ) (hn : 0 < n) : (natRust n hn).Balanced :=
  rejNat_balanced _ (size_le_byteLen n) (Nat.lt_size_self n).le

/-- **Rust's P-256 base-field sampler** (`fp_generic.rs`, `W = 4`), at modulus `p < 2^256`: 32 bytes
per attempt, the little-endian 256-bit value, rejected when `≥ p`.  The value is not masked; on 32
bytes the low 256 bits are the whole value (`p256_attempt`). -/
def p256Raw (p : ℕ) : Sampler (Fin p) := rejNat 32 256 p (by norm_num)

theorem p256_attempt {p : ℕ} {u : List Byte} (hu : u.length = 32) :
    natAttempt 256 p u = if h : leNat u < p then some ⟨leNat u, h⟩ else none := by
  have hlt : leNat u < 2 ^ 256 := by
    have := leNat_lt u; rw [hu] at this; norm_num at this ⊢; exact this
  have hlt' : leNat u % 2 ^ 256 = leNat u := Nat.mod_eq_of_lt hlt
  simp only [natAttempt, hlt']

theorem p256Raw_balanced {p : ℕ} (hp : p ≤ 2 ^ 256) : (p256Raw p).Balanced :=
  rejNat_balanced _ (by norm_num) hp

/-- **Rust's GF(2^128) sampler** (`gf2_128.rs`): 16 bytes, the little-endian `u128`; it never
rejects (`gfRaw_eq`). -/
def gfRaw : Sampler (Fin (2 ^ 128)) := rejNat 16 128 (2 ^ 128) (by norm_num)

theorem gfRaw_balanced : gfRaw.Balanced := rejNat_balanced _ (by norm_num) le_rfl

theorem gfRaw_eq (s : List Byte) :
    gfRaw s = if 16 ≤ s.length then
      some (⟨leNat (s.take 16) % 2 ^ 128, Nat.mod_lt _ (by positivity)⟩, s.drop 16) else none := by
  unfold gfRaw rejNat
  rw [Sampler.rej_eq]
  split_ifs
  · have ha : natAttempt 128 (2 ^ 128) (s.take 16)
        = some ⟨leNat (s.take 16) % 2 ^ 128, Nat.mod_lt _ (by positivity)⟩ := by
      unfold natAttempt
      rw [dif_pos (Nat.mod_lt _ (by positivity))]
    rw [ha]
  · rfl

/-- **A field element**: the raw sampler's value through the field's representation bijection
(`to_montgomery`, `Gf2_128::from`). -/
def elt {F : Type} {n : ℕ} (e : Fin n ≃ F) (raw : Sampler (Fin n)) : Sampler F := Sampler.map e raw

theorem elt_local {F : Type} {n : ℕ} (e : Fin n ≃ F) {raw : Sampler (Fin n)} (h : raw.Local) :
    (elt e raw).Local := Sampler.map_local h

theorem elt_balanced {F : Type} {n : ℕ} (e : Fin n ≃ F) {raw : Sampler (Fin n)}
    (h : raw.Balanced) : (elt e raw).Balanced := Sampler.Balanced.map_bijective h e.bijective

/-! ## 5. Tuples -/

namespace Sampler

variable {α : Type}

/-- **Draws in sequence** (`elt_field_slice`'s loop, `choose`'s loop): a tuple whose `i`-th entry
is drawn by `ps i`, first entry first. -/
def dvec : (k : ℕ) → {β : Fin k → Type} → (∀ i, Sampler (β i)) → Sampler (∀ i, β i)
  | 0, _, _ => pure (fun i => i.elim0)
  | k + 1, _, ps => map (fun ab => Fin.cons ab.1 ab.2) (seq (ps 0) (dvec k fun i => ps i.succ))

theorem dvec_local : ∀ (k : ℕ) {β : Fin k → Type} (ps : ∀ i, Sampler (β i)),
    (∀ i, (ps i).Local) → (dvec k ps).Local
  | 0, _, _, _ => pure_local _
  | k + 1, _, ps, h => map_local (seq_local (h 0) (dvec_local k (fun i => ps i.succ) fun _ => h _))

theorem cons_bijective {k : ℕ} {β : Fin (k + 1) → Type} :
    Function.Bijective (fun ab : β 0 × (∀ i : Fin k, β i.succ) => (Fin.cons ab.1 ab.2 : ∀ i, β i)) :=
  (Fin.consEquiv β).bijective

theorem dvec_balanced : ∀ (k : ℕ) {β : Fin k → Type} [∀ i, Fintype (β i)]
    (ps : ∀ i, Sampler (β i)), (∀ i, (ps i).Local) → (∀ i, (ps i).Balanced) →
    (dvec k ps).Balanced
  | 0, _, _, _, _, _ => pure_balanced _
  | k + 1, _, _, ps, hl, hb =>
    Balanced.map_bijective
      (Balanced.seq (hl 0) (hb 0) (dvec_balanced k (fun i => ps i.succ) (fun _ => hl _)
        fun _ => hb _)) cons_bijective

/-- **`elt_field_slice(k)`**: `k` draws of one sampler. -/
def vec (k : ℕ) (p : Sampler α) : Sampler (Fin k → α) := dvec k fun _ => p

theorem vec_local (k : ℕ) {p : Sampler α} (h : p.Local) : (vec k p).Local :=
  dvec_local k _ fun _ => h

theorem vec_balanced [Fintype α] (k : ℕ) {p : Sampler α} (hl : p.Local) (hb : p.Balanced) :
    (vec k p).Balanced :=
  dvec_balanced k _ (fun _ => hl) fun _ => hb

end Sampler

/-! ## 6. `choose`: the partial Fisher–Yates shuffle -/

section FisherYates

variable {n k : ℕ}

/-- Step `i`'s position `i`. -/
def fyPos (u : ∀ i : Fin k, Fin (n - i)) (i : Fin k) : Fin n :=
  ⟨i, by have := (u i).isLt; omega⟩

/-- Step `i`'s swap partner `j = i + nat(n − i)` (`< n`, so Rust's `% n` does nothing:
`fyJ_mod`). -/
def fyJ (u : ∀ i : Fin k, Fin (n - i)) (i : Fin k) : Fin n :=
  ⟨i + u i, by have := (u i).isLt; omega⟩

theorem fyJ_mod (u : ∀ i : Fin k, Fin (n - i)) (i : Fin k) :
    ((i : ℕ) + (u i : ℕ)) % n = fyJ u i := Nat.mod_eq_of_lt (fyJ u i).isLt

/-- **The array after `i` steps**, as the permutation `σᵢ` with `a[p] = σᵢ p`: `a = [0, n)` is
`σ₀ = 1`, and `a.swap(i, j)` is `σᵢ₊₁ = σᵢ * swap i j`. -/
def fyPerm (u : ∀ i : Fin k, Fin (n - i)) : ℕ → Equiv.Perm (Fin n)
  | 0 => 1
  | i + 1 => if h : i < k then fyPerm u i * Equiv.swap (fyPos u ⟨i, h⟩) (fyJ u ⟨i, h⟩)
      else fyPerm u i

/-- **`res[i] = a[i]`, read after step `i`'s swap.** -/
def fyRes (u : ∀ i : Fin k, Fin (n - i)) (i : Fin k) : Fin n := fyPerm u (i + 1) (fyPos u i)

theorem fyRes_eq (u : ∀ i : Fin k, Fin (n - i)) (i : Fin k) :
    fyRes u i = fyPerm u i (fyJ u i) := by
  unfold fyRes
  rw [fyPerm, dif_pos i.isLt]
  simp only [Equiv.Perm.coe_mul, Function.comp_apply]
  rw [show (⟨(i : ℕ), i.isLt⟩ : Fin k) = i from rfl, Equiv.swap_apply_left]

/-- Later swaps do not move a position already read. -/
theorem fyPerm_stable (u : ∀ i : Fin k, Fin (n - i)) (t : Fin k) :
    ∀ m, (t : ℕ) + 1 ≤ m → fyPerm u m (fyPos u t) = fyRes u t := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ m ih =>
    intro h
    by_cases hm : (t : ℕ) = m
    · unfold fyRes
      rw [hm]
    · have ih' := ih (by omega)
      rw [fyPerm]
      split_ifs with hk
      · simp only [Equiv.Perm.coe_mul, Function.comp_apply]
        rw [Equiv.swap_apply_of_ne_of_ne, ih']
        · intro he
          have := congrArg Fin.val he
          simp [fyPos] at this
          omega
        · intro he
          have := congrArg Fin.val he
          simp [fyPos, fyJ] at this
          omega
      · exact ih'

theorem fyRes_eq_final (u : ∀ i : Fin k, Fin (n - i)) (t : Fin k) :
    fyRes u t = fyPerm u k (fyPos u t) :=
  (fyPerm_stable u t k (by omega)).symm

/-- **The chosen indices are distinct.** -/
theorem fyRes_injective (u : ∀ i : Fin k, Fin (n - i)) : Function.Injective (fyRes u) := by
  intro t t' h
  rw [fyRes_eq_final, fyRes_eq_final] at h
  have := congrArg Fin.val ((fyPerm u k).injective h)
  exact Fin.ext (by simpa [fyPos] using this)

/-- The array after `i` steps reads only the draws before step `i`. -/
theorem fyPerm_congr {u u' : ∀ i : Fin k, Fin (n - i)} :
    ∀ i, (∀ t : Fin k, (t : ℕ) < i → u t = u' t) → fyPerm u i = fyPerm u' i := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro h
    rw [fyPerm, fyPerm]
    split_ifs with hk
    · rw [ih (fun t ht => h t (by omega))]
      have hj : fyJ u ⟨i, hk⟩ = fyJ u' ⟨i, hk⟩ := by
        apply Fin.ext
        simp only [fyJ]
        rw [h ⟨i, hk⟩ (by simp)]
      rw [hj]
      rfl
    · exact ih (fun t ht => h t (by omega))

/-- **The draws are recovered from the chosen indices.** -/
theorem fyRes_inj : Function.Injective (fyRes (n := n) (k := k)) := by
  intro u u' h
  suffices H : ∀ m, ∀ t : Fin k, (t : ℕ) < m → u t = u' t from
    funext fun t => H (t + 1) t (by omega)
  intro m
  induction m with
  | zero => intro t ht; omega
  | succ m ih =>
    intro t ht
    by_cases htm : (t : ℕ) < m
    · exact ih t htm
    · have hσ := fyPerm_congr (u := u) (u' := u') t (fun t' ht' => ih t' (by omega))
      have hr := congrFun h t
      rw [fyRes_eq, fyRes_eq, hσ] at hr
      have := congrArg Fin.val ((fyPerm u' t).injective hr)
      simp only [fyJ] at this
      exact Fin.ext (by omega)

theorem card_draws (n k : ℕ) :
    Fintype.card (∀ i : Fin k, Fin (n - i)) = Fintype.card (Fin k ↪ Fin n) := by
  rw [Fintype.card_pi, Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin,
    Nat.descFactorial_eq_prod_range]
  simp only [Fintype.card_fin]
  exact Fin.prod_univ_eq_prod_range (fun i => n - i) k

/-- The draws as an injective tuple. -/
def fyEmb (u : ∀ i : Fin k, Fin (n - i)) : Fin k ↪ Fin n := ⟨fyRes u, fyRes_injective u⟩

/-- **The partial Fisher–Yates shuffle is a bijection from the draws onto the injective
`k`-tuples**: as an ordered tuple of distinct indices, `choose`'s output is uniform. -/
theorem fyEmb_bijective : Function.Bijective (fyEmb (n := n) (k := k)) :=
  (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨fun _ _ h => fyRes_inj (congrArg (fun t : Fin k ↪ Fin n => (t : Fin k → Fin n)) h),
      card_draws n k⟩

/-- The `k`-subsets of `[0, n)` (`LigeroFamily.QuerySet n k`). -/
abbrev QSet (n k : ℕ) := ↥((univ : Finset (Fin n)).powersetCard k)

/-- An injective tuple's set of entries. -/
def embSet (t : Fin k ↪ Fin n) : QSet n k :=
  ⟨univ.map t, by simp [mem_powersetCard]⟩

/-- A permutation carrying one `k`-subset into another. -/
theorem exists_perm_maps (S S' : QSet n k) : ∃ τ : Equiv.Perm (Fin n), ∀ x ∈ S.1, τ x ∈ S'.1 := by
  have hS := (mem_powersetCard.mp S.2).2
  have hS' := (mem_powersetCard.mp S'.2).2
  let e : {x // x ∈ S.1} ≃ {x // x ∈ S'.1} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe, hS, hS'])
  exact ⟨e.extendSubtype, fun x hx => Equiv.extendSubtype_mem e x hx⟩

theorem embSet_fiber_le (S S' : QSet n k) :
    (univ.filter fun t : Fin k ↪ Fin n => embSet t = S).card
      ≤ (univ.filter fun t : Fin k ↪ Fin n => embSet t = S').card := by
  obtain ⟨τ, hτ⟩ := exists_perm_maps S S'
  refine card_le_card_of_injOn (fun t => t.trans τ.toEmbedding) ?_ ?_
  · intro t ht
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at ht ⊢
    apply Subtype.ext
    have hsub : univ.map (t.trans τ.toEmbedding) ⊆ S'.1 := by
      intro y hy
      simp only [mem_map, mem_univ, true_and, Function.Embedding.trans_apply,
        Equiv.toEmbedding_apply] at hy
      obtain ⟨i, rfl⟩ := hy
      refine hτ _ ?_
      rw [← ht]
      simp [embSet]
    refine Finset.eq_of_subset_of_card_le hsub ?_
    rw [(mem_powersetCard.mp S'.2).2]
    simp [embSet]
  · intro t _ t' _ h
    refine Function.Embedding.ext fun i => ?_
    have := congrArg (fun x : Fin k ↪ Fin n => x i) h
    simpa using this

theorem embSet_fiber (S S' : QSet n k) :
    (univ.filter fun t : Fin k ↪ Fin n => embSet t = S).card
      = (univ.filter fun t : Fin k ↪ Fin n => embSet t = S').card :=
  le_antisymm (embSet_fiber_le S S') (embSet_fiber_le S' S)

/-- **`choose`'s output as the deployed query set.** -/
def chooseSet (u : ∀ i : Fin k, Fin (n - i)) : QSet n k := embSet (fyEmb u)

theorem chooseSet_fiber (S S' : QSet n k) :
    (univ.filter fun u : (∀ i : Fin k, Fin (n - i)) => chooseSet u = S).card
      = (univ.filter fun u : (∀ i : Fin k, Fin (n - i)) => chooseSet u = S').card := by
  have h : ∀ S : QSet n k, (univ.filter fun u : (∀ i : Fin k, Fin (n - i)) => chooseSet u = S).card
      = (univ.filter fun t : Fin k ↪ Fin n => embSet t = S).card := fun S =>
    card_equiv (Equiv.ofBijective _ fyEmb_bijective) fun u => by
      simp [chooseSet]
  rw [h, h, embSet_fiber]

end FisherYates

/-- **Rust's `choose(n, k)`** (`lib.rs`), `k ≤ n`: `k` successive draws `nat(n − i)`, the partial
Fisher–Yates shuffle, and the set of chosen indices (the deployed query set). -/
def chooseRust (n k : ℕ) (hkn : k ≤ n) : Sampler (QSet n k) :=
  Sampler.map chooseSet
    (Sampler.dvec k fun i : Fin k => natRust (n - i) (by have := i.isLt; omega))

/-- `choose` as an ordered tuple of distinct indices. -/
def chooseTuple (n k : ℕ) (hkn : k ≤ n) : Sampler (Fin k ↪ Fin n) :=
  Sampler.map fyEmb
    (Sampler.dvec k fun i : Fin k => natRust (n - i) (by have := i.isLt; omega))

theorem chooseRust_local (n k : ℕ) (hkn : k ≤ n) : (chooseRust n k hkn).Local :=
  Sampler.map_local (Sampler.dvec_local k _ fun _ => natRust_local _ _)

/-- **`choose` is balanced as an ordered tuple of distinct indices.** -/
theorem chooseTuple_balanced (n k : ℕ) (hkn : k ≤ n) : (chooseTuple n k hkn).Balanced :=
  Sampler.Balanced.map_bijective
    (Sampler.dvec_balanced k _ (fun _ => natRust_local _ _) fun _ => natRust_balanced _ _)
    fyEmb_bijective

/-- **`choose` is balanced as the deployed query set**: every `k`-subset is chosen, by consuming
exactly `j` bytes, by the same number of byte strings. -/
theorem chooseRust_balanced (n k : ℕ) (hkn : k ≤ n) : (chooseRust n k hkn).Balanced :=
  Sampler.Balanced.map
    (Sampler.dvec_balanced k _ (fun _ => natRust_local _ _) fun _ => natRust_balanced _ _)
    fun S S' => by
      have := chooseSet_fiber S S'
      convert this using 3

end Lfzk.StreamSampler
