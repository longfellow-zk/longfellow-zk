/-
# The comparators

The second gadget obligation `Assertions.lean` names: `arithmetic::lt` and `memcmp::leq` on bit
vectors are `<` and `≤` on the values they encode. Three clause families rest on it —
`shift_preimage_bounds/{ge_five, lt}`, `assert_mso_validity/{cmp_from, cmp_until}`, and
`assert_nblocks`'s four bounds — and `Spec.LeBytes` is written as if it held.

## What was already there

`ECDSA/BitLt.lean` models the gadget for `rx_lt_order` and `nms_lt_order`, and most of the work
is done there:

* `step_assoc` — `lt_reduce` is associative as a polynomial identity, so `tree_fold2`'s splitting
  is irrelevant;
* `bfold_spec` — the `Bool`-level fold is exactly `(a = b, value a < value b)`;
* `base_enc`, `step_enc`, `bfold_excl` — the circuit's polynomials compute those `Bool`
  operations, including that `or_assuming_at_most_one_true` may be `+`;
* `lt_of_foldStL` — if the fold's second component is `1`, the values compare.

## What this file adds

Three things, all of which the mdoc clauses need and `rx_lt_order` did not.

1. **The other direction.** `lt_of_foldStL` is `= 1 → <`. `leq a b` is `¬ lt b a`, so asserting a
   `leq` gives a wire that is **zero**, and `≤` has to come out of that. `bfold_spec` is an
   equality of `Bool`s, so both directions are available; only one had been extracted.

2. **The tree, pinned.** `eval_eq_foldSt` says *any* shape agrees with the linear fold. That is
   the right generality, but it leaves the actual shape unstated — and a bridge that read the
   wrong shape off the DAG would still be provable. `balancedFold` is `util::array::tree_fold2`'s
   own recursion, halving at `i0 + (i1 - i0) / 2`, and `balancedFold_eq` is what says the deployed
   splitting is one of the shapes that agree.

3. **The byte reversal.** `memcmp::leq` does not compare bit vectors; it calls `arrange` first,
   which emits the bytes' bit lists **most significant byte last**, and then compares. So the
   comparison is on `beVal`, and that is what makes `Spec.LeBytes` — big-endian, hence
   chronological on ISO-8601 — the right reading.

## What stays outside

That a `V8` wire's eight bits encode its byte. That is the bit-packing convention, established by
`is_boolean` together with `as_eltw`, and it is a hypothesis here (`hbits`) rather than a
conclusion — the same convention every other clause needs, so it does not belong to the
comparator.
-/

import Mathlib
import mdoc.Spec
import ECDSA.BitLt

namespace MDoc
namespace Compare

open ECDSA2.BitLt

/-! ## Values of bit lists

`bval` is least-significant-first, matching `Bitvec`'s weighting. -/

/-- Splitting a bit list splits its value. -/
theorem bval_append : ∀ (a b : List Bool), bval (a ++ b) = bval a + 2 ^ a.length * bval b
  | [], b => by simp [bval]
  | x :: xs, b => by
      have ih := bval_append xs b
      simp only [List.cons_append, bval, ih, List.length_cons]
      ring

/-- Peeling the top byte off a big-endian value. -/
theorem beVal_cons (b : Nat) (bs : List Nat) :
    beVal (b :: bs) = b * 256 ^ bs.length + beVal bs := by
  have hfold : ∀ (l : List Nat) (s : Nat),
      l.foldl (fun acc d => acc * 256 + d) s
        = s * 256 ^ l.length + l.foldl (fun acc d => acc * 256 + d) 0 := by
    intro l
    induction l with
    | nil => intro s; simp
    | cons d ds ih =>
        intro s
        have h1 := ih (s * 256 + d)
        have h2 := ih d
        simp only [List.foldl_cons, List.length_cons, Nat.zero_mul, Nat.zero_add]
        rw [h1, h2]
        ring
  simpa [beVal] using hfold bs b

/-! ## `memcmp::arrange`

```rust
for i in (0..n).rev() { bits.extend(bytes[i].iter().cloned()); }
```

The bytes' bit lists, least significant byte **first** in the emitted list — which is the reverse
of the byte string's own order, so the value the comparator sees is the big-endian one. -/

/-- The bit list `memcmp` compares. `bits v` is the wire encoding of one byte. -/
def arranged (bits : Nat → List Bool) (bytes : List Nat) : List Bool :=
  bytes.reverse.flatMap bits

/-- Eight bits per byte, so the arranged list is eight times as long. -/
theorem arranged_length (bits : Nat → List Bool) (hlen : ∀ v, (bits v).length = 8) :
    ∀ l : List Nat, (arranged bits l).length = 8 * l.length := by
  have hflat : ∀ m : List Nat, (m.flatMap bits).length = 8 * m.length := by
    intro m
    induction m with
    | nil => simp
    | cons x xs ih =>
        simp only [List.flatMap_cons, List.length_append, ih, hlen, List.length_cons]
        ring
  intro l
  simpa [arranged] using hflat l.reverse

/-- **The reversal is what makes the comparison big-endian.** Given only that each byte's wire
    encodes it in eight bits, the arranged bit list has value `beVal`. -/
theorem bval_arranged (bits : Nat → List Bool)
    (hval : ∀ v, bval (bits v) = v) (hlen : ∀ v, (bits v).length = 8) :
    ∀ bytes : List Nat, bval (arranged bits bytes) = beVal bytes := by
  intro bytes
  induction bytes with
  | nil => simp [arranged, beVal, bval]
  | cons b bs ih =>
      have hrev : (b :: bs).reverse = bs.reverse ++ [b] := by simp
      have hsplit : arranged bits (b :: bs) = arranged bits bs ++ bits b := by
        simp only [arranged, hrev, List.flatMap_append, List.flatMap_cons,
          List.flatMap_nil, List.append_nil]
      have hlen' : (arranged bits bs).length = 8 * bs.length := arranged_length bits hlen bs
      rw [hsplit, bval_append, ih, hlen', hval, beVal_cons]
      have : (2 : Nat) ^ (8 * bs.length) = 256 ^ bs.length := by
        rw [pow_mul]; norm_num
      rw [this]
      ring

/-! ## `tree_fold2`, pinned

```rust
if i1 - i0 > 1 { let im = i0 + (i1 - i0) / 2; f(recur(i0, im), recur(im, i1)) }
else if i1 - i0 == 1 { base(&a[i0], &b[i0]) }
```

Over the list of per-bit states rather than over indices, which removes the index arithmetic
without changing the split. Fuel-driven, as this codebase's other recursions are; the fuel-out
case falls back to the linear fold, so `balancedFold_eq` needs no bound on it. -/

variable {F : Type} [Field F]

/-- `util::array::tree_fold2`'s recursion. `fold2` returns `default = (1, 0)` on an empty slice,
    which is the `[]` case; the `[s]` case is `tree_fold2`'s `i1 - i0 == 1` leaf. -/
def balancedFold : Nat → List (St F) → St F
  | 0, l => foldStL l
  | _, [] => (1, 0)
  | _, [s] => s
  | fuel + 1, l =>
      step (balancedFold fuel (l.take (l.length / 2))) (balancedFold fuel (l.drop (l.length / 2)))

/-- **The deployed splitting is one of the shapes that agree.** Whatever depth `tree_fold2`
    reaches, its value is the linear fold — so `foldStL_enc` and `bfold_spec` apply to it. -/
theorem balancedFold_eq : ∀ (fuel : Nat) (l : List (St F)), balancedFold fuel l = foldStL l
  | 0, l => rfl
  | _ + 1, [] => rfl
  | _ + 1, [s] => (foldStL_singleton s).symm
  | fuel + 1, s0 :: s1 :: rest => by
      rw [show balancedFold (fuel + 1) (s0 :: s1 :: rest)
            = step (balancedFold fuel ((s0 :: s1 :: rest).take ((s0 :: s1 :: rest).length / 2)))
                   (balancedFold fuel ((s0 :: s1 :: rest).drop ((s0 :: s1 :: rest).length / 2)))
          from rfl,
        balancedFold_eq fuel, balancedFold_eq fuel, ← foldStL_append, List.take_append_drop]

/-- The slices `balancedFold` bottoms out on, in the same recursion. Only the leaves matter:
    everywhere else `balancedFold` applies `step`, which is what `tree_fold2` does. -/
def leaves : Nat → List (St F) → List (List (St F))
  | 0, l => [l]
  | _, [] => [[]]
  | _, [s] => [[s]]
  | fuel + 1, l => leaves fuel (l.take (l.length / 2)) ++ leaves fuel (l.drop (l.length / 2))

/-- **The tree really does bottom out at singletons.** `balancedFold`'s fuel-0 case falls back to
    the *linear* fold, so a model that ran out of fuel would silently be `foldStL` again. With
    `tree_fold2`'s own depth — enough halvings that `l.length ≤ 2 ^ fuel` — every leaf has length
    at most one, and the fallback is only ever reached where the two agree.

    This is the one thing `balancedFold_eq` cannot tell you: it holds for *every* fuel, so no
    statement about the fold's value distinguishes the balanced tree from the linear one. -/
theorem leaves_le_one : ∀ (fuel : Nat) (l : List (St F)), l.length ≤ 2 ^ fuel →
    ∀ p ∈ leaves fuel l, p.length ≤ 1
  | 0, l, h, p, hp => by
      simp only [leaves, List.mem_singleton] at hp
      subst hp; simpa using h
  | _ + 1, [], _, p, hp => by simp only [leaves, List.mem_singleton] at hp; subst hp; simp
  | _ + 1, [_], _, p, hp => by simp only [leaves, List.mem_singleton] at hp; subst hp; simp
  | fuel + 1, a :: b :: rest, h, p, hp => by
      have hlen : (a :: b :: rest).length = rest.length + 2 := by simp
      have hpow : (2 : Nat) ^ (fuel + 1) = 2 ^ fuel + 2 ^ fuel := by rw [pow_succ]; ring
      have hstep : leaves (fuel + 1) (a :: b :: rest)
          = leaves fuel ((a :: b :: rest).take ((a :: b :: rest).length / 2))
            ++ leaves fuel ((a :: b :: rest).drop ((a :: b :: rest).length / 2)) := rfl
      rw [hstep] at hp
      have hL : (a :: b :: rest).length ≤ 2 ^ fuel + 2 ^ fuel := by omega
      rcases List.mem_append.mp hp with hq | hq
      · refine leaves_le_one fuel _ ?_ p hq
        rw [List.length_take]
        omega
      · refine leaves_le_one fuel _ ?_ p hq
        rw [List.length_drop]
        omega

/-! ## Both directions

The circuit asserts a wire is `1` (for `lt`) or, through `notb`, that another wire is `0` (for
`leq`). Each needs its own reading of `bfold_spec`. -/

/-- The bit-pair states the fold consumes, as `foldStL` wants them. -/
def states (a b : List Bool) : List (St F) :=
  (a.zip b).map (fun q => base (enc (F := F) q.1) (enc q.2))

/-- `assert_true` on a `lt` wire. This is `BitLt.lt_of_foldStL`, restated over `states`. -/
theorem lt_of_asserted (a b : List Bool) (hlen : a.length = b.length)
    (h : (foldStL (states (F := F) a b)).2 = 1) : bval a < bval b :=
  lt_of_foldStL a b hlen h

/-- **The direction `leq` needs.** A `lt` wire that is zero means the values do *not* compare —
    and since `leq a b` is `notb (lt b a)`, asserting a `leq` is exactly this. -/
theorem not_lt_of_asserted (a b : List Bool) (hlen : a.length = b.length)
    (h : (foldStL (states (F := F) a b)).2 = 0) : ¬ (bval a < bval b) := by
  rw [states, foldStL_enc a b hlen] at h
  obtain ⟨-, h2⟩ := bfold_spec a b hlen
  cases hb : (bfold a b).2 with
  | true =>
      simp only [hb, enc_true] at h
      exact absurd h one_ne_zero
  | false =>
      rw [hb] at h2
      simpa using h2.symm

/-- `assert_true` on a `leq` wire: `leq a b = notb (lt b a)`, so the asserted `1` is a zero on the
    `lt b a` wire, and `≤` follows. -/
theorem le_of_leq_asserted (a b : List Bool) (hlen : a.length = b.length)
    (h : (foldStL (states (F := F) b a)).2 = 0) : bval a ≤ bval b := by
  have := not_lt_of_asserted b a hlen.symm h
  omega

/-! ## Landing on `Spec`

The two forms the mdoc clauses use. -/

/-- **`cmp_from` and `cmp_until`.** `memcmp::leq x y` asserted true is `Spec.LeBytes x y`. The
    byte lists must have equal length, which for the validity window they do: both are 20-byte
    ISO-8601 timestamps. -/
theorem leBytes_of_leq_asserted (bits : Nat → List Bool)
    (hval : ∀ v, bval (bits v) = v) (hbl : ∀ v, (bits v).length = 8)
    (x y : List Nat) (hlen : x.length = y.length)
    (h : (foldStL (states (F := F) (arranged bits y) (arranged bits x))).2 = 0) :
    LeBytes x y := by
  have hal : (arranged bits x).length = (arranged bits y).length := by
    calc (arranged bits x).length = 8 * x.length := arranged_length bits hbl x
      _ = 8 * y.length := by rw [hlen]
      _ = (arranged bits y).length := (arranged_length bits hbl y).symm
  have hle := le_of_leq_asserted (F := F) (arranged bits x) (arranged bits y) hal h
  rw [bval_arranged bits hval hbl x, bval_arranged bits hval hbl y] at hle
  exact hle

/-- **`shift_preimage_bounds/lt` and `assert_nblocks`.** A `lt` wire asserted true on two bit
    vectors is `<` on the numbers they carry. -/
theorem lt_of_bitvec (a b : List Bool) (u v : Nat)
    (hlen : a.length = b.length) (ha : bval a = u) (hb : bval b = v)
    (h : (foldStL (states (F := F) a b)).2 = 1) : u < v := by
  rw [← ha, ← hb]; exact lt_of_asserted a b hlen h

/-- **`shift_preimage_bounds/ge_five`.** `leq five off` asserted true is `5 ≤ off`. -/
theorem le_of_bitvec (a b : List Bool) (u v : Nat)
    (hlen : a.length = b.length) (ha : bval a = u) (hb : bval b = v)
    (h : (foldStL (states (F := F) b a)).2 = 0) : u ≤ v := by
  rw [← ha, ← hb]; exact le_of_leq_asserted a b hlen h

end Compare
end MDoc
