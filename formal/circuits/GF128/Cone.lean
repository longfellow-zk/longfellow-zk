import GF128.Wrap

/-!
# Connecting `wrap_gf` to the artifact

`wrap_gf` consumes `wrapPolyM n (α ^ 2^32) want got = 0`. What the certificate actually delivers
is `interpDag dag inputs root = 0` for a cone the compiler emitted. This file closes the gap in
the two places where it is more than bookkeeping.

## What the cone looks like

Measured on the `Sha256Gf2` artifact (`assert_wrapping_sum_gf2`, `rounds.0/round_step`, a
six-addend `e` assertion), the top of the 632-node cone is

```
  46560 = consts  0 · v46284 · v46548  +  consts  0 · v1721 · v46550
  46558 = consts  0 · v46284 · v46548  +  consts 34 · v1721 · v46550
  46557 = consts  0 · v46284 · v46548  +  consts 35 · v1721 · v46550
  …
  46559 = consts 0 · v46557 · v46558          -- the product tree
  46561 = consts 0 · v1822  · v46560
  46562 = consts 0 · v46559 · v46561
  46556 = consts 0 · v46553 · v46555
  46563 = consts 0 · v46556 · v46562          -- the asserted node
```

so `got = v46284 · v46548`, `want = v1721 · v46550`, and the six factors `got + cⱼ · want` are
combined by a binary tree. In characteristic 2 the compiler's `sub` is `add`, which is why every
coefficient is positive.

## The two real steps

**The coefficients are powers.** `consts 0, 34, 35, 36, 37, 38, 39` are exactly `α^(j·2^32)` for
`j = 0 … 6` — the adder's `p` array (`analog_adder/src/circuit.rs:173`). `constPowers` checks
that against the deployed constant table by kernel reduction, and `const_eq_alpha_pow` carries it
into `F` through `eval_pow`. The table stops at `j = 6` because the adder's largest sum has seven
addends.

**The tree shape does not matter.** `wrapPolyM` is a right-nested recursion, but the circuit
emits a balanced tree. `wrapPolyM_eq_prod` re-associates it into a `Finset.prod`, after which any
tree shape closes by `ring` at the instance.

What is left for a generated bridge is bookkeeping: `coneIs` to match the cone against its
template, and `ring` to identify the emitted tree with the product.
-/

set_option maxRecDepth 100000

namespace GF128

variable {F : Type*} [Field F] [CharP F 2]

/-! ## The coefficients are the powers the adder builds -/

/-- `p[j] = α^(j·2^32)` — the adder's window multipliers, as bit patterns. -/
def windowConst (j : Nat) : Nat := pow (pow alpha (2 ^ 32)) j

/-- **The deployed constant table really holds those powers.** These are `constants` 0, 34, 35,
    36, 37, 38, 39 of the `Sha256Gf2` artifact, verbatim, against `j = 0 … 6`. -/
theorem constPowers :
    [0x00000000000000000000000000000001, 0x782d0a995dd3b01821777af80695052a,
     0xcec3202236b9330fde0a74a95b11a7b2, 0x296257ed0b57f45878f43f166cf9adc1,
     0xcad1b2dd09125a5f800a7b44dd8e7a70, 0xeb360cf94a2fe65e3a4966cfa00f9088,
     0x280d3b04f89584233703a881672987cf]
      = (List.range 7).map windowConst := by
  decide +kernel

/-- Every window constant is in range, so `eval` may be applied to it. -/
theorem windowConst_lt (j : Nat) : windowConst j < 2 ^ 128 :=
  pow_lt (pow_lt (by decide) _) _

/-- **The bridge for a coefficient.** A `Nat` constant that `decide` says is `windowConst j`
    evaluates to `(α ^ 2^32) ^ j` in the field. -/
theorem const_eq_alpha_pow (α : F) (h : IsGen α) {c j : Nat} (hc : c = windowConst j)
    (hj : j < 2 ^ 32) : eval α c = (α ^ 2 ^ 32) ^ j := by
  have hbase : eval α (pow alpha (2 ^ 32)) = α ^ 2 ^ 32 := by
    rw [eval_pow α h.root (by decide) (by decide), eval_alpha']
  rw [hc, windowConst, eval_pow α h.root (pow_lt (by decide) _) (by omega), hbase]


/-- `injConst i = injBasis i + 1` — the adder's `GF2_16_BASIS_V1` entry for bit `i`, plus one:
    the coefficient the compiler stores on bit `i` of every injection factor, so that the factor
    reads `1 + (injConst i) · b`. In characteristic 2 that coefficient is `α^(2^i) - 1`. -/
def injConst (i : Nat) : Nat := add (injBasis i) 1

/-- **The deployed table holds the injection basis too**, at indices 2 … 33 in order. Together
    with `constPowers` this pins every coefficient the wrapping-sum cone uses: the injection
    factors and the window multipliers. Verbatim from the `Sha256Gf2` header. -/
theorem injConsts :
    [     0x00000000000000000000000000000003, 0x00000000000000000000000000000005,
     0x00000000000000000000000000000011, 0x00000000000000000000000000000101,
     0x00000000000000000000000000010001, 0x00000000000000000000000100000001,
     0x00000000000000010000000000000001, 0x00000000000000000000000000000086,
     0x00000000000000000000000000004014, 0x00000000000000000000000010000110,
     0x00000000000000000100000000010100, 0x00010000000000000000000100010000,
     0x00000087000000010000000100000000, 0x000000000021caea0000000000000087,
     0x000000000000000000021cae93f7cfc9, 0x00000004015044544105551550555041,
     0x1001001111110961118fe6196978ef71, 0x860140d2541486c693c692c775187986,
     0x8b69509b312d6501ea618e11df04ea1f, 0xb715594eb7756558cad0352d30b311b5,
     0x01afdeffd35e5fde54e1a6f865fe82b8, 0x11b4a30358935542218289f09c0659ec,
     0x83a513579eda579397b14587eebe264c, 0x83ad91f69582bddf38d15180f9de45ac,
     0xc7f8a41756ad614d1a97936b620f481c, 0xbb844bf6957599a6e94bf5687ccf4c38,
     0x2c3bd83d0661350d5aadb3837634c245, 0x24f6fc2353c7f2321f726995c3f33828,
     0x150e344316f35f82a5b7efc52c5e9c52, 0xcbe66ebbc72d228a891738c79d5ad318,
     0xd331a77342cf2867fbb824714f38f6c3, 0x60dcdee4d2f1fc9262609e6968de22b1]
      = (List.range 32).map injConst := by
  decide +kernel

theorem injConst_lt (i : Nat) : injConst i < 2 ^ 128 :=
  Nat.xor_lt_two_pow (pow_lt (by decide) _) (by decide)

/-- **The bridge for an injection coefficient.** The bound on `i` is the word width; beyond it
    the `Nat` ladder's fuel would truncate, and the circuit never asks. -/
theorem const_eq_injBasis (α : F) (h : IsGen α) {c i : Nat} (hc : c = injConst i)
    (hi : i < 32) : eval α c = α ^ 2 ^ i - 1 := by
  have hfuel : (2 : Nat) ^ i < 2 ^ 160 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  rw [hc]
  show eval α (injBasis i ^^^ 1) = _
  rw [eval_add, injBasis, eval_pow α h.root (by decide) hfuel, eval_alpha', eval_one,
    CharTwo.sub_eq_add]

/-- **The bridge for a folded coefficient.** `algsimp` multiplies the round constant into a
    product node rather than injecting it bit by bit, so 64 of the injection cones' product rows
    carry `α^(Kₜ)` instead of `1`. A `Nat` constant that `decide` says is `pow alpha K`
    evaluates to `α^K`; `K = 0` recovers the plain product. -/
theorem const_eq_pow (α : F) (h : IsGen α) {c K : Nat} (hc : c = pow alpha K)
    (hK : K < 2 ^ 160) : eval α c = α ^ K := by
  rw [hc, eval_pow α h.root (by decide) hK, eval_alpha']

/-! ## The tree shape does not matter -/

/-- `wrapPolyM` re-associated. The recursion peels the *last* factor, so the product runs over
    `Finset.range n` in the same order. -/
theorem wrapPolyM_eq_prod :
    ∀ (n : Nat) (t z g : F), wrapPolyM n t z g = ∏ j ∈ Finset.range n, (g - t ^ j * z)
  | 0, _, _, _ => by simp [wrapPolyM]
  | n + 1, t, z, g => by
      rw [wrapPolyM, Finset.prod_range_succ, wrapPolyM_eq_prod n t z g]
      ring

/-- **The cone-side entry point.** However the compiler associated the product of the `n`
    factors, if the asserted node is zero then `wrapPolyM` is zero. `hfact` is what the emitted
    template gives after `coneIs_transfer`; `hroot` is `ring` at the instance. -/
theorem wrapPolyM_zero_of_prod (α : F) (n : Nat) (want got root : F)
    (facts : Nat → F)
    (hfact : ∀ j, j < n → facts j = got - (α ^ 2 ^ 32) ^ j * want)
    (hroot : root = ∏ j ∈ Finset.range n, facts j)
    (hzero : root = 0) :
    wrapPolyM n (α ^ 2 ^ 32) want got = 0 := by
  rw [wrapPolyM_eq_prod, ← hzero, hroot]
  exact (Finset.prod_congr rfl (fun j hj => (hfact j (Finset.mem_range.mp hj)).symm))

/-! ## The two halves composed

The shape a generated meaning lemma ends in: cone hypotheses on the left, the `Nat` statement
about 32-bit arithmetic on the right. Nothing below this line mentions a DAG, and nothing above
it mentions `SHA256`. -/

theorem wrap_of_cone (α : F) (h : IsGen α)
    (n : Nat) (hbound : n * 2 ^ 32 ≤ N)
    (bs : Nat → Nat → F) (vs : Nat → Nat) (be : Nat → F) (e : Nat)
    (hbs : ∀ k, k < n → ∀ i, i < 32 → bs k i = if (vs k).testBit i then 1 else 0)
    (hbe : ∀ i, i < 32 → be i = if e.testBit i then 1 else 0)
    (hv : ∀ k, k < n → vs k < 2 ^ 32) (he : e < 2 ^ 32)
    (facts : Nat → F) (root : F)
    (hfact : ∀ j, j < n → facts j
      = (∏ k ∈ Finset.range n, injectF α (bs k) 32)
          - (α ^ 2 ^ 32) ^ j * injectF α be 32)
    (hroot : root = ∏ j ∈ Finset.range n, facts j)
    (hzero : root = 0) :
    e = (∑ k ∈ Finset.range n, vs k) % 2 ^ 32 :=
  wrap_gf α h n hbound bs vs be e hbs hbe hv he
    (wrapPolyM_zero_of_prod α n _ _ root facts hfact hroot hzero)

/-! ## The tree discharge, on the shape the compiler actually emitted

Nodes 46556/46559/46561/46562/46563 associate the six factors as `(f₀·f₁)·((f₂·f₃)·(f₄·f₅))`.
This is what `hroot` costs at an instance. -/

example (f : Nat → F) :
    (f 0 * f 1) * ((f 2 * f 3) * (f 4 * f 5)) = ∏ j ∈ Finset.range 6, f j := by
  simp [Finset.prod_range_succ]
  ring

/-- And the seven-addend shape the `a` assertions use, associated differently. -/
example (f : Nat → F) :
    ((f 0 * f 1) * (f 2 * f 3)) * ((f 4 * f 5) * f 6) = ∏ j ∈ Finset.range 7, f j := by
  simp [Finset.prod_range_succ]
  ring

end GF128
