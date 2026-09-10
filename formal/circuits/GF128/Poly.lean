/-!
# GF(2^128), as the deployed code represents it

The mdoc **hash** circuit — SHA-256, the CBOR window checks, the MACs — is compiled over
GF(2^128) (`mdoc_zk/compile/src/generate_hash.rs:69`), not over a prime field. Its
`assert_wrapping_sum` is therefore the *multiplicative* one
(`circuits/analog_adder/src/circuit.rs:117`), which puts a 32-bit word value in the **exponent**
of the field generator:

```
inject(v) = Π_{i<32} (1 + (α^(2^i) − 1)·bᵢ)  =  α^(Σ 2^i·bᵢ)
assert     Π_{j<n} (got − α^(j·2^32)·want) = 0
```

`SHA/Wrap.lean`'s positional theory does not apply to that, and its replacement needs two things
this file supplies: a *computable* model of the field, and the multiplicative order of α.

## Why a `Nat`-backed model rather than an abstract field

The p256 bridges work over an abstract `[Field F] [CharP F p256w]` and never construct the field,
because every artifact constant is a `Nat` cast into `F`. In characteristic 2 a `Nat` cast reaches
only `0` and `1`, while the artifact's constant table holds 16-byte elements that are not in the
prime subfield. So the constant map *must* be "read these bits as polynomial coefficients", and
the field has to be constructed.

Everything here is `Nat` shifts and xors, which the Lean kernel accelerates through GMP, so the
order certificate below is a `decide +kernel` computation rather than a hand proof. No Mathlib:
this layer is deliberately import-free so that it stays cheap and so the algebraic layer above it
(the `Field` instance, via irreducibility of `P`) can be developed against a fixed model.

## Provenance

* `rp` — `core/algebra/src/gf2_128.rs:24`, `P(x) = x^128 + x^7 + x^2 + x + 1`.
* `alpha` — `compile/algebra/src/gf2_128.rs:330`, `generator() = Gf2_128(2)`, i.e. the class of `x`.
* `beta`, `gf16Basis` — `core/algebra/src/proto.rs:24`, `GF2_16_BASIS_V1`.

The Cantor basis (`proto.rs:43`) is *not* pinned here. It belongs to the LCH14 additive-FFT
encoding rather than to circuit semantics, and it does not satisfy the textbook Cantor recurrence
under this representation, so pinning it needs its own investigation.
-/

namespace GF128

/-- Extension degree. -/
abbrev w : Nat := 128

/-- Low 128 coefficients of `P(x) = x^128 + x^7 + x^2 + x + 1`, i.e. `x^7 + x^2 + x + 1`. -/
def rp : Nat := 0x87

/-- An element is a bit pattern below `2^128`; `red` is the canonical form. -/
def inRange (a : Nat) : Prop := a < 2 ^ w

instance : DecidablePred inRange := fun _ => Nat.decLt _ _

/-! ## Arithmetic

Addition is xor. Multiplication is the shift-and-add ladder of `gf2_128.rs`'s `mul`: walk the bits
of `b`, accumulating `a` and multiplying `a` by `x` each step. -/

/-- `a + b`. In characteristic 2 this is also `a - b`. -/
def add (a b : Nat) : Nat := a ^^^ b

/-- `x · a`, reduced. Doubling sets bit 128 exactly when `a` had bit 127. -/
def xtime (a : Nat) : Nat :=
  if a <<< 1 >>> w = 0 then a <<< 1 else ((a <<< 1) ^^^ (1 <<< w)) ^^^ rp

/-- `n` steps of the ladder: `acc + a·b` where only the low `n` bits of `b` are consumed. -/
def mulAux : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | n + 1, a, b, acc =>
      mulAux n (xtime a) (b >>> 1) (if b &&& 1 = 1 then acc ^^^ a else acc)

/-- `a · b`. -/
def mul (a b : Nat) : Nat := mulAux w a b 0

/-- `a²`. -/
def sq (a : Nat) : Nat := mul a a

/-- Square-and-multiply, `n` bits of `e`, exiting early once `e` is exhausted. -/
def powAux : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | n + 1, a, e, acc =>
      if e = 0 then acc
      else powAux n (mul a a) (e >>> 1) (if e &&& 1 = 1 then mul acc a else acc)

/-- `a ^ e`. The fuel covers every exponent below `2^160`, which is all we use. -/
def pow (a e : Nat) : Nat := powAux 160 a e 1

/-! ## Sanity: the ladder really is a commutative ring operation

Not a proof — those belong to the algebraic layer — but enough to catch a transcription error in
the reduction step before anything is built on it. -/

section Sanity

private def v₁ : Nat := 0x0123456789abcdeffedcba9876543210
private def v₂ : Nat := 0xdeadbeefcafebabe0f1e2d3c4b5a6978
private def v₃ : Nat := 0x5c5971877501d4b8f1871e01b64fda4c

example : mul 1 v₁ = v₁ := by decide +kernel
example : mul v₁ 1 = v₁ := by decide +kernel
example : mul 0 v₁ = 0 := by decide +kernel
example : mul v₁ v₂ = mul v₂ v₁ := by decide +kernel
example : mul (mul v₁ v₂) v₃ = mul v₁ (mul v₂ v₃) := by decide +kernel
example : mul v₁ (add v₂ v₃) = add (mul v₁ v₂) (mul v₁ v₃) := by decide +kernel
/-- `x · a` and `mul 2 a` are the same operation. -/
example : xtime v₁ = mul 2 v₁ := by decide +kernel
/-- Frobenius is additive. -/
example : sq (add v₁ v₂) = add (sq v₁) (sq v₂) := by decide +kernel
/-- Reduction actually fires: `x^127 · x = x^128 = x^7 + x^2 + x + 1`. -/
example : mul (2 ^ 127) 2 = rp := by decide +kernel

end Sanity

/-! ## α, and its multiplicative order

`compile/algebra/src/gf2_128.rs:330` takes the generator to be `Gf2_128(2)`, the class of `x`.
The wrapping-sum assertion is sound only if distinct 33-bit exponents give distinct powers, so
what is needed is a *lower bound* on `ord α`; the adder's own overflow guard demands only
`ord α > 2^32 · n` with `n ≤ 7` addends, i.e. `> 2^35`.

In fact `x` is **primitive** for this polynomial: `ord α = 2^128 − 1`, with enormous slack. The
certificate is Lucas's: `α^(N) = 1` while `α^(N/q) ≠ 1` for every prime `q ∣ N`. Both halves are
`decide +kernel` computations here; that they are the *right* computations — that the nine
factors below are prime and exhaust `N` — is discharged in the algebraic layer, which can import
`ECDSA/Pratt.lean`. -/

/-- The field generator, `Gf2_128(2)` — the class of `x`. -/
def alpha : Nat := 2

/-- `N = 2^128 − 1`, the order of the multiplicative group. -/
def N : Nat := 2 ^ 128 - 1

/-- The prime factors of `2^128 − 1`. `2^32 − 1 = 3·5·17·257·65537`,
    `2^32 + 1 = 641·6700417`, and `2^64 + 1 = 274177·67280421310721`. -/
def NFactors : List Nat := [3, 5, 17, 257, 641, 65537, 274177, 6700417, 67280421310721]

/-- The factorization is complete. (Primality of each factor is the algebraic layer's job.) -/
theorem NFactors_prod : NFactors.foldl (· * ·) 1 = N := by decide +kernel

/-- Lucas, first half. -/
theorem alpha_pow_N : pow alpha N = 1 := by decide +kernel

/-- Lucas, second half: α survives every maximal proper divisor. Together with
    `NFactors_prod` and primality of the factors this gives `ord α = 2^128 − 1`. -/
theorem alpha_pow_cofactor_ne_one :
    NFactors.all (fun q => pow alpha (N / q) != 1) = true := by decide +kernel

/-- What the adder actually needs: the ladder's `alpha_k = α^(2^32)` is not the identity, so the
    32-bit windows in `Π_j (got − α^(j·2^32)·want)` are genuinely distinct. -/
theorem alphaK_ne_one : pow alpha (2 ^ 32) ≠ 1 := by decide +kernel

/-- The injection basis the adder builds by repeated squaring: `basis i = α^(2^i)`. -/
def injBasis (i : Nat) : Nat := pow alpha (2 ^ i)

/-- `basis` really is built by squaring, as `analog_adder/src/circuit.rs:143` builds it. -/
theorem injBasis_succ : (List.range 31).all (fun i => injBasis (i + 1) == sq (injBasis i)) = true := by
  decide +kernel

/-! ## The adder's injection, and what the meaning lemma has to prove

Transcribed from `analog_adder/src/circuit.rs:150-186`. In characteristic 2 the `sub` there is
`add`, so `1 + (α^(2^i) − 1)·bᵢ` is `1 + (α^(2^i) + 1)·bᵢ`: the factor is `1` when the bit is
clear and `α^(2^i)` when it is set. Hence `inject v = α^v`, which is the lemma the field layer
owes — proved there, because it needs `α^m · α^n = α^(m+n)` and so the monoid structure. Here it
is only *checked*, which is enough to catch a misreading of the Rust. -/

/-- `inject`: the multiplicative embedding of a 32-bit word. -/
def inject (bits : Nat) : Nat :=
  (List.range 32).foldl
    (fun acc i => mul acc (add 1 (mul (add (injBasis i) 1) (bits >>> i &&& 1)))) 1

/-- `inject` is `α^(·)` on 32-bit inputs — spot-checked, including both endpoints. -/
theorem inject_spot :
    [0, 1, 2, 3, 31, 0x80000000, 0xffffffff, 0xdeadbeef, 0x0f0f0f0f].all
      (fun v => inject v == pow alpha v) = true := by decide +kernel

/-- The assertion the circuit emits for `expected = Σ terms (mod 2^32)`, with `n = terms.length`
    windows: `Π_{j<n} (got − α^(j·2^32)·want)`. Again `−` is `+`. -/
def wrapAssert (expected : Nat) (terms : List Nat) : Nat :=
  let want := inject expected
  let got := terms.foldl (fun acc t => mul acc (inject t)) 1
  (List.range terms.length).foldl
    (fun acc j => mul acc (add got (mul (pow alpha (j * 2 ^ 32)) want))) 1

/-- **The specification of the port, checked.** The assertion vanishes exactly on the wrapping
    sum: it accepts the correct `expected` (including a case that genuinely wraps, and one that
    wraps twice), and rejects `expected + 1`. The second half is the soundness direction — the one
    the meaning lemma must establish — and it is what makes the first half non-vacuous. -/
theorem wrapAssert_spot :
    -- no wrap
    wrapAssert 0x00000005 [0x00000002, 0x00000003] = 0
    -- one wrap
    ∧ wrapAssert 0x00000001 [0xffffffff, 0x00000002] = 0
    -- two wraps, three addends
    ∧ wrapAssert 0xfffffffd [0xffffffff, 0xffffffff, 0xffffffff] = 0
    -- and a wrong expected is rejected in each case
    ∧ wrapAssert 0x00000006 [0x00000002, 0x00000003] ≠ 0
    ∧ wrapAssert 0x00000002 [0xffffffff, 0x00000002] ≠ 0
    ∧ wrapAssert 0xfffffffc [0xffffffff, 0xffffffff, 0xffffffff] ≠ 0 := by
  decide +kernel

/-! ## The subfield of size 2^16

`GF2_16_BASIS_V1` is the F₂-basis the Ligero encoding uses for the subfield
(`runtime/algebra/src/subfield.rs`, `block_enc ≤ 1 <<< subfield.dimension()`). It is not an
arbitrary basis: it is the **power basis** of a single element β, which is primitive in
GF(2^16). Pinning that turns sixteen opaque 128-bit constants into one element plus a fact. -/

/-- β, the subfield generator: `GF2_16_BASIS_V1[1]`. -/
def beta : Nat := 0x5c5971877501d4b8f1871e01b64fda4c

/-- `GF2_16_BASIS_V1` verbatim from `core/algebra/src/proto.rs:24`. -/
def gf16Basis : List Nat :=
  [0x00000000000000000000000000000001,
   0x5c5971877501d4b8f1871e01b64fda4c,
   0x8bb99658eaf2cae0a6e310fb6e176ea8,
   0xb61e08da12f9665c3f8de8a2f9ff7eed,
   0xa76c2e634c6483ae9ba3282087a3f827,
   0x54944ff4a5269cedf7af4e93629f689e,
   0x5439ecfd75a950d8d0765f1873309b88,
   0x49ecdfbe06777b02e566f9fc3d9b58a2,
   0x97a401b733e66a9319af205497f8e2d0,
   0x789fd7793ce7523860e4dbdce9777814,
   0xaa440b2d4b546256c0f157187adbc05b,
   0x79f2cadb70b6115d222f207d0d8ad9f9,
   0xae72af7894ce037df6d1f84fb66c52b8,
   0xd6f226d783d454db4af94ef056d28a30,
   0x057d918d494925fc0f37a0a4d91b4220,
   0x18d4bbb6833c5ae8b683012350e55753]

/-- **The shipped basis is the power basis of β.** -/
theorem gf16Basis_eq_powers : gf16Basis = (List.range 16).map (pow beta) := by decide +kernel

/-- β is fixed by the 16th Frobenius power, so it lies in GF(2^16). -/
theorem beta_frobenius : pow beta (2 ^ 16) = beta := by decide +kernel

/-- …and in no proper subfield of it: GF(2^16)'s proper subfields are GF(2^8), GF(2^4), GF(2^2),
    GF(2), so β has degree exactly 16 over F₂ and the power basis really is a basis. -/
theorem beta_degree_16 :
    pow beta (2 ^ 8) ≠ beta ∧ pow beta (2 ^ 4) ≠ beta ∧ pow beta (2 ^ 2) ≠ beta ∧
      pow beta 2 ≠ beta := by
  decide +kernel

/-- The prime factors of `2^16 − 1 = 65535`. -/
def betaOrderFactors : List Nat := [3, 5, 17, 257]

theorem betaOrderFactors_prod : betaOrderFactors.foldl (· * ·) 1 = 65535 := by decide +kernel

/-- Lucas again: β is primitive in GF(2^16). -/
theorem beta_pow_order : pow beta 65535 = 1 := by decide +kernel

theorem beta_pow_cofactor_ne_one :
    betaOrderFactors.all (fun q => pow beta (65535 / q) != 1) = true := by decide +kernel

/-- β's minimal polynomial over F₂, as the coefficient list of
    `x^16 + x^15 + x^13 + x^12 + x^11 + x^9 + x^8 + x^7 + x^5 + x^4 + 1`
    (low 16 coefficients; the leading `x^16` is implicit). -/
def betaMinPoly : Nat := 0xbbb1

/-- The minimal polynomial evaluated at β is zero: `β^16 = Σ cᵢ βⁱ`. -/
theorem beta_minPoly_root :
    ((List.range 16).foldl
      (fun acc i => if betaMinPoly >>> i &&& 1 = 1 then add acc (pow beta i) else acc) 0)
      = pow beta 16 := by
  decide +kernel

end GF128
