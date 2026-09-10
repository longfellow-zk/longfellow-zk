# The GF(2^128) hash circuit's word layer, identified from the artifact

Produced by `tools/sha256/gf2_word_probe.py` (`SHA_ARTIFACT=Sha256Gf2`), which reads each
`assert_wrapping_sum_gf2` cone, partitions its injection factors into 32-row addend groups, and
resolves every group's wires against `Bridge/Sha256Gf2/Gf2Words.lean` — the bit-node lists the
sidecar's layout names. Nothing here is a hand-written correspondence: the words, the rotation
offsets and the register indexing all come out of the committed artifact.

**Result: every one of the 184 wrapping-sum assertions is fully identified, with zero unresolved
groups.** The rotation constants that come out are FIPS 180-4's, exactly:

| quantity | offsets found | FIPS 180-4 |
|---|---|---|
| `Σ₀` | rotate 2, 13, 22 | `(x⋙2) ⊕ (x⋙13) ⊕ (x⋙22)` |
| `Σ₁` | rotate 6, 11, 25 | `(x⋙6) ⊕ (x⋙11) ⊕ (x⋙25)` |
| `σ₀` | rotate 7, 18 + shift 3 | `(x⋙7) ⊕ (x⋙18) ⊕ (x≫3)` |
| `σ₁` | rotate 17, 19 + shift 10 | `(x⋙17) ⊕ (x⋙19) ⊕ (x≫10)` |

The shifts show up as an *arity split*: `σ₀`'s `≫3` leg vanishes at the top 3 bit positions, so
that addend is 29 three-leg rows and 3 two-leg rows; `σ₁`'s `≫10` gives 22 and 10. A rotation
would give 32 three-leg rows. So the shift/rotate distinction is measured, not assumed.

Register indexing comes out as the standard rotation — at round `t`,
`e = oute[t-1], f = oute[t-2], g = oute[t-3], h = oute[t-4]` and
`a = outa[t-1], b = outa[t-2], c = outa[t-3], d = outa[t-4]`, with `hinBits` standing in for the
first four rounds. The per-class equations:

    W4 (48)   W[t+16] = σ₁(W[t+14]) + W[t+9] + σ₀(W[t+1]) + W[t]
    W6 (63)   oute[t] = outa[t-4] + oute[t-4] + Σ₁(oute[t-1]) + Ch(oute[t-1],oute[t-2],oute[t-3])
                        + W[t] + Kₜ
    W7 (64)   outa[t] = oute[t-4] + Σ₁(oute[t-1]) + Ch(…) + W[t]
                        + Σ₀(outa[t-1]) + Maj(outa[t-1],outa[t-2],outa[t-3]) + Kₜ
    W6b (1)   the same as W6 at t = 25, associated differently
    W2 (8)    h1[i] = hin[i] + (a…h at round 63)

`Kₜ` is not a listed addend because it is not injected bit by bit: `algsimp` folded `α^(Kₜ)` into
a product node, so it appears as a *summand of the exponent*. That is why `n` is 7 for `a` and 6
for `e` — `Kₜ` counts as an addend — and it is checked separately by `Gf2Sound.constNat_round`.

The distinct "shapes" per class are the boundary rounds (where the state comes from `hinBits`
rather than from a previous round's output) and the compiler's choice of which operand slot holds
which factor. They are enumerated below verbatim.

---


### W2  (n=2, 8 instances, 8 distinct shapes)
    1 x
        got1  one   outaBits[t+63]
        got2  one   hinBits[t]
        want2 one   h1Bits[t]
    1 x
        got1  one   outaBits[t+61]
        got2  one   hinBits[t]
        want2 one   h1Bits[t]
    1 x
        got1  one   outaBits[t+59]
        got2  one   hinBits[t]
        want2 one   h1Bits[t]
    1 x
        got1  one   hinBits[t]
        got2  one   outaBits[t+57]
        want2 one   h1Bits[t]
    1 x
        got1  one   hinBits[t]
        got2  one   outeBits[t+59]
        want2 one   h1Bits[t]
    1 x
        got1  one   hinBits[t]
        got2  one   outeBits[t+57]
        want2 one   h1Bits[t]
    1 x
        got1  one   hinBits[t]
        got2  one   outeBits[t+55]
        want2 one   h1Bits[t]
    1 x
        got1  one   outeBits[t+53]
        got2  one   hinBits[t]
        want2 one   h1Bits[t]

### W4  (n=4, 48 instances, 1 distinct shapes)
   48 x
        got1  one   wordBits[t]
        got1  xor   wordBits[t+1]@[3, 7, 18] PARTIAL:29
        got1  xor   wordBits[t+1]@[7, 18] PARTIAL:3
        got2  one   wordBits[t+9]
        got2  xor   wordBits[t+14]@[10, 17, 19] PARTIAL:22
        got2  xor   wordBits[t+14]@[17, 19] PARTIAL:10
        want2 one   wordBits[t+16]

### W6  (n=6, 63 instances, 8 distinct shapes)
   26 x
        got1  ch    outeBits[t],outeBits[t-1],outeBits[t-2]
        got1  one   outeBits[t-3]
        got1  one   wordBits[t+1]
        got1  xor   outeBits[t]@[6, 11, 25]
        got2  one   outaBits[t-3]
        want2 one   outeBits[t+1]
   12 x
        got1  ch    outeBits[t-1],outeBits[t-2],outeBits[t-3]
        got1  one   outeBits[t-4]
        got1  one   wordBits[t]
        got1  xor   outeBits[t-1]@[6, 11, 25]
        got2  one   outaBits[t-4]
        want2 one   outeBits[t]
   12 x
        got1  one   outaBits[t-3]
        got2  ch    outeBits[t],outeBits[t-1],outeBits[t-2]
        got2  one   outeBits[t-3]
        got2  one   wordBits[t+1]
        got2  xor   outeBits[t]@[6, 11, 25]
        want2 one   outeBits[t+1]
    9 x
        got1  one   outaBits[t-4]
        got2  ch    outeBits[t-1],outeBits[t-2],outeBits[t-3]
        got2  one   outeBits[t-4]
        got2  one   wordBits[t]
        got2  xor   outeBits[t-1]@[6, 11, 25]
        want2 one   outeBits[t]
    1 x
        got1  ch    hinBits[t+4],hinBits[t+5],hinBits[t+6]
        got1  one   hinBits[t+7]
        got1  one   wordBits[t]
        got1  xor   hinBits[t+4]@[6, 11, 25]
        got2  one   hinBits[t+3]
        want2 one   outeBits[t]
    1 x
        got1  ch    outeBits[t-1],hinBits[t+3],hinBits[t+4]
        got1  one   hinBits[t+5]
        got1  one   wordBits[t]
        got1  xor   outeBits[t-1]@[6, 11, 25]
        got2  one   hinBits[t+1]
        want2 one   outeBits[t]
    1 x
        got1  ch    outeBits[t-1],outeBits[t-2],hinBits[t+2]
        got1  one   hinBits[t+3]
        got1  one   wordBits[t]
        got1  xor   outeBits[t-1]@[6, 11, 25]
        got2  one   hinBits[t-1]
        want2 one   outeBits[t]
    1 x
        got1  ch    outeBits[t-1],outeBits[t-2],outeBits[t-3]
        got1  one   hinBits[t+1]
        got1  one   wordBits[t]
        got1  xor   outeBits[t-1]@[6, 11, 25]
        got2  one   hinBits[t-3]
        want2 one   outeBits[t]

### W7  (n=7, 64 instances, 6 distinct shapes)
   59 x
        got1  ch    outeBits[t-1],outeBits[t-2],outeBits[t-3]
        got1  one   outeBits[t-4]
        got1  one   wordBits[t]
        got1  xor   outeBits[t-1]@[6, 11, 25]
        got2  maj   outaBits[t-3],outaBits[t-2],outaBits[t-1]
        got2  xor   outaBits[t-1]@[2, 13, 22]
        want2 one   outaBits[t]
    1 x
        got1  ch    hinBits[t+4],hinBits[t+5],hinBits[t+6]
        got1  one   hinBits[t+7]
        got1  one   wordBits[t]
        got1  xor   hinBits[t+4]@[6, 11, 25]
        got2  maj   hinBits[t],hinBits[t+1],hinBits[t+2]
        got2  xor   hinBits[t]@[2, 13, 22]
        want2 one   outaBits[t]
    1 x
        got1  ch    outeBits[t-1],hinBits[t+3],hinBits[t+4]
        got1  one   hinBits[t+5]
        got1  one   wordBits[t]
        got1  xor   outeBits[t-1]@[6, 11, 25]
        got2  maj   hinBits[t-1],hinBits[t],outaBits[t-1]
        got2  xor   outaBits[t-1]@[2, 13, 22]
        want2 one   outaBits[t]
    1 x
        got1  ch    outeBits[t-1],outeBits[t-2],hinBits[t+2]
        got1  one   hinBits[t+3]
        got1  one   wordBits[t]
        got1  xor   outeBits[t-1]@[6, 11, 25]
        got2  maj   hinBits[t-2],outaBits[t-2],outaBits[t-1]
        got2  xor   outaBits[t-1]@[2, 13, 22]
        want2 one   outaBits[t]
    1 x
        got1  ch    outeBits[t-1],outeBits[t-2],outeBits[t-3]
        got1  one   hinBits[t+1]
        got1  one   wordBits[t]
        got1  xor   outeBits[t-1]@[6, 11, 25]
        got2  maj   outaBits[t-3],outaBits[t-2],outaBits[t-1]
        got2  xor   outaBits[t-1]@[2, 13, 22]
        want2 one   outaBits[t]
    1 x
        got1  ch    outeBits[t-1],outeBits[t-2],outeBits[t-3]
        got1  one   outeBits[t-4]
        got1  one   wordBits[t]
        got1  xor   outeBits[t-1]@[6, 11, 25]
        got2  maj   outaBits[t-3],outaBits[t-2],outaBits[t-1]
        got2  xor   outaBits[t-1]@[2, 13, 22]
        want1 one   outaBits[t]

### W6b  (n=6, 1 instances, 1 distinct shapes)
    1 x
        got1  ch    outeBits[t+24],outeBits[t+23],outeBits[t+22]
        got1  one   outeBits[t+21]
        got1  one   wordBits[t+25]
        got1  xor   outeBits[t+24]@[6, 11, 25]
        got2  one   outaBits[t+21]
        want2 one   outeBits[t+25]
