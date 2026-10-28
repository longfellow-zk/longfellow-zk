# Fixed-coefficient and assertion streams

`coefficient-separated` extends the degree-separated compiler with LFD3.
`assertion-separated` additionally optimizes assertions and emits LFD4. Both
features include `degree-separated`; ordinary compilation remains unchanged.
Use separate caches for each experiment. The runtime reads LFC2, LFD2, LFD3
and LFD4 independently of the compiler feature selection.

Each degree stream has separate general-coefficient and coefficient-one arrays.
General deltas retain a coefficient-table index. Unit deltas contain coordinates
only: `(g,h0,h1)` for quadratic terms, `(g,h)` for linear terms and `(g)` for
constants. Their in-memory dictionary entries occupy 12, 8 and 4 bytes, rather
than the general entry's 16 bytes. Segments and macro tokens compress each array
independently. Fixed coefficient values are explicitly owned initialization state.

Coefficient zero denotes an assertion, not an ordinary zero-valued summand:

| Array | Meaning | Binding contribution |
|---|---|---|
| Quadratic assertion | `W[l] W[r] = 0` | `rho W[r]` in the prover's left coefficients |
| Linear assertion (LFD4) | `W[l] = 0` | `rho` in the prover's left coefficients |

Assertions retain their diagnostic g coordinate, but their independently sampled
`rho` replaces the whole output-weight/coefficient factor. They do not accumulate
an output value. Quadratic assertion dictionaries use three u32 coordinates;
linear assertion dictionaries use two. Final circuit outputs retain their implicit
zero requirement and are not included in these serialized assertion-array counts.

LFD3 stores seven arrays: general/unit/assertion quadratics, general/unit linears,
and general/unit constants. LFD4 stores an eighth array for linear assertions.
Each array has LFC2's delta dictionary, segment dictionary and token sequence.
Fixed arrays omit the coefficient index entirely. Coordinate accumulators reset
per array. The reader validates indices, macro references, arities and the combined
expanded-term budget. General arrays reject coefficients zero and one. Constant
assertions are not encoded: tautological constants are simplified; asserting a
nonzero constant is a compile-time error.

Circuit identity domains distinguish LFD3 and LFD4 and authenticate the degree,
coefficient class and expanded coordinates, including assertion order. Repeated
macro compression and coefficient-table renumbering preserve identity.

## Compiler lowering

With `assertion-separated`, a single quadratic expression passed to `assert0`
is lowered directly to an assertion over its two factors. A nonzero scalar
coefficient can be discarded because it does not change whether their product
vanishes. A structural unit factor makes the assertion linear. Products used
elsewhere are still computed for those uses; products needed only for the
assertion are not materialized. Repeated equivalent assertions share the
existing assertion-scope union mechanism.

Other asserted expressions retain their computed value wire. Internal assertions
on that wire become linear assertions instead of the old square-zero marker.
Assertions already enforced by final zero outputs keep that representation.
No One input or copied One wire is introduced.

## Sumcheck reduction

Assertion challenges are sampled in quadratic-array order followed by linear-array
order. Quadratic assertions enter Q with their replacement coefficients. Linear
assertions enter the same affine part as ordinary linear gates:

```
q_l[l] = sum_{g,r} a[g] Q[g,l,r] W[r]
         + sum_g a[g] L[g,l]
         + sum_{linear assertion j at l} rho[j].
```

The public correction at the final monomial point is

```
L_u = sum_{g,l} a[g] L[g,l] m_u[l]
      + sum_{linear assertion j} rho[j] m_u[l_j].
```

The next claim remains `A + alpha*B - alpha*L_u`, with weights `m + alpha*q_r`
formed only from Q. Both prover and verifier apply this correction. No extra
masked messages, pads or multiplication checks are added. Evaluation tests linear
assertions directly, and quadratic assertions through their product. Hot bindings
traverse separate arrays instead of classifying coefficients per quadratic term.

## Measurements

[Coefficient split](../../benches/results/2026-10-28-coefficient-streams/README.md)
compares LFD2 with LFD3. [Assertion split](../../benches/results/2026-10-28-assertion-streams/README.md)
compares LFD3 with LFD4, including term counts, bytes, decoded circuit allocations,
peak heap and paired online timings.
