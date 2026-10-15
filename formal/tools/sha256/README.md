# SHA-256 bridge generators

These emit the generated half of `circuits/quadcert/Bridge/Sha256/`: the modules that carry the
deployed circuit's 6,840 assertions to `circuits/SHA/Spec.lean`. They read the artifact **out of
the generated Lean modules** (`Gen/Sha256Blk/Sha256BlkNodes*.lean`, `…Asserts*.lean`,
`…Base.lean`, `…Data.lean`), so what they emit is checked against exactly the node table the
proofs see.

Nothing here is needed to *check* the proofs — the emitted `.lean` files are committed. These
are for regenerating after a circuit change.

## Order

Each stage depends on the `.pkl` the stage above writes.

| run | writes | emits |
|---|---|---|
| `gen_final_bridge.py` | — | `S2Final.lean` (8 `final` assertions) |
| `emit_final_comp.py` | — | `S2FinalComp.lean` (`hout`) |
| `gen_sched_all.py` | `insts.pkl` | — |
| `emit_sched.py` | — | `S2SchedA…H.lean` (48 `schedule`) |
| `emit_comp.py` | — | `S2CompA…H.lean` (`hsched`) |
| `gen_rnd.py` | `rinsts.pkl` | — |
| `emit_rnd.py all` | — | `S2RndA…P.lean` (128 `round_step`) |
| `emit_edges_rnd.py` | — | `S2EdgesRnd.lean` (n=6, n=7 wrap edge lists) |
| `emit_comp_rnd.py all` | — | `S2CRndA…P.lean` (`hrnd_a`, `hrnd_e`) |
| `emit_assemble.py` | — | `S2Assemble.lean` |
| `gen_asserttbl.py` | `asserttbl.pkl` | — |
| `emit_flat.py` | — | `S2Flat.lean` |
| `emit_assert.py` | — | `S2Assert.lean` |
| `emit_bytes.py` | — | `S2Bytes.lean` |
| `emit_connect.py` | — | `S2Connect.lean` |

### Three things that were broken and are not any more

* **Hardcoded paths.** Fifteen scripts carried `/Users/abhi/...` output paths from the machine
  they were written on, so they wrote nothing reachable (or crashed) anywhere else. Each now
  derives its root from `__file__`, the way `sha_parse.py` already did.
* **`asserttbl.pkl` had no producer.** `emit_flat`/`emit_assert`/`emit_bytes` all read it and
  nothing wrote it, so the committed copy was the only one and it went stale at the next
  recompile — `emit_assert.py` died with `KeyError: 1104`, a booleanity assertion present in the
  artifact but absent from the old table. `gen_asserttbl.py` rebuilds it from the artifact.
* **`gen_comp.py` loaded `wordtbl.pkl` and never used it.** That pickle has no producer either,
  so a dead load was all that stopped the `emit_comp.py` stage from running.

`sha_parse.py` and `sha_classify.py` are the shared artifact reader and assertion classifier.
`comp2.py` and `comp_rnd.py` hold the composition emitters for the schedule and round classes.
The `.pkl` files are derived; delete them and rerun the `gen_*` stage.

## What the generators check before emitting

Each asserts its structural model against the artifact and dies rather than emit something the
kernel would later reject. These all held on the current circuit:

* every schedule cone's five words are `{t, t-2, t-7, t-15, t-16}` — 48/48;
* every three-way σ bit's leg set matches `SHA256.sigma0`/`sigma1`'s index formula;
* every round cone's word set matches `stateBits`, with the round index recovered from its
  `K` constant — 128/128;
* Σ₁'s xor legs both come from `e`, Σ₀'s both from `a`, Maj's one from each of `a`, `b` —
  6,144 σ bits and 2,048 Maj mids, no exceptions.

## Three artifact quirks they handle

* Round 18's `n = 6` assertion **owns** the shared constant node `532`; the other 63 reference
  it, so its product-tree map is contiguous where theirs has a gap.
* Round 5's `n = 7` product tree is the one instance of 128 the compiler emitted with reversed
  operands; it gets `tnWrap7b` and a single-instance `coneIs` route.
* Maj's `a ⊕ b` mid takes its legs in either order — 1,100 of 2,048 with `a` first. The group is
  emitted in the mid's own order and reconciled by `SHA256.majb_comm`.

Two counts differ from what a reader might guess and are load-bearing: σ₀ has 29 three-way bits
(not 32 — `shr 3` kills the third leg at `j ≥ 29`) and σ₁ has 22.


## GF(2^128) variant

`sha_parse.py` and `sha_classify.py` take `SHA_ARTIFACT` (default `Sha256Blk`); set it to
`Sha256Gf2` to read the binary-field circuit. The classifier needed no change — it stops at
nodes with two or more terms, which is exactly where the wrap factors are in both fields.

| run | emits |
|---|---|
| `SHA_ARTIFACT=Sha256Gf2 python3 gen_gf2_wrap.py` | `Bridge/Sha256Gf2/Gf2WrapTmpl.lean` |

### What it checks before emitting

The binary-field assertion is `Π_j (got − α^(j·2^32)·want) = 0`, where `got` and `want` are each
a product of two earlier nodes. All 184 wrap cones were confirmed to have exactly that shape:

* every cone's factors share **one** `got` pair and **one** `want` pair — 184/184;
* their coefficients are exactly the window constants `α^(j·2^32)` for `j = 0 … n-1` — 184/184;
* only **five** distinct product trees occur across all 184 cones.

`gen_gf2_wrap.py` then simulates `Core/ConeTmpl.coneIs` in Python and refuses to write if any
instance would fail, so a template the kernel would reject is never emitted. Lean's own
`decide +kernel` confirms all 56 emitted instances in about 6 s.

### Two things the p256 generators do not have to handle

* **`j = 0` carries the unit coefficient.** `α^(0·2^32) = 1 = constNat 0`, so *both* terms of the
  first factor have coefficient index 0 and the `got`/`want` split cannot be read off the
  coefficients alone. The generator identifies `want` from a factor with a non-unit window
  coefficient and then splits the rest by operand pair.
* **The round classes carry an extra constant factor.** It is a 9-deep squaring chain rooted at
  the `one` wire — i.e. the value 1, a redundant multiplication the compiler left in. Its
  template needs those nine rows and `inputs 0 = 1`; the `n = 2` and `n = 4` classes have no such
  factor, which is why they were done first.

The single odd instance — one of the 64 `n = 6` rounds, whose product tree associates
differently from the other 63 — is the direct analogue of the p256 quirk at round 5 and gets its
own class, `W6b`.

### What it emits, and what is left

Five templates covering all 184 wrap cones, each with one instance map per assertion:

| class | instances | template nodes |
|---|---:|---:|
| `W7` | 64 | 20 |
| `W6` | 63 | 19 |
| `W4` | 48 | 11 |
| `W2` | 8 | 7 |
| `W6b` | 1 | 19 |

`Bridge/Sha256Gf2/Gf2Wrap.lean` closes each class to `GF128.wrapPolyM … = 0`. Nineteen and
twenty nodes match what `compile/compiler/examples/cone_probe.rs` measures independently for
these cones — the first version of the generator emitted 26, because `const_chain` walked *past*
a node that was already a template leaf and left seven rows nothing referenced.

**Still open: the injection layer.** What is proved is that `wrapPolyM` vanishes on the four
artifact nodes the cone names. Reading that as 32-bit arithmetic through `GF128.wrap_nat_gf`
needs `got = Π_k injectF α (bs k) 32` and `want = injectF α be 32`, i.e. the cones *below* those
four nodes. Measured: **431 distinct operand nodes** (428 real injections, 3 the shared constant
chain), cones of 7 to 416 nodes, median 192, 81,036 nodes in total.
