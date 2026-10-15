import Lfzk.LigeroV1Rows

/-!
# Certified round-by-round Ligero V1 rows at the deployed v7 geometries

`Lfzk.LigeroV1Rows` certifies `Row`s at the **v8** geometry (the current generator, not in the
registry).  The deployed registry (`rust/applications/mdoc_zk/runtime/src/zk_spec.rs`, `ZK_SPECS`)
lists version 7 as its latest registered version, with `ligero_config(rateinv 7, nreq 132,
block_enc)`: hash `block_enc` 4151 / 4265 / 4307 / 4415 for 1 / 2 / 3 / 4 attributes and signature
`block_enc` 4096.  The Ligero parameter code (`rust/runtime/ligero/src/param.rs`,
`lib/ligero/ligero_param.h`) sets `block = (block_enc + 1) / (2 + rateinv)`,
`dblock = 2·block − 1` and `block_ext = block_enc − dblock`; a row's `k` is `block` and its `n` is
`block_ext`, the columns the verifier opens:

| row | field | `block_enc` | `n` | `k` | `w = k − 132` | RBR bits |
|---|---|---|---|---|---|---|
| `v7Sig` | P-256 base | 4096 | 3187 | 455 | 323 | 122 |
| `v7Hash1` | `GF(2^128)` | 4151 | 3230 | 461 | 329 | 115 |
| `v7Hash2` | `GF(2^128)` | 4265 | 3318 | 474 | 342 | 115 |
| `v7Hash3` | `GF(2^128)` | 4307 | 3352 | 478 | 346 | 115 |
| `v7Hash4` | `GF(2^128)` | 4415 | 3436 | 490 | 358 | 115 |

The geometry was read off the deployed verifier itself (`ZkVerifier::geometry` on the stored,
ID-checked v7 circuits, `lfzk/scripts/inspect_v7_circuit_profile.py` →
`v7-circuit-profiles.json`), and agrees with the v7 rows of
`formal/ligero/examples/Ligero/Longfellow/OptimizedIOPCertificates.lean` (flat certificates).

The analysis parameters `(e, g, m, failureThreshold, arithmeticThreshold, targetBits)` are chosen by
the same search that chose the v8 rows (`rbr_v1_rows.py`'s `Scanner.best` at 132 openings over its
default box; a box twice as large finds nothing better), emitted and re-derived by
`lfzk/scripts/v7_rows.py` (`--check`).  As for v8, every hash row has `listBound = 2`, the
challenge slot `fail + arith` is the binding budget and the scan sets `e = n − 1 − g − at`,
`ft = g + at`; the signature row has `g = 0` and `listBound = 2`, and its binding budget is the
query slot `cover`.

What is proved: `Row.Valid` (hence `Row.rbr_soundness`'s premises) and `Row.Sharp` for each row, by
`native_decide` on the row's closed numerals, exactly as for `v8Hash`/`v8Sig`.  Nothing here is a
hypothesis; the deployed-geometry identification (registry → `(n, k)`) is the inspector's, outside
Lean.
-/

namespace Lfzk.LigeroV1Rows

set_option maxHeartbeats 4000000

/-- The signature component's Ligero layer at the deployed v7 geometry (`block_enc = 4096`):
`2^-122`. -/
def v7Sig : Row :=
  { certificate :=
        { n := 3187, k := 455, d := 2733, e := 1484, g := 0, m := 123306,
          fieldBits := 256, targetBits := 122, openings := 132, fieldOrder := p256Order },
      failureThreshold := 1702, arithmeticThreshold := 1702 }

/-- The 1-attribute hash component's Ligero layer at the deployed v7 geometry
(`block_enc = 4151`): `2^-115`. -/
def v7Hash1 : Row :=
  { certificate :=
        { n := 3230, k := 461, d := 2770, e := 1464, g := 35, m := 1695,
          fieldBits := 128, targetBits := 115, openings := 132 },
      failureThreshold := 1765, arithmeticThreshold := 1730 }

/-- The 2-attribute hash component's Ligero layer at the deployed v7 geometry
(`block_enc = 4265`): `2^-115`. -/
def v7Hash2 : Row :=
  { certificate :=
        { n := 3318, k := 474, d := 2845, e := 1503, g := 36, m := 1687,
          fieldBits := 128, targetBits := 115, openings := 132 },
      failureThreshold := 1814, arithmeticThreshold := 1778 }

/-- The 3-attribute hash component's Ligero layer at the deployed v7 geometry
(`block_enc = 4307`): `2^-115`. -/
def v7Hash3 : Row :=
  { certificate :=
        { n := 3352, k := 478, d := 2875, e := 1519, g := 38, m := 1604,
          fieldBits := 128, targetBits := 115, openings := 132 },
      failureThreshold := 1832, arithmeticThreshold := 1794 }

/-- The 4-attribute hash component's Ligero layer at the deployed v7 geometry
(`block_enc = 4415`): `2^-115`. -/
def v7Hash4 : Row :=
  { certificate :=
        { n := 3436, k := 490, d := 2947, e := 1557, g := 39, m := 1604,
          fieldBits := 128, targetBits := 115, openings := 132 },
      failureThreshold := 1878, arithmeticThreshold := 1839 }

theorem v7Sig_valid : v7Sig.Valid := by native_decide
theorem v7Sig_sharp : v7Sig.Sharp := by native_decide
theorem v7Sig_targetBits : v7Sig.targetBits = 122 := rfl
theorem v7Sig_listBound : v7Sig.listBound = 2 := by native_decide

theorem v7Hash1_valid : v7Hash1.Valid := by native_decide
theorem v7Hash1_sharp : v7Hash1.Sharp := by native_decide
theorem v7Hash1_targetBits : v7Hash1.targetBits = 115 := rfl
theorem v7Hash1_listBound : v7Hash1.listBound = 2 := by native_decide

theorem v7Hash2_valid : v7Hash2.Valid := by native_decide
theorem v7Hash2_sharp : v7Hash2.Sharp := by native_decide
theorem v7Hash2_targetBits : v7Hash2.targetBits = 115 := rfl
theorem v7Hash2_listBound : v7Hash2.listBound = 2 := by native_decide

theorem v7Hash3_valid : v7Hash3.Valid := by native_decide
theorem v7Hash3_sharp : v7Hash3.Sharp := by native_decide
theorem v7Hash3_targetBits : v7Hash3.targetBits = 115 := rfl
theorem v7Hash3_listBound : v7Hash3.listBound = 2 := by native_decide

theorem v7Hash4_valid : v7Hash4.Valid := by native_decide
theorem v7Hash4_sharp : v7Hash4.Sharp := by native_decide
theorem v7Hash4_targetBits : v7Hash4.targetBits = 115 := rfl
theorem v7Hash4_listBound : v7Hash4.listBound = 2 := by native_decide

end Lfzk.LigeroV1Rows
