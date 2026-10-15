import Lfzk.NizkMerkle
import Lfzk.LigeroV1Rows

/-!
# Parameters at a Ligero V1 row

A `Params` carries a certified round-by-round V1 row (`Lfzk.LigeroV1Rows.Row`), V1's payload
width `q` with `r + q = k` (the `w` of `Ligero.V1`'s `MultiplicativeCode F r w n`), the circuit's
depth and per-layer width profile, and the size model's constants.

## The bound is stated per field element, not per coin

`nizkBound` quotes the composed bound with every slot at its **density**:

```text
cardCand · ( (2·nl + 2·totalRounds + 1) / |F|  +  (fail + arith)  +  cover )  +  merkleTerm
```

`2/|F|` per layer pair and per sumcheck round, `1/|F|` for the input binding, and the V1 row's
challenge-round and query-round densities.  That is what `Lfzk.CertifiedV1.Row.nizk_ratio_le` proves
for **every** coin alphabet whose decoders are exactly balanced (`RbrSplit.FieldData.Exact`), so the
alphabet is not a row numeral.  It cannot usefully be one: exactness forces `|C| ≥ |X|`, and V1's
challenge space `X` has one field element per tested row and per equation.

The layer-pair density is `2/|F|` on every layer, not only layer 0: `RbrLayerStep.layerStep_ratio_le`
charges one budget per role class (see `RbrLongfellow.layerStep_ratio_le`).

## The size model

`proofBytes` is a **cost model**: `cleartextElems`, `columnBytes` and the paths are claims about the
deployed encoding, not derived from a wire format, and nothing here checks them against V1's.  The
four constants it rests on (`bytesF`, `bytesH`, `columnFieldCount`, `paths`) are the `gero`
development's, inlined here so that this library has no dependency on it.  `bytesF = 16` is the
width of a `GF(2^128)` element; a row over P-256's base field is modelled at the same width, which
undercounts its proof by at most a factor of two and affects no soundness statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.CostV1

open Finset

/-! ## The size model's constants (`gero/Gero/Cost.lean`) -/

/-- Bytes per field element, at `|F| = 2^128`. -/
def bytesF : ℕ := 16

/-- Bytes per Merkle digest. -/
def bytesH : ℕ := 32

/-- Field elements in one opened `LigeroFamily.SchemeColumn`: `nw` linear rows, `nq` each of
left/right/output, the four `ConstraintMask` coefficients at one repetition, and one proximity
blind. -/
def columnFieldCount (nw nq : ℕ) : ℕ := nw + 3 * nq + 5

/-- Digests in a deduplicated Merkle multiproof of `q` leaves in a tree of height `h`: at level
`l` there are `2^l` nodes, of which at most `q` are on a queried path, so at most
`min q (2^l − q)` siblings are transmitted.  An upper bound on the true multiproof size. -/
def paths (h q : ℕ) : ℕ := ∑ l ∈ Finset.Icc 1 (h - 1), min q (2 ^ l - q)

/-- **The parameter set at a V1 row.** -/
structure Params where
  /-- The certified round-by-round V1 row: `n, k, d, e, g, m`, thresholds, field, openings. -/
  row : Lfzk.LigeroV1Rows.Row
  /-- The V1 payload width `w`, with `r + w = k`. -/
  q : ℕ
  /-- Circuit depth. -/
  nl : ℕ
  /-- Per-layer width exponents — the profile. -/
  logw : ℕ → ℕ
  /-- The copy/constant width exponent. -/
  logc : ℕ
  /-- Digest width, in bits. -/
  digestBits : ℕ
  /-- Input-layer witness columns. -/
  ninp : ℕ
  /-- Bytes per opened entry of a subfield row. -/
  colBytes : ℕ
  /-- Witness rows that hold full-field elements. -/
  nfullWit : ℕ

namespace Params

variable (P : Params)

/-- **The round profile**, `2 · logw ly` sumcheck rounds at layer `ly`. -/
def rounds : ℕ → ℕ := fun ly => 2 * P.logw ly

/-- Blinders: two per sumcheck round and three per layer, summed over the profile. -/
def padSize : ℕ := ∑ ly ∈ range P.nl, (4 * P.logw ly + 3)

/-- The schedule's total sumcheck slot count. -/
def totalRounds : ℕ := ∑ ly ∈ range P.nl, P.rounds ly

/-- Transmitted field elements for LayerStep. -/
def sumcheckElems : ℕ := ∑ ly ∈ range P.nl, (2 * P.rounds ly + 2)

/-- Witness rows, and quadratic-constraint rows, at payload width `q`. -/
def nw : ℕ := (P.ninp + P.padSize + P.q - 1) / P.q
def nq : ℕ := (P.nl + P.q - 1) / P.q

theorem rounds_sum : ∑ ly ∈ range P.nl, P.rounds ly = P.totalRounds := rfl

/-! ## The bound -/

/-- The Merkle half of `Lfzk.Nizk.nizk_ratio_le_merkle`. -/
def merkleTerm (commitFuel T : ℕ) : ℚ :=
  (Bcs.merkleNumerator commitFuel T : ℚ) / (2 ^ P.digestBits : ℚ)

/-- The field rounds' density: `2/|F|` per layer pair and per sumcheck round, `1/|F|` for the
input binding. -/
def fieldDensity : ℚ :=
  ((P.nl * 2 + P.totalRounds * 2 + 1 : ℕ) : ℚ) / (P.row.fieldSize : ℚ)

/-- The two Ligero rounds' density: the V1 row's challenge-round budget `fail + arith` and its
query-round budget `cover`. -/
def ligeroDensity : ℚ := (P.row.fail + P.row.arith) + P.row.cover

/-- **The composed bound at these parameters**, every slot at its density. -/
def nizkBound (cardCand commitFuel T : ℕ) : ℚ :=
  (cardCand : ℚ) * (P.fieldDensity + P.ligeroDensity) + P.merkleTerm commitFuel T

/-- At `cardCand = listBound`, the Ligero part of the bound is exactly the V1 row's `epsRbr`. -/
theorem ligero_part_eq_epsRbr :
    (P.row.listBound : ℚ) * P.ligeroDensity = P.row.epsRbr := by
  unfold ligeroDensity Lfzk.LigeroV1Rows.Row.epsRbr
  ring

/-! ## The size model -/

/-- The transmitted test rows, `4·k + r − 2` field elements. -/
def cleartextElems : ℕ := 4 * P.row.k + P.row.openings - 2

/-- Rows per opened column. -/
def colRows : ℕ := columnFieldCount P.nw P.nq

/-- Opened rows that stay full width. -/
def nfull : ℕ := 3 * P.nq + 5 + P.nfullWit

/-- The opened columns, in bytes. -/
def columnBytes : ℕ :=
  P.row.openings * ((P.colRows - P.nfull) * P.colBytes + P.nfull * bytesF)

/-- Merkle path digests for `r` openings in a tree over `n` leaves. -/
def pathDigests : ℕ := paths (Nat.log2 P.row.n) P.row.openings

/-- Merkle leaf nonces, one digest per opened column. -/
def nonceBytes : ℕ := P.row.openings * bytesH

/-- Field elements transmitted at full width. -/
def proofElems : ℕ := P.sumcheckElems + P.cleartextElems

/-- Modelled proof size in bytes. -/
def proofBytes : ℕ :=
  P.proofElems * bytesF + P.columnBytes + Params.pathDigests P * bytesH + P.nonceBytes

end Params

end Lfzk.CostV1
