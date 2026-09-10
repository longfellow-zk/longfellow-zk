/-
# The chaining, on a real credential

`ShaChain.sha256_of_chain` reduces `meaning`'s SHA hypothesis to one `blockFrom` fact per block.
The reduction is only worth anything if `blockAt` and `chainIn` describe the circuit's actual
chaining — if `blockAt` sliced at the wrong stride, or `chainIn` fed the wrong accumulator
forward, the theorem would still be true and would still be about nothing.

So this file builds the chain explicitly on the golden credential, seven blocks from `H0`, and
checks that its last output is the digest the MACs bind. That is the same conclusion
`GoldenCheck.shaMso` reaches by evaluating `sha256` directly — but by a different route, through
`blockAt`'s slicing rather than `blocksOf`'s fuel — so agreement is evidence the two describe the
same computation.

Its own module because it is a second heavy `decide +kernel`, and N of those in one module
multiply peak memory by N.
-/

import mdoc.ShaChain
import mdoc.Golden

set_option maxRecDepth 10000000
set_option maxHeartbeats 4000000

namespace MDoc
namespace Golden

open ShaChain

/-- The words of the golden preimage. -/
def gws : List Nat := wordsOfBytes preimage

/-- The chain the circuit computes: `derived[b].h1`, built block by block from `H0`. Defined by
    the recursion rather than by `hashBlocks`, so that `chainG` below is a statement about
    `blockAt`'s slicing and not a tautology. -/
def gOut : Nat → List Nat
  | 0 => SHA256.blockFrom SHA256.H0 (blockAt gws 0)
  | b + 1 => SHA256.blockFrom (gOut b) (blockAt gws (b + 1))

/-- `gOut` satisfies `ChainOk` structurally: `chainIn` at 0 is `H0` and at `b + 1` is `gOut b`,
    which is how `gOut` was written. This carries no information about the *bytes* — that is
    `chain_digest`'s job. -/
theorem chainG : ChainOk gws maxShaBlocks gOut := by
  intro b _
  cases b with
  | zero => rfl
  | succ n => rfl

/-- The buffer holds all forty blocks. -/
theorem gbuf : 16 * maxShaBlocks ≤ gws.length :=
  mso_buf_fits preimage (by rfl)

/-- **The chain reaches the digest.** Seven `blockFrom` steps over `blockAt`'s slices, starting
    from `H0`, land on the `e` the MAC covers. This is what validates the model: a wrong stride
    in `blockAt`, or a mis-fed accumulator, changes this value. -/
theorem chain_digest : bytesOfWords (gOut 6) = w.e := by decide +kernel

/-- **The reduction, end to end on real bytes.** `sha256_of_chain` turns the seven per-block
    facts into `meaning`'s hypothesis — the same proposition `GoldenCheck.shaMso` decides
    directly. -/
theorem shaMso_via_chain : sha256 preimage 7 = w.e :=
  sha256_of_chain preimage maxShaBlocks 7 gOut w.e gbuf chainG (by omega)
    (by simp [maxShaBlocks]) chain_digest

/-- And it is the same statement, so the two routes agree. -/
theorem routes_agree : sha256 w.preimage w.nblocks = w.e := shaMso_via_chain

end Golden
end MDoc
