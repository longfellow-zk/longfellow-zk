import quadcert.Core.CircuitCommitment
import quadcert.Core.Lfc3

/-!
# The commitment root of a packed payload

`CircuitCommitment.commit` computes a root from a `List Byte`; the generated
`{Artifact}Commitment` modules instead prove a root for an explicit list of
`packedLeafHash` applications, one per page, because a 100 MB byte list cannot be hashed
in the kernel.  Neither form mentions the `Lfc3.PackedBytes` value that `Lfc3.decode`
actually consumes.

`rootOfPacked` closes that gap: it takes the payload itself and derives the page indices and
page lengths from the payload's own `byteLength` and page count.  An end-to-end theorem can
then use one term, `input`, as the subject of both halves of the certificate --- these bytes
hash to the pinned root, *and* these bytes decode to the circuit the semantic proof is about.

Each artifact's `packedInput_root` is definitionally the generated `committed_root`; if the
index or length convention here disagreed with the generator's, that step would not typecheck.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace QuadCert.CircuitCommitment

open QuadCert.Sha256

/-- Length of page `pageIndex` of a `byteLength`-byte payload. Full pages except the last. -/
def pageLengthAt (byteLength pageIndex : Nat) : Nat :=
  min pageSize (byteLength - pageSize * pageIndex)

/-- The Merkle leaves of a packed payload, read off the payload: one leaf per page, at that
    page's own index and its own length. -/
def packedLeaves (input : Quadcert.Lfc3.PackedBytes) : List Digest :=
  (List.range input.pages.length).map fun i =>
    packedLeafHash input.byteLength i (pageLengthAt input.byteLength i) (input.pages.getD i 0)

/-- The commitment root of a packed payload. -/
def rootOfPacked (input : Quadcert.Lfc3.PackedBytes) : Digest :=
  rootFromLeaves input.byteLength (packedLeaves input)

/-- The packed and byte-level definitions agree: `abc` packed little-endian into one page
    gives the same root as `commit [97, 98, 99]`.  This pins the page-index and page-length
    conventions against `commit`, which mirrors `core_proto::commitment`. -/
example : rootOfPacked { byteLength := 3, pages := [97 + 98 * 256 + 99 * 65536] }
    = (commit [97, 98, 99]).root := by decide

end QuadCert.CircuitCommitment
