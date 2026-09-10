import quadcert.Bridge.Sha256.Sha256

/-!
# Formal circuit byte commitment

This mirrors `core_proto::commitment` exactly.  A generated circuit can place
each 4096-byte page in a separate Lean module as one packed `Nat`, prove its
leaf hash by kernel reduction, and combine only the 32-byte results here.
Consequently neither an elaborator that reads an external file nor a gigantic
`ByteArray` literal is required.

The binding statement is computational: identifying the pinned bytes from the
root relies on SHA-256 collision/second-preimage resistance.  The format
decoder must still be proved to interpret those pinned bytes as the circuit
used by the semantic proof.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace QuadCert.CircuitCommitment

open QuadCert.Sha256

def pageSize : Nat := 4096

private def leafDomain : List Byte :=
  [76, 70, 90, 75, 45, 76, 70, 67, 45, 80, 65, 71, 69, 45, 86, 49, 0]

private def nodeDomain : List Byte :=
  [76, 70, 90, 75, 45, 76, 70, 67, 45, 78, 79, 68, 69, 45, 86, 49, 0]

private def rootDomain : List Byte :=
  [76, 70, 90, 75, 45, 76, 70, 67, 45, 82, 79, 79, 84, 45, 86, 49, 0]

def u32LE (value : Nat) : List Byte :=
  (List.range 4).map fun i => value / 256 ^ i % 256

def u64LE (value : Nat) : List Byte :=
  (List.range 8).map fun i => value / 256 ^ i % 256

def leafHash (byteLength pageIndex : Nat) (page : List Byte) : Digest :=
  hash (leafDomain ++ u64LE byteLength ++ u64LE pageIndex ++
    u32LE page.length ++ page)

def nodeHash (level : Nat) (left right : Digest) : Digest :=
  hash (nodeDomain ++ u32LE level ++ left ++ right)

def rootHash (byteLength pageCount : Nat) (treeRoot : Digest) : Digest :=
  hash (rootDomain ++ u32LE pageSize ++ u64LE byteLength ++
    u64LE pageCount ++ treeRoot)

private def pairLevel (level : Nat) : List Digest → List Digest
  | [] => []
  | [last] => [nodeHash level last last]
  | left :: right :: rest => nodeHash level left right :: pairLevel level rest

private def reduceTree : Nat → Nat → List Digest → List Digest
  | 0, _, nodes => nodes
  | _ + 1, _, [] => []
  | _ + 1, _, [root] => [root]
  | fuel + 1, level, nodes => reduceTree fuel (level + 1) (pairLevel level nodes)

def rootFromLeaves (byteLength : Nat) (leaves : List Digest) : Digest :=
  let nonemptyLeaves := if leaves.isEmpty then [leafHash byteLength 0 []] else leaves
  let treeRoot := (reduceTree nonemptyLeaves.length 0 nonemptyLeaves).getD 0 []
  rootHash byteLength nonemptyLeaves.length treeRoot

def pages (bytes : List Byte) : List (List Byte) :=
  if bytes.isEmpty then
    [[]]
  else
    (List.range ((bytes.length + pageSize - 1) / pageSize)).map fun i =>
      (bytes.drop (pageSize * i)).take pageSize

structure Commitment where
  root : Digest
  byteLength : Nat
  pageCount : Nat
  deriving DecidableEq, Repr

def commit (bytes : List Byte) : Commitment :=
  let ps := pages bytes
  let leaves := (List.range ps.length).map fun i =>
    leafHash bytes.length i (ps.getD i [])
  { root := rootFromLeaves bytes.length leaves
    byteLength := bytes.length
    pageCount := ps.length }

/-- Decode exactly `count` little-endian bytes from one packed natural. -/
def unpackLE : Nat → Nat → List Byte
  | 0, _ => []
  | count + 1, packed => packed % 256 :: unpackLE count (packed / 256)

/-- The page-checking entry point used by generated packed-page modules. -/
def packedLeafHash (byteLength pageIndex pageLength packed : Nat) : Digest :=
  let header := leafDomain ++ u64LE byteLength ++ u64LE pageIndex ++ u32LE pageLength
  hashPacked (header.length + pageLength)
    (packLE header + (packed <<< (8 * header.length)))

private def emptyRoot : Digest :=
  [0x66, 0x62, 0xec, 0x67, 0xad, 0x66, 0x72, 0xb6,
   0x05, 0xc1, 0xe6, 0x56, 0x31, 0x2a, 0xb3, 0xc9,
   0x36, 0xd3, 0xef, 0x73, 0x42, 0xcd, 0x05, 0x71,
   0xaf, 0x80, 0xa2, 0x76, 0x48, 0xc1, 0xaa, 0x37]

private def abcRoot : Digest :=
  [0x18, 0x7a, 0xb7, 0xe2, 0x47, 0x37, 0x1c, 0x59,
   0x4f, 0xfe, 0x6f, 0xbf, 0x4d, 0xf6, 0xc6, 0xa5,
   0x6d, 0xef, 0xbd, 0x29, 0x3c, 0x43, 0xac, 0x65,
   0xfe, 0x86, 0xc7, 0x03, 0xca, 0x9a, 0xb9, 0xe0]

private def threeLeafRoot : Digest :=
  [0x21, 0x55, 0x06, 0x1e, 0x5f, 0xd2, 0x9d, 0x7a,
   0xb4, 0x14, 0xcf, 0x38, 0xa0, 0x8f, 0xbb, 0x97,
   0xfc, 0xe1, 0xb5, 0xc5, 0x90, 0x96, 0xd6, 0xe7,
   0xd1, 0x16, 0x3c, 0x50, 0x22, 0x95, 0xea, 0xeb]

/-- Shared with the Rust empty-payload test vector. -/
example : (commit []).root = emptyRoot := by decide

/-- Shared with the Rust `abc` test vector. -/
example : (commit [97, 98, 99]).root = abcRoot := by decide

/-- Shared three-leaf vector, covering odd-node duplication and both levels. -/
example : rootFromLeaves 9000
    [List.range 32, (List.range 32).map (· + 32),
     (List.range 32).map (· + 64)] = threeLeafRoot := by decide

/-- A packed page decodes without constructing a byte literal. -/
example : unpackLE 3 0x636261 = [97, 98, 99] := by decide

end QuadCert.CircuitCommitment
