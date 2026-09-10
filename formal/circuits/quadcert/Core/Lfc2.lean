/-
# Copyright 2026 Google LLC.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
-/

import quadcert.Core.Raw

/-!
# Verified LFC2 ingestion from packed bytes

This is the byte-to-`RawCircuit` link for the formal circuit commitment.  It is deliberately
Mathlib-free: generated modules provide one little-endian `Nat` per 4096-byte page, and this
decoder consumes those naturals a byte at a time.  It never constructs a whole-file
`ByteArray` or list of bytes.

The artifact owns the circuit dimensions, canonical field constants and expanded layer terms.
The certificate sidecar remains untrusted advice only for the DAG, wire map, assertion records
and input names.  `DecodedCircuit.toRaw` makes that boundary explicit.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Quadcert.Lfc2

def pageSize : Nat := 4096
def word32Modulus : Nat := 0x100000000

def maxWires : Nat := 5000000
def maxTermsPerLayer : Nat := 20000000
def maxTotalTerms : Nat := 20000000
def maxDeltas : Nat := 20000000
def maxConstants : Nat := 5000000
def maxLayers : Nat := 10000
def maxLayerInputs : Nat := 5000000
def maxLogWidth : Nat := 40

/-- One packed natural per 4096-byte page, with the final page possibly shorter. -/
structure PackedBytes where
  byteLength : Nat
  pages : List Nat
  deriving Repr, DecidableEq

def PackedBytes.expectedPages (input : PackedBytes) : Nat :=
  if input.byteLength = 0 then 1 else (input.byteLength + pageSize - 1) / pageSize

/-- Parameters needed to turn fixed-width field encodings into canonical naturals. -/
structure FieldEncoding where
  fieldId : Nat
  byteLength : Nat
  /-- `none` means every bit pattern of the fixed width is canonical (as for GF(2^128)). -/
  modulus : Option Nat
  deriving Repr, DecidableEq

def p256 : FieldEncoding where
  fieldId := 1
  byteLength := 32
  modulus := some 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff

def gf2_128 : FieldEncoding where
  fieldId := 4
  byteLength := 16
  modulus := none

inductive Error where
  | badPageCount
  | unexpectedEnd
  | badMagic
  | noncanonicalUleb
  | ulebOverflow
  | excessiveCount
  | fieldMismatch
  | badFieldEncoding
  | unsupportedCopies
  | zeroOutputs
  | badLogWidth
  | publicInputsExceedInputs
  | constantIndexOutOfBounds
  | deltaIndexOutOfBounds
  | wireIndexOutOfRange
  | inputWidthMismatch
  | segmentIndexOutOfBounds
  | badTokenEncoding
  | excessiveExpansion
  | trailingBytes
  deriving Repr, DecidableEq

structure Cursor where
  page : Nat
  pageRemaining : Nat
  laterPages : List Nat
  remaining : Nat
  deriving Repr, DecidableEq

private def initCursor (input : PackedBytes) : Except Error Cursor :=
  if input.pages.length != input.expectedPages then
    .error .badPageCount
  else
    match input.pages with
    | [] => .error .badPageCount
    | first :: rest =>
        .ok { page := first
              pageRemaining := min pageSize input.byteLength
              laterPages := rest
              remaining := input.byteLength }

/-- The cursor positioned exactly `offset` bytes into `input`.

Generated stage certificates name their checkpoints this way.  Writing a `Cursor` out literally
costs a copy of the current page *and every later page* — 3.9 MB for one layer of SHA-256 — so a
staged parse that names ~70 checkpoints per layer would spend far more on its checkpoints than
on the data.  As a position it is one numeral. -/
def cursorAt (input : PackedBytes) (offset : Nat) : Cursor :=
  let page := offset / pageSize
  let within := offset % pageSize
  { page := (input.pages.getD page 0) >>> (8 * within)
    pageRemaining := min pageSize (input.byteLength - page * pageSize) - within
    laterPages := input.pages.drop (page + 1)
    remaining := input.byteLength - offset }

/-- Consume one byte without expanding the packed page.

    **Not `private`.** `Lfc2Bytes` states a refinement between this and a byte-list reader, which
    is what removes the SHA-256 decoder blocker (measured: 175 s / 9.5 GB against 4.5 s / 0.83 GB
    on one 1,024-delta chunk). Stating that relation requires naming this function. Nothing else
    changed: `Cursor`, `decode` and every generated module are untouched. -/
def readByte (cursor : Cursor) : Except Error (Nat × Cursor) :=
  if cursor.remaining = 0 then
    .error .unexpectedEnd
  else if cursor.pageRemaining = 0 then
    .error .badPageCount
  else
    let byte := cursor.page % 256
    let remaining := cursor.remaining - 1
    if cursor.pageRemaining = 1 then
      if remaining = 0 then
        .ok (byte, { page := 0, pageRemaining := 0, laterPages := cursor.laterPages,
                     remaining := 0 })
      else
        match cursor.laterPages with
        | [] => .error .badPageCount
        | next :: rest =>
            .ok (byte, { page := next, pageRemaining := min pageSize remaining,
                         laterPages := rest, remaining := remaining })
    else
      .ok (byte, { cursor with page := cursor.page / 256,
                               pageRemaining := cursor.pageRemaining - 1,
                               remaining := remaining })

def readUlebLoop : Nat → Nat → Nat → Cursor → Except Error (Nat × Cursor)
  | 0, _, _, _ => .error .ulebOverflow
  | fuel + 1, index, value, cursor => do
      let (byte, cursor) ← readByte cursor
      let payload := byte % 128
      let value := value + payload * 128 ^ index
      if byte < 128 then
        if index > 0 && payload = 0 then .error .noncanonicalUleb else .ok (value, cursor)
      else
        readUlebLoop fuel (index + 1) value cursor

/-- Read the unique shortest ULEB128 representation of a 28-bit natural. -/
def readUleb (cursor : Cursor) : Except Error (Nat × Cursor) :=
  readUlebLoop 4 0 0 cursor

def readBounded (maximum : Nat) (cursor : Cursor) : Except Error (Nat × Cursor) := do
  let (value, cursor) ← readUleb cursor
  if value ≤ maximum then .ok (value, cursor) else .error .excessiveCount

private def readNatLELoop : Nat → Nat → Nat → Cursor → Except Error (Nat × Cursor)
  | 0, _, value, cursor => .ok (value, cursor)
  | count + 1, place, value, cursor => do
      let (byte, cursor) ← readByte cursor
      readNatLELoop count (place * 256) (value + byte * place) cursor

private def readNatLE (count : Nat) (cursor : Cursor) : Except Error (Nat × Cursor) :=
  readNatLELoop count 1 0 cursor

private def readMagic (cursor : Cursor) : Except Error Cursor := do
  let (b0, cursor) ← readByte cursor
  let (b1, cursor) ← readByte cursor
  let (b2, cursor) ← readByte cursor
  let (b3, cursor) ← readByte cursor
  if b0 = 76 && b1 = 70 && b2 = 67 && b3 = 50 then .ok cursor else .error .badMagic

private def ceilLog2Loop : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _ => maxLogWidth + 1
  | fuel + 1, n, exponent, power =>
      if n ≤ power then exponent else ceilLog2Loop fuel n (exponent + 1) (power * 2)

private def ceilLog2 (n : Nat) : Nat := ceilLog2Loop (maxLogWidth + 1) n 0 1

structure Delta where
  g : Nat
  h0 : Nat
  h1 : Nat
  kIndex : Nat
  deriving Repr, DecidableEq

/-- A layer after byte parsing but before the potentially large term expansion. -/
structure CompressedLayer where
  logw : Nat
  nw : Nat
  deltas : Array Delta
  segments : Array (Array Nat)
  tokens : Array Nat
  tokenCount : Nat
  termCount : Nat
  deriving Repr, DecidableEq

/-- Artifact data whose layers retain the compact LFC2 dictionaries. -/
structure CompressedCircuit where
  fieldId : Nat
  ninput : Nat
  npublicInput : Nat
  noutput : Nat
  logv : Nat
  subfieldBoundary : Nat
  constants : Array Nat
  layers : List CompressedLayer
  legacyCircuitId : Nat
  deriving Repr, DecidableEq

/-- Metadata and constants parsed before the independently checkable layer stream. -/
structure CompressedHeader where
  fieldId : Nat
  ninput : Nat
  npublicInput : Nat
  noutput : Nat
  logv : Nat
  subfieldBoundary : Nat
  constants : Array Nat
  layerCount : Nat
  deriving Repr, DecidableEq

/-! ### Indexed dictionary lookups

`Array` is a `List` in a costume, so `deltas[i]?` walks `i` cons cells.  On mdoc's hash layers
that is the dominant cost of the whole decode.  A positional search tree answers the same query
in `log n` steps.

The tree is **untrusted advice**: it is emitted alongside the artifact and tied back to the list
the decoder actually produced from the committed bytes by two linear checks per layer,
`checkSize` and `toList`.  It is also passed as a *fixed argument*, never stored in the
expansion cursor — a zipper was tried instead and lost badly precisely because it had to live
in the cursor, which is rebuilt at every step. -/

/-- A search tree indexed by position.  `leftSize` is stored so a lookup never recomputes it. -/
inductive PTree (α : Type) where
  | leaf
  | node (leftSize : Nat) (l : PTree α) (a : α) (r : PTree α)
  deriving Repr

/-- Tree first, so the equation compiler sees structural recursion on it; with the `Nat` first
    it picks well-founded recursion, whose `Acc.rec` the kernel cannot cheaply unfold. -/
def PTree.lookup {α : Type} : PTree α → Nat → Option α
  | .leaf, _ => none
  | .node ls l a r, i =>
      if i < ls then l.lookup i
      else if i = ls then some a
      else r.lookup (i - ls - 1)

def PTree.toList {α : Type} : PTree α → List α
  | .leaf => []
  | .node _ l a r => l.toList ++ a :: r.toList

/-- Checks every stored `leftSize` against the actual subtree, returning the total size.  One
    pass, so this is linear rather than the quadratic a per-node `toList.length` would cost. -/
def PTree.checkSize {α : Type} : PTree α → Option Nat
  | .leaf => some 0
  | .node ls l _ r =>
      match l.checkSize, r.checkSize with
      | some nl, some nr => if nl = ls then some (nl + 1 + nr) else none
      | _, _ => none

private theorem PTree.toList_length {α : Type} :
    ∀ {t : PTree α} {n}, t.checkSize = some n → t.toList.length = n
  | .leaf, n, h => by simp only [PTree.checkSize, Option.some.injEq] at h; simp [PTree.toList, ← h]
  | .node ls l a r, n, h => by
      simp only [PTree.checkSize] at h
      cases hl : l.checkSize with
      | none => rw [hl] at h; contradiction
      | some nl =>
        cases hr : r.checkSize with
        | none => rw [hl, hr] at h; contradiction
        | some nr =>
          rw [hl, hr] at h
          simp only at h
          by_cases he : nl = ls
          · have hl' : l.toList.length = nl := PTree.toList_length hl
            have hr' : r.toList.length = nr := PTree.toList_length hr
            rw [if_pos he] at h
            simp only [Option.some.injEq] at h
            show (l.toList ++ a :: r.toList).length = n
            simp only [List.length_append, List.length_cons, hl', hr']
            omega
          · simp only [he, if_neg he] at h; contradiction

/-- **The tree answers exactly what the list would.**  Proved once; each layer then supplies its
    own `checkSize` and `toList` checks, both linear. -/
theorem PTree.lookup_eq_getElem {α : Type} :
    ∀ (t : PTree α) {n}, t.checkSize = some n → ∀ i, t.lookup i = t.toList[i]?
  | .leaf, _, _, i => by simp [PTree.lookup, PTree.toList]
  | .node ls l a r, n, h, i => by
      simp only [PTree.checkSize] at h
      cases hl : l.checkSize with
      | none => rw [hl] at h; contradiction
      | some nl =>
        cases hr : r.checkSize with
        | none => rw [hl, hr] at h; contradiction
        | some nr =>
          rw [hl, hr] at h
          simp only at h
          by_cases he : nl = ls
          · have hlen : l.toList.length = ls := he ▸ PTree.toList_length hl
            simp only [PTree.lookup, PTree.toList]
            by_cases h1 : i < ls
            · rw [if_pos h1, PTree.lookup_eq_getElem l hl i,
                List.getElem?_append_left (by omega)]
            · rw [if_neg h1]
              by_cases h2 : i = ls
              · subst h2
                rw [if_pos rfl, List.getElem?_append_right (by omega), hlen]
                simp
              · rw [if_neg h2, PTree.lookup_eq_getElem r hr (i - ls - 1),
                  List.getElem?_append_right (by omega), hlen]
                have : i - ls = (i - ls - 1) + 1 := by omega
                rw [this]
                simp
          · simp only [he, if_neg he] at h; contradiction

/-- A cursor into a dictionary that moves *relative* to where it is.

**Measured and rejected for the delta table.**  ECDSA2's locality is excellent (median jump
0-5 against tables of 23-1,221, a 6-30x theoretical win), yet threading this through the
expansion cursor made the full decode *worse*: 66 s -> 525 s CPU.  A zipper has to hold the
dictionary in the cursor, and the cursor is rebuilt at every step and written out at every
checkpoint, so the table gets copied where it used to sit once in the layer.  Kept because the
structure is sound and may suit a container that is small enough to carry; do not reattach it
to `ExpansionCursor` without re-measuring.

Dictionary references are local: on mdoc's largest hash layer the median jump between
consecutive delta indices is 71 against a table of 1,784, and for the token stream it is 1.
Indexing from the head pays for half the table every time; stepping from the current position
pays for the jump.  `before` is kept reversed so both directions cost one cons per step. -/
structure Zipper (α : Type) where
  /-- Entries before `pos`, nearest first. -/
  before : List α
  /-- Entries from `pos` onwards. -/
  ahead : List α
  pos : Nat
  deriving Repr, DecidableEq

def Zipper.ofList {α : Type} (xs : List α) : Zipper α := ⟨[], xs, 0⟩

private def Zipper.seekLoop {α : Type} : Nat → Nat → Zipper α → Option (α × Zipper α)
  | 0, _, _ => none
  | fuel + 1, target, z =>
      if target = z.pos then
        match z.ahead with
        | [] => none
        | a :: _ => some (a, z)
      else if z.pos < target then
        match z.ahead with
        | [] => none
        | a :: rest => Zipper.seekLoop fuel target ⟨a :: z.before, rest, z.pos + 1⟩
      else
        match z.before with
        | [] => none
        | b :: rest => Zipper.seekLoop fuel target ⟨rest, b :: z.ahead, z.pos - 1⟩

/-- Move to `target` and read it.  Cost is the distance travelled, not the index. -/
def Zipper.seek {α : Type} (target : Nat) (z : Zipper α) : Option (α × Zipper α) :=
  Zipper.seekLoop (target + z.pos + 1) target z

/-- A resumable position in a layer expansion.

The three streams here are consumed strictly left to right, so the cursor carries what
*remains* of each rather than an index into it.  With an index, `tokens[outer]?` restarts the
walk from the head on every single term: on mdoc's largest layer that averages 56,010 cons
cells per term and dominated the entire decode.  A residual steps in O(1).

The dictionary lookups (`segments` and `deltas`) are genuinely random and are not
addressed here. -/
structure ExpansionCursor where
  /-- Remaining tokens: the layer's segment-index stream. -/
  outer : List Nat := []
  /-- Remaining delta indices of the segment currently being expanded. -/
  segment : List Nat := []
  g : Nat := 0
  h0 : Nat := 0
  h1 : Nat := 0
  emitted : Nat := 0
  deriving Repr, DecidableEq

/-- A decoded layer retains `logw`, although `RawLayer` currently needs only `nw` and terms. -/
structure DecodedLayer where
  logw : Nat
  nw : Nat
  terms : List RawTerm
  deriving Repr, DecidableEq

/-- All data obtained from the committed LFC2 artifact. -/
structure DecodedCircuit where
  fieldId : Nat
  ninput : Nat
  npublicInput : Nat
  noutput : Nat
  logv : Nat
  subfieldBoundary : Nat
  constants : Array Nat
  layers : List DecodedLayer
  /-- Compatibility trailer; committed as bytes but not trusted as a second circuit identity. -/
  legacyCircuitId : Nat
  deriving Repr, DecidableEq

def DecodedCircuit.constNat (circuit : DecodedCircuit) (index : Nat) : Nat :=
  (circuit.constants[index]?).getD 0

def DecodedLayer.toRaw (layer : DecodedLayer) : RawLayer :=
  { nw := layer.nw, terms := layer.terms }

/-- Precisely the fields that remain certificate advice after the artifact is decoded. -/
structure RawAdvice where
  nodes : List RawNode
  wireFn : Nat → Option (Nat × Nat)
  asserts : List RawAssert
  layout : List (Nat × String)

/-- Assemble a `RawCircuit`, taking every artifact-owned field from the byte decoder. -/
noncomputable def DecodedCircuit.toRaw (circuit : DecodedCircuit) (advice : RawAdvice) : RawCircuit :=
  { ninput := circuit.ninput
    npublicInput := circuit.npublicInput
    noutput := circuit.noutput
    logv := circuit.logv
    subfieldBoundary := circuit.subfieldBoundary
    nconstants := circuit.constants.size
    layers := circuit.layers.map DecodedLayer.toRaw
    nodes := advice.nodes
    wireFn := advice.wireFn
    asserts := advice.asserts
    layout := advice.layout }

private def canonicalFieldValue (field : FieldEncoding) (value : Nat) : Bool :=
  match field.modulus with
  | none => true
  | some modulus => value < modulus

/-! ### Why these readers build lists and never accumulate into an `Array`

`Array` is a structure wrapping a `List`, so `Array.push` is `⟨as.toList ++ [a]⟩` — **linear**
under kernel reduction, making an `n`-push accumulator loop quadratic.  Measured on this
toolchain: 1,000 pushes take 25 s and 2,000 do not finish in 95 s, while 64,000 `cons` steps
take 5.1 s.  A 89,048-delta layer is hours of kernel time, which is what made
`Sha256BlkCompressedLayer5` unbuildable rather than merely slow.

So every reader below returns its own `List` built with `cons`, and the array is formed once at
the end with the `Array.mk` constructor, which is O(1) (`List.toArray` is *not* — it folds
`push`, and fails outright at 20,000 elements).  Chunking alone would not have helped: a chunk
whose accumulator starts from the prefix still pays for the prefix. -/

private def readConstantsChunk (field : FieldEncoding) :
    Nat → Cursor → Except Error (List Nat × Cursor)
  | 0, cursor => .ok ([], cursor)
  | count + 1, cursor => do
      let (value, cursor) ← readNatLE field.byteLength cursor
      if !canonicalFieldValue field value then .error .badFieldEncoding else
      let (values, cursor) ← readConstantsChunk field count cursor
      .ok (value :: values, cursor)

/-- Sequential chunk reads compose, so a generated certificate can checkpoint mid-table. -/
theorem readConstantsChunk_compose (field : FieldEncoding) {a b : Nat}
    {start middle stop : Cursor} {left right : List Nat}
    (hleft : readConstantsChunk field a start = .ok (left, middle))
    (hright : readConstantsChunk field b middle = .ok (right, stop)) :
    readConstantsChunk field (a + b) start = .ok (left ++ right, stop) := by
  induction a generalizing start left with
  | zero =>
      simp only [readConstantsChunk] at hleft
      cases hleft
      simpa using hright
  | succ a ih =>
      simp only [Nat.succ_add, readConstantsChunk, bind, Except.bind] at hleft ⊢
      cases hvalue : readNatLE field.byteLength start with
      | error e => rw [hvalue] at hleft; contradiction
      | ok pair =>
          rcases pair with ⟨value, next⟩
          rw [hvalue] at hleft
          simp only at hleft ⊢
          by_cases hcanon : canonicalFieldValue field value
          · simp only [hcanon, Bool.not_true, if_false, Bool.false_eq_true] at hleft ⊢
            cases hrest : readConstantsChunk field a next with
            | error e => rw [hrest] at hleft; contradiction
            | ok result =>
                rcases result with ⟨tail, actual⟩
                rw [hrest] at hleft
                simp only [Except.ok.injEq, Prod.mk.injEq] at hleft
                obtain ⟨rfl, rfl⟩ := hleft
                rw [ih hrest]
                rfl
          · simp only [Bool.not_eq_true] at hcanon
            simp [hcanon] at hleft

def decodeDelta (value : Nat) : Nat :=
  if value % 2 = 0 then value / 2 else word32Modulus - 1 - value / 2

def readDeltasChunk (constantCount : Nat) :
    Nat → Cursor → Except Error (List Delta × Cursor)
  | 0, cursor => .ok ([], cursor)
  | count + 1, cursor => do
      let (g, cursor) ← readUleb cursor
      let (h0, cursor) ← readUleb cursor
      let (h1, cursor) ← readUleb cursor
      let (kIndex, cursor) ← readUleb cursor
      if !(kIndex < constantCount) then .error .constantIndexOutOfBounds else
      let (deltas, cursor) ← readDeltasChunk constantCount count cursor
      .ok ({ g := decodeDelta g, h0 := decodeDelta h0,
             h1 := decodeDelta h1, kIndex := kIndex } :: deltas, cursor)

/-- Sequential delta chunks compose, so a layer's delta table can be certified in bounded
    pieces without either chunk re-reading the other. -/
theorem readDeltasChunk_compose (constantCount : Nat) {a b : Nat}
    {start middle stop : Cursor} {left right : List Delta}
    (hleft : readDeltasChunk constantCount a start = .ok (left, middle))
    (hright : readDeltasChunk constantCount b middle = .ok (right, stop)) :
    readDeltasChunk constantCount (a + b) start = .ok (left ++ right, stop) := by
  induction a generalizing start left with
  | zero =>
      simp only [readDeltasChunk] at hleft
      cases hleft
      simpa using hright
  | succ a ih =>
      simp only [Nat.succ_add, readDeltasChunk, bind, Except.bind] at hleft ⊢
      cases hg : readUleb start with
      | error e => rw [hg] at hleft; contradiction
      | ok pg =>
          rcases pg with ⟨g, c1⟩
          rw [hg] at hleft; simp only at hleft ⊢
          cases h0 : readUleb c1 with
          | error e => rw [h0] at hleft; contradiction
          | ok p0 =>
              rcases p0 with ⟨v0, c2⟩
              rw [h0] at hleft; simp only at hleft ⊢
              cases h1 : readUleb c2 with
              | error e => rw [h1] at hleft; contradiction
              | ok p1 =>
                  rcases p1 with ⟨v1, c3⟩
                  rw [h1] at hleft; simp only at hleft ⊢
                  cases hk : readUleb c3 with
                  | error e => rw [hk] at hleft; contradiction
                  | ok pk =>
                      rcases pk with ⟨k, c4⟩
                      rw [hk] at hleft; simp only at hleft ⊢
                      by_cases hbound : k < constantCount
                      · simp only [hbound, decide_true, Bool.not_true, if_false,
                          Bool.false_eq_true] at hleft ⊢
                        cases hrest : readDeltasChunk constantCount a c4 with
                        | error e => rw [hrest] at hleft; contradiction
                        | ok result =>
                            rcases result with ⟨tail, actual⟩
                            rw [hrest] at hleft
                            simp only [Except.ok.injEq, Prod.mk.injEq] at hleft
                            obtain ⟨rfl, rfl⟩ := hleft
                            rw [ih hrest]
                            rfl
                      · simp [hbound] at hleft

def readIndexListChunk (bound : Nat) (outOfBounds : Error) :
    Nat → Cursor → Except Error (List Nat × Cursor)
  | 0, cursor => .ok ([], cursor)
  | count + 1, cursor => do
      let (value, cursor) ← readUleb cursor
      if !(value < bound) then .error outOfBounds else
      let (values, cursor) ← readIndexListChunk bound outOfBounds count cursor
      .ok (value :: values, cursor)

def readSegmentsChunk (deltaCount : Nat) :
    Nat → Nat → Cursor → Except Error (List (Array Nat) × Nat × Cursor)
  | 0, symbols, cursor => .ok ([], symbols, cursor)
  | count + 1, symbols, cursor => do
      let (length, cursor) ← readBounded maxTermsPerLayer cursor
      let symbols := symbols + length
      if symbols > maxTermsPerLayer then .error .excessiveCount else
      let (segment, cursor) ←
        readIndexListChunk deltaCount .deltaIndexOutOfBounds length cursor
      let (segments, symbols, cursor) ← readSegmentsChunk deltaCount count symbols cursor
      .ok (Array.mk segment :: segments, symbols, cursor)

/-- Sequential segment chunks compose.  The running symbol budget threads through, so the
    second chunk is checked against the total the first actually consumed. -/
theorem readSegmentsChunk_compose (deltaCount : Nat) {a b : Nat}
    {s0 s1 s2 : Nat} {start middle stop : Cursor} {left right : List (Array Nat)}
    (hleft : readSegmentsChunk deltaCount a s0 start = .ok (left, s1, middle))
    (hright : readSegmentsChunk deltaCount b s1 middle = .ok (right, s2, stop)) :
    readSegmentsChunk deltaCount (a + b) s0 start = .ok (left ++ right, s2, stop) := by
  induction a generalizing start left s0 with
  | zero =>
      simp only [readSegmentsChunk] at hleft
      cases hleft
      simpa using hright
  | succ a ih =>
      simp only [Nat.succ_add, readSegmentsChunk, bind, Except.bind] at hleft ⊢
      cases hlen : readBounded maxTermsPerLayer start with
      | error e => rw [hlen] at hleft; contradiction
      | ok pl =>
          rcases pl with ⟨length, c1⟩
          rw [hlen] at hleft; simp only at hleft ⊢
          by_cases hbudget : s0 + length > maxTermsPerLayer
          · simp [hbudget] at hleft
          · simp only [hbudget, if_false] at hleft ⊢
            cases hseg : readIndexListChunk deltaCount .deltaIndexOutOfBounds length c1 with
            | error e => rw [hseg] at hleft; contradiction
            | ok ps =>
                rcases ps with ⟨segment, c2⟩
                rw [hseg] at hleft; simp only at hleft ⊢
                cases hrest : readSegmentsChunk deltaCount a (s0 + length) c2 with
                | error e => rw [hrest] at hleft; contradiction
                | ok result =>
                    rcases result with ⟨tail, symbols', actual⟩
                    rw [hrest] at hleft
                    simp only [Except.ok.injEq, Prod.mk.injEq] at hleft
                    obtain ⟨rfl, rfl, rfl⟩ := hleft
                    rw [ih hrest]
                    rfl



/-- Segment lengths only.

Counting a layer's terms needs each referenced segment's *size*, not its contents, and indexing
an `Array` is a list walk in the kernel.  Indexing the dictionary itself once per token re-walks
a structure holding every symbol — measured at 27 GB and climbing for SHA-256's largest layer,
with 2,847 tokens over 1,775 segments.  One pass to lengths first makes each lookup a walk over
numerals instead. -/
def segmentLengths (segments : Array (Array Nat)) : Array Nat :=
  Array.mk (segments.toList.map Array.size)

/-! ### Counting a layer's terms

**These recurse on the token *list*, not on a fuel counter indexing an `Array`.** The earlier
shape was `let index := tokens.size - (fuel + 1); tokens[index]?`, which recomputes `size` (a
`List.length`) and walks `index` cons cells on every iteration — `O(T²)` before the segment
lookups are counted. On SHA-256's layer 5 that is 2,847 tokens over a 1,775-entry dictionary, and
it exhausted the 12 GB cap even *after* the reader was switched to bytes: the counting is shared
between the two readers, so switching the cursor could not help it.

The `none` branch of the old `tokens[index]?` was unreachable — `index` ran `0 … size-1` by
construction — so nothing is lost by recursing structurally. `lengths[segmentIndex]?` stays: that
one is a real bounds check on untrusted data. -/

def countSegmentTermsLoop (lengths : Array Nat) : List Nat → Nat → Except Error Nat
  | [], total => .ok total
  | segmentIndex :: rest, total =>
      match lengths[segmentIndex]? with
      | none => .error .segmentIndexOutOfBounds
      | some size =>
          let total := total + size
          if total > maxTermsPerLayer then .error .excessiveExpansion
          else countSegmentTermsLoop lengths rest total

def countSegmentTerms (lengths : Array Nat) (tokens : Array Nat)
    (initial : Nat := 0) : Except Error Nat :=
  countSegmentTermsLoop lengths tokens.toList initial




/-- The token stage needs only how many segments there are (for bounds) and how long each is
    (for the term count) -- never their contents.  Taking the dictionary itself made `bound` an
    unreduced term carrying every symbol, re-walked once per token: 25 GB on SHA-256's largest
    layer.  Both arguments here are supplied already reduced by the staged certificate. -/
def readCompressedTokens (segmentCount : Nat) (lengths : Array Nat) (cursor : Cursor) :
    Except Error (Array Nat × Nat × Nat × Cursor) := do
  let (count, cursor) ← readBounded maxTermsPerLayer cursor
  let (tokens, cursor) ←
    readIndexListChunk segmentCount .segmentIndexOutOfBounds count cursor
  let tokens := Array.mk tokens
  let termCount ← countSegmentTerms lengths tokens
  .ok (tokens, tokens.size, termCount, cursor)

/-! ### Staging the layer parser

`readCompressedLayer` reads a layer's whole delta table and segment dictionary.  Proved as one
`rfl`, the goal contains the entire `CompressedLayer` literal — 11,952 deltas and 56,145 segment
symbols for SHA-256's largest layer — which measured 14.0 GB and did not finish.  The stages
below let a generated certificate check the layer in bounded pieces and compose them, the same
treatment `expandChunk` already has, so no single module holds the whole table. -/

/-- The layer's fixed prefix: `logw`, `nw`, and the delta count. -/
def readLayerPrefix (cursor : Cursor) : Except Error (Nat × Nat × Nat × Cursor) := do
  let (logw, cursor) ← readUleb cursor
  if logw > maxLogWidth then .error .badLogWidth else
  let (nw, cursor) ← readBounded maxLayerInputs cursor
  let (deltaCount, cursor) ← readBounded maxDeltas cursor
  .ok (logw, nw, deltaCount, cursor)

/-- The segment count, between the delta table and the segment dictionary. -/
def readSegmentCount (cursor : Cursor) : Except Error (Nat × Cursor) :=
  readBounded maxDeltas cursor

def readCompressedLayer (constantCount totalTerms : Nat) (cursor : Cursor) :
    Except Error (CompressedLayer × Nat × Cursor) := do
  let (logw, nw, deltaCount, cursor) ← readLayerPrefix cursor
  let (deltas, cursor) ← readDeltasChunk constantCount deltaCount cursor
  let deltas := Array.mk deltas
  let (segmentCount, cursor) ← readSegmentCount cursor
  let (segments, _, cursor) ← readSegmentsChunk deltas.size segmentCount 0 cursor
  let segments := Array.mk segments
  let (tokens, tokenCount, termCount, cursor) ←
    readCompressedTokens segmentCount (segmentLengths segments) cursor
  let totalTerms := totalTerms + termCount
  if totalTerms > maxTotalTerms then .error .excessiveExpansion else
  .ok ({ logw := logw, nw := nw, deltas := deltas, segments := segments,
         tokens := tokens, tokenCount := tokenCount, termCount := termCount }, totalTerms, cursor)

/-- Compose independently checked layer-parser stages.  `deltaList` and `segmentList` are
    themselves append chains of chunk constants, built with `readDeltasChunk_compose` and
    `readSegmentsChunk_compose`, so nothing here forces a whole table into one module. -/
theorem readCompressedLayer_eq_of_stages
    (constantCount totalTerms : Nat)
    {start c1 c2 c3 c4 stop : Cursor}
    {logw nw deltaCount segmentCount symbols tokenCount termCount : Nat}
    {deltaList : List Delta} {segmentList : List (Array Nat)} {tokens : Array Nat}
    (hprefix : readLayerPrefix start = .ok (logw, nw, deltaCount, c1))
    (hdeltas : readDeltasChunk constantCount deltaCount c1 = .ok (deltaList, c2))
    (hsegcount : readSegmentCount c2 = .ok (segmentCount, c3))
    (hsegs : readSegmentsChunk (Array.mk deltaList).size segmentCount 0 c3
               = .ok (segmentList, symbols, c4))
    (htokens : readCompressedTokens segmentCount (segmentLengths (Array.mk segmentList)) c4
               = .ok (tokens, tokenCount, termCount, stop))
    (hbound : ¬ (totalTerms + termCount > maxTotalTerms)) :
    readCompressedLayer constantCount totalTerms start
      = .ok ({ logw := logw, nw := nw, deltas := Array.mk deltaList,
               segments := Array.mk segmentList, tokens := tokens,
               tokenCount := tokenCount, termCount := termCount },
             totalTerms + termCount, stop) := by
  simp only [readCompressedLayer, hprefix, hdeltas, hsegcount, hsegs, htokens,
    bind, Except.bind, if_neg hbound]

def readCompressedLayersLoop (constantCount : Nat) :
    Nat → Nat → List CompressedLayer → Cursor → Except Error (List CompressedLayer × Cursor)
  | 0, _, revLayers, cursor => .ok (revLayers.reverse, cursor)
  | count + 1, totalTerms, revLayers, cursor => do
      let (layer, totalTerms, cursor) ← readCompressedLayer constantCount totalTerms cursor
      readCompressedLayersLoop constantCount count totalTerms (layer :: revLayers) cursor

/-- A generated, term-list-opaque chain of independently checked layer-parser transitions. -/
inductive LayerParseSteps (constantCount : Nat) :
    Nat → Nat → List CompressedLayer → Cursor → Cursor → Prop where
  | nil {total cursor} : LayerParseSteps constantCount 0 total [] cursor cursor
  | cons {count total total' layer layers start middle stop} :
      readCompressedLayer constantCount total start = .ok (layer, total', middle) →
      LayerParseSteps constantCount count total' layers middle stop →
      LayerParseSteps constantCount (count + 1) total (layer :: layers) start stop

theorem readCompressedLayersLoop_eq_of_steps {constantCount count total layers start stop}
    (hsteps : LayerParseSteps constantCount count total layers start stop)
    (revLayers : List CompressedLayer) :
    readCompressedLayersLoop constantCount count total revLayers start =
      .ok (revLayers.reverse ++ layers, stop) := by
  induction hsteps generalizing revLayers with
  | nil => simp [readCompressedLayersLoop]
  | cons hhead _ ih =>
      simp only [readCompressedLayersLoop, hhead, bind, Except.bind]
      rw [ih]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

private structure ExpandState where
  g : Nat := 0
  h0 : Nat := 0
  h1 : Nat := 0
  count : Nat := 0
  revTerms : List RawTerm := []

private def applyDelta (deltas : Array Delta) (index : Nat)
    (state : ExpandState) : Except Error ExpandState :=
  match deltas[index]? with
  | none => .error .deltaIndexOutOfBounds
  | some delta =>
      if state.count = maxTermsPerLayer then
        .error .excessiveExpansion
      else
        let g := (state.g + delta.g) % word32Modulus
        let h0 := (state.h0 + delta.h0) % word32Modulus
        let h1 := (state.h1 + delta.h1) % word32Modulus
        .ok { g := g, h0 := h0, h1 := h1, count := state.count + 1,
              revTerms := { g := g, h0 := h0, h1 := h1,
                            kIndex := delta.kIndex } :: state.revTerms }

private def applySegmentLoop (deltas : Array Delta) (segment : Array Nat) :
    Nat → ExpandState → Except Error ExpandState
  | 0, state => .ok state
  | fuel + 1, state =>
      let index := segment.size - (fuel + 1)
      match segment[index]? with
      | none => .error .deltaIndexOutOfBounds
      | some deltaIndex => do
          let state ← applyDelta deltas deltaIndex state
          applySegmentLoop deltas segment fuel state

private def applySegment (deltas : Array Delta) (segment : Array Nat)
    (state : ExpandState) : Except Error ExpandState :=
  applySegmentLoop deltas segment segment.size state

private def applySegmentIndex (deltas : Array Delta) (segments : Array (Array Nat))
    (index : Nat) (state : ExpandState) : Except Error ExpandState :=
  match segments[index]? with
  | none => .error .segmentIndexOutOfBounds
  | some segment => applySegment deltas segment state

private def applyTokenArrayLoop (deltas : Array Delta) (segments : Array (Array Nat))
    (tokens : Array Nat) : Nat → ExpandState → Except Error ExpandState
  | 0, state => .ok state
  | fuel + 1, state =>
      let index := tokens.size - (fuel + 1)
      match tokens[index]? with
      | none => .error .segmentIndexOutOfBounds
      | some segmentIndex => do
          let state ← applySegmentIndex deltas segments segmentIndex state
          applyTokenArrayLoop deltas segments tokens fuel state

private def applyTokenArray (deltas : Array Delta) (segments : Array (Array Nat))
    (tokens : Array Nat) (state : ExpandState) : Except Error ExpandState :=
  applyTokenArrayLoop deltas segments tokens tokens.size state



private def readExpandedTerms (deltas : Array Delta) (segments : Array (Array Nat))
    (cursor : Cursor) : Except Error (ExpandState × Cursor) := do
  let (count, cursor) ← readBounded maxTermsPerLayer cursor
  let (tokens, cursor) ←
    readIndexListChunk segments.size .segmentIndexOutOfBounds count cursor
  let state ← applyTokenArray deltas segments (Array.mk tokens) {}
  .ok (state, cursor)


/-- Does `tree` faithfully stand in for this layer's delta table?  `.leaf` means "no advice
    supplied" and is trivially fine, since lookups then fall back to indexing the array.
    Otherwise this is two linear passes, run once per layer, and it is what ties the untrusted
    tree back to the list the decoder actually read from the committed bytes. -/
def CompressedLayer.deltasOk (layer : CompressedLayer) (tree : PTree Delta) : Bool :=
  match tree with
  | .leaf => true
  | _ => tree.checkSize.isSome && decide (tree.toList = layer.deltas.toList)

/-- Read delta `i`: through the tree when advice was supplied, by indexing otherwise. -/
def CompressedLayer.deltaAt (layer : CompressedLayer) (tree : PTree Delta) (i : Nat) :
    Option Delta :=
  match tree with
  | .leaf => layer.deltas[i]?
  | _ => tree.lookup i

/-- The payoff: validated advice answers exactly what indexing would, in `log n` steps
    instead of `i`.  Expansion is therefore unchanged in meaning, only in cost. -/
theorem CompressedLayer.deltaAt_eq (layer : CompressedLayer) (tree : PTree Delta)
    (h : layer.deltasOk tree = true) (i : Nat) : layer.deltaAt tree i = layer.deltas[i]? := by
  cases tree with
  | leaf => rfl
  | node ls l a r =>
      simp only [CompressedLayer.deltasOk, Bool.and_eq_true, decide_eq_true_eq,
        Option.isSome_iff_exists] at h
      obtain ⟨⟨n, hn⟩, hlist⟩ := h
      show PTree.lookup (.node ls l a r) i = _
      rw [PTree.lookup_eq_getElem _ hn i, hlist]
      simp

/-- Every wire index a term mentions must address a wire that actually exists.

`h0`/`h1` index the valuation feeding this layer, which has `layer.nw` entries; `g` indexes
the layer's own output block, whose width is `gBound` — `noutput` for layer 0 and the
previous layer's `nw` otherwise, exactly as `eval.rs` chooses it.

Without this the decoder accepts artifacts on which the Lean and Rust semantics disagree:
`evalLayer` reads a missing wire as `0` because its valuation is a total `Nat → F`, while
`eval_layer` indexes a `Vec` and panics.  The `g` bound is enforced for assertion terms too,
which is marginally stricter than `eval.rs` (it only writes `vout[g]` when `k ≠ 0`); a
scheduler that assigned an assertion an out-of-range output wire would be rejected here. -/
private def termInRange (layer : CompressedLayer) (gBound g h0 h1 : Nat) : Bool :=
  g < gBound && h0 < layer.nw && h1 < layer.nw

private def nextTermLoop (layer : CompressedLayer) (gBound : Nat) (tree : PTree Delta) :
    Nat → ExpansionCursor → Except Error (Option (RawTerm × ExpansionCursor))
  | 0, _ => .error .excessiveExpansion
  | fuel + 1, cursor =>
      match cursor.segment with
      | deltaIndex :: restSegment =>
          match layer.deltaAt tree deltaIndex with
          | none => .error .deltaIndexOutOfBounds
          | some delta =>
              let g := (cursor.g + delta.g) % word32Modulus
              let h0 := (cursor.h0 + delta.h0) % word32Modulus
              let h1 := (cursor.h1 + delta.h1) % word32Modulus
              if termInRange layer gBound g h0 h1 then
                .ok (some ({ g := g, h0 := h0, h1 := h1, kIndex := delta.kIndex },
                           { cursor with segment := restSegment,
                                         g := g, h0 := h0, h1 := h1,
                                         emitted := cursor.emitted + 1 }))
              else
                .error .wireIndexOutOfRange
      | [] =>
          -- The current segment is spent; open the next one from the token stream.  This happens
          -- once per segment, not once per term.
          match cursor.outer with
          | [] => .ok none
          | token :: restOuter =>
              match layer.segments[token]? with
              | none => .error .segmentIndexOutOfBounds
              | some segment =>
                  nextTermLoop layer gBound tree fuel
                    { cursor with segment := segment.toList, outer := restOuter }

/-- Where expansion starts: the whole token stream still to be read. -/
def CompressedLayer.initialCursor (layer : CompressedLayer) : ExpansionCursor :=
  { outer := layer.tokens.toList }

/-- Decode one term and return a checkpoint from which expansion can resume. -/
def CompressedLayer.nextTerm (layer : CompressedLayer) (gBound : Nat) (tree : PTree Delta)
    (cursor : ExpansionCursor) :
    Except Error (Option (RawTerm × ExpansionCursor)) :=
  nextTermLoop layer gBound tree (layer.tokenCount + 2) cursor

/-- Expand at most the requested number of terms. Generated modules use a fixed small count
    and prove each transition independently, bounding kernel memory. -/
def CompressedLayer.expandChunk (layer : CompressedLayer) (gBound : Nat) (tree : PTree Delta) :
    Nat → ExpansionCursor → Except Error (List RawTerm × ExpansionCursor)
  | 0, cursor => .ok ([], cursor)
  | count + 1, cursor => do
      let next? ← layer.nextTerm gBound tree cursor
      match next? with
      | none => .error .unexpectedEnd
      | some (term, cursor) =>
          let (terms, cursor) ← layer.expandChunk gBound tree count cursor
          .ok (term :: terms, cursor)

/-- Successful sequential chunk checks compose without re-running either chunk. -/
theorem CompressedLayer.expandChunk_compose (layer : CompressedLayer) (gBound : Nat)
    (tree : PTree Delta)
    {a b : Nat} {start middle stop : ExpansionCursor}
    {left right : List RawTerm}
    (hleft : layer.expandChunk gBound tree a start = .ok (left, middle))
    (hright : layer.expandChunk gBound tree b middle = .ok (right, stop)) :
    layer.expandChunk gBound tree (a + b) start = .ok (left ++ right, stop) := by
  induction a generalizing start middle left with
  | zero =>
      simp only [CompressedLayer.expandChunk] at hleft
      cases hleft
      simpa using hright
  | succ a ih =>
      simp only [Nat.succ_add, CompressedLayer.expandChunk] at hleft ⊢
      cases hnext : layer.nextTerm gBound tree start with
      | error error =>
          rw [hnext] at hleft
          contradiction
      | ok next =>
          cases next with
          | none =>
              rw [hnext] at hleft
              contradiction
          | some pair =>
              rcases pair with ⟨term, nextCursor⟩
              rw [hnext] at hleft
              simp only [bind, Except.bind] at hleft ⊢
              cases hrest : layer.expandChunk gBound tree a nextCursor with
              | error error =>
                  rw [hrest] at hleft
                  contradiction
              | ok result =>
                  rcases result with ⟨tail, actualMiddle⟩
                  rw [hrest] at hleft
                  obtain ⟨rfl, rfl⟩ := hleft
                  have hall := ih (start := nextCursor) (middle := actualMiddle)
                    (left := tail) hrest hright
                  rw [hall]
                  rfl

def CompressedLayer.finished (layer : CompressedLayer) (gBound : Nat) (tree : PTree Delta)
    (cursor : ExpansionCursor) : Bool :=
  match layer.nextTerm gBound tree cursor with
  | .ok none => cursor.emitted == layer.termCount
  | _ => false

def CompressedLayer.expand (layer : CompressedLayer) (gBound : Nat)
    (tree : PTree Delta := .leaf) : Except Error DecodedLayer := do
  if !layer.deltasOk tree then .error .deltaIndexOutOfBounds else
  let (terms, cursor) ← layer.expandChunk gBound tree layer.termCount layer.initialCursor
  if layer.finished gBound tree cursor then
    .ok { logw := layer.logw, nw := layer.nw, terms := terms }
  else .error .excessiveExpansion

/-- A chain of generated chunk checks is enough to certify the decoded layer. -/
theorem CompressedLayer.expand_eq_of_chunk (layer : CompressedLayer) (gBound : Nat)
    (tree : PTree Delta) (hadvice : layer.deltasOk tree = true)
    {terms : List RawTerm} {cursor : ExpansionCursor}
    (hchunk : layer.expandChunk gBound tree layer.termCount layer.initialCursor
                = .ok (terms, cursor))
    (hfinished : layer.finished gBound tree cursor = true) :
    layer.expand gBound tree = .ok { logw := layer.logw, nw := layer.nw, terms := terms } := by
  simp only [CompressedLayer.expand, hadvice, Bool.not_true, Bool.false_eq_true, if_false,
    hchunk, bind, Except.bind]
  simp [hfinished]

/-- Layers are stored output-first, and layer `l` writes into the block that layer `l - 1`
    reads, so the `g` bound for the next layer is this layer's `nw`.  The initial bound is
    `noutput`; `eval.rs` makes the same choice with
    `if l == 0 { raw.noutput } else { raw.layers[l - 1].nw() }`. -/
def expandLayers :
    Nat → List (PTree Delta) → List CompressedLayer → List DecodedLayer →
      Except Error (List DecodedLayer)
  | _, _, [], revLayers => .ok revLayers.reverse
  | gBound, trees, layer :: rest, revLayers => do
      let decoded ← layer.expand gBound (trees.headD .leaf)
      expandLayers layer.nw trees.tail rest (decoded :: revLayers)

/-- A term-list-opaque correspondence between compressed and decoded layers. -/
inductive LayersExpand : Nat → List (PTree Delta) → List CompressedLayer → List DecodedLayer →
    Prop where
  | nil {gBound trees} : LayersExpand gBound trees [] []
  | cons {gBound trees source result sources results} :
      source.expand gBound (trees.headD .leaf) = .ok result →
      LayersExpand source.nw trees.tail sources results →
      LayersExpand gBound trees (source :: sources) (result :: results)

/-- Lift pointwise layer expansion proofs through the accumulator used by `expandLayers`.
    Unlike simplification of a concrete circuit, this never unfolds a decoded term list. -/
theorem expandLayers_eq_of_pairs {gBound : Nat} {trees : List (PTree Delta)}
    {compressed : List CompressedLayer} {decoded : List DecodedLayer}
    (hlayers : LayersExpand gBound trees compressed decoded) (revLayers : List DecodedLayer) :
    expandLayers gBound trees compressed revLayers = .ok (revLayers.reverse ++ decoded) := by
  induction hlayers generalizing revLayers with
  | nil => simp [expandLayers]
  | cons hexpand _ ih =>
      simp only [expandLayers, hexpand, bind, Except.bind]
      rw [ih]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

def CompressedCircuit.expand (circuit : CompressedCircuit)
    (trees : List (PTree Delta) := []) : Except Error DecodedCircuit := do
  let layers ← expandLayers circuit.noutput trees circuit.layers []
  .ok { fieldId := circuit.fieldId
        ninput := circuit.ninput
        npublicInput := circuit.npublicInput
        noutput := circuit.noutput
        logv := circuit.logv
        subfieldBoundary := circuit.subfieldBoundary
        constants := circuit.constants
        layers := layers
        legacyCircuitId := circuit.legacyCircuitId }

/-- Generated per-layer expansion theorems can be lifted to the whole circuit without
    unfolding any of their (potentially very large) term lists. -/
theorem CompressedCircuit.expand_eq_of_layers (circuit : CompressedCircuit)
    (trees : List (PTree Delta)) {layers : List DecodedLayer}
    (hlayers : expandLayers circuit.noutput trees circuit.layers [] = .ok layers) :
    circuit.expand trees = .ok
      { fieldId := circuit.fieldId
        ninput := circuit.ninput
        npublicInput := circuit.npublicInput
        noutput := circuit.noutput
        logv := circuit.logv
        subfieldBoundary := circuit.subfieldBoundary
        constants := circuit.constants
        layers := layers
        legacyCircuitId := circuit.legacyCircuitId } := by
  simp only [CompressedCircuit.expand, hlayers, bind, Except.bind]

private def readLayer (constantCount totalTerms : Nat) (cursor : Cursor) :
    Except Error (DecodedLayer × Nat × Cursor) := do
  let (logw, cursor) ← readUleb cursor
  if logw > maxLogWidth then .error .badLogWidth else
  let (nw, cursor) ← readBounded maxLayerInputs cursor
  let (deltaCount, cursor) ← readBounded maxDeltas cursor
  let (deltas, cursor) ← readDeltasChunk constantCount deltaCount cursor
  let deltas := Array.mk deltas
  let (segmentCount, cursor) ← readBounded maxDeltas cursor
  let (segments, _, cursor) ← readSegmentsChunk deltas.size segmentCount 0 cursor
  let segments := Array.mk segments
  let (state, cursor) ← readExpandedTerms deltas segments cursor
  let totalTerms := totalTerms + state.count
  if totalTerms > maxTotalTerms then
    .error .excessiveExpansion
  else
    .ok ({ logw := logw, nw := nw, terms := state.revTerms.reverse }, totalTerms, cursor)

private def readLayersLoop (constantCount : Nat) :
    Nat → Nat → List DecodedLayer → Cursor → Except Error (List DecodedLayer × Cursor)
  | 0, _, revLayers, cursor => .ok (revLayers.reverse, cursor)
  | count + 1, totalTerms, revLayers, cursor => do
      let (layer, totalTerms, cursor) ← readLayer constantCount totalTerms cursor
      readLayersLoop constantCount count totalTerms (layer :: revLayers) cursor

/-- Parse and validate the fixed header and constant table, stopping immediately before the
    first layer. Generated certificates pin the returned cursor explicitly. -/
def parseHeader (field : FieldEncoding) (input : PackedBytes) :
    Except Error (CompressedHeader × Cursor) := do
  if field.byteLength = 0 then .error .badFieldEncoding else
  let cursor ← initCursor input
  let cursor ← readMagic cursor
  let (fieldId, cursor) ← readUleb cursor
  if fieldId != field.fieldId then .error .fieldMismatch else
  let (noutput, cursor) ← readBounded maxWires cursor
  if noutput = 0 then .error .zeroOutputs else
  let logv := ceilLog2 noutput
  if logv > maxLogWidth then .error .badLogWidth else
  let (copies, cursor) ← readUleb cursor
  if copies != 1 then .error .unsupportedCopies else
  let (npublicInput, cursor) ← readBounded maxWires cursor
  let (subfieldBoundary, cursor) ← readBounded maxWires cursor
  let (ninput, cursor) ← readBounded maxWires cursor
  if npublicInput > ninput then .error .publicInputsExceedInputs else
  let (layerCount, cursor) ← readBounded maxLayers cursor
  let (constantCount, cursor) ← readBounded maxConstants cursor
  let (constants, cursor) ← readConstantsChunk field constantCount cursor
  .ok ({ fieldId := fieldId, ninput := ninput, npublicInput := npublicInput,
         noutput := noutput, logv := logv, subfieldBoundary := subfieldBoundary,
         constants := Array.mk constants, layerCount := layerCount }, cursor)

/-- The deepest layer reads the circuit inputs directly rather than another layer's outputs,
    so it may not claim more input wires than the circuit has.  `eval.rs` hands that layer a
    `vin` of exactly `ninput` entries and would panic beyond it, whereas Lean's valuation is a
    total function that would silently read `0`.  The per-term check bounds `h0`/`h1` by
    `nw`, so this is what makes that bound meaningful for the deepest layer. -/
def deepestWidthOk (ninput : Nat) (layers : List CompressedLayer) : Bool :=
  match layers.getLast? with
  | none => true
  | some deepest => deepest.nw ≤ ninput

/-- Consume the compatibility trailer and require exact end of the committed payload. -/
def CompressedHeader.finish (header : CompressedHeader) (layers : List CompressedLayer)
    (cursor : Cursor) : Except Error CompressedCircuit := do
  if layers.length != header.layerCount then .error .excessiveCount else
  if !deepestWidthOk header.ninput layers then .error .inputWidthMismatch else
  let (legacyCircuitId, cursor) ← readNatLE 32 cursor
  if cursor.remaining != 0 || !cursor.laterPages.isEmpty then .error .trailingBytes else
  .ok { fieldId := header.fieldId
        ninput := header.ninput
        npublicInput := header.npublicInput
        noutput := header.noutput
        logv := header.logv
        subfieldBoundary := header.subfieldBoundary
        constants := header.constants
        layers := layers
        legacyCircuitId := legacyCircuitId }

/-- Parse an exact packed LFC2 payload while retaining its compact dictionaries.  This is the
    entry point used by generated chunk certificates. -/
def decodeCompressed (field : FieldEncoding) (input : PackedBytes) :
    Except Error CompressedCircuit := do
  let (header, cursor) ← parseHeader field input
  let (layers, cursor) ←
    readCompressedLayersLoop header.constants.size header.layerCount 0 [] cursor
  header.finish layers cursor

/-- Compose independently checked header, layer, and trailer transitions into the ordinary
    decoder theorem without re-running the monolithic parser. -/
theorem decodeCompressed_eq_of_stages (field : FieldEncoding) (input : PackedBytes)
    {header : CompressedHeader} {start stop : Cursor}
    {layers : List CompressedLayer} {circuit : CompressedCircuit}
    (hheader : parseHeader field input = .ok (header, start))
    (hsteps : LayerParseSteps header.constants.size header.layerCount 0 layers start stop)
    (hfinish : header.finish layers stop = .ok circuit) :
    decodeCompressed field input = .ok circuit := by
  simp only [decodeCompressed, hheader, bind, Except.bind]
  rw [readCompressedLayersLoop_eq_of_steps hsteps []]
  simpa only [List.reverse_nil, List.nil_append, bind, Except.bind] using hfinish

/-- Decode and fully expand an exact packed LFC2 payload. Success implies that no committed
    byte is ignored. Large generated proofs should use `decodeCompressed` and `expandChunk`
    rather than reducing this whole-circuit convenience function in one theorem. -/
def decode (field : FieldEncoding) (input : PackedBytes)
    (trees : List (PTree Delta) := []) : Except Error DecodedCircuit := do
  let circuit ← decodeCompressed field input
  circuit.expand trees

/-- Compose the staged byte parser and chunked expansion results opaquely. -/
theorem decode_eq_of_compressed (field : FieldEncoding) (input : PackedBytes)
    (trees : List (PTree Delta))
    {compressed : CompressedCircuit} {decoded : DecodedCircuit}
    (hdecode : decodeCompressed field input = .ok compressed)
    (hexpand : compressed.expand trees = .ok decoded) :
    decode field input trees = .ok decoded := by
  simp only [decode, hdecode, bind, Except.bind, hexpand]

end Quadcert.Lfc2
