/-!
# SHA-256 for the LFC2 page commitment

Kernel-reducible SHA-256, used by `CircuitCommitment` to check a packed page's Merkle leaf hash
without `native_decide`. `hashPacked` is the variant that takes a page as one packed `Nat`, so a
generated module can store a 4,096-byte page as a single literal and still check its leaf.

**Reconstructed 2026-08-12 from the compiled `.olean` after the source was deleted by a careless
`rm circuits/quadcert/Sha*.lean` during SHA-256 *circuit* work — this file's name collided with
the generated `Sha*` modules.** Every definition below was recovered by printing the surviving
declarations, so the semantics are exactly what was there; only comments and formatting are new.
The reconstruction is self-checking: `Ecdsa2Commitment*` and `MdocSigCommitment*` prove
page-leaf hashes by `decide` against this module, so any deviation fails to build.
-/

namespace QuadCert.Sha256

private def modulus : Nat := 4294967296
private def wordMask : Nat := 4294967295

@[reducible] def Byte : Type := Nat
@[reducible] def Word : Type := Nat
@[reducible] def Digest : Type := List Byte

def word (x : Nat) : Word := x % modulus

def add (x y : Word) : Word := word (x + y)
def and (x y : Word) : Word := x &&& y
def not (x : Word) : Word := wordMask - word x
def xor (x y : Word) : Word := Nat.xor x y
def xor3 (x y z : Word) : Word := xor (xor x y) z

def shr (x : Word) (n : Nat) : Word := x >>> n
def rotr (x : Word) (n : Nat) : Word := word (shr x n + (x % 2 ^ n) <<< (32 - n))

def ch (x y z : Word) : Word := xor (and x y) (and (not x) z)
def maj (x y z : Word) : Word := xor3 (and x y) (and x z) (and y z)

def bigSigma0 (x : Word) : Word := xor3 (rotr x 2) (rotr x 13) (rotr x 22)
def bigSigma1 (x : Word) : Word := xor3 (rotr x 6) (rotr x 11) (rotr x 25)
def smallSigma0 (x : Word) : Word := xor3 (rotr x 7) (rotr x 18) (shr x 3)
def smallSigma1 (x : Word) : Word := xor3 (rotr x 17) (rotr x 19) (shr x 10)

/-- The eight working variables, FIPS 180-4 §6.2.2. -/
private structure Registers where
  a : Word
  b : Word
  c : Word
  d : Word
  e : Word
  f : Word
  g : Word
  h : Word

private def initial : List Word :=
  [1779033703, 3144134277, 1013904242, 2773480762,
   1359893119, 2600822924, 528734635, 1541459225]

private def roundConstants : List Word :=
  [1116352408, 1899447441, 3049323471, 3921009573, 961987163, 1508970993, 2453635748, 2870763221,
   3624381080, 310598401, 607225278, 1426881987, 1925078388, 2162078206, 2614888103, 3248222580,
   3835390401, 4022224774, 264347078, 604807628, 770255983, 1249150122, 1555081692, 1996064986,
   2554220882, 2821834349, 2952996808, 3210313671, 3336571891, 3584528711, 113926993, 338241895,
   666307205, 773529912, 1294757372, 1396182291, 1695183700, 1986661051, 2177026350, 2456956037,
   2730485921, 2820302411, 3259730800, 3345764771, 3516065817, 3600352804, 4094571909, 275423344,
   430227734, 506948616, 659060556, 883997877, 958139571, 1322822218, 1537002063, 1747873779,
   1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298]

private def round (state : Registers) (k w : Word) : Registers :=
  let t1 := add (add (add (add state.h (bigSigma1 state.e)) (ch state.e state.f state.g)) k) w
  let t2 := add (bigSigma0 state.a) (maj state.a state.b state.c)
  { a := add t1 t2, b := state.a, c := state.b, d := state.c,
    e := add state.d t1, f := state.e, g := state.f, h := state.g }

private def rounds : Nat → Nat → List Word → Registers → Registers
  | 0, _, _, state => state
  | fuel + 1, i, w, state =>
      rounds fuel (i + 1) w (round state (roundConstants.getD i 0) (w.getD i 0))

private def byteAt (bytes : List Byte) (i : Nat) : Byte := bytes.getD i 0 % 256

private def loadWord (block : List Byte) (i : Nat) : Word :=
  let j := 4 * i
  byteAt block j * 2 ^ 24 + byteAt block (j + 1) * 2 ^ 16 +
    byteAt block (j + 2) * 2 ^ 8 + byteAt block (j + 3)

/-- The same word, read out of a packed page rather than a byte list. -/
private def loadPackedWord (packed : Nat) : Word :=
  packed % 256 * 2 ^ 24 + packed >>> 8 % 256 * 2 ^ 16 +
    packed >>> 16 % 256 * 2 ^ 8 + packed >>> 24 % 256

private def wordBytes (value : Word) : List Byte :=
  [value / 2 ^ 24 % 256, value / 2 ^ 16 % 256, value / 2 ^ 8 % 256, value % 256]

private def lengthBytes (byteLength : Nat) : List Byte :=
  let bitLength := byteLength * 8
  (List.range 8).map (fun i => bitLength / 256 ^ (7 - i) % 256)

def pad (bytes : List Byte) : List Byte :=
  let zeroCount := (55 + 64 - bytes.length % 64) % 64
  bytes ++ [128] ++ List.replicate zeroCount 0 ++ lengthBytes bytes.length

private def blocks (bytes : List Byte) : List (List Byte) :=
  let padded := pad bytes
  (List.range (padded.length / 64)).map (fun i => (padded.drop (64 * i)).take 64)

private def scheduleLoop (block : List Byte) : Nat → Nat → List Word → List Word
  | 0, _, acc => acc.reverse
  | fuel + 1, i, acc =>
      scheduleLoop block fuel (i + 1)
        ((if i < 16 then loadWord block i
          else add (add (smallSigma1 (acc.getD 1 0)) (acc.getD 6 0))
                   (add (smallSigma0 (acc.getD 14 0)) (acc.getD 15 0))) :: acc)

private def schedule (block : List Byte) : List Word := scheduleLoop block 64 0 []

private def packedScheduleLoop : Nat → Nat → Nat → List Word → List Word
  | 0, _, _, acc => acc.reverse
  | fuel + 1, i, block, acc =>
      packedScheduleLoop fuel (i + 1) (if i < 16 then block >>> 32 else block)
        ((if i < 16 then loadPackedWord block
          else add (add (smallSigma1 (acc.getD 1 0)) (acc.getD 6 0))
                   (add (smallSigma0 (acc.getD 14 0)) (acc.getD 15 0))) :: acc)

private def packedSchedule (block : Nat) : List Word := packedScheduleLoop 64 0 block []

private def compress (state : List Word) (block : List Byte) : List Word :=
  let start : Registers :=
    { a := state.getD 0 0, b := state.getD 1 0, c := state.getD 2 0, d := state.getD 3 0,
      e := state.getD 4 0, f := state.getD 5 0, g := state.getD 6 0, h := state.getD 7 0 }
  let result := rounds 64 0 (schedule block) start
  [add (state.getD 0 0) result.a, add (state.getD 1 0) result.b,
   add (state.getD 2 0) result.c, add (state.getD 3 0) result.d,
   add (state.getD 4 0) result.e, add (state.getD 5 0) result.f,
   add (state.getD 6 0) result.g, add (state.getD 7 0) result.h]

private def compressPacked (state : List Word) (block : Nat) : List Word :=
  let start : Registers :=
    { a := state.getD 0 0, b := state.getD 1 0, c := state.getD 2 0, d := state.getD 3 0,
      e := state.getD 4 0, f := state.getD 5 0, g := state.getD 6 0, h := state.getD 7 0 }
  let result := rounds 64 0 (packedSchedule block) start
  [add (state.getD 0 0) result.a, add (state.getD 1 0) result.b,
   add (state.getD 2 0) result.c, add (state.getD 3 0) result.d,
   add (state.getD 4 0) result.e, add (state.getD 5 0) result.f,
   add (state.getD 6 0) result.g, add (state.getD 7 0) result.h]

private def packedBlocks : Nat → List Word → Nat → List Word
  | 0, state, _ => state
  | count + 1, state, block => packedBlocks count (compressPacked state block) (block >>> 512)

/-- Little-endian packing of a byte list, matching how a page is stored as one `Nat`. -/
def packLE : List Byte → Nat
  | [] => 0
  | b :: bs => b + 256 * packLE bs

def hash (bytes : List Byte) : Digest :=
  ((blocks bytes).foldl compress initial).flatMap wordBytes

/-- The page-commitment entry point: hash `byteLength` bytes supplied as one packed natural. -/
def hashPacked (byteLength : Nat) (packed : Nat) : Digest :=
  let paddedLength := (byteLength + 9 + 63) / 64 * 64
  let message := packed % 1 <<< (8 * byteLength)
  let padded := message + 128 <<< (8 * byteLength) +
    packLE (lengthBytes byteLength) <<< (8 * (paddedLength - 8))
  (packedBlocks (paddedLength / 64) initial padded).flatMap wordBytes

end QuadCert.Sha256
