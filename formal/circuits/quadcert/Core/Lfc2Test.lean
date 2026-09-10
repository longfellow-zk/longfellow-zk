import quadcert.Core.Lfc2

/-! Small kernel tests for canonical parsing and the wire-index bounds. -/

namespace Quadcert.Lfc2.Test

-- The phrase-dictionary fixture that used to live here tested `TokenEncoding.phrases`, which
-- the format no longer has: every layer now carries a flat segment-index stream, which is LFC2's
-- token encoding. The bounded-expansion property it checked is covered by the wire-index tests
-- below and by `Bridge/Rung1`, which decodes a real artifact.

-- Field id 4 encoded as the non-shortest ULEB sequence 0x84 0x00.
example : decode gf2_128 { byteLength := 6, pages := [0x843243464c] }
    = .error .noncanonicalUleb := by
  rfl

example : decode gf2_128 { byteLength := 4, pages := [] } = .error .badPageCount := by
  rfl

/-! ### Wire-index bounds

One layer emitting the single term `(g, h0, h1) = (1, 1, 1)`.  Each index is rejected
independently, so the check cannot pass vacuously. -/

private def oneTermLayer (nw : Nat) : CompressedLayer :=
  { logw := 1, nw := nw
    deltas := #[⟨1, 1, 1, 0⟩]
    segments := #[#[0]]
    tokens := #[0]
    tokenCount := 1
    termCount := 1 }

/-- In range: `g < 2` and `h0, h1 < nw = 2`. -/
example : (oneTermLayer 2).expand 2
    = .ok { logw := 1, nw := 2, terms := [⟨1, 1, 1, 0⟩] } := by rfl

/-- `h0 = h1 = 1` is out of range once the layer declares only one input wire. -/
example : (oneTermLayer 1).expand 2 = .error .wireIndexOutOfRange := by rfl

/-- `g = 1` is out of range when the block written by this layer has width 1. -/
example : (oneTermLayer 2).expand 1 = .error .wireIndexOutOfRange := by rfl

/-- The deepest layer may not claim more input wires than the circuit has. -/
example : deepestWidthOk 1 [oneTermLayer 2] = false := by rfl

example : deepestWidthOk 2 [oneTermLayer 2] = true := by rfl

/-- Only the deepest layer is constrained by `ninput`; earlier layers read their successor. -/
example : deepestWidthOk 2 [oneTermLayer 9, oneTermLayer 2] = true := by rfl


/-! ### `cursorAt` agrees with stepping the parser

A checkpoint named as a position must be the very cursor the parser would have reached.  These
pin that on a two-page input, including the page boundary at 4096. -/

private def twoPage : PackedBytes :=
  { byteLength := 4100, pages := [0xab, 0xcd] }

example : cursorAt twoPage 0
    = { page := 0xab, pageRemaining := 4096, laterPages := [0xcd], remaining := 4100 } := by rfl

example : (cursorAt twoPage 4096).pageRemaining = 4 := by rfl
example : (cursorAt twoPage 4096).laterPages = [] := by rfl
example : (cursorAt twoPage 4096).remaining = 4 := by rfl
example : (cursorAt twoPage 4099).remaining = 1 := by rfl

end Quadcert.Lfc2.Test
