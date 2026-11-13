import TranscriptV2.Framing

/-! Stored LFC3 streams and their circuit-ID encoding. Coordinates are wrapping
32-bit deltas, coefficient indices are absolute, and tokens select segments.
The identifier traverses stored arrays without expanding repeated segments. -/
namespace LfzkV2.Current.SegmentedCircuit
open TranscriptV2.Framing

abbrev Word := Fin (2^32)
abbrev Record (arity : ℕ) := Fin arity → Word

def word (n : ℕ) : Word := ⟨n % 2^32, Nat.mod_lt _ (by decide)⟩

structure Stream (arity : ℕ) where
  deltas : List (Record arity) := []
  segments : List (List Word) := []
  tokens : List Word := []

/-- The coefficient index is the final component and is never delta encoded. -/
def delta {arity : ℕ} (previous current : Record arity) : Record arity := fun i =>
  if i.val+1 < arity then word (current i + 2^32 - previous i) else current i

private def intern {arity : ℕ} (state : List (Record arity) × List Word)
    (record : Record arity) : List (Record arity) × List Word :=
  let index := state.1.findIdx fun existing => List.ofFn existing == List.ofFn record
  (if index < state.1.length then state.1 else state.1 ++ [record],
    state.2 ++ [word index])

/-- Rust's `Stream::from_terms`: delta encode, intern in first-occurrence order,
then store one segment and one token. This does not run the compiler compressor. -/
def fromTerms {arity : ℕ} (terms : List (Record arity)) : Stream arity :=
  if terms.isEmpty then {} else
    let deltas := (terms.foldl (fun state current =>
      (current,state.2 ++ [delta state.1 current])) ((fun _ => word 0),[])).2
    let table := deltas.foldl intern ([],[])
    ⟨table.1,[table.2],[word 0]⟩

def streamBytes {arity : ℕ} (tag : ℕ) (s : Stream arity) : Bytes :=
  encodeLE 1 tag ++
    [s.deltas.length,s.segments.length,(s.segments.map List.length).sum,s.tokens.length].flatMap (encodeLE 8) ++
    s.deltas.flatMap (fun record => (List.ofFn record).flatMap fun n => encodeLE 4 n.val) ++
    s.segments.flatMap (fun segment => encodeLE 4 segment.length) ++
    s.segments.flatten.flatMap (fun n => encodeLE 4 n.val) ++
    s.tokens.flatMap (fun n => encodeLE 4 n.val)

structure Layer where
  inputs : ℕ
  logInputs : ℕ
  quadratic : Stream 4 := {}
  linear : Stream 3 := {}
  constant : Stream 2 := {}

def layerBytes (layer : Layer) : Bytes :=
  encodeLE 8 layer.inputs ++ encodeLE 8 layer.logInputs ++
    streamBytes 0 layer.quadratic ++ streamBytes 1 layer.linear ++ streamBytes 2 layer.constant

/-- Each expanded delta is determined by its token, segment and dictionary
index. Reader validation requires every lookup to succeed. -/
def expand {arity : ℕ} (s : Stream arity) : Option (List (Record arity)) := do
  let segments ← s.tokens.mapM fun token => s.segments[token.val]?
  segments.flatten.mapM fun index => s.deltas[index.val]?

end LfzkV2.Current.SegmentedCircuit
