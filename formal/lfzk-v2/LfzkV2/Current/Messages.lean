import LfzkV2.Current.Schedule
import WitnessSelection.Algebra

/-! Message and ideal challenge shapes for the current schedule. Uniformity of
these samples is an ideal-XOF correspondence obligation, not a claim about a
particular finite seed or a replacement generator. All coordinates in one
`Samples` value are read from the same boundary answer, after its 32-byte link. -/
namespace LfzkV2.Current

abbrev Digest := Fin 32 → Fin 256

/-- Matches the v2 runtime's `NONCE_LEN`; SHA-256 digests remain 32 bytes. -/
def merkleNonceBytes : ℕ := 32
abbrev MerkleNonce := Fin merkleNonceBytes → Fin 256
abbrev Fields := Side → Type

abbrev Fingerprints (F : Fields) := (F .binary × F .binary) × (F .prime × F .prime)

abbrev Candidate (g : Geometry) (F : Fields) (side : Side) :=
  WitnessSelection.Candidate (F side) (Fin (g.cells side))

abbrev FingerprintCoins (g : Geometry) (F : Fields) :=
  WitnessSelection.Coins (F .binary) (Fin g.binaryCells) ×
    WitnessSelection.Coins (F .prime) (Fin g.primeCells)

structure BatchSamples (g : Geometry) (F : Fields) (side : Side) where
  affine : Fin (g.affineRows side) → F side
  polynomials : Fin (g.batchedRows side) → Fin (g.maskingDegree + 1) → F side

/-- Ordered columns sampled without replacement; both fields use this one
value. Treating their opening sets as independent would give the wrong bound. -/
abbrev OpeningSamples (g : Geometry) := Fin g.openings ↪ Fin g.columns

abbrev Samples (g : Geometry) (F : Fields) [∀ side, Zero (F side)] : Role → Type
  | .fingerprint => FingerprintCoins g F
  | .inputAssertions side entries => Fin ((entries.map (·.outputs)).sum) → F side
  | .assertions side _ entries fragments =>
      (Fin ((entries.map (·.outputs)).sum) → F side) ×
        (Fin ((fragments.map (·.quadraticAssertions)).sum +
          (fragments.map (·.linearAssertions)).sum) → F side)
  | .sumcheck side .. => F side
  | .terminal side .. => {x : F side // x ≠ 0}
  | .combine side _ entries => F side × (Fin ((entries.map (·.outputs)).sum) → F side)
  -- Pure-foreign storage only; absent from the mdoc schedule.
  | .rowBatching => Fin (g.prime.stages.length + 1) → F .prime
  | .rescaling => {x : F .prime // x ≠ 0}
  | .conversion => Fin 2 → {x : F .prime // x ≠ 0}
  | .packing => Fin g.packingDegree → F .binary
  | .batching => BatchSamples g F .binary × BatchSamples g F .prime
  | .opening => OpeningSamples g

structure LayerPayload (F : Type) (rounds : ℕ) where
  coefficients : Fin rounds → F × F
  cross : F
  claims : F × F

abbrev FrontendPayload (F : Type) (frontend : Frontend) :=
  (i : Fin frontend.stages.length) → LayerPayload F (frontend.stages.get i).rounds

abbrev PackingPayload (F : Type) (degree : ℕ) : Type :=
  if degree = 1 then Unit else (Fin degree → F) × F

structure Response (g : Geometry) (F : Type) where
  h : Fin (g.rowDimension + g.maskingDegree) → F
  z : Fin (2 * g.rowDimension) → F

structure FieldBody (g : Geometry) (F : Fields) (side : Side) where
  response : Response g (F side)
  rows : Fin (g.dataRows side + 3) → Fin g.openings → F side

/-- The complete logical proof body, including terminal authentication. The
codec fixes advice size/canonical padding and the Merkle frontier format; its
correspondence is separate from these logical types. Statement identifiers are
derived locally, so are absent from the body. The final seal is also separate. -/
structure Body (g : Geometry) (F : Fields) (Advice Authentication : Type) where
  commitment : Digest
  fingerprints : Fingerprints F
  mu : F .prime
  advice : Advice
  binary : FrontendPayload (F .binary) g.binary
  prime : FrontendPayload (F .prime) g.prime
  packing : PackingPayload (F .binary) g.packingDegree
  binaryBackend : FieldBody g F .binary
  primeBackend : FieldBody g F .prime
  authentication : Authentication

structure Proof (g : Geometry) (F : Fields) (Advice Authentication : Type) where
  body : Body g F Advice Authentication
  finalSeal : Digest

/-- The fresh payload absorbed inside a boundary, in addition to the earlier
bind-only actions, role metadata and counter. Batching binds source identifiers,
not prover-supplied sparse equations; the verifier derives the equations. -/
abbrev RoundPayload (g : Geometry) (F : Fields) : Role → Type
  | .sumcheck side .. => F side × F side
  | .terminal side .. => F side
  | .combine side .. => F side × F side
  | .packing => Fin g.packingDegree → F .binary
  | .batching => Digest × Digest
  | .opening => Response g (F .binary) × Response g (F .prime)
  | _ => Unit

end LfzkV2.Current
