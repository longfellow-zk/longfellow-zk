import Mathlib
import Merkle

/-!
# Rust-shaped Merkle proof serialization and core refinement

The security proofs use exact dependent `Opening` values. This file describes
the list representation consumed on the wire and proves that exact canonical
serialization refines the core verifier. Byte-level SHA serialization remains
outside this layer.
-/

open Finset Nat Heap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Merkle

namespace MH

universe uSalt uMsg uDigest uEnc

variable {Salt : Type uSalt} {M : Type uMsg} {D : Type uDigest}
variable {Enc : Type uEnc}

/-- Observable validation classes corresponding to the relevant Rust
`MerkleError` branches. -/
inductive WireError where
  | emptyLeaves
  | leafIndexOutOfBounds
  | duplicateLeafIndex
  | invalidNonceLength
  | proofLengthMismatch
  | rootMismatch
  deriving DecidableEq, Repr

/-- On-wire proof fields from `MerkleProof { nonce, path }`. -/
structure WireProof (Salt : Type uSalt) (D : Type uDigest) where
  nonce : List Salt
  path : List D
  deriving DecidableEq

/-- Bounds-check natural-number indices before the typed core sees them. -/
def parseBounds (n : ℕ) : List ℕ → Except WireError (List (Fin n))
  | [] => .ok []
  | x :: xs =>
      if hx : x < n then
        match parseBounds n xs with
        | .error e => .error e
        | .ok rest => .ok (⟨x, hx⟩ :: rest)
      else
        .error .leafIndexOutOfBounds

/-- Empty, bounds, and duplicate validation performed by
`mark_paths_to_root`. -/
def parseIndices (n : ℕ) (xs : List ℕ) : Except WireError (List (Fin n)) :=
  if xs.isEmpty then
    .error .emptyLeaves
  else
    match parseBounds n xs with
    | .error e => .error e
    | .ok ys =>
        if ys.Nodup then .ok ys else .error .duplicateLeafIndex

@[simp] theorem parseBounds_map_val {n : ℕ} (idxs : List (Fin n)) :
    parseBounds n (idxs.map Fin.val) = .ok idxs := by
  induction idxs with
  | nil => rfl
  | cons i rest ih =>
    simp [parseBounds, i.isLt, ih]

theorem parseIndices_map_val {n : ℕ} (idxs : List (Fin n))
    (hne : idxs ≠ []) (hnodup : idxs.Nodup) :
    parseIndices n (idxs.map Fin.val) = .ok idxs := by
  simp [parseIndices, hne, hnodup]

/-- Serialize exact nonce coordinates in caller query order. -/
def serializeNonces {n : ℕ} (idxs : List (Fin n))
    (pf : Opening n idxs.toFinset Salt D) : List Salt :=
  idxs.attach.map (fun i =>
    pf.nonce ⟨i.val, by simpa using i.property⟩)

/-- Serialize frontier coordinates in the decreasing heap order used by both
`generate_proof` and `verify_proof`. -/
def serializePath {n : ℕ} (idxs : List (Fin n))
    (pf : Opening n idxs.toFinset Salt D) : List D :=
  (Heap.frontierList n idxs.toFinset).attach.map (fun v =>
    pf.frontierValue ⟨v.val, Heap.mem_frontierList.mp v.property⟩)

def serializeProof {n : ℕ} (idxs : List (Fin n))
    (pf : Opening n idxs.toFinset Salt D) : WireProof Salt D where
  nonce := serializeNonces idxs pf
  path := serializePath idxs pf

@[simp] theorem serializeNonces_length {n : ℕ} (idxs : List (Fin n))
    (pf : Opening n idxs.toFinset Salt D) :
    (serializeNonces idxs pf).length = idxs.length := by
  simp [serializeNonces]

@[simp] theorem serializePath_length {n : ℕ} (idxs : List (Fin n))
    (pf : Opening n idxs.toFinset Salt D) :
    (serializePath idxs pf).length = (Heap.frontier n idxs.toFinset).card := by
  simp [serializePath]

/-- Relational wire verifier. Existential parsing is intentional: it states
exactly that the supplied lists are the canonical serialization of a unique
consumed core proof, without adding irrelevant coordinates to `Opening`. -/
def WireAccepts (S : Scheme Salt M D Enc) [Inhabited D]
    (n : ℕ) (rt : D) (idxs : List (Fin n)) (a : Fin n → M)
    (wire : WireProof Salt D) : Prop :=
  idxs ≠ [] ∧ idxs.Nodup ∧
    ∃ pf : Opening n idxs.toFinset Salt D,
      serializeProof idxs pf = wire ∧
      Accepts S n rt idxs.toFinset a pf

/-- Honest exact openings, serialized in canonical order, pass the wire
verifier. -/
theorem mh_wire_completeness (S : Scheme Salt M D Enc) [Inhabited D]
    (n : ℕ) (idxs : List (Fin n))
    (hne : idxs ≠ []) (hnodup : idxs.Nodup)
    (nonce : Fin n → Salt) (m : Fin n → M) :
    WireAccepts S n
      (root S n nonce m) idxs m
      (serializeProof idxs
        (openCore S n idxs.toFinset nonce m)) := by
  refine ⟨hne, hnodup, openCore S n idxs.toFinset nonce m,
    rfl, ?_⟩
  apply mh_core_completeness
  simpa [Finset.nonempty_iff_ne_empty] using hne

/-- Natural-index entry point: index validation precedes the relational wire
verifier. -/
def WireAcceptsNat (S : Scheme Salt M D Enc) [Inhabited D]
    (n : ℕ) (rt : D) (idxs : List ℕ) (a : Fin n → M)
    (wire : WireProof Salt D) : Prop :=
  match parseIndices n idxs with
  | .error _ => False
  | .ok typed => WireAccepts S n rt typed a wire

/-- Honest typed indices remain complete through the natural-number bounds
and duplicate parser. -/
theorem mh_wire_nat_completeness (S : Scheme Salt M D Enc) [Inhabited D]
    (n : ℕ) (idxs : List (Fin n))
    (hne : idxs ≠ []) (hnodup : idxs.Nodup)
    (nonce : Fin n → Salt) (m : Fin n → M) :
    WireAcceptsNat S n
      (root S n nonce m) (idxs.map Fin.val) m
      (serializeProof idxs
        (openCore S n idxs.toFinset nonce m)) := by
  rw [WireAcceptsNat, parseIndices_map_val idxs hne hnodup]
  exact mh_wire_completeness S n idxs hne hnodup nonce m

end MH

end Merkle
