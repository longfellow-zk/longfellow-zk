import LfzkV2.Current.CanonicalRuntime
import LfzkV2.Current.ConcreteSetup
import LfzkV2.Current.MerkleWireCodec

/-! Public constructors shared by canonical execution and its simulation.
The field maps, indexed backend participants and Merkle codec are independent
of the simulator's acceptance and distribution proofs. Keeping them here
lets public setup use those constructors without importing those proofs. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.CompleteCanonicalVerifier
open Application ApplicationSetup RecursivePolygero Merkle Merkle.MH LigeroFamily
open scoped Classical
set_option maxRecDepth 4096

variable {g : Geometry} {fields : Fields} {Advice C B : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable [∀ side, Fintype (fields side)] [Fintype Advice]
variable {shared maskBits adviceBits : ℕ}
variable (binary : BinaryPublic B shared maskBits adviceBits)
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable (prime : PrimePublic N shared)
variable (binaryNodes : Fin 2792 ↪ B) (primeNodes : Fin 2792 ↪ N)
local notation "P" => ConcreteSetup.backend binaryNodes binary.cells
local notation "R" => ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (shape : WireBlocks.Shape g fields) (setup : FingerprintPrefix.Setup)
variable (cfg : RuntimeVerifier.Public (g := g) binary prime
  (ConcreteSetup.backend binaryNodes binary.cells)
  (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (fields := fields) (Advice := Advice)
  (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
  (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := Fin 2443 × Digest))

def basePublic := { cfg with bindSalt := MerkleWireCodec.bindSalt }

def publicConfig := CanonicalRuntime.wirePublic binary prime P R repr shape setup
  (basePublic binary prime binaryNodes primeNodes repr shape setup cfg)

def merkleCodec := MerkleWireCodec.codec
  (RuntimeVerifier.first binary prime P R (publicConfig binary prime binaryNodes primeNodes repr shape setup cfg)).participant
  (RuntimeVerifier.second binary prime P R (publicConfig binary prime binaryNodes primeNodes repr shape setup cfg)).participant
  repr cfg.binaryField cfg.primeField setup.jointContext (by decide)

instance leafInhabited : Inhabited (RuntimeVerifier.Family binary prime P R
    (publicConfig binary prime binaryNodes primeNodes repr shape setup cfg)).Leaf :=
  ⟨MerkleWireCodec.physicalLeafEquiv _ _ (fun _ => 0,fun _ => 0)⟩

omit [DecidableEq B] in
@[simp] theorem publicConfig_countBinary :
    (publicConfig binary prime binaryNodes primeNodes repr shape setup cfg).countBinary = cfg.countBinary := rfl

omit [DecidableEq B] in
@[simp] theorem publicConfig_countPrime :
    (publicConfig binary prime binaryNodes primeNodes repr shape setup cfg).countPrime = cfg.countPrime := rfl

omit [DecidableEq B] in
@[simp] theorem publicConfig_binaryField :
    (publicConfig binary prime binaryNodes primeNodes repr shape setup cfg).binaryField = cfg.binaryField := rfl

omit [DecidableEq B] in
@[simp] theorem publicConfig_primeField :
    (publicConfig binary prime binaryNodes primeNodes repr shape setup cfg).primeField = cfg.primeField := rfl

end LfzkV2.Current.ZeroKnowledge.CompleteCanonicalVerifier
