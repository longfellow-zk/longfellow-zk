import LfzkV2.Current.CanonicalRequest
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
variable {shared maskBits adviceBits : ℕ}
variable (binary : BinaryPublic B shared maskBits adviceBits)
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable (prime : PrimePublic N shared)
variable (binaryNodes : Fin 2792 ↪ B) (primeNodes : Fin 2792 ↪ N)
local notation "P" => ConcreteSetup.backend binaryNodes binary.cells
local notation "R" => ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)
variable (fmt : Format g fields Advice binary.nPublic)
variable (cfg : RuntimeVerifier.Public (g := g) binary prime
  (ConcreteSetup.backend binaryNodes binary.cells)
  (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (fields := fields) (Advice := Advice)
  (Base := fmt.Base)
  (Key := fmt.Key) (C := C) (Salt := Fin 2443 × MerkleNonce))

def basePublic := { cfg with bindSalt := MerkleWireCodec.bindSalt }

def publicConfig := CanonicalRuntime.wirePublic binary prime P R fmt
  (basePublic binary prime binaryNodes primeNodes fmt cfg)

instance leafInhabited : Inhabited (RuntimeVerifier.Family binary prime P R
    (publicConfig binary prime binaryNodes primeNodes fmt cfg)).Leaf :=
  ⟨MerkleWireCodec.physicalLeafEquiv _ _ (fun _ => 0,fun _ => 0)⟩

omit [DecidableEq B] in
@[simp] theorem publicConfig_countBinary :
    (publicConfig binary prime binaryNodes primeNodes fmt cfg).countBinary = cfg.countBinary := rfl

omit [DecidableEq B] in
@[simp] theorem publicConfig_countPrime :
    (publicConfig binary prime binaryNodes primeNodes fmt cfg).countPrime = cfg.countPrime := rfl

omit [DecidableEq B] in
@[simp] theorem publicConfig_binaryField :
    (publicConfig binary prime binaryNodes primeNodes fmt cfg).binaryField = cfg.binaryField := rfl

omit [DecidableEq B] in
@[simp] theorem publicConfig_primeField :
    (publicConfig binary prime binaryNodes primeNodes fmt cfg).primeField = cfg.primeField := rfl

end LfzkV2.Current.ZeroKnowledge.CompleteCanonicalVerifier
