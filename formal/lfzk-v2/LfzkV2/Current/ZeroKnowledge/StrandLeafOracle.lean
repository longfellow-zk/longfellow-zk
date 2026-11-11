import LfzkV2.Current.ZeroKnowledge.StrandGhostMerkleTree

/-! Finite leaf-oracle coordinates and nonce/label coins. This data layer is independent of the statistical hiding theorem. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.StrandGhostMerkle.Swap.Slice
open Merkle.RandomOracle
open scoped Classical

variable {Leaf Index Raw Digest Context : Type} {fuel : ℕ}
variable (encode : Leaf ↪ Raw) (outside : Raw → Digest)

def oracle (table : Leaf → Digest) : Raw → Digest := replace encode outside table

theorem oracle_at (table : Leaf → Digest) (leaf : Leaf) :
    oracle encode outside table (encode leaf) = table leaf := replace_at _ _ _ _

theorem oracle_injective : Function.Injective (oracle encode outside) := by
  intro first second same
  funext leaf
  simpa only [oracle_at] using congrFun same (encode leaf)


end LfzkV2.Current.ZeroKnowledge.StrandGhostMerkle.Swap.Slice

namespace LfzkV2.Current.ZeroKnowledge.StrandGhostMerkle.Probability
open Merkle.Indexed
variable {Salt Message Digest Raw : Type} {n : ℕ}
variable (codec : Codec (Fin n × Salt) Message Digest Raw) (dec : RoleDecoders codec)

def leafEmbedding : ((Fin n × Salt) × Message) ↪ Raw := ⟨codec.leafEnc,dec.inj.leaf⟩

abbrev Coins (n : ℕ) (Salt Raw Digest : Type) :=
  (Fin n → Salt) × ((Raw → Digest) × (Fin n → Digest))


end LfzkV2.Current.ZeroKnowledge.StrandGhostMerkle.Probability
