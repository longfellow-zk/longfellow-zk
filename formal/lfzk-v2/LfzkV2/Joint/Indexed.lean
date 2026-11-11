import LfzkV2.Joint.Backend
import Bcs.Indexed
import Merkle.Indexed.Extraction

/-! Indexed authentication uses the same tuple of columns as the algebraic
backend. Recovering each column from the fixed query cut avoids requiring a
complete Merkle tree when only the opened columns need to agree. -/
noncomputable section
namespace LfzkV2.Joint.Family
open Merkle.Indexed

variable {k s n t : ℕ} (G : Joint.Family k s n t)
variable {Salt D Enc : Type} [DecidableEq D] [Inhabited G.Leaf]
variable {codec : Codec Salt G.Leaf D Enc} (dec : RoleDecoders codec)

def indexedOracle (root : D) (trace : List (Enc × D)) : G.Oracle :=
  G.columnsEquiv.symm (messages dec trace root n)

theorem indexedOracle_columns (root : D) (trace : List (Enc × D)) :
    G.columnsEquiv (G.indexedOracle dec root trace) = messages dec trace root n :=
  G.columnsEquiv.apply_symm_apply _

/-- Once the actual indexed opening agrees with the fixed extracted columns,
all field checks transfer together. No full-tree extraction certificate is
needed, and the opening challenge never enters the extracted oracle. -/
theorem verify_of_indexedAgreement [Inhabited D] (ht : 0 < t)
    (scheme : Scheme Salt G.Leaf D Enc) (statement : G.Statement) (root : D)
    (trace : List (Enc × D)) (coin : G.Coin) (response : G.Response)
    (query : LigeroFamily.QuerySet n t) (claim : Merkle.MH.OpeningClaim n Salt G.Leaf D)
    (agree : ∀ i ∈ claim.I, messages dec trace root n i = claim.a i)
    (accepted : (G.compiler ht).AcceptsIndexed scheme statement root coin response query claim) :
    G.Verify statement (G.indexedOracle dec root trace) coin response query := by
  apply (G.compiler_verify ht statement _ coin response query).mp
  apply (G.compiler ht).verify_of_acceptsIndexed scheme statement root coin response query claim
    (G.indexedOracle dec root trace) ?_ accepted
  simpa only [compiler,indexedOracle_columns] using agree

end LfzkV2.Joint.Family
