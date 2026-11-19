import TranscriptV2.Memoize
import Bcs.TotalOracleCommit

/-! Partial evaluation of transcript queries against a total oracle, which
leaves the Merkle queries as the only external calls. -/
noncomputable section
namespace TranscriptV2.Memoize
open Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree Bcs.TotalOracle Finset
open Bcs.AdaptiveCommit Bcs.TotalOracleCommit
open scoped Classical

variable {QL DL P A Out Result : Type} [DecidableEq QL] [DecidableEq P]

/-- Partially evaluate transcript queries against their actual total oracle.
Only the original Merkle queries remain as externally visible calls. -/
def left (H : P → A) : {l r : ℕ} → TwoOracleTree QL DL P A Out l r → Tree QL DL Out l
  | _, _, .done out => .done out
  | _, _, .queryLeft q next => .query q fun answer => left H (next answer)
  | _, _, .queryRight q next => left H (next (H q))

end TranscriptV2.Memoize
