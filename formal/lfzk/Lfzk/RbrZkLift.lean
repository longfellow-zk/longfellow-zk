import Lfzk.RbrZkSplit

/-!
# Reuse of a Ligero query classifier at a larger extraction radius

The verifier's acceptance test and its old round-by-round classifier are
unchanged when the analysis adds lift candidates.  Only the no-satisfying-
candidate premise is strengthened.  This adapter transfers the classifier
whenever failure at the larger list implies failure at the old list.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.RbrZkSplit.ZkLigeroData

open Lfzk.RbrZkLongfellow

variable {C F X Q Msg Gpt : Type} [Field F]
variable {M ninp logw logc : ℕ}
variable {V : ZkCode C F X Q Msg Gpt M ninp logw logc}
variable {Small Large : Type}
variable {asgSmall : Small → LigeroAssignment ninp M F}
variable {asgLarge : Large → LigeroAssignment ninp M F}

/-- Keep the exact accepting-query predicate and its round-by-round
classifier while moving to a larger candidate list. -/
def changeCandidates
    (LD : ZkLigeroData C X Q Msg V asgSmall)
    (hno : ∀ sys, NoSat asgLarge sys → NoSat asgSmall sys) :
    ZkLigeroData C X Q Msg V asgLarge where
  LigDoomed := LD.LigDoomed
  accepting := LD.accepting
  escaping := LD.escaping
  hesc := by
    intro sys hf hn x hx
    exact LD.hesc sys hf (hno sys hn) x hx
  bq := LD.bq
  hbq := LD.hbq

end Lfzk.RbrZkSplit.ZkLigeroData
