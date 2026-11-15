import LfzkV2.Current.CanonicalPrefix

/-! The parsed values of a chain of role packets. A canonical point is the
first packet's value and, after each boundary, either nothing (the query of
that boundary) or its actual link and the rest; after the last packet only the
complete body remains. `StrandQueryCodec` parses strand histories into these
values; `TaggedGrammar` proves them determined by the node grammar. -/
noncomputable section
namespace LfzkV2.Current.QueryCodec
open CanonicalPrefix

/-- One fixed role schema. Its data contains only writes bound at this
boundary; no later statement or other-field interpretation is encoded here. -/
structure Block where
  Data : Type
  codec : PrefixCodec Data
  domain : Domain

variable {Body : Type}

/-- A round may stop at its own query, or retain its actual answer link and
continue. After the last round only complete-body finalization is possible. -/
def Value (bodyCodec : WholeCodec Body) : List Block → Type
  | [] => {body // (bodyCodec.encode body).length ≤ maxLength}
  | block :: tail => block.Data × (Unit ⊕ (Digest × Value bodyCodec tail))

end LfzkV2.Current.QueryCodec
