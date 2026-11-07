import LfzkV2.Current.SHARouting

/-! Merkle verification consults SHA only on the leaf/node domains.
Its result is unchanged when all other coordinates are filled by the same
auxiliary function used for public identifiers. -/
noncomputable section
namespace LfzkV2.Current.SHAAuthentication
open Merkle Merkle.MH ZeroKnowledge
open scoped Classical

variable {Raw D Salt Leaf : Type} [Inhabited D]
variable (domain : Raw → Prop) (outside inside : Raw → D)
variable (codec : Codec Salt Leaf D Raw)
variable (leaves : ∀ value, domain (codec.leafEnc value))
variable (nodes : ∀ value, domain (codec.nodeEnc value))

include leaves nodes in
theorem checkValues (n : ℕ) (I : Finset (Fin n)) (values : Fin n → Leaf)
    (opening : Opening n I Salt D) (vertex : ℕ) :
    MH.checkValues (codec.withOracle (SHAOracle.merge domain outside inside)) n I values opening vertex =
      MH.checkValues (codec.withOracle inside) n I values opening vertex := by
  conv_lhs => rw [MH.checkValues]
  conv_rhs => rw [MH.checkValues]
  split_ifs with leaf opened frontier frontier path
  · exact SHAOracle.merge_inside domain outside inside _ (leaves _)
  · rfl
  · rfl
  · rfl
  · rw [checkValues n I values opening (2*vertex),checkValues n I values opening (2*vertex+1)]
    exact SHAOracle.merge_inside domain outside inside _ (nodes _)
  · rfl
termination_by 2*n-vertex
decreasing_by all_goals omega

include leaves nodes in
theorem accepts (n : ℕ) (root : D) (I : Finset (Fin n)) (values : Fin n → Leaf)
    (opening : Opening n I Salt D) :
    MH.Accepts (codec.withOracle (SHAOracle.merge domain outside inside)) n root I values opening ↔
      MH.Accepts (codec.withOracle inside) n root I values opening := by
  unfold MH.Accepts
  rw [checkValues domain outside inside codec leaves nodes]

end LfzkV2.Current.SHAAuthentication
