import Merkle.Indexed.Commit
import Bcs.TotalOracle

/-! A verifier's internal-node input depends only on descendants. The heap
index separates those descendant queries from the node being charged, even
when digest outputs coincide. Frontier labels are fixed proof data. -/
namespace Merkle.Indexed
open Bcs.TotalOracle

variable {Salt M D Enc : Type} [Inhabited D]
variable (codec : Codec Salt M D Enc)
variable (n : ℕ) (I : Finset (Fin n)) (a : Fin n → M) (proof : Opening n I Salt D)

/-- The concrete byte codec proves these laws from its domain tags and
bounded heap indices. They are input-encoding properties, not collision
assumptions about the hash output. -/
structure Separated : Prop where
  leaf_node : ∀ index saltMessage children,
    codec.leafEnc saltMessage ≠ codec.nodeEnc index children
  nodes : ∀ first second, 0 < first → first < n → 0 < second → second < n →
    first ≠ second → ∀ left right, codec.nodeEnc first left ≠ codec.nodeEnc second right

theorem checkValues_above_congr (H H' : Enc → D) (input : Enc) (cutoff : ℕ)
    (leaves : ∀ value, codec.leafEnc value ≠ input)
    (nodes : ∀ index, cutoff < index → index < n → ∀ children, codec.nodeEnc index children ≠ input)
    (agree : AgreeOff input H H') :
    ∀ vertex, cutoff < vertex →
      checkValues (codec.withOracle H) n I a proof vertex =
        checkValues (codec.withOracle H') n I a proof vertex := by
  intro vertex
  refine WellFounded.induction (measure (fun v : ℕ => 2*n-v)).wf vertex
    (C := fun v => cutoff < v → checkValues (codec.withOracle H) n I a proof v =
      checkValues (codec.withOracle H') n I a proof v) ?_
  intro v ih above
  conv_lhs => rw [checkValues]
  conv_rhs => rw [checkValues]
  split_ifs with leaf opened frontier frontier path
  · exact agree _ (leaves _)
  · rfl
  · rfl
  · rfl
  · have left := ih (2*v) (by change 2*n-2*v < 2*n-v; omega) (by omega)
    have right := ih (2*v+1) (by change 2*n-(2*v+1) < 2*n-v; omega) (by omega)
    change H (codec.nodeEnc v _) = H' (codec.nodeEnc v _)
    rw [left,right]
    exact agree _ (nodes v above path.2.1 _)
  · rfl

def nodeInput (H : Enc → D) (vertex : ℕ) : Enc :=
  codec.nodeEnc vertex
    (checkValues (codec.withOracle H) n I a proof (2*vertex),
      checkValues (codec.withOracle H) n I a proof (2*vertex+1))

theorem nodeInput_off (separated : Separated codec n) (H H' : Enc → D)
    (vertex : ℕ) (positive : 0 < vertex) (internal : vertex < n)
    (agree : AgreeOff (nodeInput codec n I a proof H vertex) H H') :
    nodeInput codec n I a proof H vertex = nodeInput codec n I a proof H' vertex := by
  have descendants := checkValues_above_congr codec n I a proof H H'
    (nodeInput codec n I a proof H vertex) vertex
    (fun value => separated.leaf_node vertex value _)
    (fun index above within children => separated.nodes index vertex
      (by omega) within positive internal (by omega) children _) agree
  unfold nodeInput
  rw [descendants (2*vertex) (by omega),descendants (2*vertex+1) (by omega)]

end Merkle.Indexed
