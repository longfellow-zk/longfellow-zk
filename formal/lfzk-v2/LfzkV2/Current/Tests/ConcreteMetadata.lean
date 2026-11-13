import Mathlib.Algebra.Field.ZMod
import LfzkV2.Current.ConcreteMetadataReadback
import Mathlib.Tactic.NormNum.NatLog

namespace LfzkV2.Current.ConcreteMetadata.Tests

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
open SumcheckV2 Layered MetadataIdentifiers Adapter.Circuit
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

-- Exact current fragment dimensions for 1034 leaves per tree: the first
-- reduction reads the virtual leaves, nine more reductions follow, then the
-- final zero-output layer. This is independent of challenges.
example : (reductions (F := ZMod 2) (Adapter.ProductTree.plan (half 1034) (by decide))).length = 9 := by
  repeat' (rw [Adapter.ProductTree.plan]; norm_num only [half, Nat.reduceEqDiff, Nat.reduceAdd, Nat.reduceDiv, dite_false, dite_true]; simp only [reductions,List.length_append,List.length_singleton])
  rfl

-- Odd carries retain their own stream position; the pair tree is not padded
-- with fictitious multiplications. The second tree follows the first, and the
-- first reduction reads absolute input addresses from the virtual start.
example : (pairLayer (F := ZMod 2) 100 3 106).terms =
    [.quadratic 0 100 101 1, .linear 1 102 1, .quadratic 2 103 104 1, .linear 3 105 1] := by
  have rows : Adapter.ProductTree.pairRows (F := ZMod 2) 3 =
      ![[.quadratic () (0,0) (0,1) 1],[.linear () (0,2) 1],
        [.quadratic () (1,0) (1,1) 1],[.linear () (1,2) 1]] := by
    funext i
    change Fin 4 at i
    fin_cases i
    · change pairRow (fun j : Fin 3 => ((0 : Fin 2),j)) ⟨0,by decide⟩ = _
      simp [pairRow]
    · change pairRow (fun j : Fin 3 => ((0 : Fin 2),j)) ⟨1,by decide⟩ = _
      simp [pairRow]
    · change pairRow (fun j : Fin 3 => ((1 : Fin 2),j)) ⟨0,by decide⟩ = _
      simp [pairRow]
    · change pairRow (fun j : Fin 3 => ((1 : Fin 2),j)) ⟨1,by decide⟩ = _
      simp [pairRow]
  change ((List.ofFn fun i : Fin 4 => i).flatMap fun i => (Adapter.ProductTree.pairRows (F := ZMod 2) 3 i).map
    (Term.map (fun _ => i) id)).map (Term.map Fin.val (fun wire => 100+(Adapter.ProductTree.wireIndex 3 wire).val)) = _
  rw [rows]
  simp only [Adapter.ProductTree.wireIndex,List.ofFn_succ,finProdFinEquiv]
  rfl

-- The final layer: one product and the constant one per tree.
example : (finalLayer (F := ZMod 2)).terms =
    [.quadratic 0 0 1 1, .constant 0 1, .quadratic 1 2 3 1, .constant 1 1] := by
  simp [finalLayer,stream,Adapter.ProductTree.finalRows,Adapter.ProductTree.wireIndex,Term.map,
    List.ofFn_succ,finProdFinEquiv]

-- All identity integers use 64-bit words, independently of the stored
-- 32-bit representation. Segment lengths, indices and tokens follow records.
example : SegmentedCircuit.streamBytes 0
    (SegmentedCircuit.fromTerms [![SegmentedCircuit.word 0,SegmentedCircuit.word 1,
      SegmentedCircuit.word 2,SegmentedCircuit.word 3]]) =
      TranscriptV2.Framing.encodeLE 8 0 ++
      [1,1,1,1].flatMap (TranscriptV2.Framing.encodeLE 8) ++
      [0,1,2,3,1,0,0].flatMap (TranscriptV2.Framing.encodeLE 8) := by decide

-- Repeated deltas are interned; the coefficient index is absolute, not a delta.
example : (SegmentedCircuit.fromTerms
    [![SegmentedCircuit.word 3,SegmentedCircuit.word 4,SegmentedCircuit.word 9,SegmentedCircuit.word 2],
     ![SegmentedCircuit.word 6,SegmentedCircuit.word 8,SegmentedCircuit.word 18,SegmentedCircuit.word 2]]).segments =
      [[SegmentedCircuit.word 0,SegmentedCircuit.word 0]] := by decide

-- Coordinate differences wrap, while the final coefficient index stays absolute.
example : List.ofFn (SegmentedCircuit.delta
    ![SegmentedCircuit.word 3,SegmentedCircuit.word 7,SegmentedCircuit.word 9]
    ![SegmentedCircuit.word 1,SegmentedCircuit.word 2,SegmentedCircuit.word 4]) =
      [SegmentedCircuit.word (2^32-2),SegmentedCircuit.word (2^32-5),SegmentedCircuit.word 4] := by decide

-- The hash authenticates negative numerical deltas in signed 64-bit form.
example : SegmentedCircuit.coordinateValue (SegmentedCircuit.word (2^32-2)) = 2^64-2 := by decide

-- Tokens select complete segments, in order, including repeated dictionary entries.
example : (SegmentedCircuit.expand (⟨
    [![SegmentedCircuit.word 1,SegmentedCircuit.word 2],
      ![SegmentedCircuit.word 3,SegmentedCircuit.word 4]],
    [[SegmentedCircuit.word 0,SegmentedCircuit.word 1],[SegmentedCircuit.word 0]],
    [SegmentedCircuit.word 1,SegmentedCircuit.word 0]⟩ : SegmentedCircuit.Stream 2)).map
      (List.map List.ofFn) = some
        [[SegmentedCircuit.word 1,SegmentedCircuit.word 2],
         [SegmentedCircuit.word 1,SegmentedCircuit.word 2],
         [SegmentedCircuit.word 3,SegmentedCircuit.word 4]] := by decide

-- The split target is the input row's constant and its weights negate the
-- row coefficients (`split.rs::split_claim`); duplicate coordinates add.
example : (Prime.Claim.split []
    (⟨3,[(Sum.inl (0 : Fin 1),(4 : ZMod 7)),(Sum.inl 0,5),
      (Sum.inr (0 : Fin 1),6)]⟩ : LinearRow (Fin 1 ⊕ Fin 1) (ZMod 7))).target = 3 := by decide
example : (Prime.Claim.split []
    (⟨3,[(Sum.inl (0 : Fin 1),(4 : ZMod 7)),(Sum.inl 0,5),
      (Sum.inr (0 : Fin 1),6)]⟩ : LinearRow (Fin 1 ⊕ Fin 1) (ZMod 7))).sharedWeights 0 = 5 := by
  norm_num [Prime.Claim.split,Prime.coefficients,Sum.inr_ne_inl]
  decide

example {g : Geometry} {fields : Fields} {Advice C : Type} {index : ℕ}
    (history : Prefix g fields Advice C index) : history.answer index = history.fallback :=
  history.answer_current

end LfzkV2.Current.ConcreteMetadata.Tests
