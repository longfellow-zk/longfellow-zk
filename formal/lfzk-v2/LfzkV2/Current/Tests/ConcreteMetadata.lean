import Mathlib.Algebra.Field.ZMod
import LfzkV2.Current.ConcreteMetadataReadback
import Mathlib.Tactic.NormNum.NatLog

namespace LfzkV2.Current.ConcreteMetadata.Tests

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
open SumcheckV2 Layered MetadataIdentifiers Adapter.Circuit
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

-- Exact current adapter dimensions: ten product reductions, plus its final
-- zero-output layer and its mux leaves. This is independent of challenges.
example : (reductions (F := ZMod 2) (plan 1024 10 (by decide) (by decide))).length = 10 := by
  repeat' (rw [plan]; norm_num only [half, Nat.reduceEqDiff, Nat.reduceAdd, Nat.reduceDiv, and_false, false_and, and_true, true_and, dite_false, dite_true]; simp only [reductions,List.length_append,List.length_singleton])
  change (reductions (F := ZMod 2) (plan 1 1 (by decide) (by decide))).length+10 = 10
  rw [plan]
  rfl

-- Odd carries retain their own stream position; the pair tree is not padded
-- with fictitious multiplications. The second tree follows the first.
example : (pairLayer (F := ZMod 2) 3 1).terms =
    [.quadratic 0 0 1 1, .linear 1 2 1, .linear 2 3 1,
     .quadratic 3 4 5 1, .linear 4 6 1, .linear 5 7 1] := by
  have rows : pairRows (F := ZMod 2) 3 1 =
      ![[.quadratic () (0,Sum.inl 0) (0,Sum.inl 1) 1],
        [.linear () (0,Sum.inl 2) 1],[.linear () (0,Sum.inr 0) 1],
        [.quadratic () (1,Sum.inl 0) (1,Sum.inl 1) 1],
        [.linear () (1,Sum.inl 2) 1],[.linear () (1,Sum.inr 0) 1]] := by
    funext i
    change Fin 6 at i
    fin_cases i
    · change pairRow (fun j : Fin 3 => ((0 : Fin 2),Sum.inl j)) ⟨0,by decide⟩ = _
      simp [pairRow]
    · change pairRow (fun j : Fin 3 => ((0 : Fin 2),Sum.inl j)) ⟨1,by decide⟩ = _
      simp [pairRow]
    · change pairRow (fun j : Fin 1 => ((0 : Fin 2),Sum.inr j)) ⟨0,by decide⟩ = _
      simp [pairRow]
    · change pairRow (fun j : Fin 3 => ((1 : Fin 2),Sum.inl j)) ⟨0,by decide⟩ = _
      simp [pairRow]
    · change pairRow (fun j : Fin 3 => ((1 : Fin 2),Sum.inl j)) ⟨1,by decide⟩ = _
      simp [pairRow]
    · change pairRow (fun j : Fin 1 => ((1 : Fin 2),Sum.inr j)) ⟨0,by decide⟩ = _
      simp [pairRow]
  change ((List.ofFn fun i : Fin 6 => i).flatMap fun i => (pairRows (F := ZMod 2) 3 1 i).map
    (Term.map (fun _ => i) id)).map (Term.map Fin.val (fun wire => (wireIndex 3 1 wire).val)) = _
  rw [rows]
  simp only [wireIndex,List.ofFn_succ,finProdFinEquiv,finSumFinEquiv]
  rfl

-- LFC3 identity retains duplicate linear records even when their sum is
-- zero. The masked quotient bit changes only its constant record.
example : (stream (leafRows (F := ZMod 2) (fun _ : Fin 1 => 10)
      (fun t (_ : Fin 1) => 11+t.val) (fun _ _ => 1) 1 (fun t _ => t = 1))).map
      (Term.map Fin.val id) =
    [.linear 0 10 1, .linear 0 10 1, .constant 0 1,
     .linear 1 11 1, .linear 1 11 1, .constant 1 1,
     .linear 2 10 1, .linear 2 10 1, .constant 2 1,
     .linear 3 12 1, .linear 3 12 1, .constant 3 1] := by
  simp [stream,leafRows,wireIndex,Term.map,List.ofFn_succ,finProdFinEquiv,finSumFinEquiv,Equiv.trans,Equiv.prodCongr,Fin.divNat,Fin.modNat,Fin.addCases,quotientPower,Equiv.coe_fn_mk]

-- Stored records use 32-bit words; the stream tag is one byte and array
-- counts are 64-bit words. Segment lengths, indices and tokens follow records.
example : SegmentedCircuit.streamBytes 0
    (SegmentedCircuit.fromTerms [![SegmentedCircuit.word 0,SegmentedCircuit.word 1,
      SegmentedCircuit.word 2,SegmentedCircuit.word 3]]) =
      TranscriptV2.Framing.encodeLE 1 0 ++
      [1,1,1,1].flatMap (TranscriptV2.Framing.encodeLE 8) ++
      [0,1,2,3,1,0,0].flatMap (TranscriptV2.Framing.encodeLE 4) := by decide

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

-- The template appends duplicate power/base values rather than interning them.
example : leafConstants (⟨13,
    [.linear 0 10 (1 : ZMod 2),.linear 0 10 1,.constant 0 1,
     .linear 1 11 1,.linear 1 11 1,.constant 1 1]⟩ : Layer (ZMod 2)) =
    [1,1,1,1] := by decide

-- A scalar row's target is the negative constant; duplicate coordinates add.
example : (Prime.Claim.fromRow
    (⟨3,[(Sum.inl (0 : Fin 1),(4 : ZMod 7)),(Sum.inl 0,5),
      (Sum.inr (0 : Fin 1),6)]⟩ : LinearRow (Fin 1 ⊕ Fin 1) (ZMod 7))).target = 4 := by decide
example : (Prime.Claim.fromRow
    (⟨3,[(Sum.inl (0 : Fin 1),(4 : ZMod 7)),(Sum.inl 0,5),
      (Sum.inr (0 : Fin 1),6)]⟩ : LinearRow (Fin 1 ⊕ Fin 1) (ZMod 7))).sharedWeights 0 = 2 := by
  norm_num [Prime.Claim.fromRow,Prime.coefficients,Sum.inr_ne_inl]
  decide

example {g : Geometry} {fields : Fields} {Advice C : Type} {index : ℕ}
    (history : Prefix g fields Advice C index) : history.answer index = history.fallback :=
  history.answer_current

end LfzkV2.Current.ConcreteMetadata.Tests
