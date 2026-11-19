import TranscriptV2.StrandVerifier
import TranscriptV2.StrandTrace

/-! Deferred-sampling transport for the raw strand verifier. The executable
verifier model is independent of this probability coupling. -/
namespace TranscriptV2.StrandVerifier
open Framing Strand Merkle.RandomOracle

variable {P C Out : Type} {rounds blocks : ℕ}
variable (history : P → History) (sample : P → Tree Word Digest (Option C) blocks) (fallback : C)
variable (model : Chain P Digest C Out rounds)

namespace Coupling
open StrandCoupling

private def key (point : OtherPoint) (digest : Digest) : PrfKey := nodeKey point.val digest

/-- Splitting byte addresses is a bijective change of query names. The
node hash and every actual PRF block remain the same oracle evaluations. -/
theorem split_readRound (point : P) :
    mapQueries rawPoint (readRound history sample fallback point) =
      .query (.inl ((history point).nodePoint)) fun digest =>
        mapQueries (fun counter => (.inr (((history point).id,digest),counter) : Point OtherPoint PrfKey Word))
          ((sample point).map fun value => (digest,value.getD fallback)) := by
  have node : rawPoint (history point).input.encode = .inl ((history point).nodePoint) :=
    rawPoint_bytes (.inl ((history point).nodePoint))
  change Tree.query (rawPoint (history point).input.encode) _ = _
  rw [node]
  apply congrArg (fun next : Digest → Tree (Point OtherPoint PrfKey Word) Digest (Digest × C) blocks =>
    Tree.query (.inl ((history point).nodePoint)) next)
  funext digest
  rw [mapQueries_map]
  change (mapQueries rawPoint (mapQueries (fun counter => (Input.prf (history point).id digest counter).encode) (sample point))).map _ = _
  rw [mapQueries_comp,← mapQueries_map]
  have addresses : rawPoint ∘ (fun counter => (Input.prf (history point).id digest counter).encode) =
      fun counter => (.inr (((history point).id,digest),counter) : Point OtherPoint PrfKey Word) := by
    funext counter
    simpa only [Function.comp_apply,rawBytes] using rawPoint_bytes (.inr (((history point).id,digest),counter))
  rw [addresses]

theorem round_length (point : P) (state : Cache OtherPoint PrfKey Digest Word)
    (H : SamplePoint OtherPoint PrfKey → Sample Digest Word) (reserved : state.Reserved key) :
    ((eagerState key (mapQueries rawPoint (readRound history sample fallback point)) state).run H).2.length ≤ 1 := by
  rw [split_readRound]
  simpa only [key,History.nodeKey] using
    eagerState_round_length key (history point).nodePoint
      (fun digest => (sample point).map fun value => (digest,value.getD fallback)) state H reserved

/-- All challenge-block reads within a boundary reuse the node's reserved
row. Thus the complete ordinary replay has at most `rounds` fresh samples,
irrespective of rejection counts and the size of the challenge vectors. -/
theorem replay_length (out : Out) (state : Cache OtherPoint PrfKey Digest Word)
    (H : SamplePoint OtherPoint PrfKey → Sample Digest Word) (reserved : state.Reserved key) :
    ((eagerState key (mapQueries rawPoint (replay history sample fallback model out)) state).run H).2.length ≤ rounds := by
  rw [replay,mapQueries_expand]
  have bound := eagerState_expand_length key
    (fun point => mapQueries rawPoint (readRound history sample fallback point))
    (round_length history sample fallback) (model.recompute out) state H reserved
  simpa only [Nat.one_mul] using bound

/-- Finalization adds one node read. Its PRF seal check is deliberately
outside this replay, and cannot supply a missing prover seal query. -/
theorem beforeSeal_length (out : Out) (state : Cache OtherPoint PrfKey Digest Word)
    (H : SamplePoint OtherPoint PrfKey → Sample Digest Word) (reserved : state.Reserved key) :
    ((eagerState key (mapQueries rawPoint (beforeSeal history sample fallback model out)) state).run H).2.length ≤ rounds+1 := by
  rw [beforeSeal,mapQueries_bind,eagerState_comp,Tree.run_bind,List.length_append]
  apply Nat.add_le_add (replay_length history sample fallback model out state H reserved)
  let cut := ((eagerState key (mapQueries rawPoint (replay history sample fallback model out)) state).run H).1
  let finalNode : Tree Bytes Digest (Out × model.State) 1 :=
    .query (history (model.input cut.1.2)).input.encode fun _ => .done cut.1
  change ((eagerState key (mapQueries rawPoint finalNode) cut.2).run H).2.length ≤ 1
  simpa only [Bcs.TotalOracle.queried,List.length_map] using
    Bcs.TotalOracle.queried_length_le (eagerState key (mapQueries rawPoint finalNode) cut.2) H

end Coupling

end TranscriptV2.StrandVerifier
