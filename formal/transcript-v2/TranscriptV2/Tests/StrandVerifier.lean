import TranscriptV2.StrandVerifierCoupling

namespace TranscriptV2.Tests.StrandVerifier
open Strand Merkle.RandomOracle

private def pairSampler : Tree Word Digest (Option (Digest × Digest)) 2 :=
  .query 0 fun first => .query 1 fun second => .done (some (first,second))

-- Both values come from one round's stream. There is no node hash between
-- them, and the complete raw trace is retained by the verifier model.
example (id : Word) (parent : Digest) (G : Strand.Oracle) :
    (TranscriptV2.StrandVerifier.stream id parent pairSampler).run G =
      (some (G (Input.prf id parent 0).encode,G (Input.prf id parent 1).encode),
        [((Input.prf id parent 0).encode,G (Input.prf id parent 0).encode),
         ((Input.prf id parent 1).encode,G (Input.prf id parent 1).encode)]) := rfl

example (reader : Reader) (count : ℕ) (G : Strand.Oracle) (raw : Framing.Bytes) (answer : Digest)
    (member : (raw,answer) ∈ ((Reader.read count reader).run G).2) :
    ∃ counter, raw = (Input.prf reader.prf.id reader.prf.parent counter).encode :=
  (Reader.read_key_and_queries count reader G).2 raw answer member

private def model : StrandSealCharging.Model Bool Bool Bool where
  node _ := false
  prf _ _ := true
  provided := id
  domains _ _ := Bool.false_ne_true

private def partialReplay (provided : Bool) : Tree Bool Bool Bool 1 :=
  .query false fun _ => .done provided

-- Verifier reconstruction of the final node cannot replace the prover's
-- missing seal query. With an empty search, acceptance is still a guess.
example (provided : Bool) (G : Bool → Bool) :
    StrandSealCharging.Guess model ((.done provided : Tree Bool Bool Bool 0).bind partialReplay) G ↔
      G true = provided := by
  simp [StrandSealCharging.Guess,StrandSealCharging.bad,StrandSealCharging.Model.point,
    model,partialReplay,Tree.bind,Tree.weakenAdd,seen,Bcs.TotalOracle.queried]

/--
info: 'TranscriptV2.StrandVerifier.seal_fresh' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms TranscriptV2.StrandVerifier.seal_fresh

-- Splitting SHA addresses preserves even malformed non-PRF inputs and
-- every counter value; it is not a new source of oracle answers.
example (raw : Framing.Bytes) : rawBytes (rawPoint raw) = raw := rawBytes_point raw

example (parent : PrfKey) (counter : Word) :
    rawPoint (rawBytes (.inr (parent,counter))) = .inr (parent,counter) :=
  rawPoint_bytes (.inr (parent,counter))

-- A two-value sampler extends one already reserved answer and adds no
-- coordinate to the coupled trace. Both actual raw blocks are retained.
example (state : StrandCoupling.Cache OtherPoint PrfKey Digest Word)
    (H : StrandCoupling.SamplePoint OtherPoint PrfKey → StrandCoupling.Sample Digest Word)
    (parent : PrfKey) (row : Word → Digest) (known : state.streams parent = some row) :
    ((StrandCoupling.eagerState (fun point digest => nodeKey point.val digest)
      (mapQueries (fun counter => (.inr (parent,counter) : StrandCoupling.Point OtherPoint PrfKey Word)) pairSampler)
      state).run H).2 = [] := by
  rw [StrandCoupling.eagerState_stream (fun point digest => nodeKey point.val digest) pairSampler state H parent row known]

/--
info: 'TranscriptV2.StrandVerifier.Coupling.beforeSeal_length' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms TranscriptV2.StrandVerifier.Coupling.beforeSeal_length

/--
info: 'TranscriptV2.StrandVerifier.beforeSeal_nonPrf_card' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms TranscriptV2.StrandVerifier.beforeSeal_nonPrf_card

end TranscriptV2.Tests.StrandVerifier
