import LfzkV2.Current.StrandCommitment

namespace LfzkV2.Current.Tests.StrandCommitment
open TranscriptV2.Strand

-- PRF stream keys are not Merkle extraction targets.
example {P T Key : Type} (readChildren : P → Option (Digest × Digest))
    (context : T → Key) (root : Key → Digest) (parent : PrfKey) :
    StrandCommitment.claims readChildren context root (.inr parent) = ∅ := rfl

-- A recognized protocol input contributes only its root. The actual
-- decoder/domain theorem separately rules out Merkle children at this input.
example {P T Key : Type} (readChildren : P → Option (Digest × Digest))
    (context : T → Key) (root : Key → Digest) (raw : P) (value : T) :
    StrandCommitment.claims readChildren context root (.inl (raw,some value)) =
      {root (context value)} := rfl

/--
info: 'LfzkV2.Current.StrandCommitment.missing_cut_hit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms StrandCommitment.missing_cut_hit

#guard_msgs (drop info) in #check StrandCommitment.claims_card
end LfzkV2.Current.Tests.StrandCommitment
