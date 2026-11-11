import LfzkV2.Current.StrandSearch

/-! The commitment extractor uses the first query naming a public context.
Its cut retains only actual non-PRF hash queries. Reserving an entire PRF row
does not expose additional commitment inputs to this extractor. The Merkle
explanation and its probability bound remain separate obligations. -/
noncomputable section
namespace LfzkV2.Current.StrandCut
open Merkle.RandomOracle TranscriptV2 TranscriptV2.Strand TranscriptV2.StrandCoupling
open scoped Classical

variable {P T Key Out : Type}

/-- Every decoded query names its commitment context. Stopping at the
first such query also fixes the cut off all later answers in that context,
including the fingerprint answer used by witness selection. -/
def label (context : T → Key) : StrandSearch.Name P T → Option Key
  | .inl (_,some value) => some (context value)
  | _ => none

private def nodeEntry : StrandSearch.Name P T × Sample Digest Word → Option (P × Digest)
  | (.inl (raw,_),answer) => some (raw,answer.1)
  | (.inr _,_) => none

def trace (context : T → Key) {fuel : ℕ}
    (tree : Tree (StrandSearch.Name P T) (Sample Digest Word) Out fuel)
    (H : StrandSearch.Name P T → Sample Digest Word) (key : Key) : List (P × Digest) :=
  (beforeLabel (label context) (some key) tree H).filterMap nodeEntry

/-- Resampling any typed point leaves its context's extracted prefix
unchanged. This is the independence required by all local algebraic charges;
it is derived from the actual search tree, not supplied as a certificate. -/
theorem trace_off (context : T → Key) {fuel : ℕ}
    (tree : Tree (StrandSearch.Name P T) (Sample Digest Word) Out fuel)
    (H H' : StrandSearch.Name P T → Sample Digest Word) (raw : P) (value : T)
    (agreement : Bcs.TotalOracle.AgreeOff (.inl (raw,some value)) H H') :
    trace context tree H (context value) = trace context tree H' (context value) :=
  congrArg (List.filterMap nodeEntry)
    (beforeLabel_off (label context) tree (.inl (raw,some value)) H H' agreement)

/-- PRF samples' dummy digest coordinates never appear in the cut. Every
retained entry comes from a queried node in the stopped named execution. -/
theorem trace_source (context : T → Key) {fuel : ℕ}
    (tree : Tree (StrandSearch.Name P T) (Sample Digest Word) Out fuel)
    (H : StrandSearch.Name P T → Sample Digest Word) (key : Key)
    (raw : P) (digest : Digest) (member : (raw,digest) ∈ trace context tree H key) :
    ∃ logical row, ((.inl (raw,logical),(digest,row)) : StrandSearch.Name P T × Sample Digest Word) ∈
      beforeLabel (label context) (some key) tree H := by
  obtain ⟨⟨point,answer⟩,prefixMember,entry⟩ := List.mem_filterMap.mp member
  cases point with
  | inr _ => cases entry
  | inl point =>
      rcases point with ⟨point,logical⟩
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj entry)
      exact ⟨logical,answer.2,prefixMember⟩

/-- When applied to the coupled strand search, each cut entry is an
actual raw hash input with its actual answer. The final-cache agreement
is the existing coupling invariant, not an additional oracle assumption. -/
theorem trace_raw (schema : History.Codec T) (bytes : P → Framing.Bytes) (context : T → Key)
    {fuel : ℕ} (program : Tree (Point P PrfKey Word) Digest Out fuel)
    (H : StrandSearch.Name P T → Sample Digest Word) (G : Point P PrfKey Word → Digest)
    (agreement : ((StrandSearch.searchState schema bytes program Cache.empty []).run H).1.1.2.Matches G)
    (key : Key) (raw : P) (digest : Digest)
    (member : (raw,digest) ∈ trace context (StrandSearch.searchState schema bytes program Cache.empty []) H key) :
    (.inl raw,digest) ∈ (program.run G).2 := by
  obtain ⟨logical,row,source⟩ := trace_source context _ H key raw digest member
  rw [beforeLabel_eq_takeWhile] at source
  have source := (List.takeWhile_sublist _).subset source
  have queried := StrandSearch.searchState_node_queried schema bytes program Cache.empty []
    H G agreement raw logical (digest,row) source
  have answer := (StrandSearch.searchState_source schema bytes program Cache.empty [] H G agreement).2
    raw logical (digest,row) source
  obtain ⟨⟨point,value⟩,member,same⟩ := List.mem_map.mp queried
  change point = .inl raw at same
  subst point
  have actual := Tree.trace_sound program G (.inl raw,value) member
  change value = G (.inl raw) at actual
  rw [actual,answer] at member
  exact member

end LfzkV2.Current.StrandCut
