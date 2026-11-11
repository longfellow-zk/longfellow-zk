import LfzkV2.Current.StrandRecognition

namespace LfzkV2.Current.Tests.StrandSearch
open TranscriptV2 TranscriptV2.Strand TranscriptV2.StrandCoupling Merkle.RandomOracle
open scoped Classical

private def historySchema : History.Codec History := ⟨id,some,fun _ => rfl,fun _ _ h => Option.some.inj h.symm⟩
private def zeroDigest : Digest := fun _ => 0
private def oneDigest : Digest := fun _ => 1
private def rootBytes : Framing.Bytes := (Strand.Input.root []).encode
private def childBytes : Framing.Bytes := (Strand.Input.node 1 [zeroDigest] []).encode

private theorem root_ne_child : rootBytes ≠ childBytes := by
  intro equal
  have parsed := Strand.Input.encode_injective (a := .root []) (b := .node 1 [zeroDigest] [])
    trivial ⟨List.cons_ne_nil _ _,by change 1 < 2^32; decide⟩ equal
  cases parsed

private def earlyChild : Tree (Point Framing.Bytes Strand.PrfKey Word) Digest Digest 3 :=
  .query (.inl childBytes) fun _ => .query (.inl rootBytes) fun _ =>
    .query (.inl childBytes) fun answer => .done answer

private def answers : StrandSearch.Name Framing.Bytes History → Sample Digest Word
  | .inl (_,none) => (oneDigest,fun _ => zeroDigest)
  | _ => (zeroDigest,fun _ => zeroDigest)

-- The first child query lacks its parent and remains auxiliary. Resolving
-- the parent later must not relabel the stored answer or query it again.
example : ((StrandSearch.search historySchema id earlyChild).run answers).1 = oneDigest := by
  have rootParsed : Strand.Input.decode rootBytes = some (.root []) :=
    Strand.Input.decode_encode _ trivial
  have childParsed : Strand.Input.decode childBytes = some (.node 1 [zeroDigest] []) :=
    Strand.Input.decode_encode _ ⟨List.cons_ne_nil _ _,by change 1 < 2^32; decide⟩
  simp [StrandSearch.search,StrandSearch.searchState,earlyChild,eagerState,Cache.empty,Cache.node,
    Cache.stream,FreshOracle.relabel,StrandSearch.name,StrandSearch.decode,StrandSearch.advance,
    historySchema,unfoldNode,rootParsed,childParsed,unfoldInput,resolve,record,answers,
    StrandSearch.key,nodeKey,Input.id,History.id,History.depth,
    root_ne_child,Ne.symm root_ne_child,Tree.run_query,Tree.weaken]

-- Typed names are not speculative targets. Early stream queries are.
example {P T : Type} (bytes : P → TranscriptV2.Framing.Bytes) (point : P) (logical : T) :
    StrandSearch.claims bytes (.inl (point,some logical) : StrandSearch.Name P T) = ∅ := rfl

example {P T : Type} (bytes : P → TranscriptV2.Framing.Bytes) (id : Word) (digest : Digest) :
    StrandSearch.claims bytes (.inr (id,digest) : StrandSearch.Name P T) = {digest} := rfl

#guard_msgs (drop info) in #check StrandSearch.search_source
#guard_msgs (drop info) in #check StrandSearch.search_law
#guard_msgs (drop info) in #check StrandSearch.search_speculation_le
#guard_msgs (drop info) in #check StrandSearch.replay_law
#guard_msgs (drop info) in #check StrandPath.path_queries
#guard_msgs (drop info) in #check StrandRecognition.path_recognized

/--
info: 'LfzkV2.Current.StrandSearch.search_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms StrandSearch.search_uniform

/--
info: 'LfzkV2.Current.StrandSearch.search_charges_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms StrandSearch.search_charges_le

/--
info: 'LfzkV2.Current.StrandSearch.replay_law' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms StrandSearch.replay_law

/--
info: 'LfzkV2.Current.StrandSearch.node_stream' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms StrandSearch.node_stream

/--
info: 'LfzkV2.Current.StrandPath.path_queries' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms StrandPath.path_queries

/--
info: 'LfzkV2.Current.StrandRecognition.path_recognized' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms StrandRecognition.path_recognized

#guard_msgs (drop info) in #check StrandRecognition.path_or_charge

#guard_msgs (drop info) in #check DigestProjection.Replay.guess_split
#guard_msgs (drop info) in #check DigestProjection.Replay.guess_ratio_le

end LfzkV2.Current.Tests.StrandSearch
