import LfzkV2.Current.StrandCommitment
import LfzkV2.Current.MerkleWireCodec
import TranscriptV2.CompositionTransport
import LfzkV2.Current.StrandRuntime
import LfzkV2.Current.StrandReplay
import LfzkV2.Current.StrandMerkleDomains

/-! Merkle extraction uses the actual byte codec. A finite query address
is only a name for those bytes; it is not a second codec with fallback leaf
or node encodings. Mapping a stopped cut preserves its order and answers. -/
noncomputable section
namespace LfzkV2.Current.StrandMerkleRealization
open Merkle Merkle.Indexed Merkle.RandomOracle TranscriptV2 TranscriptV2.Strand
open Merkle.MH (CollisionFree)
open scoped Classical

variable {Raw T Key Out : Type}

def byteName (bytes : Raw → Framing.Bytes) : StrandSearch.Name Raw T → StrandSearch.Name Framing.Bytes T
  | .inl (raw,value) => .inl (bytes raw,value)
  | .inr digest => .inr digest

theorem byteName_injective (bytes : Raw → Framing.Bytes) (injective : Function.Injective bytes) :
    Function.Injective (byteName (T := T) bytes) := by
  intro first second same
  cases first with
  | inl first =>
      cases second with
      | inl second =>
          have equal := Prod.mk.inj (Sum.inl.inj same)
          exact congrArg Sum.inl (Prod.ext (injective equal.1) equal.2)
      | inr _ => cases same
  | inr _ =>
      cases second with
      | inl _ => cases same
      | inr _ => exact congrArg Sum.inr (Sum.inr.inj same)

/-- Reading child labels commutes with renaming the finite raw addresses. -/
theorem claims_bytes (readChildren : Framing.Bytes → Option (Digest × Digest))
    (bytes : Raw → Framing.Bytes) (context : T → Key) (root : Key → Digest) :
    StrandCommitment.claims readChildren context root ∘ byteName bytes =
      StrandCommitment.claims (readChildren ∘ bytes) context root := by
  funext point
  cases point with
  | inr _ => rfl
  | inl point =>
      rcases point with ⟨raw,value⟩
      cases value <;> rfl

/-- The original byte decoder receives precisely the extractor's actual
stopped cut. Renaming query addresses adds neither a new boundary nor a new
hash call and does not change which context query stops extraction. -/
theorem trace_map (bytes : Raw → Framing.Bytes) (context : T → Key) {fuel : ℕ}
    (tree : Tree (StrandSearch.Name Raw T) (StrandCoupling.Sample Digest Word) Out fuel)
    (H : StrandSearch.Name Framing.Bytes T → StrandCoupling.Sample Digest Word) (key : Key) :
    StrandCut.trace context (mapQueries (byteName bytes) tree) H key =
      (StrandCut.trace context tree (H ∘ byteName bytes) key).map (fun qa => (bytes qa.1,qa.2)) := by
  induction tree with
  | done _ => rfl
  | query point next ih =>
      cases point with
      | inr digest =>
          simp only [StrandCut.trace,mapQueries,beforeLabel,StrandCut.label,byteName,
            reduceCtorEq,if_false,Function.comp_apply]
          change StrandCut.trace context (mapQueries (byteName bytes) (next (H (.inr digest)))) H key =
            (StrandCut.trace context (next (H (.inr digest))) (H ∘ byteName bytes) key).map
              (fun qa => (bytes qa.1,qa.2))
          exact ih (H (.inr digest))
      | inl point =>
          rcases point with ⟨raw,value⟩
          cases value with
          | none =>
              simp only [StrandCut.trace,mapQueries,beforeLabel,StrandCut.label,byteName,
                reduceCtorEq,if_false,Function.comp_apply]
              change (bytes raw,(H (.inl (bytes raw,none))).1) :: _ =
                (bytes raw,(H (.inl (bytes raw,none))).1) :: _
              exact congrArg (List.cons _) (ih (H (.inl (bytes raw,none))))
          | some value =>
              by_cases stop : context value = key
              · simp [StrandCut.trace,mapQueries,beforeLabel,StrandCut.label,byteName,stop]
              · simp only [StrandCut.trace,mapQueries,beforeLabel,StrandCut.label,byteName,
                  Option.some.injEq,stop,if_false,Function.comp_apply]
                change (bytes raw,(H (.inl (bytes raw,some value))).1) :: _ =
                  (bytes raw,(H (.inl (bytes raw,some value))).1) :: _
                exact congrArg (List.cons _) (ih (H (.inl (bytes raw,some value))))

/-- Extend only the names used by this deterministic renamed execution.
The arbitrary values elsewhere are not additional oracle samples. -/
def byteOracle (bytes : Raw → Framing.Bytes)
    (H : StrandSearch.Name Raw T → StrandCoupling.Sample Digest Word) :
    StrandSearch.Name Framing.Bytes T → StrandCoupling.Sample Digest Word :=
  Function.extend (byteName bytes) H (fun _ => (0,fun _ => 0))

theorem byteOracle_pullback (bytes : Raw → Framing.Bytes) (injective : Function.Injective bytes)
    (H : StrandSearch.Name Raw T → StrandCoupling.Sample Digest Word) :
    byteOracle bytes H ∘ byteName bytes = H := by
  funext point
  exact (byteName_injective bytes injective).extend_apply H (fun _ => (0,fun _ => 0)) point

theorem trace_bytes (bytes : Raw → Framing.Bytes) (injective : Function.Injective bytes)
    (context : T → Key) {fuel : ℕ}
    (tree : Tree (StrandSearch.Name Raw T) (StrandCoupling.Sample Digest Word) Out fuel)
    (H : StrandSearch.Name Raw T → StrandCoupling.Sample Digest Word) (key : Key) :
    StrandCut.trace context (mapQueries (byteName bytes) tree) (byteOracle bytes H) key =
      (StrandCut.trace context tree H key).map (fun qa => (bytes qa.1,qa.2)) := by
  rw [trace_map,byteOracle_pullback bytes injective]

/-- A stopped commitment cut inherits collision freedom from the actual
raw hash queries that supplied its answers. No decoder or extraction
certificate is needed: every retained entry has a named trace source. -/
theorem mapped_cut_collision_free (bytes : Raw → Framing.Bytes) (context : T → Key)
    {fuel : ℕ}
    (tree : Tree (StrandSearch.Name Raw T) (StrandCoupling.Sample Digest Word) Out fuel)
    (H : StrandSearch.Name Raw T → StrandCoupling.Sample Digest Word)
    (SHA : Framing.Bytes → Digest) (scope : Framing.Bytes → Prop) (key : Key)
    (sound : ∀ raw logical answer, ((.inl (raw,logical),answer) : StrandSearch.Name Raw T × _) ∈
      (tree.run H).2 → answer.1 = SHA (bytes raw))
    (covered : ∀ raw logical answer, ((.inl (raw,logical),answer) : StrandSearch.Name Raw T × _) ∈
      (tree.run H).2 → scope (bytes raw))
    (free : ∀ first second, scope first → scope second → SHA first = SHA second → first = second) :
    CollisionFree ((StrandCut.trace context tree H key).map (fun qa => (bytes qa.1,qa.2))) := by
  intro first firstMember second secondMember same
  obtain ⟨⟨firstRaw,firstDigest⟩,firstSource,rfl⟩ := List.mem_map.mp firstMember
  obtain ⟨⟨secondRaw,secondDigest⟩,secondSource,rfl⟩ := List.mem_map.mp secondMember
  obtain ⟨firstLogical,firstRow,firstSource⟩ :=
    StrandCut.trace_source context tree H key firstRaw firstDigest firstSource
  obtain ⟨secondLogical,secondRow,secondSource⟩ :=
    StrandCut.trace_source context tree H key secondRaw secondDigest secondSource
  rw [beforeLabel_eq_takeWhile] at firstSource secondSource
  have firstMember := (List.takeWhile_sublist _).subset firstSource
  have secondMember := (List.takeWhile_sublist _).subset secondSource
  exact free _ _ (covered _ _ _ firstMember) (covered _ _ _ secondMember)
    ((sound _ _ _ firstMember).symm.trans (same.trans (sound _ _ _ secondMember)))

section QueryTransport
variable {P Q A D Output : Type} [DecidableEq P] [DecidableEq Q] [DecidableEq D]
variable (encode : P → Q) (injective : Function.Injective encode)

include injective in
/-- Genuine root/child targets are unchanged by an injective renaming of
query addresses. This is a deterministic identity, not a new hash assumption. -/
theorem guess_map {Challenge : Type} {fuel : ℕ} (claims : Q → Finset D)
    (tree : Tree P (D × Challenge) Output fuel) (H : Q → D × Challenge) :
    DigestProjection.Guess claims (mapQueries encode tree) H ↔
      DigestProjection.Guess (claims ∘ encode) tree (H ∘ encode) := by
  constructor
  · rintro ⟨point,member,hit⟩
    rw [TranscriptV2.seen_mapQueries] at member
    obtain ⟨raw,present,rfl⟩ := Finset.mem_image.mp member
    refine ⟨raw,present,?_⟩
    simpa only [Composition.targets_mapQueries encode injective,Function.comp_apply] using hit
  · rintro ⟨raw,present,hit⟩
    refine ⟨encode raw,?_,?_⟩
    · rw [TranscriptV2.seen_mapQueries]
      exact Finset.mem_image.mpr ⟨raw,present,rfl⟩
    · simpa only [Composition.targets_mapQueries encode injective,Function.comp_apply] using hit

end QueryTransport

/-- A logical name recovered by the actual online decoder encodes a
strand input. Its bytes therefore cannot also contribute Merkle children.
This discharges the root/children exclusivity premise of target charging. -/
theorem ordinary_no_children [DecidableEq Raw]
    (schema : History.Codec T) (bytes : Raw → Framing.Bytes) {fuel : ℕ}
    (program : Tree (StrandCoupling.Point Raw PrfKey Word) Digest Out fuel)
    (H : StrandSearch.Name Raw T → StrandCoupling.Sample Digest Word)
    (raw : Raw) (value : T) (answer : StrandCoupling.Sample Digest Word)
    (member : ((.inl (raw,some value),answer) : StrandSearch.Name Raw T × _) ∈
      ((StrandReplay.search schema bytes program).run H).2) :
    MerkleWireCodec.nodeChildren (bytes raw) = none := by
  have named : FreshOracle.NamedTrace (StrandSearch.name schema bytes)
      (StrandSearch.advance bytes) StrandSearch.erase []
        ((StrandReplay.search schema bytes program).run H).2 := by
    simpa only [StrandReplay.search,StrandSearch.search,Tree.run_map] using
      StrandSearch.search_trace schema bytes (recordTrace program) H
  obtain ⟨first,rest,same⟩ := List.append_of_mem member
  have split := same ▸ named
  have decoded : StrandSearch.decode schema bytes
      (first.foldl (fun past qa => StrandSearch.advance bytes past (StrandSearch.erase qa.1) qa.2) []) raw =
      some value := (Prod.mk.inj (Sum.inl.inj split.name_after)).2
  rw [← StrandSearch.decode_erases schema bytes _ raw value decoded]
  exact StrandMerkleDomains.nodeChildren_input _

section Receiving
variable {Leaf Salt Point Challenge : Type} {valid : Point → Prop}
variable [DecidableEq Raw] [Fintype Raw] [Fintype T]
variable [Fintype Challenge] [Nonempty Challenge]
variable (codec : Codec Salt Leaf Digest Framing.Bytes)
variable (readChildren : Framing.Bytes → Option (Digest × Digest))
variable (bytes : Raw → Framing.Bytes) (context : T → Key) (root : Key → Digest)

/-- A receiving input is an actual Merkle leaf or internal-node preimage.
It need not be used by the eventual verifier; selecting that future subset
would destroy the stopped-prefix averaging argument. PRF addresses are absent. -/
def receives : StrandSearch.Name Raw T → Prop
  | .inl (raw,_) => (∃ leaf, bytes raw = codec.leafEnc leaf) ∨
      (∃ index children, bytes raw = codec.nodeEnc index children)
  | .inr _ => False

omit [DecidableEq Raw] [Fintype Raw] [Fintype T] in
/-- Canonical typed inputs and Merkle receiving inputs are disjoint.
This is a byte-codec fact, not a claim that all non-PRF inputs are auxiliary. -/
theorem receives_auxiliary
    (names : ByteOracleTransport.Codec Point (StrandSearch.Name Raw T) valid)
    (disjoint : ∀ point, ¬receives codec bytes (names.encode point))
    (raw : StrandSearch.Name Raw T) (receiving : receives codec bytes raw) :
    names.decode raw = none := by
  cases found : names.decode raw with
  | none => rfl
  | some point =>
      exact False.elim (disjoint point ((names.encode_decode raw point found).symm ▸ receiving))

omit [DecidableEq Raw] [Fintype Raw] [Fintype T] in
/-- Receiving inputs occupy the auxiliary branch of the same injective
query tag used for ordinary algebraic charges. -/
theorem receives_tag
    (names : ByteOracleTransport.Codec Point (StrandSearch.Name Raw T) valid)
    (disjoint : ∀ point, ¬receives codec bytes (names.encode point))
    (raw : StrandSearch.Name Raw T) (receiving : receives codec bytes raw) :
    names.tag raw = .inr raw := by
  simp only [ByteOracleTransport.Codec.tag,receives_auxiliary codec bytes names disjoint raw receiving]

/-- Original-search receiving hits cost at most `2Q/M` per auxiliary slot.
The mean is taken in the original joint digest/row experiment, with no
conditioning on successful sampling, acceptance, or eventual opening use. -/
theorem receiving_sum_le {fuel Q : ℕ}
    (names : ByteOracleTransport.Codec Point (StrandSearch.Name Raw T) valid)
    (disjoint : ∀ point, ¬receives codec bytes (names.encode point))
    (tree : Tree (StrandSearch.Name Raw T) (Digest × Challenge) Out fuel)
    (queries : ∀ H, (seen tree H).card ≤ Q) :
    (∑ H : StrandSearch.Name Raw T → Digest × Challenge,
      DigestProjection.receivingCharge (receives codec bytes)
        (StrandCommitment.claims readChildren context root ∘ byteName bytes) tree H) ≤
      ∑ H : StrandSearch.Name Raw T → Digest × Challenge, ∑ p ∈ seen tree H,
        if names.decode p = none then (Q*2 : ℚ)/Fintype.card Digest else 0 := by
  have auxiliary (p : StrandSearch.Name Raw T) (hit : receives codec bytes p) : names.decode p = none :=
    receives_auxiliary codec bytes names disjoint p hit
  have arity (p : StrandSearch.Name Raw T) :
      ((StrandCommitment.claims readChildren context root ∘ byteName bytes) p).card ≤ 2 :=
    StrandCommitment.claims_card readChildren context root (byteName bytes p)
  have bound := DigestProjection.receiving_sum_le (P := StrandSearch.Name Raw T) (D := Digest)
    (C := Challenge) (Q := Q) (arity := 2) (receives codec bytes)
    (fun p => names.decode p = none) auxiliary
    (StrandCommitment.claims readChildren context root ∘ byteName bytes) tree queries arity
  apply bound.trans_eq
  apply Finset.sum_congr rfl
  intro H _
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> rfl

end Receiving

section WireDomains
variable {k s n t : ℕ} (P R : Joint.Participant k s n t)
variable {fields : Fields} {Advice : Type}
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (binary : fields .binary ≃ P.Carrier) (prime : fields .prime ≃ R.Carrier)
variable (context : Digest) (columnsFit : n ≤ 2^64)

/-- A Merkle input cannot plant a speculative strand parent or PRF key.
This is disjointness of literal input domains, not an oracle-output claim. -/
theorem receiving_claims_empty (bytes : Raw → Framing.Bytes) (point : StrandSearch.Name Raw T)
    (receiving : receives (MerkleWireCodec.codec P R repr binary prime context columnsFit) bytes point) :
    StrandSearch.claims bytes point = ∅ := by
  cases point with
  | inr _ => exact False.elim receiving
  | inl point =>
      rcases point with ⟨raw,value⟩
      have rejected : Strand.Input.decode (bytes raw) = none := by
        cases found : Strand.Input.decode (bytes raw) with
        | none => rfl
        | some input =>
            have same := (Strand.Input.decode_sound (bytes raw) input found).2
            exfalso
            rcases receiving with ⟨leaf,encoded⟩ | ⟨index,children,encoded⟩
            · exact StrandMerkleDomains.input_ne_leaf P R repr binary prime context columnsFit
                input leaf (same.symm.trans encoded)
            · exact StrandMerkleDomains.input_ne_node P R repr binary prime context columnsFit
                input index children (same.symm.trans encoded)
      cases value <;> simp only [StrandSearch.claims,rejected]

/-- The concrete original-search charge covers a late authentication
query. Its target comes from the fixed root or an indexed node already in
the extraction cut; no future opening index is used in the charge itself. -/
theorem wire_late_query_charged [DecidableEq Raw]
    (schema : History.Codec T) (bytes : Raw → Framing.Bytes) (keyOf : T → Key) (root : Key → Digest)
    {fuel : ℕ} (program : Tree (StrandCoupling.Point Raw PrfKey Word) Digest Out fuel)
    (H : StrandSearch.Name Raw T → StrandCoupling.Sample Digest Word) (SHA : Framing.Bytes → Digest)
    (sound : ∀ raw logical answer,
      ((.inl (raw,logical),answer) : StrandSearch.Name Raw T × _) ∈
        ((StrandReplay.search schema bytes program).run H).2 → answer.1 = SHA (bytes raw))
    (key : Key) (raw : Raw) (logical : Option T) (answer : StrandCoupling.Sample Digest Word)
    (queried : ((.inl (raw,logical),answer) : StrandSearch.Name Raw T × _) ∈
      ((StrandReplay.search schema bytes program).run H).2)
    (receiving : receives (MerkleWireCodec.codec P R repr binary prime context columnsFit) bytes (.inl (raw,logical)))
    (missing : (bytes raw,answer.1) ∉
      (StrandCut.trace keyOf (StrandReplay.search schema bytes program) H key).map
        (fun qa => (bytes qa.1,qa.2)))
    (target : answer.1 = root key ∨ ∃ index input digest children,
      (input,digest) ∈ (StrandCut.trace keyOf (StrandReplay.search schema bytes program) H key).map
        (fun qa => (bytes qa.1,qa.2)) ∧
      (MerkleWireCodec.decoders P R repr binary prime context columnsFit).nodeDec index input = some children ∧
        (answer.1 = children.1 ∨ answer.1 = children.2)) :
    1 ≤ DigestProjection.receivingCharge
      (receives (MerkleWireCodec.codec P R repr binary prime context columnsFit) bytes)
      (StrandCommitment.claims MerkleWireCodec.nodeChildren keyOf root ∘ byteName bytes)
      (StrandReplay.search schema bytes program) H := by
  let tree := StrandReplay.search schema bytes program
  have value := sound raw logical answer queried
  rw [value] at missing target
  have absent : ∀ digest, (raw,digest) ∉ StrandCut.trace keyOf tree H key := by
    intro digest member
    obtain ⟨value,row,source⟩ := StrandCut.trace_source keyOf tree H key raw digest member
    rw [beforeLabel_eq_takeWhile] at source
    have correct := sound raw value (digest,row) ((List.takeWhile_sublist _).subset source)
    apply missing
    rw [← correct]
    exact List.mem_map_of_mem (f := fun qa => (bytes qa.1,qa.2)) member
  have hit : SHA (bytes raw) = root key ∨ ∃ input digest,
      (input,digest) ∈ StrandCut.trace keyOf tree H key ∧
        SHA (bytes raw) ∈ StrandCommitment.children (MerkleWireCodec.nodeChildren ∘ bytes) input := by
    rcases target with atRoot | ⟨index,input,digest,children,member,decoded,child⟩
    · exact Or.inl atRoot
    · obtain ⟨⟨source,result⟩,sourceMember,same⟩ := List.mem_map.mp member
      have sameInput : bytes source = input := congrArg Prod.fst same
      have read := MerkleWireCodec.nodeChildren_of_decoded P R repr binary prime context columnsFit
        index input children decoded
      refine Or.inr ⟨source,result,sourceMember,?_⟩
      simp only [StrandCommitment.children,Function.comp_apply,sameInput,read,
        Finset.mem_insert,Finset.mem_singleton]
      exact child
  have charged := StrandCommitment.missing_cut_hit (MerkleWireCodec.nodeChildren ∘ bytes) keyOf root tree H
    (SHA ∘ bytes) key raw logical answer queried value
    (ordinary_no_children schema bytes program H) absent hit
  rw [claims_bytes]
  exact DigestProjection.receiving_hit_charged _ _ tree H _ receiving charged

section RuntimeReceiving
variable {g : Geometry} (shape : WireBlocks.Shape g fields) (setup : FingerprintPrefix.Setup)
variable (publicCount : ℕ) (fits : g.roles.length < 2^64)
variable (locate : QueryRuntime.Runtime.Value repr shape setup publicCount → Raw)
variable (bytes : Raw → Framing.Bytes)
variable (located : ∀ value, bytes (locate value) =
  ((StrandRuntime.Runtime.schema repr shape setup publicCount).encode value).input.encode)
include located

/-- The concrete codecs establish the auxiliary classification required
by the receiving mean, including arbitrary annotations on the raw name. -/
theorem wire_receives_auxiliary
    (raw : Raw) (value : Option (QueryRuntime.Runtime.Value repr shape setup publicCount))
    (receiving : receives (MerkleWireCodec.codec P R repr binary prime context columnsFit) bytes (.inl (raw,value))) :
    (StrandRuntime.Runtime.pointCodec repr shape setup publicCount fits locate).decode (.inl (raw,value)) = none := by
  apply StrandRuntime.Runtime.pointCodec_merkle_auxiliary repr shape setup publicCount fits locate bytes located
  rcases receiving with ⟨leaf,equal⟩ | ⟨index,children,equal⟩
  · rw [equal]
    rfl
  · rw [equal]
    rfl

/-- The runtime codec's entire canonical image is outside the Merkle
receiving domain. No recognition, query-order, or hash assumption is needed. -/
theorem wire_receives_disjoint
    (point : {point // QueryRuntime.Runtime.Canonical repr shape setup publicCount point}) :
    ¬receives (MerkleWireCodec.codec P R repr binary prime context columnsFit) bytes
      ((StrandRuntime.Runtime.pointCodec repr shape setup publicCount fits locate).encode point) := by
  intro receiving
  have missing := wire_receives_auxiliary P R repr binary prime context columnsFit
    shape setup publicCount fits locate bytes located _ _ receiving
  have decoded := (StrandRuntime.Runtime.pointCodec repr shape setup publicCount fits locate).decode_encode point
  change (StrandRuntime.Runtime.pointCodec repr shape setup publicCount fits locate).decode
    ((StrandRuntime.Runtime.pointCodec repr shape setup publicCount fits locate).encode point) = none at missing
  have impossible := missing.symm.trans decoded
  cases impossible

variable [DecidableEq Raw] [Fintype Raw]
variable [Fintype (QueryRuntime.Runtime.Value repr shape setup publicCount)]
variable {Challenge : Type} [Fintype Challenge] [Nonempty Challenge]

/-- The actual wire codecs discharge the sole disjointness premise of the
receiving mean. The remaining `located` identity is the definition of the
runtime's canonical finite node location, not a probabilistic assumption. -/
theorem wire_receiving_sum_le {fuel Q : ℕ}
    (tree : Tree (StrandSearch.Name Raw (QueryRuntime.Runtime.Value repr shape setup publicCount))
      (Digest × Challenge) Out fuel)
    (queries : ∀ H, (seen tree H).card ≤ Q)
    {Key : Type} (key : QueryRuntime.Runtime.Value repr shape setup publicCount → Key) (root : Key → Digest) :
    (∑ H,
      DigestProjection.receivingCharge
        (receives (MerkleWireCodec.codec P R repr binary prime context columnsFit) bytes)
        (StrandCommitment.claims MerkleWireCodec.nodeChildren key root ∘ byteName bytes) tree H) ≤
      ∑ H, ∑ p ∈ seen tree H,
        if (StrandRuntime.Runtime.pointCodec repr shape setup publicCount fits locate).decode p = none
          then (Q*2 : ℚ)/(2^256 : ℚ) else 0 := by
  have bound := receiving_sum_le (MerkleWireCodec.codec P R repr binary prime context columnsFit)
    MerkleWireCodec.nodeChildren bytes key root
    (StrandRuntime.Runtime.pointCodec repr shape setup publicCount fits locate)
    (wire_receives_disjoint P R repr binary prime context columnsFit shape setup publicCount fits locate bytes located)
    tree queries
  simpa only [TranscriptV2.Strand.digest_card,Nat.cast_pow,Nat.cast_ofNat] using bound

/-- The two hash mechanisms share disjoint auxiliary slots: parent/PRF
speculation uses strand inputs, while Merkle receiving uses Merkle inputs.
The combined allowance is 2Q/M per auxiliary slot, not the sum 3Q/M. -/
theorem wire_hash_sum_le {fuel Q : ℕ}
    (tree : Tree (StrandSearch.Name Raw (QueryRuntime.Runtime.Value repr shape setup publicCount))
      (Digest × Challenge) Out fuel)
    (queries : ∀ H, (seen tree H).card ≤ Q)
    {Key : Type} (key : QueryRuntime.Runtime.Value repr shape setup publicCount → Key) (root : Key → Digest) :
    (∑ H, (DigestProjection.charge (StrandSearch.claims bytes) tree H +
      DigestProjection.receivingCharge
        (receives (MerkleWireCodec.codec P R repr binary prime context columnsFit) bytes)
        (StrandCommitment.claims MerkleWireCodec.nodeChildren key root ∘ byteName bytes) tree H)) ≤
      ∑ H, ∑ p ∈ seen tree H,
        if (StrandRuntime.Runtime.pointCodec repr shape setup publicCount fits locate).decode p = none
          then (2*Q : ℚ)/(2^256 : ℚ) else 0 := by
  let names := StrandRuntime.Runtime.pointCodec repr shape setup publicCount fits locate
  let plants := fun point : StrandSearch.Name Raw (QueryRuntime.Runtime.Value repr shape setup publicCount) =>
    (StrandSearch.claims bytes point).Nonempty
  have plantAuxiliary point (planted : plants point) : names.decode point = none := by
    cases point with
    | inr _ => rfl
    | inl point =>
        rcases point with ⟨raw,value⟩
        cases value with
        | none => rfl
        | some value => exact False.elim (Finset.not_nonempty_empty planted)
  have receiveAuxiliary point (receiving :
      receives (MerkleWireCodec.codec P R repr binary prime context columnsFit) bytes point) :
      names.decode point = none :=
    receives_auxiliary (MerkleWireCodec.codec P R repr binary prime context columnsFit) bytes names
      (wire_receives_disjoint P R repr binary prime context columnsFit shape setup publicCount
        fits locate bytes located) point receiving
  have disjoint point (planted : plants point) :
      ¬receives (MerkleWireCodec.codec P R repr binary prime context columnsFit) bytes point := by
    intro receiving
    have empty := receiving_claims_empty P R repr binary prime context columnsFit bytes point receiving
    change (StrandSearch.claims bytes point).Nonempty at planted
    rw [empty] at planted
    exact Finset.not_nonempty_empty planted
  have strandBound point : (StrandSearch.claims bytes point).card ≤ if plants point then 1 else 0 := by
    by_cases planted : plants point
    · rw [if_pos planted]
      exact (StrandSearch.claims_card bytes point).trans (by split_ifs <;> decide)
    · rw [if_neg planted,Finset.not_nonempty_iff_eq_empty.mp planted]
      simp only [Finset.card_empty,le_refl]
  have bound := StrandCharging.disjoint_hash_sum_le tree queries plants
    (receives (MerkleWireCodec.codec P R repr binary prime context columnsFit) bytes)
    (fun point => names.decode point = none) plantAuxiliary receiveAuxiliary disjoint
    (StrandSearch.claims bytes)
    (StrandCommitment.claims MerkleWireCodec.nodeChildren key root ∘ byteName bytes)
    (fun point => by
      by_cases planted : plants point
      · simpa only [if_pos planted] using strandBound point
      · simpa only [if_neg planted] using strandBound point)
    (fun point => StrandCommitment.claims_card MerkleWireCodec.nodeChildren key root (byteName bytes point))
  simpa only [TranscriptV2.Strand.digest_card,Nat.cast_pow,Nat.cast_ofNat] using bound

end RuntimeReceiving

/-- Merkle leaf preimages begin with ASCII `p`; PRF preimages begin with
binary type word zero. This follows from the actual byte codec prefix. -/
theorem leaf_nonPrf (value : MerkleWireCodec.Salt n × (Joint.Pair.family P R).Leaf) :
    Strand.decodePrf ((MerkleWireCodec.leaf P R repr binary prime context columnsFit).encode value) = none := by
  cases found : Strand.decodePrf ((MerkleWireCodec.leaf P R repr binary prime context columnsFit).encode value) with
  | none => rfl
  | some address =>
      have encoded := Strand.decodePrf_sound _ address found
      have first := congrArg List.head? encoded
      change some (112 : Framing.Byte) = some (0 : Framing.Byte) at first
      exact False.elim ((by decide : (112 : Framing.Byte) ≠ 0) (Option.some.inj first))

/-- Internal Merkle nodes have the same explicit disjointness from PRF
inputs, independently of either child digest. -/
theorem node_nonPrf (index : ℕ) (children : Digest × Digest) :
    Strand.decodePrf ((MerkleWireCodec.node context index).encode children) = none := by
  cases found : Strand.decodePrf ((MerkleWireCodec.node context index).encode children) with
  | none => rfl
  | some address =>
      have encoded := Strand.decodePrf_sound _ address found
      have first := congrArg List.head? encoded
      change some (112 : Framing.Byte) = some (0 : Framing.Byte) at first
      exact False.elim ((by decide : (112 : Framing.Byte) ≠ 0) (Option.some.inj first))

end WireDomains
end LfzkV2.Current.StrandMerkleRealization
