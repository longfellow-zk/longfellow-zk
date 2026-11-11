import LfzkV2.Current.ObserverWindow
import LfzkV2.Current.MerkleWireCodec
import LfzkV2.Current.MetadataIdentifiers

/-! One SHA oracle with independent domain slices. Complementary inputs
are answered by the same fixed slice used for public identifiers. Observer
queries on that slice remain in the recorded original mixed trace. Only
Merkle-domain queries remain as random-oracle nodes; their syntactic budget
is still bounded by the original total SHA-query budget. -/
noncomputable section
namespace LfzkV2.Current.SHAOracle
open Merkle Merkle.MH Merkle.RandomOracle Finset
open scoped Classical

section Generic
variable {Raw D QT AT Value : Type}
variable (domain : Raw → Prop) (outside : Raw → D)

def merge (inside : Raw → D) (query : Raw) : D :=
  if domain query then inside query else outside query

theorem merge_inside (inside : Raw → D) (query : Raw) (member : domain query) :
    merge domain outside inside query = inside query := if_pos member

theorem merge_outside (inside : Raw → D) (query : Raw) (member : ¬domain query) :
    merge domain outside inside query = outside query := if_neg member

/-- This is an exact split of function coordinates, including on infinite
raw-string types. Finite random-oracle marginals use the same equivalence. -/
def split : (Raw → D) ≃ (({query // domain query} → D) × ({query // ¬domain query} → D)) where
  toFun H := (fun query => H query.val,fun query => H query.val)
  invFun pair query := if member : domain query then pair.1 ⟨query,member⟩ else pair.2 ⟨query,member⟩
  left_inv _ := by funext query; dsimp only; split_ifs <;> rfl
  right_inv pair := by
    apply Prod.ext
    · funext query
      simp only [dif_pos query.property]
    · funext query
      simp only [dif_neg query.property]

def weakenLeft : {left right : ℕ} → TwoOracleTree Raw D QT AT Value left right →
    TwoOracleTree Raw D QT AT Value (left+1) right
  | _,_,.done value => .done value
  | _,_,.queryLeft query next => .queryLeft query fun answer => weakenLeft (next answer)
  | _,_,.queryRight query next => .queryRight query fun answer => weakenLeft (next answer)

theorem weakenLeft_run {left right : ℕ} (tree : TwoOracleTree Raw D QT AT Value left right)
    (HM : Raw → D) (HT : QT → AT) :
    Observer.run HM HT (weakenLeft tree) = Observer.run HM HT tree := by
  induction tree with
  | done value => rfl
  | queryLeft query next ih => simp only [weakenLeft,Observer.run,ih]
  | queryRight query next ih => simp only [weakenLeft,Observer.run,ih]

def route : {left right : ℕ} → TwoOracleTree Raw D QT AT Value left right →
    TwoOracleTree Raw D QT AT Value left right
  | _,_,.done value => .done value
  | _,_,.queryLeft query next =>
      if domain query then .queryLeft query fun answer => route (next answer)
      else weakenLeft (route (next (outside query)))
  | _,_,.queryRight query next => .queryRight query fun answer => route (next answer)

theorem route_output {left right : ℕ} (tree : TwoOracleTree Raw D QT AT Value left right)
    (HM : Raw → D) (HT : QT → AT) :
    (Observer.run HM HT (route domain outside tree)).1 =
      (Observer.run (merge domain outside HM) HT tree).1 := by
  induction tree with
  | done value => rfl
  | queryLeft query next ih =>
      by_cases member : domain query
      · simp only [route,if_pos member,Observer.run,merge,ih]
      · simp only [route,if_neg member,weakenLeft_run,Observer.run,merge,ih]
  | queryRight query next ih => simp only [route,Observer.run,ih]

theorem route_trace {left right : ℕ} (tree : TwoOracleTree Raw D QT AT Value left right)
    (inside : Raw → D) (HT : QT → AT) :
    (Observer.run inside HT (route domain outside tree)).2 =
      ((Observer.run (merge domain outside inside) HT tree).2.filter fun event =>
        match event with | .inl qa => decide (domain qa.1) | .inr _ => true) := by
  induction tree with
  | done value => rfl
  | queryLeft query next ih =>
      by_cases member : domain query
      · simp [route,Observer.run,merge,ih,member]
      · simp [route,weakenLeft_run,Observer.run,merge,ih,member]
  | queryRight query next ih => simp only [route,Observer.run,ih,List.filter_cons,if_true]

/-- Record before specializing. Queries to public identifier bytes are
answered from the complementary SHA slice and remain visible to the observer. -/
def observer {left right : ℕ} (tree : TwoOracleTree Raw D QT AT Value left right) :=
  route domain outside (Observer.record [] tree)

theorem observer_output {left right : ℕ} (tree : TwoOracleTree Raw D QT AT Value left right)
    (HM : Raw → D) (HT : QT → AT) :
    (Observer.run HM HT (observer domain outside tree)).1 =
      Observer.run (merge domain outside HM) HT tree := by
  rw [observer,route_output,Observer.record_output]
  simp only [List.nil_append,Prod.eta]

variable [Fintype D] [Fintype AT] [DecidableEq Raw]

theorem queries_weakenLeft {left right : ℕ} (tree : TwoOracleTree Raw D QT AT Value left right) :
    ObserverWindow.mixedQueries (weakenLeft tree) = ObserverWindow.mixedQueries tree := by
  induction tree with
  | done value => rfl
  | queryLeft query next ih => simp only [weakenLeft,ObserverWindow.mixedQueries,ih]
  | queryRight query next ih => simp only [weakenLeft,ObserverWindow.mixedQueries,ih]

theorem queries_route_domain {left right : ℕ} (tree : TwoOracleTree Raw D QT AT Value left right) :
    ∀ query ∈ ObserverWindow.mixedQueries (route domain outside tree), domain query := by
  induction tree with
  | done value => simp [route,ObserverWindow.mixedQueries]
  | queryLeft query next ih =>
      by_cases member : domain query
      · intro point inside
        simp only [route,if_pos member,ObserverWindow.mixedQueries,mem_insert] at inside
        rcases inside with rfl | inside
        · exact member
        · obtain ⟨answer,_,inside⟩ := mem_biUnion.mp inside
          exact ih answer point inside
      · simpa only [route,if_neg member,queries_weakenLeft] using ih (outside query)
  | queryRight query next ih =>
      intro point inside
      obtain ⟨answer,_,inside⟩ := mem_biUnion.mp inside
      exact ih answer point inside

end Generic

section ActualBytes

/-- Exact leaf/node-tag domains leave all other SHA uses, including static
context hashes, in the complementary slice. -/
def merkleDomain (bytes : Bytes) : Prop :=
  MerkleWireCodec.leafDomain <+: bytes ∨ MerkleWireCodec.nodeDomain <+: bytes

variable {k s n t : ℕ} (P R : Joint.Participant k s n t)
variable {fields : Fields} {Advice : Type}
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (binary : fields .binary ≃ P.Carrier) (prime : fields .prime ≃ R.Carrier)
variable (context : Digest) (fits : n ≤ 2^64)

theorem leaf_in_domain (value : MerkleWireCodec.Salt n × (Joint.Pair.family P R).Leaf) :
    merkleDomain ((MerkleWireCodec.codec P R repr binary prime context fits).leafEnc value) := by
  left
  rw [MerkleWireCodec.leaf_encode]
  refine ⟨List.ofFn context ++ TranscriptV2.Framing.encodeLE 8 value.1.1.val ++ List.ofFn value.1.2 ++
    (MerkleWireCodec.physical P R repr binary prime).encode ((MerkleWireCodec.physicalLeafEquiv P R).symm value.2),?_⟩
  simp only [List.append_assoc]

theorem node_in_domain (value : Digest × Digest) (index : ℕ := 0) :
    merkleDomain ((MerkleWireCodec.codec P R repr binary prime context fits).nodeEnc index value) := by
  right
  rw [MerkleWireCodec.node_encode]
  exact ⟨List.ofFn context ++ TranscriptV2.Framing.encodeLE 8 index ++ List.ofFn value.1 ++ List.ofFn value.2,
    by simp only [List.append_assoc]⟩

variable {F : Type} [Field F]

theorem identifier_not_domain (isBinary : Bool) (width : ℕ) (encode : F → Bytes)
    (outputs logOutput inputs publicInputs : ℕ) (layers : List (MetadataIdentifiers.Layer F)) :
    ¬merkleDomain (MetadataIdentifiers.circuitBytes isBinary width encode outputs logOutput inputs publicInputs layers) := by
  rintro (⟨tail,equal⟩ | ⟨tail,equal⟩)
  all_goals
    have first := congrArg List.head? equal
    change some (112 : TranscriptV2.Framing.Byte) = some (76 : TranscriptV2.Framing.Byte) at first
    exact (by decide : (112 : TranscriptV2.Framing.Byte) ≠ 76) (Option.some.inj first)

theorem adapter_identifier (outside inside : Bytes → Digest) {d q : ℕ}
    (encode : F → Bytes) (shape : Adapter.Circuit.Shape d q)
    (inputs publicInputs : ℕ) (sources : Fin d → ℕ) (pads : Fin 2 → Fin q → ℕ)
    (powers : Fin 2 → Fin d → Fˣ) (base : Fˣ)
    (masked : Fin 2 → Fin q → Bool) (targets : Fin 2 → Fˣ) :
    MetadataIdentifiers.adapterId (merge merkleDomain outside inside) encode shape
        inputs publicInputs sources pads powers base masked targets =
      MetadataIdentifiers.adapterId outside encode shape inputs publicInputs sources pads powers base masked targets := by
  apply merge_outside
  exact identifier_not_domain _ _ _ _ _ _ _ _

end ActualBytes
end LfzkV2.Current.SHAOracle
