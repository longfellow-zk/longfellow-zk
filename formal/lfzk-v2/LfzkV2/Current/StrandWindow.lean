import LfzkV2.Current.OracleWindow
import TranscriptV2.StrandVerifier
import TranscriptV2.StrandTrace

/-! A bounded raw program has finite support even though byte strings have
unbounded length. Keep every PRF coordinate and only a finite complement of
other inputs. This is a restriction of addresses, not an additional oracle. -/
noncomputable section
namespace LfzkV2.Current.StrandWindow
open Finset Merkle.RandomOracle TranscriptV2 TranscriptV2.Strand Framing
open scoped Classical

variable {Out T : Type}

abbrev Node (other : Finset OtherPoint) := {raw : OtherPoint // raw ∈ other}
abbrev Point (other : Finset OtherPoint) := StrandCoupling.Point (Node other) PrfKey Word

abbrev Node.bytes {other : Finset OtherPoint} (raw : Node other) : Bytes := raw.val.val

def encode {other : Finset OtherPoint} : Point other → Bytes
  | .inl raw => raw.bytes
  | .inr prf => (Input.prf prf.1.1 prf.1.2 prf.2).encode

theorem encode_injective (other : Finset OtherPoint) :
    Function.Injective (encode (other := other)) := by
  have comm (point : Point other) :
      Strand.windowEncode ((Equiv.sumComm (Node other) Strand.PrfPoint) point) = encode point := by
    cases point with
    | inl raw => rfl
    | inr address => rcases address with ⟨parent,counter⟩; rfl
  intro first second same
  apply (Equiv.sumComm (Node other) Strand.PrfPoint).injective
  apply Strand.windowEncode_injective other
  rw [comm,comm]
  exact same

def complement (window : Finset Bytes) : Finset OtherPoint :=
  window.attach.biUnion fun raw => match found : decodePrf raw.val with
    | some _ => ∅
    | none => {⟨raw.val,found⟩}

theorem mem_complement (window : Finset Bytes) (raw : OtherPoint) :
    raw ∈ complement window ↔ raw.val ∈ window := by
  constructor
  · intro present
    obtain ⟨input,_,present⟩ := mem_biUnion.mp present
    split at present
    · exact False.elim ((Finset.notMem_empty raw) present)
    · have same := mem_singleton.mp present
      rw [congrArg Subtype.val same]
      exact input.property
  · intro present
    apply mem_biUnion.mpr
    refine ⟨⟨raw.val,present⟩,mem_attach _ _,?_⟩
    simp only [Subtype.coe_mk]
    split
    next _ found => cases found.symm.trans raw.property
    next => exact mem_singleton.mpr (Subtype.ext rfl)

/-- Include canonical node addresses so locating an accepted logical point
is total, including points not reached in a particular execution. -/
def canonical [Fintype T] (schema : History.Codec T) : Finset OtherPoint :=
  univ.image fun value => TranscriptV2.Strand.History.nodePoint (schema.encode value)

theorem mem_canonical [Fintype T] (schema : History.Codec T) (value : T) :
    TranscriptV2.Strand.History.nodePoint (schema.encode value) ∈ canonical schema :=
  mem_image.mpr ⟨value,mem_univ _,rfl⟩

/-- One finite complement covers adversarial search, full authentication
replay and every canonical protocol node. Its cardinality is not the query
budget: soundness continues to count distinct inputs actually queried. -/
def support [Fintype T] (schema : History.Codec T) {fuel : ℕ}
    (program : Tree Bytes Digest Out fuel) : Finset OtherPoint :=
  complement (OracleWindow.queries program) ∪ canonical schema

/-- A total decoder lets the search and every verifier continuation use
one address map. The fallback is unreachable on a program covered by the
window; canonical protocol nodes are also included explicitly. -/
def decode (other : Finset OtherPoint) (fallback : Node other) (raw : Bytes) : Point other :=
  match rawPoint raw with
  | .inl point => if member : point ∈ other then .inl ⟨point,member⟩ else .inl fallback
  | .inr address => .inr address

theorem decode_encode (other : Finset OtherPoint) (fallback : Node other) (point : Point other) :
    decode other fallback (encode point) = point := by
  cases point with
  | inl raw =>
      have same : rawPoint raw.val.val = .inl raw.val := rawPoint_bytes (.inl raw.val)
      simp only [decode,encode,same,raw.property,↓reduceDIte]
  | inr address =>
      rcases address with ⟨parent,counter⟩
      have same : rawPoint (Input.prf parent.1 parent.2 counter).encode = .inr (parent,counter) :=
        rawPoint_bytes (.inr (parent,counter))
      simp only [decode,encode,same]

/-- A finite PRF coordinate has exactly its canonical raw preimage.
Neither a malformed input nor an out-of-window node can alias this branch. -/
theorem decode_prf_fiber (other : Finset OtherPoint) (fallback : Node other)
    (raw : Bytes) (digest : PrfKey) (counter : Word)
    (found : decode other fallback raw = .inr (digest,counter)) :
    raw = (Input.prf digest.1 digest.2 counter).encode := by
  cases source : rawPoint raw with
  | inl point =>
      simp only [decode,source] at found
      split at found <;> cases found
  | inr address =>
      have same : address = (digest,counter) := by simpa only [decode,source,Sum.inr.injEq] using found
      have bytes := congrArg rawBytes source
      rw [rawBytes_point,same] at bytes
      exact bytes

/-- Only the fallback coordinate can stand for more than one raw input.
Every other finite address therefore retains its single physical preimage,
even when considering counterfactual oracle tables. -/
theorem decode_fiber (other : Finset OtherPoint) (fallback : Node other)
    (point : Point other) (notFallback : point ≠ .inl fallback) (raw : Bytes)
    (found : decode other fallback raw = point) : raw = encode point := by
  cases source : rawPoint raw with
  | inl node =>
      simp only [decode,source] at found
      split at found
      · rw [← found]
        have same := congrArg rawBytes source
        rw [rawBytes_point] at same
        exact same
      · exact False.elim (notFallback found.symm)
  | inr address =>
      simp only [decode,source] at found
      rw [← found]
      have same := congrArg rawBytes source
      rw [rawBytes_point] at same
      exact same

/-- Every history node stays in the non-PRF branch of the finite
compiler, including an out-of-window history using the fixed fallback. -/
theorem decode_history (other : Finset OtherPoint) (fallback : Node other) (history : Strand.History) :
    ∃ raw, decode other fallback history.input.encode = .inl raw := by
  let point := TranscriptV2.Strand.History.nodePoint history
  have found : rawPoint history.input.encode = .inl point := rawPoint_bytes (.inl point)
  simp only [decode,found]
  split
  · exact ⟨_,rfl⟩
  · exact ⟨fallback,rfl⟩

theorem encode_decode (other : Finset OtherPoint) (fallback : Node other) (raw : Bytes)
    (covered : ∀ point : OtherPoint, point.val = raw → point ∈ other) :
    encode (decode other fallback raw) = raw := by
  unfold decode
  cases found : rawPoint raw with
  | inl point =>
      have same := congrArg rawBytes found
      rw [rawBytes_point] at same
      change raw = point.val at same
      have member := covered point same.symm
      simp only [member,↓reduceDIte,encode]
      exact same.symm
  | inr address =>
      have same := congrArg rawBytes found
      rw [rawBytes_point] at same
      exact same.symm

/-- The total compiler preserves the exact raw run whenever the finite
window contains its all-branch non-PRF support. -/
theorem decode_run (other : Finset OtherPoint) (fallback : Node other) {fuel : ℕ}
    (program : Tree Bytes Digest Out fuel)
    (contains : complement (OracleWindow.queries program) ⊆ other)
    (G : Point other → Digest) :
    (((mapQueries (decode other fallback) program).run G).1,
      ((mapQueries (decode other fallback) program).run G).2.map (fun qa => (encode qa.1,qa.2))) =
        program.run (G ∘ decode other fallback) := by
  rw [run_mapQueries]
  simp only [List.map_map,Function.comp_def]
  apply Prod.ext
  · rfl
  · have names : ∀ qa ∈ (program.run (G ∘ decode other fallback)).2,
        (encode (decode other fallback qa.1),qa.2) = qa := by
      intro qa member
      have address := encode_decode other fallback qa.1 (by
        intro point equal
        apply contains
        apply (mem_complement _ point).mpr
        rw [equal]
        exact OracleWindow.trace_mem_queries program _ qa member)
      exact Prod.ext address rfl
    exact (List.map_congr_left names).trans (List.map_id _)


/-- The finite compiler does not introduce additional raw SHA inputs
along a covered execution. This is the visibility direction used when
transferring the actual raw collision event. -/
theorem decode_seen (other : Finset OtherPoint) (fallback : Node other) {fuel : ℕ}
    (program : Tree Bytes Digest Out fuel)
    (contains : complement (OracleWindow.queries program) ⊆ other)
    (G : Point other → Digest) (point : Point other)
    (member : point ∈ seen (mapQueries (decode other fallback) program) G) :
    encode point ∈ seen program (G ∘ decode other fallback) := by
  obtain ⟨⟨address,answer⟩,present,same⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
  change address = point at same
  subst address
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  refine ⟨(encode point,answer),?_,rfl⟩
  rw [← congrArg Prod.snd (decode_run other fallback program contains G)]
  exact List.mem_map_of_mem (f := fun qa => (encode qa.1,qa.2)) present

/-- Decode any raw input known to lie in a finite supporting window. -/
def locate (other : Finset OtherPoint) (window : Finset Bytes)
    (contains : complement window ⊆ other) (raw : {raw // raw ∈ window}) : Point other :=
  match found : rawPoint raw.val with
  | .inl point => .inl ⟨point,contains ((mem_complement window point).mpr (by
      have same := congrArg rawBytes found
      rw [rawBytes_point] at same
      change raw.val = point.val at same
      rw [← same]
      exact raw.property))⟩
  | .inr address => .inr address

theorem encode_locate (other : Finset OtherPoint) (window : Finset Bytes)
    (contains : complement window ⊆ other) (raw : {raw // raw ∈ window}) :
    encode (locate other window contains raw) = raw.val := by
  unfold locate
  split
  · have same := congrArg rawBytes (by assumption : rawPoint raw.val = .inl _)
    rw [rawBytes_point] at same
    exact same.symm
  · have same := congrArg rawBytes (by assumption : rawPoint raw.val = .inr _)
    rw [rawBytes_point] at same
    exact same.symm

/-- Compile the address restriction using the existing finite-window tree.
Every branch remains executable; no successful-output condition is used. -/
def restrict (other : Finset OtherPoint) {fuel : ℕ} (program : Tree Bytes Digest Out fuel)
    (contains : complement (OracleWindow.queries program) ⊆ other) :
    Tree (Point other) Digest Out fuel :=
  mapQueries (locate other (OracleWindow.queries program) contains)
    (OracleWindow.restrict (OracleWindow.queries program) program (fun _ present => present))

/-- Restriction preserves every raw answer and the complete ordered trace. -/
theorem restrict_run (other : Finset OtherPoint) {fuel : ℕ} (program : Tree Bytes Digest Out fuel)
    (contains : complement (OracleWindow.queries program) ⊆ other)
    (SHA : Bytes → Digest) :
    (((restrict other program contains).run (SHA ∘ encode)).1,
      ((restrict other program contains).run (SHA ∘ encode)).2.map (fun qa => (encode qa.1,qa.2))) =
        program.run SHA := by
  have projected : (SHA ∘ encode) ∘ locate other (OracleWindow.queries program) contains =
      fun raw => SHA raw.val := by
    funext raw
    simp only [Function.comp_apply,encode_locate]
  simp only [restrict,run_mapQueries,projected,List.map_map]
  have exactTrace := OracleWindow.restrict_run
    (OracleWindow.queries program) program (fun _ present => present) SHA
  simpa only [Function.comp_def,encode_locate] using exactTrace

/-- A finite table supplies all PRF addresses and its finite non-PRF
complement. Inputs outside this marginal use a fixed fallback. -/
def oracle (other : Finset OtherPoint) (H : Point other → Digest) (raw : Bytes) : Digest :=
  match rawPoint raw with
  | .inl point => if member : point ∈ other then H (.inl ⟨point,member⟩) else 0
  | .inr address => H (.inr address)

theorem oracle_encode (other : Finset OtherPoint) (H : Point other → Digest) (point : Point other) :
    oracle other H (encode point) = H point := by
  cases point with
  | inl raw =>
      have same : rawPoint raw.val.val = .inl raw.val := rawPoint_bytes (.inl raw.val)
      simp only [oracle,encode,same,raw.property,↓reduceDIte]
  | inr address =>
      have same := rawPoint_bytes (.inr address)
      simp only [rawBytes] at same
      simp only [oracle,encode,same]

/-- Running the finite tree directly agrees with one raw-SHA execution.
This is the deterministic bridge used before applying the exact named-query
probability law. -/
theorem restrict_oracle_run (other : Finset OtherPoint) {fuel : ℕ} (program : Tree Bytes Digest Out fuel)
    (contains : complement (OracleWindow.queries program) ⊆ other)
    (H : Point other → Digest) :
    (((restrict other program contains).run H).1,
      ((restrict other program contains).run H).2.map (fun qa => (encode qa.1,qa.2))) =
        program.run (oracle other H) := by
  have same : (oracle other H) ∘ encode = H := by
    funext point
    exact oracle_encode other H point
  simpa only [same] using restrict_run other program contains (oracle other H)

end LfzkV2.Current.StrandWindow
