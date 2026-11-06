import LfzkV2.Current.RuntimeCover
import LfzkV2.Current.BackendOracle

/-! Backend charges for the actual verifier decoder. The statement reader,
batching codec and complete response-pair encoder are fixed by runtime
construction. A malformed prefix uses a zero statement only to totalize
counting; the actual verifier rejects that prefix before authentication. -/
noncomputable section
namespace LfzkV2.Current.RuntimeBackend
open Application ApplicationSetup ApplicationOracle RecursivePolygero SumcheckV2
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice Base Key C B Salt : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B] [Fintype C]
variable {shared maskBits adviceBits k s n t : ℕ}
variable (binary : BinaryPublic B shared maskBits adviceBits)
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable (prime : PrimePublic N shared)
variable (P : FieldBackend B k s n t) (R : FieldBackend N k s n t)
variable (cfg : RuntimeVerifier.Public (g := g) binary prime P R (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key) (C := C) (Salt := Salt))
local notation "Point" => RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key)
local notation "Output" => RuntimeVerifier.Output (g := g) (fields := fields) (Advice := Advice)
local notation "First" => RuntimeVerifier.first binary prime P R cfg
local notation "Second" => RuntimeVerifier.second binary prime P R cfg
local notation "E" => RuntimeVerifier.encoding binary prime P R cfg
local notation "Parent" => BackendQueries.Parent g.roles Key
  (RuntimeVerifier.Block (g := g) (fields := fields) (Advice := Advice) (Base := Base)) Digest g.batchingIndex
local notation "Decoded" => RuntimeVerifier.Decoded binary prime P R cfg

/-- The total compiler has a fixed algebraic fallback, not a fabricated
certified application. No accepted decoding can select this branch. -/
def zeroStatement : JointResponse.Statement (First).participant (Second).participant :=
  (⟨fun _ _ _ _ => 0,fun _ => 0⟩,⟨fun _ _ _ _ => 0,fun _ => 0⟩)

def derive (parent : Parent) (past : Fin g.batchingIndex.val → C) :
    JointResponse.Statement (First).participant (Second).participant :=
  ((RuntimeVerifier.statementAt binary prime P R cfg parent.point past).map
    (fun data => data.2.statement)).getD (zeroStatement binary prime P R cfg)

def queryDecoder (answer : C) : LigeroFamily.QuerySet n t := OrderedOpening.query (cfg.sample answer)

variable (draw : C → RuntimeVerifier.RawSamples binary prime P R cfg)
variable (cutOracle : (RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key) → Digest × C) → Key → JointResponse.Oracle
    (RuntimeVerifier.first binary prime P R cfg).participant
    (RuntimeVerifier.second binary prime P R cfg).participant)
variable (cutoff : ℕ × ℕ) (epsilon : ℚ)

/-- The one-input backend charge is zero outside the two actual counters.
The canonical opening decoder retains both complete participant responses. -/
def single (point : Point) (H : Point → Digest × C) (answer : Digest × C) : ℚ :=
  BackendOracle.single (First).participant (Second).participant g.batchingIndex_next
    (RuntimeVerifier.encodeResponses binary prime P R cfg) (derive binary prime P R cfg)
    cutOracle (RuntimeVerifier.batchingDecoder binary prime P R cfg draw)
    (queryDecoder binary prime P R cfg) cutoff epsilon point H answer

def high (parent : Parent) (response : Digest × JointResponse.Response (First).participant (Second).participant)
    (H : Point → Digest × C) (first second : Digest × C) : ℚ :=
  BackendFS.high (First).participant (Second).participant (derive binary prime P R cfg)
    cutOracle (RuntimeVerifier.batchingDecoder binary prime P R cfg draw)
    (queryDecoder binary prime P R cfg) epsilon parent response H first second

/-- Both branches use the same context-keyed recovered commitment oracle. -/
def oracleAt (proof : Output) (H : Point → Digest × C) :
    JointResponse.Oracle (First).participant (Second).participant :=
  cutOracle H ((E).context proof)

def authentication (proof : Output) (H : Point → Digest × C) (decoded : Decoded) :=
  RuntimeCover.authentication binary prime P R cfg proof decoded
    (oracleAt binary prime P R cfg cutOracle proof H) cutoff

/-- The first three concrete backend alternatives; witness-selection
collisions are charged separately at the fingerprint boundary. -/
def Bad (proof : Output) (H : Point → Digest × C) (decoded : Decoded) : Prop :=
  let a := authentication binary prime P R cfg cutOracle cutoff proof H decoded
  JointResponse.failure (First).participant (Second).participant a.statement a.oracle a.coin a.response ∨
    NonrecursiveFS.decodedOutsideList (First).backend a.statement.1 a.oracle.1 a.coin.1 a.response.1 cutoff.1 ∨
    NonrecursiveFS.decodedOutsideList (Second).backend a.statement.2 a.oracle.2 a.coin.2 a.response.2 cutoff.2

omit [Fintype C] in
/-- Splitting a backend failure leaves selection collisions at their early
fingerprint boundary rather than charging them again at the backend. -/
theorem bad_or_collision (proof : Output) (H : Point → Digest × C) (decoded : Decoded) :
    (authentication binary prime P R cfg cutOracle cutoff proof H decoded).BackendBad ↔
      Bad binary prime P R cfg cutOracle cutoff proof H decoded ∨
        (authentication binary prime P R cfg cutOracle cutoff proof H decoded).context.Collision := by
  simp only [Authentication.BackendBad,Bad]
  tauto

omit [Fintype C] in
theorem single_nonneg (point : Point) (H : Point → Digest × C) (answer : Digest × C) :
    0 ≤ single binary prime P R cfg draw cutOracle cutoff epsilon point H answer :=
  BackendOracle.single_nonneg ..

omit [Fintype C] in
/-- The public schedule places every application boundary away from these
two counters; malformed nonbackend preimages also receive zero charge. -/
theorem single_zero_of_rank (point : Point) (hparent : point.rank ≠ g.batchingIndex.val)
    (hchild : point.rank ≠ g.openingIndex.val) (H : Point → Digest × C) (answer : Digest × C) :
    single binary prime P R cfg draw cutOracle cutoff epsilon point H answer = 0 :=
  BackendOracle.single_zero_of_rank (First).participant (Second).participant g.batchingIndex_next
    (RuntimeVerifier.encodeResponses binary prime P R cfg)
    (RuntimeVerifier.encodeResponses_injective binary prime P R cfg) (derive binary prime P R cfg)
    cutOracle (RuntimeVerifier.batchingDecoder binary prime P R cfg draw)
    (queryDecoder binary prime P R cfg) cutoff epsilon point hparent
    (by simpa only [g.openingIndex_val] using hchild) H answer

variable [Inhabited (RuntimeVerifier.Family binary prime P R cfg).Leaf]

omit [Fintype C] in
/-- Successful decoding identifies the total statement compiler with the
actual affine statement, including both fingerprint equations. -/
theorem decoded_statement (proof : Output) (H : Point → Digest × C) (decoded : Decoded)
    (hd : RuntimeVerifier.decode binary prime P R cfg draw proof H = some decoded) :
    (BackendPath.parent (E) cfg.initialLink proof H g.batchingIndex).statement
      (derive binary prime P R cfg) H = decoded.statement.statement := by
  have hs := (RuntimeVerifier.decode_spec binary prime P R cfg draw proof H decoded hd).1
  simp only [BackendQueries.Parent.statement,derive,hs,Option.map_some,Option.getD_some]

omit [Fintype C] [Inhabited (RuntimeVerifier.Family binary prime P R cfg).Leaf] in
/-- The adjacent opening preimage contains the actual parent link and both
complete H/Z responses. This identity follows from verifier encoding. -/
theorem opening_eq (proof : Output) (H : Point → Digest × C) :
    ((E).chain cfg.initialLink).point proof H g.openingIndex.val =
      (BackendPath.parent (E) cfg.initialLink proof H g.batchingIndex).child g.batchingIndex_next
        (RuntimeVerifier.encodeResponses binary prime P R cfg)
        ((H (BackendPath.parent (E) cfg.initialLink proof H g.batchingIndex).point).1,
          RuntimeVerifier.responses binary prime P R cfg proof) := by
  have h := BackendPath.opening_eq (E) cfg.initialLink proof H g.batchingIndex g.batchingIndex_next
    (RuntimeVerifier.encodeResponses binary prime P R cfg)
    (RuntimeVerifier.responses binary prime P R cfg) (fun past => by
      exact RuntimeVerifier.encoding_opening binary prime P R cfg proof past)
  simpa only [g.openingIndex_val] using h

omit [Fintype C] in
/-- Actual decoding and the one explained joint opening imply a backend
charge at batching, opening, or their linked two-answer event. No path or
statement correspondence is supplied by the caller. -/
theorem failure_charged (proof : Output) (H : Point → Digest × C) (decoded : Decoded)
    (hd : RuntimeVerifier.decode binary prime P R cfg draw proof H = some decoded)
    (hv : let a := authentication binary prime P R cfg cutOracle cutoff proof H decoded
      JointResponse.Verify (First).participant (Second).participant a.statement a.oracle a.coin a.response decoded.query)
    (hf : Bad binary prime P R cfg cutOracle cutoff proof H decoded) :
    let parent := BackendPath.parent (E) cfg.initialLink proof H g.batchingIndex
    1 ≤ single binary prime P R cfg draw cutOracle cutoff epsilon parent.point H (H parent.point) ∨
      1 ≤ single binary prime P R cfg draw cutOracle cutoff epsilon
        (((E).chain cfg.initialLink).point proof H g.openingIndex.val) H
        (H (((E).chain cfg.initialLink).point proof H g.openingIndex.val)) ∨
      1 ≤ high binary prime P R cfg draw cutOracle epsilon parent
        ((H parent.point).1,RuntimeVerifier.responses binary prime P R cfg proof) H
        (H parent.point) (H (((E).chain cfg.initialLink).point proof H g.openingIndex.val)) := by
  let parent := BackendPath.parent (E) cfg.initialLink proof H g.batchingIndex
  let response := ((H parent.point).1,RuntimeVerifier.responses binary prime P R cfg proof)
  have hs := decoded_statement binary prime P R cfg draw proof H decoded hd
  have hc := (RuntimeVerifier.decode_spec binary prime P R cfg draw proof H decoded hd).2.2.1
  have hq := (RuntimeVerifier.decode_spec binary prime P R cfg draw proof H decoded hd).2.2.2
  have hopen := opening_eq binary prime P R cfg proof H
  have hcontext := BackendPath.parent_context (E) cfg.initialLink proof H g.batchingIndex
  have hv' : JointResponse.Verify (First).participant (Second).participant
      (parent.statement (derive binary prime P R cfg) H) (cutOracle H (parent.point : Point).context)
      (RuntimeVerifier.batchingDecoder binary prime P R cfg draw (H parent.point).2) response.2
      (queryDecoder binary prime P R cfg (H (parent.child g.batchingIndex_next
        (RuntimeVerifier.encodeResponses binary prime P R cfg) response)).2) := by
    rw [hs,hcontext,← hc,← hopen]
    change JointResponse.Verify (First).participant (Second).participant decoded.statement.statement
      (oracleAt binary prime P R cfg cutOracle proof H) decoded.coin
      (RuntimeVerifier.responses binary prime P R cfg proof)
      (queryDecoder binary prime P R cfg (H (((E).chain cfg.initialLink).point proof H g.openingIndex.val)).2)
    rw [queryDecoder,← hq]
    exact hv
  have hf' : JointResponse.failure (First).participant (Second).participant
        (parent.statement (derive binary prime P R cfg) H) (cutOracle H (parent.point : Point).context)
        (RuntimeVerifier.batchingDecoder binary prime P R cfg draw (H parent.point).2) response.2 ∨
      NonrecursiveFS.decodedOutsideList (First).backend
        (parent.statement (derive binary prime P R cfg) H).1 (cutOracle H (parent.point : Point).context).1
        (RuntimeVerifier.batchingDecoder binary prime P R cfg draw (H parent.point).2).1 response.2.1 cutoff.1 ∨
      NonrecursiveFS.decodedOutsideList (Second).backend
        (parent.statement (derive binary prime P R cfg) H).2 (cutOracle H (parent.point : Point).context).2
        (RuntimeVerifier.batchingDecoder binary prime P R cfg draw (H parent.point).2).2 response.2.2 cutoff.2 := by
    rw [hs,hcontext,← hc]
    exact hf
  have hcharged := BackendFS.failure_charged (First).participant (Second).participant
    (derive binary prime P R cfg) cutOracle (RuntimeVerifier.batchingDecoder binary prime P R cfg draw)
    (queryDecoder binary prime P R cfg) cutoff epsilon g.batchingIndex_next
    (RuntimeVerifier.encodeResponses binary prime P R cfg) parent response H rfl hv' hf'
  rcases hcharged with h | h | h
  · exact Or.inl (by simpa only [single,BackendOracle.single_point] using h)
  · refine Or.inr (Or.inl ?_)
    rw [hopen]
    simpa only [single,BackendOracle.single_child (First).participant (Second).participant
      g.batchingIndex_next (RuntimeVerifier.encodeResponses binary prime P R cfg)
      (RuntimeVerifier.encodeResponses_injective binary prime P R cfg)] using h
  · exact Or.inr (Or.inr (by simpa only [high,hopen] using h))

end LfzkV2.Current.RuntimeBackend
