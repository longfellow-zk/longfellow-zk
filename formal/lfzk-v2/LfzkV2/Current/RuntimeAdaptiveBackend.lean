import LfzkV2.Current.RuntimeAdaptiveVerifier
import LfzkV2.Current.RuntimeVerifier
import LfzkV2.Current.BackendOracle

/-! Joint-backend charging on the one adaptive runtime path. The affine
statement comes from the bound prefix, while the opening retains both actual
responses and the batching answer's link. -/
noncomputable section
namespace LfzkV2.Current.RuntimeAdaptiveBackend
open Application ApplicationSetup ApplicationOracle RecursivePolygero SumcheckV2
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice Base Key C B Salt Request : Type}
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
local notation "First" => RuntimeVerifier.first binary prime P R cfg
local notation "Second" => RuntimeVerifier.second binary prime P R cfg
local notation "Decoded" => RuntimeVerifier.Decoded binary prime P R cfg
local notation "Output" => RuntimeAdaptiveVerifier.Output (g := g) (fields := fields)
  (Advice := Advice) (Request := Request)
local notation "Parent" => BackendQueries.Parent g.roles Key
  (RuntimeVerifier.Block (g := g) (fields := fields) (Advice := Advice) (Base := Base)) Digest g.batchingIndex
variable (earlier : Request → Replay.Encoding g fields Advice (RuntimeVerifier.Authentication (g := g)) Key
  (RuntimeVerifier.Block (g := g) (fields := fields) (Advice := Advice) (Base := Base)) C)
local notation "encodings" => RuntimeAdaptiveVerifier.encodings binary prime P R cfg earlier
local notation "M" => RuntimeAdaptiveVerifier.chain binary prime P R cfg earlier
variable (hashPublic : Key → Option (Fin binary.nPublic → Bool))
variable (decodePublic : Base → Option (Fin prime.nPublic → N))

def derive (parent : Parent) (past : Fin g.batchingIndex.val → C) :
    JointResponse.Statement (First).participant (Second).participant :=
  ((RuntimeAdaptive.statementAt binary prime P R cfg hashPublic decodePublic parent.point past).map
    (fun data => data.2.statement)).getD (RuntimeVerifier.zeroStatement binary prime P R cfg)

variable (draw : C → RuntimeVerifier.RawSamples binary prime P R cfg)
variable (cutOracle : (RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key) → Digest × C) → Key → JointResponse.Oracle
    (RuntimeVerifier.first binary prime P R cfg).participant (RuntimeVerifier.second binary prime P R cfg).participant)
variable (cutoff : ℕ × ℕ) (epsilon : ℚ)

def authentication (output : Output) (H : Point → Digest × C) (decoded : Decoded) :=
  ZkJoint.authenticate decoded.statement
    (cutOracle H ((encodings output.request).context output.proof)) decoded.coin
    (RuntimeVerifier.responses binary prime P R cfg output.proof) cutoff

def Bad (output : Output) (H : Point → Digest × C) (decoded : Decoded) : Prop :=
  let a := authentication binary prime P R cfg earlier cutOracle cutoff output H decoded
  JointResponse.failure (First).participant (Second).participant a.statement a.oracle a.coin a.response ∨
    NonrecursiveFS.decodedOutsideList (First).backend a.statement.1 a.oracle.1 a.coin.1 a.response.1 cutoff.1 ∨
    NonrecursiveFS.decodedOutsideList (Second).backend a.statement.2 a.oracle.2 a.coin.2 a.response.2 cutoff.2

omit [Fintype C] in
theorem bad_or_collision (output : Output) (H : Point → Digest × C) (decoded : Decoded) :
    (authentication binary prime P R cfg earlier cutOracle cutoff output H decoded).BackendBad ↔
      Bad binary prime P R cfg earlier cutOracle cutoff output H decoded ∨
        (authentication binary prime P R cfg earlier cutOracle cutoff output H decoded).context.Collision := by
  simp only [Authentication.BackendBad,Bad]
  tauto

variable [Inhabited (RuntimeVerifier.Family binary prime P R cfg).Leaf]

omit [Fintype C] in
theorem decoded_statement (output : Output) (H : Point → Digest × C) (decoded : Decoded)
    (hd : RuntimeAdaptiveVerifier.decode binary prime P R cfg earlier hashPublic decodePublic draw output H = some decoded) :
    (BackendPath.parent (encodings output.request) cfg.initialLink output.proof H g.batchingIndex).statement
      (derive binary prime P R cfg hashPublic decodePublic) H = decoded.statement.statement := by
  have hs := (RuntimeAdaptiveVerifier.decode_spec binary prime P R cfg earlier hashPublic decodePublic
    draw output H decoded hd).1
  simp only [BackendQueries.Parent.statement,derive,hs,Option.map_some,Option.getD_some]

omit [Fintype C] [Inhabited (RuntimeVerifier.Family binary prime P R cfg).Leaf] in
theorem opening_eq (output : Output) (H : Point → Digest × C) :
    (M).point output H g.openingIndex.val =
      (BackendPath.parent (encodings output.request) cfg.initialLink output.proof H g.batchingIndex).child
        g.batchingIndex_next (RuntimeVerifier.encodeResponses binary prime P R cfg)
        ((H (BackendPath.parent (encodings output.request) cfg.initialLink output.proof H g.batchingIndex).point).1,
          RuntimeVerifier.responses binary prime P R cfg output.proof) := by
  rw [RuntimeAdaptiveVerifier.point_eq]
  have h := BackendPath.opening_eq (encodings output.request) cfg.initialLink output.proof H
    g.batchingIndex g.batchingIndex_next (RuntimeVerifier.encodeResponses binary prime P R cfg)
    (RuntimeVerifier.responses binary prime P R cfg) (fun past => by
      exact Replay.Encoding.withOpening_block _ _ _ _ _)
  simpa only [g.openingIndex_val] using h

omit [Fintype C] in
/-- The accepted joint arithmetic, on its one recovered oracle, is covered
by rank, opening or the linked full-response pair event. -/
theorem failure_charged (output : Output) (H : Point → Digest × C) (decoded : Decoded)
    (hd : RuntimeAdaptiveVerifier.decode binary prime P R cfg earlier hashPublic decodePublic draw output H = some decoded)
    (hv : let a := authentication binary prime P R cfg earlier cutOracle cutoff output H decoded
      JointResponse.Verify (First).participant (Second).participant a.statement a.oracle a.coin a.response decoded.query)
    (hf : Bad binary prime P R cfg earlier cutOracle cutoff output H decoded) :
    let parent := BackendPath.parent (encodings output.request) cfg.initialLink output.proof H g.batchingIndex
    let response := ((H parent.point).1,RuntimeVerifier.responses binary prime P R cfg output.proof)
    1 ≤ BackendFS.rank (First).participant (Second).participant cutOracle
        (RuntimeVerifier.batchingDecoder binary prime P R cfg draw) parent H (H parent.point) ∨
      1 ≤ BackendFS.opening (First).participant (Second).participant (derive binary prime P R cfg hashPublic decodePublic)
        cutOracle (RuntimeVerifier.batchingDecoder binary prime P R cfg draw)
        (RuntimeVerifier.queryDecoder binary prime P R cfg) cutoff epsilon parent response H
        (H ((M).point output H g.openingIndex.val)) ∨
      1 ≤ BackendFS.high (First).participant (Second).participant (derive binary prime P R cfg hashPublic decodePublic)
        cutOracle (RuntimeVerifier.batchingDecoder binary prime P R cfg draw)
        (RuntimeVerifier.queryDecoder binary prime P R cfg) epsilon parent response H
        (H parent.point) (H ((M).point output H g.openingIndex.val)) := by
  let parent := BackendPath.parent (encodings output.request) cfg.initialLink output.proof H g.batchingIndex
  let response := ((H parent.point).1,RuntimeVerifier.responses binary prime P R cfg output.proof)
  have hs := decoded_statement binary prime P R cfg earlier hashPublic decodePublic draw output H decoded hd
  have spec := RuntimeAdaptiveVerifier.decode_spec binary prime P R cfg earlier hashPublic decodePublic draw output H decoded hd
  have hc := spec.2.2.1
  have hq : decoded.query = RuntimeVerifier.queryDecoder binary prime P R cfg
      (H ((M).point output H g.openingIndex.val)).2 := by
    simpa only [RuntimeVerifier.queryDecoder,RuntimeAdaptiveVerifier.point_eq] using spec.2.2.2
  have hopen := opening_eq binary prime P R cfg earlier output H
  have hcontext := BackendPath.parent_context (encodings output.request) cfg.initialLink output.proof H g.batchingIndex
  have hv' : JointResponse.Verify (First).participant (Second).participant
      (parent.statement (derive binary prime P R cfg hashPublic decodePublic) H)
      (cutOracle H (parent.point : Point).context)
      (RuntimeVerifier.batchingDecoder binary prime P R cfg draw (H parent.point).2) response.2
      (RuntimeVerifier.queryDecoder binary prime P R cfg (H (parent.child g.batchingIndex_next
        (RuntimeVerifier.encodeResponses binary prime P R cfg) response)).2) := by
    rw [hs,hcontext,← hc,← hopen,← hq]
    exact hv
  have hf' : JointResponse.failure (First).participant (Second).participant
        (parent.statement (derive binary prime P R cfg hashPublic decodePublic) H)
        (cutOracle H (parent.point : Point).context)
        (RuntimeVerifier.batchingDecoder binary prime P R cfg draw (H parent.point).2) response.2 ∨
      NonrecursiveFS.decodedOutsideList (First).backend
        (parent.statement (derive binary prime P R cfg hashPublic decodePublic) H).1
        (cutOracle H (parent.point : Point).context).1
        (RuntimeVerifier.batchingDecoder binary prime P R cfg draw (H parent.point).2).1 response.2.1 cutoff.1 ∨
      NonrecursiveFS.decodedOutsideList (Second).backend
        (parent.statement (derive binary prime P R cfg hashPublic decodePublic) H).2
        (cutOracle H (parent.point : Point).context).2
        (RuntimeVerifier.batchingDecoder binary prime P R cfg draw (H parent.point).2).2 response.2.2 cutoff.2 := by
    rw [hs,hcontext,← hc]
    exact hf
  have h := BackendFS.failure_charged (First).participant (Second).participant
    (derive binary prime P R cfg hashPublic decodePublic) cutOracle
    (RuntimeVerifier.batchingDecoder binary prime P R cfg draw) (RuntimeVerifier.queryDecoder binary prime P R cfg)
    cutoff epsilon g.batchingIndex_next (RuntimeVerifier.encodeResponses binary prime P R cfg)
    parent response H rfl hv' hf'
  rcases h with h | h | h
  · exact Or.inl h
  · refine Or.inr (Or.inl ?_)
    rw [hopen]
    exact h
  · refine Or.inr (Or.inr ?_)
    rw [hopen]
    exact h

end LfzkV2.Current.RuntimeAdaptiveBackend
