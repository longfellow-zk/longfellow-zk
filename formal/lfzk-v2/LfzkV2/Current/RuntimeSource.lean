import LfzkV2.Current.RuntimeVerifier
import LfzkV2.Current.ApplicationViews

/-! The runtime's selected witness source, sampler laws and decoded affine
statement. Layouts and selected parameters are reconstructed from the actual
decoded application; accepted-failure coverage lives in `Soundness.FailureCover`. -/
noncomputable section
namespace LfzkV2.Current.RuntimeSource
open Application ApplicationSetup ApplicationViews ApplicationOracle RecursivePolygero SumcheckV2
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice Base Key C B Salt Enc : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B] [Fintype C]
variable {shared maskBits adviceBits k s n t : ℕ}
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable (binary : BinaryPublic B shared maskBits adviceBits)
variable (prime : PrimePublic N shared)
variable (P : FieldBackend B k s n t) (R : FieldBackend N k s n t)
variable (cfg : RuntimeVerifier.Public (g := g) binary prime P R (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key) (C := C) (Salt := Salt))

local notation "Pair" => Selection.Pair B N binary.Original prime.Original
local notation "Point" => RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key)
local notation "Output" => RuntimeVerifier.Output (g := g) (fields := fields) (Advice := Advice)
local notation "Decoded" => RuntimeVerifier.Decoded binary prime P R cfg
local notation "First" => RuntimeVerifier.first binary prime P R cfg
local notation "Second" => RuntimeVerifier.second binary prime P R cfg
local notation "Generator" => cfg.polynomialX^Adapter.Mdoc.generatorExponent

section Queries
open ApplicationCharging Counting Finset
variable {Oracle : Type}

abbrev Source := SelectionSource g.roles Key
  (RuntimeVerifier.Block (g := g) (fields := fields) (Advice := Advice) (Base := Base))
  Digest (Body g fields Advice (RuntimeVerifier.Authentication (g := g))) C Oracle
  B N binary.Original prime.Original

/-- Ideal sampling laws at the actual runtime boundaries. Every dimension
is fixed by public circuit/layout data; no sampler for arbitrary row lists
or unbounded assertion blocks is requested. -/
structure SamplerLaws (S : Source (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key) (C := C) binary prime (Oracle := Oracle)) where
  primeCapacity : ℕ
  binaryCapacity : ℕ
  primeDecoder : FrontendReplay.Decoder primeCapacity cfg.primeDecode cfg.primeNonzero
  binaryDecoder : FrontendReplay.Decoder binaryCapacity cfg.binaryDecode cfg.binaryNonzero
  rescaleDecoder : BalancedDecoder C (Linear.TerminalSampling.Nonzero N)
  rescale_agrees : rescaleDecoder.decode = cfg.primeNonzero
  conversionDecoder : BalancedDecoder C (Linear.TerminalSampling.Nonzero N × Linear.TerminalSampling.Nonzero N)
  conversion_agrees : ∀ answer, conversionDecoder.decode answer =
    (cfg.conversion answer 0,cfg.conversion answer 1)
  packingDecoder : BalancedDecoder C (Fin binary.degree → B)
  packing_agrees : ∀ answer i, packingDecoder.decode answer i = cfg.binaryDecode answer i.val
  binarySelectionDecoder : BalancedDecoder C (WitnessSelection.Coins B binary.Original)
  primeSelectionDecoder : BalancedDecoder C (WitnessSelection.Coins N prime.Original)
  binarySelection_agrees : ∀ answer, binarySelectionDecoder.decode answer = (S.coins answer).1
  primeSelection_agrees : ∀ answer, primeSelectionDecoder.decode answer = (S.coins answer).2
  bits_le : shared+maskBits ≤ Adapter.Mdoc.quotientBound

end Queries

section CanonicalSelection

/-- Read the fingerprint responses from the actual current block. The
zk-v2 selection wrapper restricts this reader to the bound rank-one prefix. -/
def fingerprintResponses (point : Point) : (B × B) × (N × N) :=
  (((point.block).bind fun block => block.2.fingerprints).map fun targets =>
    ((cfg.binaryField targets.1.1,cfg.binaryField targets.1.2),
      (cfg.primeField targets.2.1,cfg.primeField targets.2.2))).getD ((0,0),(0,0))

/-- The selected-field views use exactly the canonical full-cell maps used
by the late statement compiler. Both fields belong to zk-v2's one joint
selection exchange, before either frontend starts. -/
def selectedParam
    (layout : StatementCompiler.Addresses P R binary.cells prime.remaining prime.pads)
    (cutoff : ℕ × ℕ) :
    ZkJoint.JointParam (First).participant (Second).participant binary.Original prime.Original Key :=
  StatementCompiler.selected P R layout cfg.countBinary cfg.countPrime cutoff.1 cutoff.2
    (CellLayout.selected binary.cells) (CellLayout.Prime.layout prime.remaining prime.pads)

def source
    (layout : StatementCompiler.Addresses P R binary.cells prime.remaining prime.pads)
    (cutoff : ℕ × ℕ)
    (cutOracle : (Point → Digest × C) → Key → JointResponse.Oracle (First).participant (Second).participant)
    (cutOff : ∀ point H H', Bcs.TotalOracle.AgreeOff point H H' →
      cutOracle H point.context = cutOracle H' point.context) :
    Source (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key) (C := C)
      binary prime (Oracle := JointResponse.Oracle (First).participant (Second).participant) :=
  (selectedParam binary prime P R cfg layout cutoff).source
    (fun answer => (cfg.fingerprintBinary answer,cfg.fingerprintPrime answer))
    (fingerprintResponses (B := B) binary prime P R cfg) ((0,0),(0,0)) cutOracle cutOff

omit [Fintype C] in
/-- Successful application reconstruction fixes both public cell maps. -/
theorem decoded_layouts (nd : PrimeData prime C) (bd : BinaryData binary nd Generator)
    (A : RuntimeVerifier.System binary prime (C := C))
    (h : ApplicationSetup.decodeChecked binary prime nd cfg.card cfg.polynomialX cfg.quotientBound bd = some A) :
    A.binaryLayout = CellLayout.selected binary.cells ∧
      A.primeLayout = CellLayout.Prime.layout prime.remaining prime.pads := by
  unfold ApplicationSetup.decodeChecked at h
  split at h
  · unfold ApplicationSetup.decode at h
    split at h
    · cases Option.some.inj h
      exact ⟨rfl,rfl⟩
    · contradiction
  · contradiction

omit [Fintype C] [DecidableEq B] in
/-- The response reader is exactly the pair already bound at rank one;
there is no later statement-identifier query or mutable response source. -/
theorem fingerprintResponses_at (point : Point)
    (targets : (fields .binary × fields .binary) × (fields .prime × fields .prime))
    (h : point.readAt g.primeStart (fun block => block.2.fingerprints) = some targets) :
    Selection.responsesAt (fingerprintResponses (B := B) binary prime P R cfg) ((0,0),(0,0)) point =
      ((cfg.binaryField targets.1.1,cfg.binaryField targets.1.2),
        (cfg.primeField targets.2.1,cfg.primeField targets.2.2)) := by
  unfold Input.readAt at h
  change ((point.atRank 1).bind Input.block).bind (fun block => block.2.fingerprints) = some targets at h
  unfold Selection.responsesAt
  cases hp : point.atRank 1 with
  | none => simp only [hp,Option.bind_none] at h; contradiction
  | some previous =>
      cases hb : previous.block with
      | none => simp only [hp,hb,Option.bind_some,Option.bind_none] at h; contradiction
      | some block =>
          simp only [hp,hb,Option.bind_some] at h
          simp only [Option.map_some,Option.getD_some,fingerprintResponses,hb,Option.bind_some,h,
            Option.map_some,Option.getD_some]

omit [Fintype C] in
/-- Compiling the authenticated rows preserves exactly the early selection
context, including both physical full-cell projections and both responses. -/
theorem compiled_context
    (layout : StatementCompiler.Addresses P R binary.cells prime.remaining prime.pads)
    (nd : PrimeData prime C) (bd : BinaryData binary nd Generator)
    (A : RuntimeVerifier.System binary prime (C := C))
    (hA : ApplicationSetup.decodeChecked binary prime nd cfg.card cfg.polynomialX cfg.quotientBound bd = some A)
    (data : StatementData A First Second) (fingerprint : C)
    (targetsB : B × B) (targetsN : N × N)
    (hdata : StatementCompiler.compile P R A layout cfg.countBinary cfg.countPrime
      (cfg.fingerprintBinary fingerprint) (cfg.fingerprintPrime fingerprint) targetsB targetsN = some data)
    (W : JointResponse.Oracle (First).participant (Second).participant)
    (coin : JointResponse.Coin (First).participant (Second).participant)
    (response : JointResponse.Response (First).participant (Second).participant)
    (cutoff : ℕ × ℕ) (key : Key) :
    (ZkJoint.authenticate data W coin response cutoff).context =
      Selection.Context.mk
        ((RecursivePolygero.Counting.committedCandidates (First).backend W.1 cutoff.1).image
          ((selectedParam binary prime P R cfg layout cutoff).first.view key))
        ((RecursivePolygero.Counting.committedCandidates (Second).backend W.2 cutoff.2).image
          ((selectedParam binary prime P R cfg layout cutoff).second.view key))
        (cfg.fingerprintBinary fingerprint) (cfg.fingerprintPrime fingerprint) targetsB targetsN := by
  have hl := decoded_layouts binary prime P R cfg nd bd A hA
  have hd := StatementCompiler.compile_fields P R A layout cfg.countBinary cfg.countPrime
    (cfg.fingerprintBinary fingerprint) (cfg.fingerprintPrime fingerprint) targetsB targetsN data hdata
  unfold Application.Authentication.context ZkJoint.authenticate
  simp only [hd.1,hd.2.1,hd.2.2.1,hd.2.2.2.1,hd.2.2.2.2.1,hd.2.2.2.2.2,hl.1,hl.2]
  rfl

omit [Fintype C] in
theorem binarySelection_eq
    (layout : StatementCompiler.Addresses P R binary.cells prime.remaining prime.pads)
    (cutoff : ℕ × ℕ)
    (cutOracle : (Point → Digest × C) → Key → JointResponse.Oracle (First).participant (Second).participant)
    (cutOff : ∀ point H H', Bcs.TotalOracle.AgreeOff point H H' →
      cutOracle H point.context = cutOracle H' point.context)
    (point : Point) (H : Point → Digest × C) (answer : C) :
    (RuntimeSource.source binary prime P R cfg layout cutoff cutOracle cutOff).binarySelection point H answer ↔
      cfg.fingerprintBinary answer ∈ WitnessSelection.badCoins
        ((Counting.committedCandidates (First).backend (cutOracle H point.context).1 cutoff.1).image
          ((RuntimeSource.selectedParam binary prime P R cfg layout cutoff).first.view point.context)) := by
  simp only [ApplicationOracle.SelectionSource.binarySelection,RuntimeSource.source,ZkJoint.JointParam.source,
    RuntimeSource.selectedParam,StatementCompiler.selected,WitnessSelection.badCoins,Finset.mem_filter,
    Finset.mem_univ,true_and]
  constructor
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩
  · intro h
    exact (Finset.mem_filter.mp h).2

omit [Fintype C] in
theorem primeSelection_eq
    (layout : StatementCompiler.Addresses P R binary.cells prime.remaining prime.pads)
    (cutoff : ℕ × ℕ)
    (cutOracle : (Point → Digest × C) → Key → JointResponse.Oracle (First).participant (Second).participant)
    (cutOff : ∀ point H H', Bcs.TotalOracle.AgreeOff point H H' →
      cutOracle H point.context = cutOracle H' point.context)
    (point : Point) (H : Point → Digest × C) (answer : C) :
    (RuntimeSource.source binary prime P R cfg layout cutoff cutOracle cutOff).primeSelection point H answer ↔
      cfg.fingerprintPrime answer ∈ WitnessSelection.badCoins
        ((Counting.committedCandidates (Second).backend (cutOracle H point.context).2 cutoff.2).image
          ((RuntimeSource.selectedParam binary prime P R cfg layout cutoff).second.view point.context)) := by
  simp only [ApplicationOracle.SelectionSource.primeSelection,RuntimeSource.source,ZkJoint.JointParam.source,
    RuntimeSource.selectedParam,StatementCompiler.selected,WitnessSelection.badCoins,Finset.mem_filter,
    Finset.mem_univ,true_and]
  constructor
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩
  · intro h
    exact (Finset.mem_filter.mp h).2


end CanonicalSelection

end LfzkV2.Current.RuntimeSource
