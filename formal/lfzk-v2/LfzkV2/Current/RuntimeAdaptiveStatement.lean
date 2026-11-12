import LfzkV2.Current.RuntimeAdaptive
import LfzkV2.Current.RuntimeSelection

/-! The adaptive prefix statement authenticates the same early selected cells.
Public values are parsed where bound; layouts and fingerprint equations are
constructed from the fixed topology, with no execution certificate. -/
noncomputable section
namespace LfzkV2.Current.RuntimeAdaptiveStatement
open RuntimeAdaptive RuntimeCover Application ApplicationSetup ApplicationViews ApplicationOracle RecursivePolygero SumcheckV2
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice Base Key C B Salt : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
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

variable (hashPublic : Key → Option (Fin binary.nPublic → Bool))
variable (decodePublic : Base → Option (Fin prime.nPublic → N))

theorem statementAt_spec (point : Point) (past : Fin point.rank → C)
    (data : Σ A : RuntimeVerifier.System binary prime (C := C), StatementData A First Second)
    (h : RuntimeAdaptive.statementAt binary prime P R cfg hashPublic decodePublic point past = some data) :
    RuntimeAdaptive.application binary prime P R cfg hashPublic decodePublic point past = some data.1 ∧
    ∃ layout fingerprint targets,
      StatementCompiler.addresses P R binary.cells prime.remaining prime.pads = some layout ∧
      ApplicationPrefix.strictAnswer point past 0 = some fingerprint ∧
      point.readAt g.primeStart (fun block => block.2.fingerprints) = some targets ∧
      StatementCompiler.compile P R data.1 layout cfg.countBinary cfg.countPrime
        (cfg.fingerprintBinary fingerprint) (cfg.fingerprintPrime fingerprint)
        (cfg.binaryField targets.1.1,cfg.binaryField targets.1.2)
        (cfg.primeField targets.2.1,cfg.primeField targets.2.2) = some data.2 := by
  simp only [RuntimeAdaptive.statementAt,Option.bind_eq_bind,Option.bind_eq_some_iff] at h
  obtain ⟨A,hA,layout,hlayout,fingerprint,hfingerprint,targets,htargets,statement,hstatement,hresult⟩ := h
  cases Option.some.inj hresult
  exact ⟨hA,layout,fingerprint,targets,hlayout,hfingerprint,htargets,hstatement⟩

theorem application_layouts (point : Point) (past : Fin point.rank → C)
    (A : RuntimeVerifier.System binary prime (C := C))
    (h : RuntimeAdaptive.application binary prime P R cfg hashPublic decodePublic point past = some A) :
    A.binaryLayout = CellLayout.selected binary.cells ∧
      A.primeLayout = CellLayout.Prime.layout prime.remaining prime.pads := by
  obtain ⟨bits,inputs,_,_,happlication⟩ :=
    RuntimeAdaptive.application_spec binary prime P R cfg hashPublic decodePublic point past A h
  obtain ⟨nd,bd,_,_,hsetup⟩ := ApplicationPrefix.decodeChecked_spec (binaryWithBits binary bits)
    (primeWithInputs prime inputs) cfg.card cfg.polynomialX cfg.quotientBound cfg.packingDegree
    cfg.binaryField cfg.primeField cfg.binaryDecode cfg.binaryNonzero cfg.primeDecode cfg.primeNonzero
    cfg.conversion cfg.advice cfg.fallback point past A happlication
  unfold ApplicationSetup.decodeChecked at hsetup
  split at hsetup
  · unfold ApplicationSetup.decode at hsetup
    split at hsetup
    · cases Option.some.inj hsetup
      exact ⟨rfl,rfl⟩
    · contradiction
  · contradiction

theorem compiled_context
    (point : Point) (past : Fin point.rank → C)
    (layout : StatementCompiler.Addresses P R binary.cells prime.remaining prime.pads)
    (A : RuntimeVerifier.System binary prime (C := C))
    (hA : RuntimeAdaptive.application binary prime P R cfg hashPublic decodePublic point past = some A)
    (data : StatementData A First Second) (fingerprint : C) (targetsB : B × B) (targetsN : N × N)
    (hdata : StatementCompiler.compile P R A layout cfg.countBinary cfg.countPrime
      (cfg.fingerprintBinary fingerprint) (cfg.fingerprintPrime fingerprint) targetsB targetsN = some data)
    (W : JointResponse.Oracle (First).participant (Second).participant)
    (coin : JointResponse.Coin (First).participant (Second).participant)
    (response : JointResponse.Response (First).participant (Second).participant)
    (cutoff : ℕ × ℕ) (key : Key) :
    (ZkJoint.authenticate data W coin response cutoff).context =
      Selection.Context.mk
        ((Counting.committedCandidates (First).backend W.1 cutoff.1).image
          ((RuntimeCover.selectedParam binary prime P R cfg layout cutoff).first.view key))
        ((Counting.committedCandidates (Second).backend W.2 cutoff.2).image
          ((RuntimeCover.selectedParam binary prime P R cfg layout cutoff).second.view key))
        (cfg.fingerprintBinary fingerprint) (cfg.fingerprintPrime fingerprint) targetsB targetsN := by
  have hl := application_layouts binary prime P R cfg hashPublic decodePublic point past A hA
  have hd := StatementCompiler.compile_fields P R A layout cfg.countBinary cfg.countPrime
    (cfg.fingerprintBinary fingerprint) (cfg.fingerprintPrime fingerprint) targetsB targetsN data hdata
  unfold Application.Authentication.context ZkJoint.authenticate
  simp only [hd.1,hd.2.1,hd.2.2.1,hd.2.2.2.1,hd.2.2.2.2.1,hd.2.2.2.2.2,hl.1,hl.2]
  rfl

theorem selected_of_statement
    (layout : StatementCompiler.Addresses P R binary.cells prime.remaining prime.pads)
    (hlayout : StatementCompiler.addresses P R binary.cells prime.remaining prime.pads = some layout)
    (cutoff : ℕ × ℕ)
    (cutOracle : (Point → Digest × C) → Key → JointResponse.Oracle (First).participant (Second).participant)
    (cutOff : ∀ point H H', Bcs.TotalOracle.AgreeOff point H H' →
      cutOracle H point.context = cutOracle H' point.context)
    (point : Point) (H : Point → Digest × C)
    (data : Σ A : RuntimeVerifier.System binary prime (C := C), StatementData A First Second)
    (hdata : RuntimeAdaptive.statementAt binary prime P R cfg hashPublic decodePublic point (point.priorAnswers H) = some data)
    (coin : JointResponse.Coin (First).participant (Second).participant)
    (response : JointResponse.Response (First).participant (Second).participant) :
    (RuntimeCover.source binary prime P R cfg layout cutoff cutOracle cutOff).selected point H =
      (ZkJoint.authenticate data.2 (cutOracle H point.context) coin response cutoff).context.extract := by
  have hs := statementAt_spec binary prime P R cfg hashPublic decodePublic point (point.priorAnswers H) data hdata
  obtain ⟨layout',fingerprint,targets,hlayout',hfingerprint,htargets,hcompile⟩ := hs.2
  have he : layout' = layout := Option.some.inj (hlayout'.symm.trans hlayout)
  subst layout'
  have hpos : 0 < point.rank := by
    unfold ApplicationPrefix.strictAnswer at hfingerprint
    split_ifs at hfingerprint with hpos
    exact hpos
  have hfp : point.priorAnswers H ⟨0,hpos⟩ = fingerprint := by
    unfold ApplicationPrefix.strictAnswer at hfingerprint
    simpa only [dif_pos hpos,Option.some.injEq] using hfingerprint
  have hresponse := RuntimeCover.fingerprintResponses_at binary prime P R cfg point targets htargets
  have hcontext := compiled_context binary prime P R cfg hashPublic decodePublic point (point.priorAnswers H) layout data.1 hs.1 data.2
    fingerprint (cfg.binaryField targets.1.1,cfg.binaryField targets.1.2)
    (cfg.primeField targets.2.1,cfg.primeField targets.2.2) hcompile
    (cutOracle H point.context) coin response cutoff point.context
  rw [hcontext]
  unfold RuntimeCover.source ZkJoint.JointParam.source ApplicationOracle.SelectionSource.selected Selection.atPoint
  rw [dif_pos hpos]
  simp only [hfp]
  exact congrArg (fun target : (B × B) × (N × N) =>
    (Selection.Context.mk
      ((Counting.committedCandidates (First).backend (cutOracle H point.context).1 cutoff.1).image
        ((selectedParam binary prime P R cfg layout cutoff).first.view point.context))
      ((Counting.committedCandidates (Second).backend (cutOracle H point.context).2 cutoff.2).image
        ((selectedParam binary prime P R cfg layout cutoff).second.view point.context))
      (cfg.fingerprintBinary fingerprint) (cfg.fingerprintPrime fingerprint) target.1 target.2).extract) hresponse


theorem selected_replay_same
    (layout : StatementCompiler.Addresses P R binary.cells prime.remaining prime.pads)
    (cutoff : ℕ × ℕ)
    (cutOracle : (Point → Digest × C) → Key → JointResponse.Oracle (First).participant (Second).participant)
    (cutOff : ∀ point H H', Bcs.TotalOracle.AgreeOff point H H' →
      cutOracle H point.context = cutOracle H' point.context)
    (e : Replay.Encoding g fields Advice (RuntimeVerifier.Authentication (g := g)) Key
      (Base × ProtocolWrites.Fresh g fields Advice) C)
    (initialLink : Digest) (proof : Output) (H : Point → Digest × C) (n m : ℕ)
    (hn : n ≤ g.roles.length) (hm : m ≤ g.roles.length) (hpn : 0 < n) (hpm : 0 < m) :
    (RuntimeCover.source binary prime P R cfg layout cutoff cutOracle cutOff).selected
        ((e.chain initialLink).point proof H n) H =
      (RuntimeCover.source binary prime P R cfg layout cutoff cutOracle cutOff).selected
        ((e.chain initialLink).point proof H m) H := by
  exact Selection.atPoint_replay_same e initialLink proof H
    (RuntimeCover.source binary prime P R cfg layout cutoff cutOracle cutOff).lists
    (fun answer => (cfg.fingerprintBinary answer,cfg.fingerprintPrime answer))
    (RuntimeCover.fingerprintResponses (B := B) binary prime P R cfg) ((0,0),(0,0)) cutOracle n m hn hm hpn hpm

/-- The global prefix reader authenticates the one early-selected pair on
all later points, even when prime-field public inputs were chosen after FP. -/
theorem selected_on_replay
    (layout : StatementCompiler.Addresses P R binary.cells prime.remaining prime.pads)
    (hlayout : StatementCompiler.addresses P R binary.cells prime.remaining prime.pads = some layout)
    (cutoff : ℕ × ℕ)
    (cutOracle : (Point → Digest × C) → Key → JointResponse.Oracle (First).participant (Second).participant)
    (cutOff : ∀ point H H', Bcs.TotalOracle.AgreeOff point H H' →
      cutOracle H point.context = cutOracle H' point.context)
    (e : Replay.Encoding g fields Advice (RuntimeVerifier.Authentication (g := g)) Key
      (Base × ProtocolWrites.Fresh g fields Advice) C)
    (initialLink : Digest) (proof : Output) (H : Point → Digest × C) (n m : ℕ)
    (hn : n ≤ g.roles.length) (hm : m ≤ g.roles.length) (hpn : 0 < n) (hpm : 0 < m)
    (data : Σ A : RuntimeVerifier.System binary prime (C := C), StatementData A First Second)
    (hdata : RuntimeAdaptive.statementAt binary prime P R cfg hashPublic decodePublic
      ((e.chain initialLink).point proof H m) (((e.chain initialLink).point proof H m).priorAnswers H) = some data)
    (coin : JointResponse.Coin (First).participant (Second).participant)
    (response : JointResponse.Response (First).participant (Second).participant) :
    (RuntimeCover.source binary prime P R cfg layout cutoff cutOracle cutOff).selected
        ((e.chain initialLink).point proof H n) H =
      (ZkJoint.authenticate data.2 (cutOracle H (e.context proof)) coin response cutoff).context.extract := by
  have hsame := selected_replay_same binary prime P R cfg layout cutoff cutOracle cutOff
    e initialLink proof H n m hn hm hpn hpm
  have hselected := selected_of_statement binary prime P R cfg hashPublic decodePublic layout hlayout cutoff
    cutOracle cutOff _ H data hdata coin response
  rw [e.point_context initialLink proof H m] at hselected
  exact hsame.trans hselected

theorem collision_of_statement
    (layout : StatementCompiler.Addresses P R binary.cells prime.remaining prime.pads)
    (hlayout : StatementCompiler.addresses P R binary.cells prime.remaining prime.pads = some layout)
    (cutoff : ℕ × ℕ)
    (cutOracle : (Point → Digest × C) → Key → JointResponse.Oracle (First).participant (Second).participant)
    (cutOff : ∀ point H H', Bcs.TotalOracle.AgreeOff point H H' →
      cutOracle H point.context = cutOracle H' point.context)
    (point : Point) (H : Point → Digest × C)
    (data : Σ A : RuntimeVerifier.System binary prime (C := C), StatementData A First Second)
    (hdata : RuntimeAdaptive.statementAt binary prime P R cfg hashPublic decodePublic point (point.priorAnswers H) = some data)
    (coin : JointResponse.Coin (First).participant (Second).participant)
    (response : JointResponse.Response (First).participant (Second).participant)
    (fingerprint : C)
    (hfp : ApplicationPrefix.strictAnswer point (point.priorAnswers H) 0 = some fingerprint)
    (hcollision : (ZkJoint.authenticate data.2 (cutOracle H point.context) coin response cutoff).context.Collision) :
    (RuntimeCover.source binary prime P R cfg layout cutoff cutOracle cutOff).binarySelection point H fingerprint ∨
      (RuntimeCover.source binary prime P R cfg layout cutoff cutOracle cutOff).primeSelection point H fingerprint := by
  have hs := statementAt_spec binary prime P R cfg hashPublic decodePublic point (point.priorAnswers H) data hdata
  obtain ⟨layout',fingerprint',targets,hlayout',hfingerprint,htargets,hcompile⟩ := hs.2
  have he : layout' = layout := Option.some.inj (hlayout'.symm.trans hlayout)
  subst layout'
  have hf : fingerprint' = fingerprint := Option.some.inj (hfingerprint.symm.trans hfp)
  subst fingerprint'
  have hcontext := compiled_context binary prime P R cfg hashPublic decodePublic point
    (point.priorAnswers H) layout data.1 hs.1 data.2 fingerprint
    (cfg.binaryField targets.1.1,cfg.binaryField targets.1.2)
    (cfg.primeField targets.2.1,cfg.primeField targets.2.2) hcompile
    (cutOracle H point.context) coin response cutoff point.context
  rw [RuntimeSelection.binarySelection_eq binary prime P R cfg layout cutoff cutOracle cutOff,
    RuntimeSelection.primeSelection_eq binary prime P R cfg layout cutoff cutOracle cutOff]
  rw [hcontext] at hcollision
  exact hcollision

theorem collision_on_replay
    (layout : StatementCompiler.Addresses P R binary.cells prime.remaining prime.pads)
    (hlayout : StatementCompiler.addresses P R binary.cells prime.remaining prime.pads = some layout)
    (cutoff : ℕ × ℕ)
    (cutOracle : (Point → Digest × C) → Key → JointResponse.Oracle (First).participant (Second).participant)
    (cutOff : ∀ point H H', Bcs.TotalOracle.AgreeOff point H H' →
      cutOracle H point.context = cutOracle H' point.context)
    (e : Replay.Encoding g fields Advice (RuntimeVerifier.Authentication (g := g)) Key
      (Base × ProtocolWrites.Fresh g fields Advice) C)
    (initialLink : Digest) (proof : Output) (H : Point → Digest × C) (m : ℕ)
    (hm : m ≤ g.roles.length) (hpm : 0 < m)
    (data : Σ A : RuntimeVerifier.System binary prime (C := C), StatementData A First Second)
    (hdata : RuntimeAdaptive.statementAt binary prime P R cfg hashPublic decodePublic
      ((e.chain initialLink).point proof H m) (((e.chain initialLink).point proof H m).priorAnswers H) = some data)
    (coin : JointResponse.Coin (First).participant (Second).participant)
    (response : JointResponse.Response (First).participant (Second).participant)
    (hcollision : (ZkJoint.authenticate data.2 (cutOracle H (e.context proof)) coin response cutoff).context.Collision) :
    let point := (e.chain initialLink).point proof H 0
    (RuntimeCover.source binary prime P R cfg layout cutoff cutOracle cutOff).binarySelection point H (H point).2 ∨
      (RuntimeCover.source binary prime P R cfg layout cutoff cutOracle cutOff).primeSelection point H (H point).2 := by
  let point := (e.chain initialLink).point proof H m
  have hfp := ApplicationViewReplay.strictAnswer_replay e initialLink proof H m 0 hm hpm
  have hcol : (ZkJoint.authenticate data.2 (cutOracle H point.context) coin response cutoff).context.Collision := by
    simpa only [point,e.point_context initialLink proof H m] using hcollision
  have hbad := collision_of_statement binary prime P R cfg hashPublic decodePublic layout hlayout cutoff
    cutOracle cutOff point H data hdata coin response (H ((e.chain initialLink).point proof H 0)).2 hfp hcol
  simpa only [ApplicationOracle.SelectionSource.binarySelection,ApplicationOracle.SelectionSource.primeSelection,
    point,e.point_context initialLink proof H m,e.point_context initialLink proof H 0] using hbad

end LfzkV2.Current.RuntimeAdaptiveStatement
