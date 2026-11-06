import LfzkV2.Current.RuntimeCover
import LfzkV2.Current.ApplicationViewReplay

/-! Canonical early witness selection agrees with the rows reconstructed by
the actual late runtime statement decoder. -/
noncomputable section
namespace LfzkV2.Current.RuntimeSelection
open RuntimeCover Application ApplicationSetup ApplicationViews ApplicationOracle RecursivePolygero SumcheckV2
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
local notation "Generator" => cfg.generator^Adapter.Mdoc.generatorExponent

variable [Inhabited (RuntimeVerifier.Family binary prime P R cfg).Leaf]

omit [Fintype C] [Inhabited (RuntimeVerifier.Family binary prime P R cfg).Leaf] in
theorem selected_of_statement
    (layout : StatementCompiler.Addresses P R binary.cells prime.remaining prime.pads)
    (hlayout : StatementCompiler.addresses P R binary.cells prime.remaining prime.pads = some layout)
    (cutoff : ℕ × ℕ)
    (cutOracle : (Point → Digest × C) → Key → JointResponse.Oracle (First).participant (Second).participant)
    (cutOff : ∀ point H H', Bcs.TotalOracle.AgreeOff point H H' →
      cutOracle H point.context = cutOracle H' point.context)
    (point : Point) (H : Point → Digest × C)
    (data : Σ A : RuntimeVerifier.System binary prime (C := C), StatementData A First Second)
    (hdata : RuntimeVerifier.statementAt binary prime P R cfg point (point.priorAnswers H) = some data)
    (coin : JointResponse.Coin (First).participant (Second).participant)
    (response : JointResponse.Response (First).participant (Second).participant) :
    (RuntimeCover.source binary prime P R cfg layout cutoff cutOracle cutOff).selected point H =
      (ZkJoint.authenticate data.2 (cutOracle H point.context) coin response cutoff).context.extract := by
  have hs := RuntimeVerifier.statementAt_spec binary prime P R cfg point (point.priorAnswers H) data hdata
  obtain ⟨layout',fingerprint,targets,hlayout',hfingerprint,htargets,hcompile⟩ := hs.2
  have he : layout' = layout := Option.some.inj (hlayout'.symm.trans hlayout)
  subst layout'
  obtain ⟨nd,bd,hprime,hbinary,hsetup⟩ :=
    ApplicationPrefix.decodeChecked_spec binary prime cfg.card cfg.generator cfg.quotientBound
      cfg.packingDegree cfg.binaryField cfg.primeField cfg.binaryDecode cfg.binaryNonzero
      cfg.primeDecode cfg.primeNonzero cfg.conversion cfg.advice cfg.fallback _ _ _ hs.1
  have hpos : 0 < point.rank := by
    unfold ApplicationPrefix.strictAnswer at hfingerprint
    split_ifs at hfingerprint with hpos
    exact hpos
  have hfp : point.priorAnswers H ⟨0,hpos⟩ = fingerprint := by
    unfold ApplicationPrefix.strictAnswer at hfingerprint
    simpa only [dif_pos hpos,Option.some.injEq] using hfingerprint
  have hresponse := RuntimeCover.fingerprintResponses_at binary prime P R cfg point targets htargets
  have hcontext := RuntimeCover.compiled_context binary prime P R cfg layout nd bd data.1 hsetup data.2
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

omit [Fintype C] [Inhabited (RuntimeVerifier.Family binary prime P R cfg).Leaf] in
theorem selected_replay_same
    (layout : StatementCompiler.Addresses P R binary.cells prime.remaining prime.pads)
    (cutoff : ℕ × ℕ)
    (cutOracle : (Point → Digest × C) → Key → JointResponse.Oracle (First).participant (Second).participant)
    (cutOff : ∀ point H H', Bcs.TotalOracle.AgreeOff point H H' →
      cutOracle H point.context = cutOracle H' point.context)
    (proof : Output) (H : Point → Digest × C) (n m : ℕ)
    (hn : n ≤ g.roles.length) (hm : m ≤ g.roles.length) (hpn : 0 < n) (hpm : 0 < m) :
    (RuntimeCover.source binary prime P R cfg layout cutoff cutOracle cutOff).selected
        (((RuntimeVerifier.encoding binary prime P R cfg).chain cfg.initialLink).point proof H n) H =
      (RuntimeCover.source binary prime P R cfg layout cutoff cutOracle cutOff).selected
        (((RuntimeVerifier.encoding binary prime P R cfg).chain cfg.initialLink).point proof H m) H := by
  exact Selection.atPoint_replay_same (RuntimeVerifier.encoding binary prime P R cfg) cfg.initialLink
    proof H (RuntimeCover.source binary prime P R cfg layout cutoff cutOracle cutOff).lists
    (fun answer => (cfg.fingerprintBinary answer,cfg.fingerprintPrime answer))
    (RuntimeCover.fingerprintResponses (B := B) binary prime P R cfg) ((0,0),(0,0)) cutOracle n m hn hm hpn hpm

omit [Fintype C] in
/-- Every actual later runtime point uses the selected witness authenticated
at the backend. This follows from the bound rank-one prefix and the decoded
statement, without an assumed accepted-path selection identity. -/
theorem selected_of_decode
    (layout : StatementCompiler.Addresses P R binary.cells prime.remaining prime.pads)
    (hlayout : StatementCompiler.addresses P R binary.cells prime.remaining prime.pads = some layout)
    (cutoff : ℕ × ℕ)
    (cutOracle : (Point → Digest × C) → Key → JointResponse.Oracle (First).participant (Second).participant)
    (cutOff : ∀ point H H', Bcs.TotalOracle.AgreeOff point H H' →
      cutOracle H point.context = cutOracle H' point.context)
    (draw : C → RuntimeVerifier.RawSamples binary prime P R cfg)
    (proof : Output) (H : Point → Digest × C) (decoded : Decoded)
    (hd : RuntimeVerifier.decode binary prime P R cfg draw proof H = some decoded)
    (n : ℕ) (hn : n ≤ g.roles.length) (hpos : 0 < n) :
    (RuntimeCover.source binary prime P R cfg layout cutoff cutOracle cutOff).selected
        (((RuntimeVerifier.encoding binary prime P R cfg).chain cfg.initialLink).point proof H n) H =
      (RuntimeCover.authentication binary prime P R cfg proof decoded
        (cutOracle H (cfg.context proof.body.commitment)) cutoff).context.extract := by
  let e := RuntimeVerifier.encoding binary prime P R cfg
  let parent := BackendPath.parent e cfg.initialLink proof H g.batchingIndex
  have hs := (RuntimeVerifier.decode_spec binary prime P R cfg draw proof H decoded hd).1
  have hp := selected_of_statement binary prime P R cfg layout hlayout cutoff cutOracle cutOff
    parent.point H ⟨decoded.application,decoded.statement⟩ hs decoded.coin
    (RuntimeVerifier.responses binary prime P R cfg proof)
  have hcontext : parent.point.context = cfg.context proof.body.commitment :=
    BackendPath.parent_context e cfg.initialLink proof H g.batchingIndex
  have hbatch : 0 < g.batchingIndex.val := by
    change 0 < g.backendPrefix.length
    simp only [Geometry.backendPrefix,List.length_append,List.length_cons,List.length_nil]
    omega
  have hsame := selected_replay_same binary prime P R cfg layout cutoff cutOracle cutOff proof H n
    g.batchingIndex.val hn (Nat.le_of_lt g.batchingIndex.isLt) hpos hbatch
  rw [← BackendPath.parent_point e cfg.initialLink proof H g.batchingIndex] at hsame
  rw [hcontext] at hp
  exact hsame.trans hp

omit [Fintype C] [Inhabited (RuntimeVerifier.Family binary prime P R cfg).Leaf] in
theorem binarySelection_eq
    (layout : StatementCompiler.Addresses P R binary.cells prime.remaining prime.pads)
    (cutoff : ℕ × ℕ)
    (cutOracle : (Point → Digest × C) → Key → JointResponse.Oracle (First).participant (Second).participant)
    (cutOff : ∀ point H H', Bcs.TotalOracle.AgreeOff point H H' →
      cutOracle H point.context = cutOracle H' point.context)
    (point : Point) (H : Point → Digest × C) (answer : C) :
    (RuntimeCover.source binary prime P R cfg layout cutoff cutOracle cutOff).binarySelection point H answer ↔
      cfg.fingerprintBinary answer ∈ WitnessSelection.badCoins
        ((Counting.committedCandidates (First).backend (cutOracle H point.context).1 cutoff.1).image
          ((RuntimeCover.selectedParam binary prime P R cfg layout cutoff).first.view point.context)) := by
  simp only [ApplicationOracle.SelectionSource.binarySelection,RuntimeCover.source,ZkJoint.JointParam.source,
    RuntimeCover.selectedParam,StatementCompiler.selected,WitnessSelection.badCoins,Finset.mem_filter,
    Finset.mem_univ,true_and]
  constructor
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩
  · intro h
    exact (Finset.mem_filter.mp h).2

omit [Fintype C] [Inhabited (RuntimeVerifier.Family binary prime P R cfg).Leaf] in
theorem primeSelection_eq
    (layout : StatementCompiler.Addresses P R binary.cells prime.remaining prime.pads)
    (cutoff : ℕ × ℕ)
    (cutOracle : (Point → Digest × C) → Key → JointResponse.Oracle (First).participant (Second).participant)
    (cutOff : ∀ point H H', Bcs.TotalOracle.AgreeOff point H H' →
      cutOracle H point.context = cutOracle H' point.context)
    (point : Point) (H : Point → Digest × C) (answer : C) :
    (RuntimeCover.source binary prime P R cfg layout cutoff cutOracle cutOff).primeSelection point H answer ↔
      cfg.fingerprintPrime answer ∈ WitnessSelection.badCoins
        ((Counting.committedCandidates (Second).backend (cutOracle H point.context).2 cutoff.2).image
          ((RuntimeCover.selectedParam binary prime P R cfg layout cutoff).second.view point.context)) := by
  simp only [ApplicationOracle.SelectionSource.primeSelection,RuntimeCover.source,ZkJoint.JointParam.source,
    RuntimeCover.selectedParam,StatementCompiler.selected,WitnessSelection.badCoins,Finset.mem_filter,
    Finset.mem_univ,true_and]
  constructor
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩
  · intro h
    exact (Finset.mem_filter.mp h).2

set_option maxHeartbeats 400000 in
omit [Fintype C] [Inhabited (RuntimeVerifier.Family binary prime P R cfg).Leaf] in
/-- Fingerprint collisions are charged to their existing coefficient query;
they are not folded into later frontend or backend query budgets. -/
theorem collision_of_statement
    (layout : StatementCompiler.Addresses P R binary.cells prime.remaining prime.pads)
    (hlayout : StatementCompiler.addresses P R binary.cells prime.remaining prime.pads = some layout)
    (cutoff : ℕ × ℕ)
    (cutOracle : (Point → Digest × C) → Key → JointResponse.Oracle (First).participant (Second).participant)
    (cutOff : ∀ point H H', Bcs.TotalOracle.AgreeOff point H H' →
      cutOracle H point.context = cutOracle H' point.context)
    (point : Point) (H : Point → Digest × C)
    (data : Σ A : RuntimeVerifier.System binary prime (C := C), StatementData A First Second)
    (hdata : RuntimeVerifier.statementAt binary prime P R cfg point (point.priorAnswers H) = some data)
    (coin : JointResponse.Coin (First).participant (Second).participant)
    (response : JointResponse.Response (First).participant (Second).participant)
    (fingerprint : C)
    (hfp : ApplicationPrefix.strictAnswer point (point.priorAnswers H) 0 = some fingerprint)
    (hcollision : (ZkJoint.authenticate data.2 (cutOracle H point.context) coin response cutoff).context.Collision) :
    (RuntimeCover.source binary prime P R cfg layout cutoff cutOracle cutOff).binarySelection point H fingerprint ∨
      (RuntimeCover.source binary prime P R cfg layout cutoff cutOracle cutOff).primeSelection point H fingerprint := by
  have hs := RuntimeVerifier.statementAt_spec binary prime P R cfg point (point.priorAnswers H) data hdata
  obtain ⟨layout',fingerprint',targets,hlayout',hfingerprint,htargets,hcompile⟩ := hs.2
  have he : layout' = layout := Option.some.inj (hlayout'.symm.trans hlayout)
  subst layout'
  have hf : fingerprint' = fingerprint := Option.some.inj (hfingerprint.symm.trans hfp)
  subst fingerprint'
  obtain ⟨nd,bd,hprime,hbinary,hsetup⟩ :=
    ApplicationPrefix.decodeChecked_spec binary prime cfg.card cfg.generator cfg.quotientBound
      cfg.packingDegree cfg.binaryField cfg.primeField cfg.binaryDecode cfg.binaryNonzero
      cfg.primeDecode cfg.primeNonzero cfg.conversion cfg.advice cfg.fallback _ _ _ hs.1
  have hcontext := RuntimeCover.compiled_context binary prime P R cfg layout nd bd data.1 hsetup data.2
    fingerprint (cfg.binaryField targets.1.1,cfg.binaryField targets.1.2)
    (cfg.primeField targets.2.1,cfg.primeField targets.2.2) hcompile
    (cutOracle H point.context) coin response cutoff point.context
  rw [binarySelection_eq binary prime P R cfg layout cutoff cutOracle cutOff,
    primeSelection_eq binary prime P R cfg layout cutoff cutOracle cutOff]
  rw [hcontext] at hcollision
  exact hcollision

omit [Fintype C] in
theorem collision_of_decode
    (layout : StatementCompiler.Addresses P R binary.cells prime.remaining prime.pads)
    (hlayout : StatementCompiler.addresses P R binary.cells prime.remaining prime.pads = some layout)
    (cutoff : ℕ × ℕ)
    (cutOracle : (Point → Digest × C) → Key → JointResponse.Oracle (First).participant (Second).participant)
    (cutOff : ∀ point H H', Bcs.TotalOracle.AgreeOff point H H' →
      cutOracle H point.context = cutOracle H' point.context)
    (draw : C → RuntimeVerifier.RawSamples binary prime P R cfg)
    (proof : Output) (H : Point → Digest × C) (decoded : Decoded)
    (hd : RuntimeVerifier.decode binary prime P R cfg draw proof H = some decoded)
    (hcollision : (RuntimeCover.authentication binary prime P R cfg proof decoded
      (cutOracle H (cfg.context proof.body.commitment)) cutoff).context.Collision) :
    let point := ((RuntimeVerifier.encoding binary prime P R cfg).chain cfg.initialLink).point proof H 0
    (RuntimeCover.source binary prime P R cfg layout cutoff cutOracle cutOff).binarySelection point H (H point).2 ∨
      (RuntimeCover.source binary prime P R cfg layout cutoff cutOracle cutOff).primeSelection point H (H point).2 := by
  let e := RuntimeVerifier.encoding binary prime P R cfg
  let parent := BackendPath.parent e cfg.initialLink proof H g.batchingIndex
  let point := (e.chain cfg.initialLink).point proof H 0
  have hs := (RuntimeVerifier.decode_spec binary prime P R cfg draw proof H decoded hd).1
  have hcontext : parent.point.context = cfg.context proof.body.commitment :=
    BackendPath.parent_context e cfg.initialLink proof H g.batchingIndex
  have hbatch : 0 < g.batchingIndex.val := by
    change 0 < g.backendPrefix.length
    simp only [Geometry.backendPrefix,List.length_append,List.length_cons,List.length_nil]
    omega
  have hfp : ApplicationPrefix.strictAnswer parent.point (parent.point.priorAnswers H) 0 = some (H point).2 := by
    rw [BackendPath.parent_point e cfg.initialLink proof H g.batchingIndex]
    exact ApplicationViewReplay.strictAnswer_replay e cfg.initialLink proof H g.batchingIndex.val 0
      (Nat.le_of_lt g.batchingIndex.isLt) hbatch
  have hc : (ZkJoint.authenticate decoded.statement (cutOracle H (parent.point (Body := Body g fields Advice (RuntimeVerifier.Authentication (g := g)))).context) decoded.coin
      (RuntimeVerifier.responses binary prime P R cfg proof) cutoff).context.Collision := by
    simpa only [RuntimeCover.authentication,hcontext] using hcollision
  have hbad := collision_of_statement binary prime P R cfg layout hlayout cutoff cutOracle cutOff
    parent.point H ⟨decoded.application,decoded.statement⟩ hs decoded.coin
    (RuntimeVerifier.responses binary prime P R cfg proof) (H point).2 hfp hc
  have hpoint : parent.point.context = point.context :=
    (BackendPath.parent_context e cfg.initialLink proof H g.batchingIndex).trans
      (e.point_context cfg.initialLink proof H 0).symm
  simpa only [ApplicationOracle.SelectionSource.binarySelection,
    ApplicationOracle.SelectionSource.primeSelection,hpoint] using hbad

end LfzkV2.Current.RuntimeSelection
