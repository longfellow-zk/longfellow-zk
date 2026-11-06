import LfzkV2.Current.RuntimeVerifier
import LfzkV2.Current.ApplicationViews
import LfzkV2.Current.ApplicationCover
import LfzkV2.Current.ZkJoint
import LfzkV2.Current.BackendFS

/-! Failure coverage starting from the concrete runtime decoder. The
application, layouts and affine statement below are reconstructed values;
no execution or frontend-correspondence certificate is accepted as input. -/
noncomputable section
namespace LfzkV2.Current.RuntimeCover
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
local notation "Generator" => cfg.generator^Adapter.Mdoc.generatorExponent

/-- The concrete six alternatives obtained from parsed prime/binary data.
All witness readers are the fixed full-cell layouts, including the two
fingerprint cells and excluding the shared prime input prefix. -/
def ParsedBad (nd : PrimeData prime C) (bd : BinaryData binary nd Generator) (w : Pair) : Prop :=
  (∃ query < FrontendReplay.slots bd.setup.circuit,
    FrontendReplay.BadAt bd.decode bd.nonzero bd.setup.circuit bd.setup.plan bd.payload bd.answers
      (binary.inputs (binaryValues binary prime w))
      (fun i => binaryValues binary prime w (CellLayout.Binary.pad binary.words binary.degree binary.pads i)) query) ∨
  bd.frontend.source.Bad (binaryValues binary prime w) bd.U bd.delta ∨
  (∃ query < FrontendReplay.slots prime.circuit,
    FrontendReplay.BadAt nd.decode nd.nonzero prime.circuit prime.setup.plan nd.payload nd.answers
      (primeInputs binary prime w)
      (fun i => primeFullValues binary prime w (.inr (CellLayout.Prime.pad prime.remaining prime.pads i))) query) ∨
  Prime.BatchBad (fun i => (nd.frontend.rows.get i).eval (primeFullValues binary prime w)) nd.rho ∨
  Prime.RescalingBad
    (nd.claim.residual (fun i => if binary.sharedValues w.1 i then 1 else 0)
      (fun i => primeValues binary prime w (.inl i)))
    (Handoff.binaryMask (binary.mask w.1) - primeValues binary prime w (.inr ())) bd.eta ∨
  Handoff.ConversionBad nd.claim.sharedWeights bd.eta bd.mu
    (binary.sharedValues w.1) (binary.mask w.1) Adapter.Mdoc.groupOrder Adapter.Mdoc.quotientBound bd.alpha

omit [Fintype C] in
/-- Successful runtime generator/trace checks identify the algebraic
application events with the actual parsed data. Generated adapter semantics
are supplied by the constructor, not by this theorem's caller. -/
theorem parsedBad_iff (nd : PrimeData prime C) (bd : BinaryData binary nd Generator)
    (A : RuntimeVerifier.System binary prime (C := C))
    (h : ApplicationSetup.decodeChecked binary prime nd cfg.card cfg.generator cfg.quotientBound bd = some A)
    (w : Pair) : A.Bad w ↔ ParsedBad binary prime P R cfg nd bd w := by
  unfold ApplicationSetup.decodeChecked at h
  split at h
  · unfold ApplicationSetup.decode at h
    split at h
    · cases Option.some.inj h
      rfl
    · contradiction
  · contradiction

/-- The runtime's late authentication is built from its decoded statement,
actual response arrays and the shared recovered column oracle. -/
def authentication (proof : Output) (decoded : Decoded)
    (W : JointResponse.Oracle (First).participant (Second).participant) (cutoff : ℕ × ℕ) :
    Application.Authentication decoded.application First Second :=
  ZkJoint.authenticate decoded.statement W decoded.coin
    (RuntimeVerifier.responses binary prime P R cfg proof) cutoff

variable [Inhabited (RuntimeVerifier.Family binary prime P R cfg).Leaf]

omit [Fintype C] in
/-- Actual accepted decoding yields the parsed frontend records. The
resulting error cover contains concrete backend/list/selection alternatives
or a parsed local application event; it assumes no execution certificate. -/
theorem decoded_failure_cover
    (draw : C → RuntimeVerifier.RawSamples binary prime P R cfg)
    (proof : Output) (H : Point → Digest × C) (decoded : Decoded)
    (hd : RuntimeVerifier.decode binary prime P R cfg draw proof H = some decoded)
    (W : JointResponse.Oracle (First).participant (Second).participant) (cutoff : ℕ × ℕ)
    (hfailure : ¬ ∃ w,
      (authentication binary prime P R cfg proof decoded W cutoff).context.extract = some w ∧
        decoded.application.True w) :
    (authentication binary prime P R cfg proof decoded W cutoff).BackendBad ∨
      ∃ (nd : PrimeData prime C) (bd : BinaryData binary nd Generator) (w : Pair),
        let parent := BackendPath.parent (RuntimeVerifier.encoding binary prime P R cfg)
          cfg.initialLink proof H g.batchingIndex
        ApplicationPrefix.readPrime prime cfg.primeField cfg.primeDecode cfg.primeNonzero cfg.fallback
          parent.point (parent.point.priorAnswers H) = some nd ∧
        ApplicationPrefix.readBinary binary nd Generator cfg.packingDegree cfg.binaryField cfg.primeField
          cfg.binaryDecode cfg.binaryNonzero cfg.primeNonzero cfg.conversion cfg.advice cfg.fallback
          parent.point (parent.point.priorAnswers H) = some bd ∧
        ApplicationSetup.decodeChecked binary prime nd cfg.card cfg.generator cfg.quotientBound bd =
          some decoded.application ∧
        (authentication binary prime P R cfg proof decoded W cutoff).context.extract = some w ∧
        ParsedBad binary prime P R cfg nd bd w := by
  let auth := authentication binary prime P R cfg proof decoded W cutoff
  rcases auth.extraction_failure_cover hfailure with hbackend | ⟨w,hselected,hbad⟩
  · exact Or.inl hbackend
  · have hs := (RuntimeVerifier.decode_spec binary prime P R cfg draw proof H decoded hd).1
    have ha := (RuntimeVerifier.statementAt_spec binary prime P R cfg _ _ _ hs).1
    obtain ⟨nd,bd,hprime,hbinary,hsetup⟩ :=
      ApplicationPrefix.decodeChecked_spec binary prime cfg.card cfg.generator cfg.quotientBound
        cfg.packingDegree cfg.binaryField cfg.primeField cfg.binaryDecode cfg.binaryNonzero
        cfg.primeDecode cfg.primeNonzero cfg.conversion cfg.advice cfg.fallback _ _ _ ha
    exact Or.inr ⟨nd,bd,w,hprime,hbinary,hsetup,hselected,
      (parsedBad_iff binary prime P R cfg nd bd decoded.application hsetup w).mp hbad⟩

omit [Fintype C] in
/-- The Boolean verifier's successful branch supplies this cover directly;
the verifier's arithmetic, authentication and final-seal checks are retained. -/
theorem verified_failure_cover
    (draw : C → RuntimeVerifier.RawSamples binary prime P R cfg)
    (codec : Merkle.MH.Codec Salt (RuntimeVerifier.Family binary prime P R cfg).Leaf Digest Enc)
    (HM : Enc → Digest) (proof : Output) (H : Point → Digest × C)
    (hverify : RuntimeVerifier.verify binary prime P R cfg draw codec HM proof H = true)
    (W : JointResponse.Oracle (First).participant (Second).participant) (cutoff : ℕ × ℕ)
    (hfailure : ∀ decoded, RuntimeVerifier.decode binary prime P R cfg draw proof H = some decoded →
      ¬ ∃ w, (authentication binary prime P R cfg proof decoded W cutoff).context.extract = some w ∧
        decoded.application.True w) :
    ∃ decoded, RuntimeVerifier.decode binary prime P R cfg draw proof H = some decoded ∧
      RuntimeVerifier.Checks binary prime P R cfg codec HM proof H decoded ∧
      ((authentication binary prime P R cfg proof decoded W cutoff).BackendBad ∨
        ∃ nd bd w, ParsedBad binary prime P R cfg nd bd w) := by
  obtain ⟨decoded,hd,hchecks⟩ :=
    (RuntimeVerifier.verify_true_iff binary prime P R cfg draw codec HM proof H).mp hverify
  refine ⟨decoded,hd,hchecks,?_⟩
  rcases decoded_failure_cover binary prime P R cfg draw proof H decoded hd W cutoff
      (hfailure decoded hd) with hbackend | ⟨nd,bd,w,_,_,_,_,hbad⟩
  · exact Or.inl hbackend
  · exact Or.inr ⟨nd,bd,w,hbad⟩

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
  batchDecoder : BalancedDecoder C (Fin (prime.circuit.layers+1) → N)
  batch_agrees : ∀ answer i, batchDecoder.decode answer i = cfg.primeDecode answer i.val
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

/-- Wellformed public circuit representations accompany the fixed samplers.
A single generated-adapter template constructs these shape fields through
`RuntimeShape.publicQueries`; callers need no challenge-indexed certificates. -/
structure PublicQueries (S : Source (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key) (C := C) binary prime (Oracle := Oracle))
    extends SamplerLaws binary prime P R cfg S where
  primeShape : FrontendSchedule.Plan N prime.circuit
  primeGeometry : primeShape.frontend = g.prime
  binaryShape : (packet : AdapterPacket binary prime C) →
    FrontendSchedule.Plan B (packet.setup Generator).circuit
  binaryGeometry : ∀ packet, (binaryShape packet).frontend = g.binary
  primeFits : primeShape.capacity ≤ primeCapacity
  binaryFits : ∀ packet, (binaryShape packet).capacity ≤ binaryCapacity

/-- Query counting augments public shapes and ideal sampler laws with the
actual selected-list caps. Checked profile constructors derive these two
bounds from the committed-column code; they are not oracle assumptions. -/
structure QuerySetup (S : Source (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key) (C := C) binary prime (Oracle := Oracle)) (LB LN : ℕ)
    extends PublicQueries binary prime P R cfg S where
  binaryList_bound : ∀ (point : Point) H,
    (S.lists point.context (S.oracle H point.context)).1.card ≤ LB
  primeList_bound : ∀ (point : Point) H,
    (S.lists point.context (S.oracle H point.context)).2.card ≤ LN

namespace QuerySetup
variable {binary : BinaryPublic B shared maskBits adviceBits}
  {prime : PrimePublic N shared}
  {P : FieldBackend B k s n t} {R : FieldBackend N k s n t}
  {cfg : RuntimeVerifier.Public (g := g) binary prime P R (fields := fields) (Advice := Advice)
    (Base := Base) (Key := Key) (C := C) (Salt := Salt)}
variable {S : Source (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key) (C := C) binary prime (Oracle := Oracle)} {LB LN : ℕ}
variable (q : QuerySetup binary prime P R cfg S LB LN)

def primeRead (point : Point) (past : Fin point.rank → C) := readPrimeView binary prime q.primeShape q.primeCapacity
  cfg.primeDecode cfg.primeNonzero q.primeDecoder q.primeFits cfg.primeField cfg.fallback point past

def binaryRead (point : Point) (past : Fin point.rank → C) := readBinaryView binary prime (cfg.generator^Adapter.Mdoc.generatorExponent) q.binaryCapacity q.binaryShape
  cfg.binaryDecode cfg.binaryNonzero q.binaryDecoder q.binaryFits cfg.binaryField cfg.primeField
  cfg.primeDecode cfg.primeNonzero cfg.conversion cfg.advice cfg.fallback point past

def batchRead (point : Point) (past : Fin point.rank → C) := readBatchPacket binary prime cfg.primeDecode cfg.primeNonzero q.batchDecoder
  cfg.primeField cfg.fallback point past

def rescaleRead (_q : QuerySetup binary prime P R cfg S LB LN)
    (point : Point) (past : Fin point.rank → C) := readRescalePacket binary prime cfg.primeField cfg.primeDecode cfg.primeNonzero cfg.fallback point past

def conversionRead (_q : QuerySetup binary prime P R cfg S LB LN)
    (point : Point) (past : Fin point.rank → C) := readConversionPacket binary prime cfg.primeField cfg.primeDecode cfg.primeNonzero cfg.fallback point past

def packingRead (_q : QuerySetup binary prime P R cfg S LB LN)
    (point : Point) (past : Fin point.rank → C) := readPackingPacket binary prime (cfg.generator^Adapter.Mdoc.generatorExponent) cfg.packingDegree cfg.binaryField cfg.primeField
  cfg.binaryDecode cfg.binaryNonzero cfg.primeDecode cfg.primeNonzero cfg.conversion cfg.advice cfg.fallback point past

/-- Each oracle point has one protocol role. In particular, fragments and
fields do not produce extra independent charges at the same boundary. -/
def roleCharge (role : Role) (point : Point) (H : Point → Digest × C) (answer : Digest × C) : ℚ :=
  match role with
  | .fingerprint => indicator (S.binarySelection point H answer.2) + indicator (S.primeSelection point H answer.2)
  | .inputAssertions .binary .. | .assertions .binary .. | .sumcheck .binary .. |
      .terminal .binary .. | .combine .binary .. => frontendCharge S q.binaryRead point H answer
  | .inputAssertions .prime .. | .assertions .prime .. | .sumcheck .prime .. |
      .terminal .prime .. | .combine .prime .. => frontendCharge S q.primeRead point H answer
  | .rowBatching => indicator (batchBad S q.batchRead point H answer.2)
  | .rescaling => indicator (rescaleBad S q.rescaleRead q.rescaleDecoder point H answer.2)
  | .conversion => indicator (conversionBad S q.conversionRead q.conversionDecoder
      Adapter.Mdoc.groupOrder Adapter.Mdoc.quotientBound point H answer.2)
  | .packing => indicator (packingBad S q.packingRead q.packingDecoder point H answer.2)
  | .batching | .opening => 0

def single (point : Point) (H : Point → Digest × C) (answer : Digest × C) : ℚ :=
  match point.role with
  | some role => q.roleCharge role point H answer
  | none => 0

def budget (_q : QuerySetup binary prime P R cfg S LB LN) (point : Point) : ℚ :=
  match point.role with
  | some role => roundBudget B Adapter.Mdoc.primeOrder Adapter.Mdoc.groupOrder
      Adapter.Mdoc.quotientBound LB LN role
  | none => 0

theorem roleCharge_nonneg (role : Role) (point : Point) (H : Point → Digest × C)
    (answer : Digest × C) : 0 ≤ q.roleCharge role point H answer := by
  have hi (P : Prop) : 0 ≤ indicator P := by unfold indicator; split_ifs <;> norm_num
  cases role with
  | fingerprint => exact add_nonneg (hi _) (hi _)
  | inputAssertions side entries => cases side <;> exact hi _
  | assertions side stage entries fragments => cases side <;> exact hi _
  | sumcheck side stage index => cases side <;> exact hi _
  | terminal side stage => cases side <;> exact hi _
  | combine side stage entries => cases side <;> exact hi _
  | rowBatching | rescaling | conversion | packing => exact hi _
  | batching | opening => exact le_rfl

theorem single_nonneg (point : Point) (H : Point → Digest × C) (answer : Digest × C) :
    0 ≤ q.single point H answer := by
  unfold single
  cases point.role with
  | none => exact le_rfl
  | some role => exact q.roleCharge_nonneg role point H answer

theorem roleCharge_off (role : Role) (point : Point) (H H' : Point → Digest × C)
    (h : Bcs.TotalOracle.AgreeOff point H H') (answer : Digest × C) :
    q.roleCharge role point H answer = q.roleCharge role point H' answer := by
  have hb := propext (S.binarySelection_off point H H' h answer.2)
  have hn := propext (S.primeSelection_off point H H' h answer.2)
  have hbf := frontendCharge_off S q.binaryRead point H H' h answer
  have hnf := frontendCharge_off S q.primeRead point H H' h answer
  have hbatch := propext (packetBad_off S q.batchRead (fun packet w a => packet.bad w a) point H H' h answer.2)
  have hs := propext (packetBad_off S q.rescaleRead
    (fun packet w a => packet.bad w (q.rescaleDecoder.decode a)) point H H' h answer.2)
  have hc := propext (packetBad_off S q.conversionRead
    (fun packet w a => packet.bad Adapter.Mdoc.groupOrder Adapter.Mdoc.quotientBound w
      (q.conversionDecoder.decode a)) point H H' h answer.2)
  have hp := propext (packetBad_off S q.packingRead
    (fun packet w a => packet.bad w (q.packingDecoder.decode a)) point H H' h answer.2)
  cases role with
  | fingerprint => simp only [roleCharge,hb,hn]
  | inputAssertions side entries => cases side <;> first | exact hbf | exact hnf
  | assertions side stage entries fragments => cases side <;> first | exact hbf | exact hnf
  | sumcheck side stage index => cases side <;> first | exact hbf | exact hnf
  | terminal side stage => cases side <;> first | exact hbf | exact hnf
  | combine side stage entries => cases side <;> first | exact hbf | exact hnf
  | rowBatching => simp only [roleCharge,batchBad,hbatch]
  | rescaling => simp only [roleCharge,rescaleBad,hs]
  | conversion => simp only [roleCharge,conversionBad,hc]
  | packing => simp only [roleCharge,packingBad,hp]
  | batching | opening => rfl

theorem single_off (point : Point) (H H' : Point → Digest × C)
    (h : Bcs.TotalOracle.AgreeOff point H H') (answer : Digest × C) :
    q.single point H answer = q.single point H' answer := by
  unfold single
  cases point.role with
  | none => rfl
  | some role => exact q.roleCharge_off role point H H' h answer

theorem single_zero_of_role (point : Point) (H : Point → Digest × C) (answer : Digest × C)
    (hrole : point.role = some .batching ∨ point.role = some .opening) :
    q.single point H answer = 0 := by
  rcases hrole with hrole | hrole <;> simp only [single,hrole,roleCharge]

theorem roleCharge_sum (role : Role) (point : Point) (H : Point → Digest × C) :
    (∑ answer, q.roleCharge role point H answer) ≤ Fintype.card (Digest × C) *
      roundBudget B Adapter.Mdoc.primeOrder Adapter.Mdoc.groupOrder Adapter.Mdoc.quotientBound LB LN role := by
  have hB : 0 < Fintype.card B-1 := Nat.sub_pos_of_lt Fintype.one_lt_card
  have hp : 0 < Adapter.Mdoc.primeOrder-1 := Nat.sub_pos_of_lt (Fact.out : Adapter.Mdoc.primeOrder.Prime).one_lt
  have hbcount := (S.binarySelection_card_mul_le q.binarySelectionDecoder
    q.binarySelection_agrees point H).trans (Nat.mul_le_mul_right (Fintype.card C)
      (Nat.choose_le_choose 2 (q.binaryList_bound point H)))
  have hncount := (S.primeSelection_card_mul_le q.primeSelectionDecoder
    q.primeSelection_agrees point H).trans (Nat.mul_le_mul_right (Fintype.card C)
      (Nat.choose_le_choose 2 (q.primeList_bound point H)))
  have hb := indicator_link_sum_le (Link := Digest) (S.binarySelection point H)
    (LB.choose 2) (Fintype.card B^2) (by positivity) hbcount
  have hn := indicator_link_sum_le (Link := Digest) (S.primeSelection point H)
    (LN.choose 2) (Adapter.Mdoc.primeOrder^2) (by norm_num [Adapter.Mdoc.primeOrder])
    (by simpa only [ZMod.card] using hncount)
  have hbf := frontendCharge_sum S q.binaryRead point H
  have hnf := frontendCharge_sum S q.primeRead point H
  have hbatch := indicator_link_sum_le (Link := Digest) (batchBad S q.batchRead point H)
    1 Adapter.Mdoc.primeOrder (by norm_num [Adapter.Mdoc.primeOrder])
    (by simpa only [ZMod.card,one_mul] using batchBad_card_mul_le S q.batchRead point H)
  have hs := indicator_link_sum_le (Link := Digest) (rescaleBad S q.rescaleRead q.rescaleDecoder point H)
    1 (Adapter.Mdoc.primeOrder-1) hp (by simpa only [ZMod.card,one_mul] using (rescaleBad_card_mul_le S q.rescaleRead q.rescaleDecoder point H))
  have hc := indicator_link_sum_le (Link := Digest)
    (conversionBad S q.conversionRead q.conversionDecoder Adapter.Mdoc.groupOrder Adapter.Mdoc.quotientBound point H)
    ((2*(Adapter.Mdoc.quotientBound*Adapter.Mdoc.primeOrder/Adapter.Mdoc.groupOrder)+1)^2)
    ((Adapter.Mdoc.primeOrder-1)^2) (by positivity)
    (conversionBad_card_mul_le S q.conversionRead q.conversionDecoder
      (by norm_num [Adapter.Mdoc.groupOrder,Adapter.Mdoc.binaryOrder]) q.bits_le point H)
  have hpack := indicator_link_sum_le (Link := Digest) (packingBad S q.packingRead q.packingDecoder point H)
    1 (Fintype.card B) Fintype.card_pos
    (by simpa only [one_mul] using packingBad_card_mul_le S q.packingRead q.packingDecoder point H)
  cases role with
  | fingerprint =>
      simp only [roleCharge,sum_add_distrib,roundBudget]
      exact (add_le_add hb hn).trans_eq (by push_cast; ring)
  | inputAssertions side entries => cases side with
      | binary => exact hbf
      | prime => simpa only [roleCharge,roundBudget,ZMod.card] using hnf
  | assertions side stage entries fragments => cases side with
      | binary => exact hbf
      | prime => simpa only [roleCharge,roundBudget,ZMod.card] using hnf
  | sumcheck side stage index => cases side with
      | binary => exact hbf
      | prime => simpa only [roleCharge,roundBudget,ZMod.card] using hnf
  | terminal side stage => cases side with
      | binary => exact hbf
      | prime => simpa only [roleCharge,roundBudget,ZMod.card] using hnf
  | combine side stage entries => cases side with
      | binary => exact hbf
      | prime => simpa only [roleCharge,roundBudget,ZMod.card] using hnf
  | rowBatching => exact hbatch
  | rescaling => exact hs
  | conversion => simpa only [roleCharge,roundBudget,Nat.cast_pow] using hc
  | packing => exact hpack
  | batching | opening => simp only [roleCharge,roundBudget,sum_const_zero,mul_zero,le_refl]

theorem single_sum (point : Point) (H : Point → Digest × C) :
    (∑ answer, q.single point H answer) ≤ Fintype.card (Digest × C)*q.budget point := by
  unfold single budget
  cases point.role with
  | none => simp only [sum_const_zero,mul_zero,le_refl]
  | some role => exact q.roleCharge_sum role point H

/-- Role dispatch takes one maximum, rather than adding unrelated protocol
round budgets at a single oracle point. -/
theorem budget_le (point : Point) (bound : ℚ) (hzero : 0 ≤ bound)
    (hrole : ∀ role, roundBudget B Adapter.Mdoc.primeOrder Adapter.Mdoc.groupOrder
      Adapter.Mdoc.quotientBound LB LN role ≤ bound) : q.budget point ≤ bound := by
  unfold budget
  cases point.role with
  | none => exact hzero
  | some role => exact hrole role

end QuerySetup
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

omit [Fintype C] [Inhabited (RuntimeVerifier.Family binary prime P R cfg).Leaf] in
/-- Successful application reconstruction fixes both public cell maps. -/
theorem decoded_layouts (nd : PrimeData prime C) (bd : BinaryData binary nd Generator)
    (A : RuntimeVerifier.System binary prime (C := C))
    (h : ApplicationSetup.decodeChecked binary prime nd cfg.card cfg.generator cfg.quotientBound bd = some A) :
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

omit [Fintype C] [DecidableEq B] [Inhabited (RuntimeVerifier.Family binary prime P R cfg).Leaf] in
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

omit [Fintype C] [Inhabited (RuntimeVerifier.Family binary prime P R cfg).Leaf] in
/-- Compiling the authenticated rows preserves exactly the early selection
context, including both physical full-cell projections and both responses. -/
theorem compiled_context
    (layout : StatementCompiler.Addresses P R binary.cells prime.remaining prime.pads)
    (nd : PrimeData prime C) (bd : BinaryData binary nd Generator)
    (A : RuntimeVerifier.System binary prime (C := C))
    (hA : ApplicationSetup.decodeChecked binary prime nd cfg.card cfg.generator cfg.quotientBound bd = some A)
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

end CanonicalSelection

end LfzkV2.Current.RuntimeCover
