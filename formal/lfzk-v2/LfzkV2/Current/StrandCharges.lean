import LfzkV2.Current.StrandBackendCharges
import LfzkV2.Current.SurvivalPrefix
import LfzkV2.Current.StrandCut
import LfzkV2.Joint.Indexed
import LfzkV2.Current.ByteOracleTransport
import LfzkV2.Current.RuntimeParameters
import LfzkV2.Current.RuntimeAdaptiveReduction
import LfzkV2.Current.StrandComposition
import Survival.PrefixCache
import LfzkV2.Current.Soundness.RuntimeRoles
import Survival.StoppedCharges
import LfzkV2.Current.Soundness.ProfileBudget

/-! Local protocol charges on the tagged strand search. The commitment
oracle is extracted from that execution's first-context cut, then held fixed
while counting one current answer or the adjacent backend pair. Auxiliary
addresses remain in the execution but receive no algebraic charge. -/
noncomputable section
namespace LfzkV2.Current.StrandCharges
open Application ApplicationSetup ApplicationOracle RecursivePolygero ProfileAnalysis Finset
open Merkle Merkle.Indexed Merkle.RandomOracle TranscriptV2 Bcs.TotalOracle
open scoped Classical

section Cut
variable {Logical Raw T Key C Out : Type} {valid : Logical → Prop}
variable (codec : ByteOracleTransport.Codec Logical (StrandSearch.Name Raw T) valid)
variable (key : Logical → Key) (context : T → Key)

def label : Logical ⊕ StrandSearch.Name Raw T → Option Key :=
  Sum.elim (some ∘ key) (StrandCut.label context)

private def namedEntry : StrandSearch.Name Raw T × (Digest × C) → Option (Raw × Digest)
  | (.inl (raw,_),answer) => some (raw,answer.1)
  | (.inr _,_) => none

private def entry (qa : (Logical ⊕ StrandSearch.Name Raw T) × (Digest × C)) : Option (Raw × Digest) :=
  (codec.untag qa.1).bind fun name => namedEntry (name,qa.2)

/-- Only actual non-PRF node inputs enter the extracted tuple. A padded
noncanonical logical coordinate has no raw input and supplies no entry. -/
def trace {fuel : ℕ} (tree : Tree (Logical ⊕ StrandSearch.Name Raw T) (Digest × C) Out fuel)
    (H : (Logical ⊕ StrandSearch.Name Raw T) → Digest × C) (target : Key) : List (Raw × Digest) :=
  (beforeLabel (label key context) (some target) tree H).filterMap (entry codec)

theorem trace_off {fuel : ℕ} (tree : Tree (Logical ⊕ StrandSearch.Name Raw T) (Digest × C) Out fuel)
    (H H' : (Logical ⊕ StrandSearch.Name Raw T) → Digest × C) (point : Logical)
    (same : AgreeOff (.inl point) H H') :
    trace codec key context tree H (key point) = trace codec key context tree H' (key point) :=
  congrArg (List.filterMap (entry codec)) (beforeLabel_off (label key context) tree (.inl point) H H' same)

/-- Tagging query addresses preserves the actual stopped node trace. This
is an identity about execution, not a caller-supplied extraction certificate. -/
theorem trace_tag {fuel : ℕ} (tree : Tree (StrandSearch.Name Raw T) (Digest × C) Out fuel)
    (H : (Logical ⊕ StrandSearch.Name Raw T) → Digest × C) (target : Key)
    (compatible : ∀ name point, codec.decode name = some point →
      StrandCut.label context name = some (key point.val)) :
    trace codec key context (mapQueries codec.tag tree) H target =
      (beforeLabel (StrandCut.label context) (some target) tree (H ∘ codec.tag)).filterMap namedEntry := by
  induction tree with
  | done output => rfl
  | query name next ih =>
      have sameLabel := codec.tag_label key (StrandCut.label context) compatible name
      change label key context (codec.tag name) = StrandCut.label context name at sameLabel
      by_cases stop : StrandCut.label context name = some target
      · simp only [trace,mapQueries,beforeLabel,sameLabel,stop,↓reduceIte,List.filterMap_nil]
      · simp only [trace,mapQueries,beforeLabel,sameLabel,stop,↓reduceIte,List.filterMap_cons]
        have node : entry codec (codec.tag name,H (codec.tag name)) = namedEntry (name,H (codec.tag name)) := by
          simp only [entry,codec.untag_tag,Option.bind_some]
        dsimp only [Function.comp_apply]
        rw [node]
        have tail := ih (H (codec.tag name))
        unfold trace at tail
        rw [tail]

theorem trace_pad {Extra : Type} {fuel : ℕ}
    (tree : Tree (Logical ⊕ StrandSearch.Name Raw T) (Digest × C) Out fuel)
    (H : (Logical ⊕ StrandSearch.Name Raw T) → Digest × (C × Extra)) (target : Key) :
    trace codec key context (StrandComposition.pad tree) H target =
      trace codec key context tree (StrandComposition.drop H) target := by
  induction tree with
  | done _ => rfl
  | query point next ih =>
      simp only [trace,StrandComposition.pad,beforeLabel]
      split_ifs
      · rfl
      · simp only [List.filterMap_cons]
        have tail := ih ((H point).1,(H point).2.1)
        unfold trace at tail
        rw [show StrandComposition.drop H point = ((H point).1,(H point).2.1) from rfl]
        cases choice : codec.untag point with
        | none => simpa only [entry,choice,Option.bind_none] using tail
        | some name =>
            cases name with
            | inl pair =>
                simpa only [entry,choice,Option.bind_some,namedEntry,StrandComposition.drop] using
                  congrArg (List.cons (pair.1,(H point).1)) tail
            | inr digest => simpa only [entry,choice,Option.bind_some,namedEntry] using tail

theorem trace_reindex {Challenge Residual : Type} {fuel : ℕ}
    (split : (Logical ⊕ StrandSearch.Name Raw T) → C ≃ Challenge × Residual)
    (residual : (Logical ⊕ StrandSearch.Name Raw T) → Residual)
    (tree : Tree (Logical ⊕ StrandSearch.Name Raw T) (Digest × C) Out fuel)
    (H : (Logical ⊕ StrandSearch.Name Raw T) → Digest × Challenge) (target : Key) :
    trace codec key context (StrandSampling.reindex split residual tree) H target =
      trace codec key context tree ((StrandSampling.oracleEquiv split).symm (H,residual)) target := by
  induction tree with
  | done _ => rfl
  | query point next ih =>
      simp only [trace,StrandSampling.reindex,beforeLabel]
      split_ifs
      · rfl
      · simp only [List.filterMap_cons]
        have tail := ih ((H point).1,(split point).symm ((H point).2,residual point))
        unfold trace at tail
        rw [show ((StrandSampling.oracleEquiv split).symm (H,residual)) point =
          ((H point).1,(split point).symm ((H point).2,residual point)) from rfl]
        cases choice : codec.untag point with
        | none => simpa only [entry,choice,Option.bind_none] using tail
        | some name =>
            cases name with
            | inl pair =>
                simpa only [entry,choice,Option.bind_some,namedEntry] using congrArg (List.cons (pair.1,(H point).1)) tail
            | inr digest => simpa only [entry,choice,Option.bind_some,namedEntry] using tail

private theorem map_pad {Name Point D A Extra Result : Type} (rename : Name → Point) {fuel : ℕ}
    (tree : Tree Name (D × A) Result fuel) :
    mapQueries rename (StrandComposition.pad (Extra := Extra) tree) =
      StrandComposition.pad (mapQueries rename tree) := by
  induction tree with
  | done _ => rfl
  | query point next ih =>
      simp only [mapQueries,StrandComposition.pad]
      congr 1
      funext answer
      exact ih (answer.1,answer.2.1)

/-- Padding and inverse sampling coordinates preserve the exact stopped
physical node trace. Only the digest coordinate enters the Merkle extractor;
the prover's retained raw bytes still determine the executed branches. -/
theorem trace_physical {Extra Challenge Residual : Type} {fuel : ℕ}
    (split : (Logical ⊕ StrandSearch.Name Raw T) → ((Strand.Word → Digest) × Extra) ≃ Challenge × Residual)
    (residual : (Logical ⊕ StrandSearch.Name Raw T) → Residual)
    (tree : Tree (StrandSearch.Name Raw T) (Digest × (Strand.Word → Digest)) Out fuel)
    (H : (Logical ⊕ StrandSearch.Name Raw T) → Digest × Challenge) (target : Key)
    (compatible : ∀ name point, codec.decode name = some point →
      StrandCut.label context name = some (key point.val)) :
    trace codec key context
        (StrandSampling.reindex split residual (mapQueries codec.tag (StrandComposition.pad tree))) H target =
      StrandCut.trace context tree
        (fun name => let answer := ((StrandSampling.oracleEquiv split).symm (H,residual)) (codec.tag name)
          (answer.1,answer.2.1)) target := by
  rw [trace_reindex,map_pad,trace_pad]
  apply (trace_tag codec key context tree
    (StrandComposition.drop ((StrandSampling.oracleEquiv split).symm (H,residual))) target compatible).trans
  unfold StrandCut.trace
  apply List.filterMap_congr
  intro qa member
  rcases qa with ⟨name,answer⟩
  cases name <;> rfl

variable {k s n t : ℕ} (binary prime : Joint.Participant k s n t)
variable {Salt Enc : Type}
variable (merkle : Codec Salt (Joint.Pair.family binary prime).Leaf Digest Enc)
variable (dec : RoleDecoders merkle) (root : Key → Digest) (bytes : Raw → Enc)
variable [Inhabited (Joint.Pair.family binary prime).Leaf]

def cutOracle {fuel : ℕ}
    (tree : Tree (Logical ⊕ StrandSearch.Name Raw T) (Digest × C) Out fuel)
    (H : (Logical ⊕ StrandSearch.Name Raw T) → Digest × C) (target : Key) : JointResponse.Oracle binary prime :=
  Joint.Pair.oracleEquiv binary prime
    ((Joint.Pair.family binary prime).indexedOracle dec (root target) ((trace codec key context tree H target).map fun entry => (bytes entry.1,entry.2)))

theorem cutOracle_off {fuel : ℕ}
    (tree : Tree (Logical ⊕ StrandSearch.Name Raw T) (Digest × C) Out fuel)
    (H H' : (Logical ⊕ StrandSearch.Name Raw T) → Digest × C) (point : Logical)
    (same : AgreeOff (.inl point) H H') :
    cutOracle codec key context binary prime merkle dec root bytes tree H (key point) =
      cutOracle codec key context binary prime merkle dec root bytes tree H' (key point) := by
  unfold cutOracle
  rw [trace_off codec key context tree H H' point same]

end Cut

section Runtime
variable (c : CertifiedProfile)
variable {g : Geometry} {fields : Fields} {Advice Base Key B Salt Raw Enc T Out : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable {shared maskBits adviceBits : ℕ}
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable (binary : BinaryPublic B shared maskBits adviceBits) (prime : PrimePublic N shared)
variable (P : FieldBackend B c.k c.s c.n c.t) (R : FieldBackend N c.k c.s c.n c.t)
variable (countBinary countPrime binaryCapacity primeCapacity : ℕ)
local notation "Answer" => IdealRuntime.Answer binary prime P R countBinary countPrime binaryCapacity primeCapacity
local notation "Point" => RuntimeVerifier.Point (g := g) (fields := fields)
  (Advice := Advice) (Base := Base) (Key := Key)
local notation "Parent" => BackendQueries.Parent g.roles Key
  (RuntimeVerifier.Block (g := g) (fields := fields) (Advice := Advice) (Base := Base)) Digest g.batchingIndex
local notation "First" => FieldBackend.participant (FieldBackend.indexed P countBinary)
local notation "Second" => FieldBackend.participant (FieldBackend.indexed R countPrime)
local notation "Name" => StrandSearch.Name Raw T
local notation "Tagged" => Point ⊕ StrandSearch.Name Raw T
local notation "Tuple" => JointResponse.Oracle First Second
local notation "Response" => Digest × JointResponse.Response First Second
local notation "factor" => StrandRoleSampling.factor B N binary.Original prime.Original
  (IdealRuntime.RawBinary P countBinary) (IdealRuntime.RawPrime R countPrime)
  (Fin c.t ↪ Fin c.n) binaryCapacity primeCapacity

local instance answerFintype : Fintype Answer := by
  dsimp only [IdealRuntime.Answer,IdealSamples.Answer]
  infer_instance

variable (cfg : RuntimeVerifier.Public (g := g) binary prime P R (fields := fields)
  (Advice := Advice) (Base := Base) (Key := Key)
  (C := IdealRuntime.Answer binary prime P R countBinary countPrime binaryCapacity primeCapacity) (Salt := Salt))
local notation "publicCfg" => IdealRuntime.challengePublic (g := g) (fields := fields)
  (Advice := Advice) (Base := Base) (Key := Key) (Salt := Salt)
  binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg
local notation "draw" => IdealRuntime.draw binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg
local notation "coin" => RuntimeVerifier.batchingDecoder binary prime P R publicCfg draw
local notation "query" => RuntimeBackend.queryDecoder binary prime P R publicCfg
local notation "encode" => RuntimeVerifier.encodeResponses binary prime P R publicCfg

variable (roleFits : ∀ i : Fin g.roles.length, StrandRoleSampling.Fits binaryCapacity primeCapacity
  (StrandRoleSampling.roleKind binary.degree (prime.circuit.layers+1) (g.roles.get i)))

/-- The public role controls the physical block. The final seal has no
field-sampling role, so its unused ideal answer is left untouched. -/
def normalize (fallback answer : Answer) : Point → Answer
  | .round index _ _ => StrandSampling.normalize
      (factor (StrandRoleSampling.roleKind binary.degree (prime.circuit.layers+1) (g.roles.get index)) (roleFits index))
      fallback answer
  | .finalSeal .. => answer

omit [Fintype B] [DecidableEq B] in
theorem normalize_role (fallback answer : Answer) (point : Point) (role : Role)
    (current : point.role = some role)
    (fits : StrandRoleSampling.Fits binaryCapacity primeCapacity
      (StrandRoleSampling.roleKind binary.degree (prime.circuit.layers+1) role)) :
    normalize c binary prime P R countBinary countPrime binaryCapacity primeCapacity roleFits fallback answer point =
      StrandSampling.normalize
        (factor (StrandRoleSampling.roleKind binary.degree (prime.circuit.layers+1) role) fits) fallback answer := by
  cases point with
  | round index history block =>
      have same := Option.some.inj current
      subst role
      rfl
  | finalSeal history body => cases current

def logicalOracle (fallback : Answer) (H : Tagged → Digest × Answer) (point : Point) : Digest × Answer :=
  ((H (.inl point)).1,
    normalize c binary prime P R countBinary countPrime binaryCapacity primeCapacity roleFits
      fallback (H (.inl point)).2 point)

omit [Fintype B] [DecidableEq B] in
theorem logicalOracle_off (fallback : Answer) (H H' : Tagged → Digest × Answer) (point : Point)
    (same : AgreeOff (.inl point) H H') :
    AgreeOff point
      (logicalOracle c binary prime P R countBinary countPrime binaryCapacity primeCapacity roleFits fallback H)
      (logicalOracle c binary prime P R countBinary countPrime binaryCapacity primeCapacity roleFits fallback H') := by
  intro other different
  have agree := same (.inl other) (fun equal => different (Sum.inl.inj equal))
  simp only [logicalOracle,agree]

variable (layout : StatementCompiler.Addresses P R binary.cells prime.remaining prime.pads)
variable (degreeFits : binary.degree ≤ binaryCapacity) (rowsFit : prime.circuit.layers+1 ≤ primeCapacity)
variable (bitsFit : shared+maskBits ≤ Adapter.Mdoc.quotientBound)

/-- One tuple recovered from the current context is fixed throughout its
local count. This source uses the runtime's actual selected-cell maps and
fingerprint response parser. -/
def frozenSource (tuple : Tuple) :=
  RuntimeCover.source binary prime P R publicCfg layout c.cutoff (fun _ _ => tuple)
    (fun _ _ _ _ => rfl)

def frozenLaws (tuple : Tuple) : RuntimeCover.SamplerLaws binary prime P R publicCfg
    (frozenSource c binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg layout tuple) :=
  IdealRuntime.samplerLaws binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg
    (frozenSource c binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg layout tuple)
    (by rfl) degreeFits rowsFit bitsFit

variable (hashPublic : Key → Option (Fin binary.nPublic → Bool))
variable (decodePublic : Base → Option (Fin prime.nPublic → N))
variable (primeShape : FrontendSchedule.Plan N prime.circuit) (primeGeometry : primeShape.frontend = g.prime)
variable (primeCapacityFits : primeShape.capacity ≤ primeCapacity)
variable (binaryShape : FrontendSchedule.Plan B binary.template) (binaryGeometry : binaryShape.frontend = g.binary)
variable (binaryCapacityFits : binaryShape.capacity ≤ binaryCapacity)
local notation "source" => frozenSource c binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg layout
local notation "samplers" => frozenLaws c binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg layout
  degreeFits rowsFit bitsFit
local notation "derive" => RuntimeAdaptiveBackend.derive binary prime P R publicCfg hashPublic decodePublic

def readers (tuple : Tuple) :=
  RuntimeAdaptiveCharges.concreteReaders (source tuple) (samplers tuple) hashPublic decodePublic
    primeShape primeCapacityFits binaryShape binaryCapacityFits

local notation "readersOf" => readers c binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg layout
  degreeFits rowsFit bitsFit hashPublic decodePublic primeShape primeCapacityFits binaryShape binaryCapacityFits

def frozenSingle (tuple : Tuple) (point : Point) (H : Point → Digest × Answer) (answer : Digest × Answer) : ℚ :=
  RuntimeAdaptiveFS.single (samplers tuple) (readersOf tuple) encode derive coin query c.cutoff c.threshold point H answer

/-- Both the application and the low-response backend test use only the
strict ancestor tape once the original committed tuple is fixed. -/
theorem frozenSingle_prior (tuple : Tuple) (point : Point) (H H' : Point → Digest × Answer)
    (prior : point.priorAnswers H = point.priorAnswers H') (answer : Digest × Answer) :
    frozenSingle c binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg layout
      degreeFits rowsFit bitsFit hashPublic decodePublic primeShape primeCapacityFits binaryShape binaryCapacityFits
      tuple point H answer =
    frozenSingle c binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg layout
      degreeFits rowsFit bitsFit hashPublic decodePublic primeShape primeCapacityFits binaryShape binaryCapacityFits
      tuple point H' answer := by
  unfold frozenSingle RuntimeAdaptiveFS.single
  rw [RuntimeAdaptiveCharges.single_prior (source tuple) (samplers tuple) (readersOf tuple)
    point H H' prior rfl answer]
  apply congrArg (fun value => RuntimeAdaptiveCharges.single (source tuple) (samplers tuple)
    (readersOf tuple) point H' answer + value)
  exact BackendOracle.backend_cached_eq _ _ g.batchingIndex_next encode
    (RuntimeVerifier.encodeResponses_injective binary prime P R publicCfg) derive (source tuple).oracle
    coin query c.cutoff c.threshold point H H' prior (fun _ => rfl) answer

def frozenPair (tuple : Tuple) (parent : Parent) (response : Response)
    (H : Point → Digest × Answer) (first second : Digest × Answer) : ℚ :=
  RuntimeAdaptiveFS.pair (S := source tuple) derive coin query c.threshold parent response H first second

include cfg in
private theorem binaryCard : Nat.card (First).Carrier = Adapter.Mdoc.binaryOrder := by
  change Nat.card B = Adapter.Mdoc.binaryOrder
  simpa only [Nat.card_eq_fintype_card] using cfg.card

private theorem primeCard : Nat.card (Second).Carrier = Adapter.Mdoc.primeOrder := by
  change Nat.card N = Adapter.Mdoc.primeOrder
  simp only [Nat.card_eq_fintype_card,ZMod.card]

def binaryParameters : HahnSystemCertificate (First).backend :=
  c.parameters (First).backend (First).columns (First).dimension (First).batching (First).openings
    (Or.inl (binaryCard c binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg))

def primeParameters : HahnSystemCertificate (Second).backend :=
  c.parameters (Second).backend (Second).columns (Second).dimension (Second).batching (Second).openings
    (Or.inr (primeCard c R countPrime))

local notation "pc" => binaryParameters c binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg
local notation "rc" => primeParameters c R countPrime
local notation "oneFrozen" => frozenSingle c binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg layout
  degreeFits rowsFit bitsFit hashPublic decodePublic primeShape primeCapacityFits binaryShape binaryCapacityFits
local notation "twoFrozen" => frozenPair c binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg layout
  hashPublic decodePublic

def singleBudget (point : Point) : ℚ :=
  RuntimeAdaptiveFS.budget (LB := c.binaryList) (LN := c.primeList) encode c.cutoff c.threshold
    (pc).toProfileParameters (rc).toProfileParameters point

def pairBudget : ℚ := JointResponse.activeHighBudget First Second (pc)

private theorem binaryListBound (tuple : Tuple) (point : Point) (H : Point → Digest × Answer) :
    ((source tuple).lists point.context ((source tuple).oracle H point.context)).1.card ≤ c.binaryList :=
  RuntimeParameters.binary_list_card c binary prime P R publicCfg layout (fun _ _ => tuple)
    (fun _ _ _ _ => rfl) point.context tuple

private theorem primeListBound (tuple : Tuple) (point : Point) (H : Point → Digest × Answer) :
    ((source tuple).lists point.context ((source tuple).oracle H point.context)).2.card ≤ c.primeList :=
  RuntimeParameters.prime_list_card c binary prime P R publicCfg layout (fun _ _ => tuple)
    (fun _ _ _ _ => rfl) point.context tuple

include primeGeometry binaryGeometry in
private theorem frozenSingle_mean (tuple : Tuple) (point : Point) (fallback : Answer) (H : Point → Digest × Answer) :
    (∑ answer : Digest × Answer, oneFrozen tuple point H
      (answer.1,normalize c binary prime P R countBinary countPrime binaryCapacity primeCapacity roleFits
        fallback answer.2 point)) ≤
      Fintype.card (Digest × Answer)*singleBudget c binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg point := by
  have nonnegative : 0 ≤ c.threshold := by unfold CertifiedProfile.threshold ParameterBounds.tail; positivity
  cases point with
  | round index history block =>
      exact StrandBackendCharges.runtime_single_sum binary prime P R countBinary countPrime binaryCapacity primeCapacity
        cfg derive c.cutoff c.threshold (source tuple) (samplers tuple) hashPublic decodePublic
        primeShape primeGeometry primeCapacityFits binaryShape binaryGeometry binaryCapacityFits (fun _ => rfl)
        c.binaryList c.primeList
        (binaryListBound c binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg layout tuple)
        (primeListBound c binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg layout tuple)
        (pc).toProfileParameters (rc).toProfileParameters nonnegative
        (g.roles.get index) (.round index history block) rfl (roleFits index) fallback H
  | finalSeal history body =>
      let rawSampler := IdealRuntime.rawSampler binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg
      let coinSampler := BackendChallenges.decoder P R countBinary countPrime
        (RuntimeVerifier.rowPositive binary prime P R publicCfg) rawSampler
      exact RuntimeAdaptiveFS.single_sum (binary := binary) (prime := prime) (P := P) (R := R) (cfg := publicCfg)
        (samplers tuple) (readersOf tuple) encode derive coin query c.cutoff c.threshold
        (binaryListBound c binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg layout tuple)
        (primeListBound c binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg layout tuple)
        coinSampler (IdealRuntime.querySampler binary prime P R countBinary countPrime binaryCapacity primeCapacity)
        rfl rfl (pc).toProfileParameters (rc).toProfileParameters nonnegative (.finalSeal history body) H

private theorem frozenPair_mean [Nonempty (IdealRuntime.Answer binary prime P R countBinary countPrime binaryCapacity primeCapacity)]
    (tuple : Tuple) (parent : Parent) (H : Point → Digest × Answer) (fallback : Answer) :
    (∑ response, ∑ first : Digest × Answer, ∑ second : Digest × Answer,
      twoFrozen tuple parent response H
        (first.1,StrandSampling.normalize (factor .batching trivial) fallback first.2)
        (second.1,StrandSampling.normalize (factor .opening trivial) fallback second.2)) ≤
      (Fintype.card (Digest × Answer) : ℚ)^2*pairBudget c binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg := by
  have bound : (pc).listBound ≤ Nat.card (First).Carrier := by
    change c.activeList ≤ Nat.card (First).Carrier
    rw [binaryCard c binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg]
    exact c.active_list_le_field
  exact StrandBackendCharges.runtime_pair_sum binary prime P R countBinary countPrime binaryCapacity primeCapacity
    cfg derive c.threshold (source tuple) (pc) (rc).toProfileParameters le_rfl c.active_bound bound parent H fallback

variable {valid : RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key) → Prop}
variable (names : ByteOracleTransport.Codec
  (RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key))
  (StrandSearch.Name Raw T) valid)
variable (context : T → Key)
variable (merkle : Codec Salt (Joint.Pair.family
  (P.indexed countBinary).participant (R.indexed countPrime).participant).Leaf Digest Enc)
variable (dec : RoleDecoders merkle) (root : Key → Digest) (bytes : Raw → Enc)
variable [Inhabited (Joint.Pair.family (P.indexed countBinary).participant (R.indexed countPrime).participant).Leaf]
variable {fuel : ℕ}
variable (tree : Tree
  ((RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key)) ⊕
    StrandSearch.Name Raw T)
  (Digest × IdealRuntime.Answer binary prime P R countBinary countPrime binaryCapacity primeCapacity) Out fuel)

local notation "tupleAt" => cutOracle names Input.context context First Second merkle dec root bytes tree
local notation "typed" => logicalOracle c binary prime P R countBinary countPrime binaryCapacity primeCapacity roleFits
local notation "normal" => normalize c binary prime P R countBinary countPrime binaryCapacity primeCapacity roleFits

/-- Auxiliary queries stay visible to the cut and transcript simulation,
but only a logical protocol boundary has an algebraic one-answer charge. -/
def single (fallback : Answer) (point : Tagged) (H : Tagged → Digest × Answer) (answer : Digest × Answer) : ℚ :=
  match point with
  | .inl p => oneFrozen (tupleAt H p.context) p (typed fallback H) (answer.1,normal fallback answer.2 p)
  | .inr _ => 0

def pair (fallback : Answer) (parent : Parent) (response : Response)
    (H : Tagged → Digest × Answer) (first second : Digest × Answer) : ℚ :=
  twoFrozen (tupleAt H (parent.point : Point).context) parent response (typed fallback H)
    (first.1,StrandSampling.normalize (factor .batching trivial) fallback first.2)
    (second.1,StrandSampling.normalize (factor .opening trivial) fallback second.2)

local notation "singleOf" => single c binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg roleFits layout
  degreeFits rowsFit bitsFit hashPublic decodePublic primeShape primeCapacityFits binaryShape binaryCapacityFits
  names context merkle dec root bytes tree
local notation "pairOf" => pair c binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg roleFits layout
  hashPublic decodePublic names context merkle dec root bytes tree

/-- Cached monitoring agrees with the actual local test whenever its
strict ancestor tape and original first-context cut agree. -/
theorem single_prior (fallback : Answer) (point : Point) (H H' : Tagged → Digest × Answer)
    (tuple : tupleAt H point.context = tupleAt H' point.context)
    (prior : point.priorAnswers (typed fallback H) = point.priorAnswers (typed fallback H'))
    (answer : Digest × Answer) :
    singleOf fallback (.inl point) H answer = singleOf fallback (.inl point) H' answer := by
  simp only [single]
  rw [tuple]
  exact frozenSingle_prior c binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg layout
    degreeFits rowsFit bitsFit hashPublic decodePublic primeShape primeCapacityFits binaryShape binaryCapacityFits
    _ point _ _ prior _

/-- At an actual query prefix, the chronological cache reconstructs the
original context cut. Only ancestor membership needs the recovered-path order. -/
theorem single_cache [cacheDecidable : DecidableEq Tagged] (fallback : Answer) (point : Point) (H : Tagged → Digest × Answer)
    (cacheFallback : Digest × Answer) (past rest : List (Tagged × (Digest × Answer)))
    (answer : Digest × Answer)
    (executed : (tree.run H).2 = past ++ ((.inl point),answer)::rest)
    (ancestors : ∀ i : Fin point.rank, (.inl (point.priorPoints i) : Tagged) ∈ past.map Prod.fst) :
    singleOf fallback (.inl point) (Survival.PrefixCache.cache cacheFallback past) answer =
      singleOf fallback (.inl point) H answer := by
  apply single_prior
  · unfold cutOracle trace
    have cut := Survival.PrefixCache.cut_cache (label Input.context context) tree H cacheFallback
      past rest (.inl point) answer executed
    change beforeLabel (label Input.context context) (some point.context) tree
      (Survival.PrefixCache.cache cacheFallback past) =
        beforeLabel (label Input.context context) (some point.context) tree H at cut
    rw [cut]
  · funext i
    have agree := Survival.PrefixCache.cache_agrees cacheFallback past H (fun qa member => by
      apply Merkle.RandomOracle.Tree.trace_sound tree H qa
      rw [executed]
      exact List.mem_append_left _ member) (.inl (point.priorPoints i)) (ancestors i)
    simp only [Input.priorAnswers, logicalOracle, agree]

theorem single_nonneg (fallback : Answer) (point : Tagged) (H : Tagged → Digest × Answer) (answer : Digest × Answer) :
    0 ≤ singleOf fallback point H answer := by
  cases point with
  | inr _ => exact le_rfl
  | inl point => exact RuntimeAdaptiveFS.single_nonneg ..

theorem pair_nonneg (fallback : Answer) (parent : Parent) (response : Response)
    (H : Tagged → Digest × Answer) (first second : Digest × Answer) :
    0 ≤ pairOf fallback parent response H first second :=
  RuntimeAdaptiveFS.pair_nonneg ..

/-- The cut itself is fixed by stopping before this context's first query.
The old local off-answer lemma then applies to the frozen extracted tuple. -/
theorem single_off (fallback : Answer) (point : Tagged) (H H' : Tagged → Digest × Answer)
    (same : AgreeOff point H H') (answer : Digest × Answer) :
    singleOf fallback point H answer = singleOf fallback point H' answer := by
  cases point with
  | inr _ => rfl
  | inl point =>
      have cut := cutOracle_off names Input.context context First Second merkle dec root bytes tree H H' point same
      unfold single
      dsimp only
      rw [cut]
      exact RuntimeAdaptiveFS.single_off (samplers (tupleAt H' point.context)) (readersOf (tupleAt H' point.context))
        encode derive coin query c.cutoff c.threshold
        (RuntimeVerifier.encodeResponses_injective binary prime P R publicCfg)
        point (typed fallback H) (typed fallback H')
        (logicalOracle_off c binary prime P R countBinary countPrime binaryCapacity primeCapacity roleFits
          fallback H H' point same) _

theorem pair_off (fallback : Answer) (parent : Parent) (response : Response)
    (H H' : Tagged → Digest × Answer)
    (same : ∀ point, point ≠ .inl parent.point →
      point ≠ .inl (parent.child g.batchingIndex_next encode response) → H point = H' point)
    (first second : Digest × Answer) :
    pairOf fallback parent response H first second = pairOf fallback parent response H' first second := by
  let middle := Function.update H (.inl parent.point) (H' (.inl parent.point))
  have left : AgreeOff (.inl parent.point) H middle := by
    intro point different
    simp [middle,different]
  have right : AgreeOff (.inl (parent.child g.batchingIndex_next encode response)) middle H' := by
    intro point different
    by_cases atParent : point = .inl parent.point
    · simp [middle,atParent]
    · simpa [middle,atParent] using same point atParent different
  have cut : tupleAt H (parent.point : Point).context = tupleAt H' (parent.point : Point).context :=
    (cutOracle_off names Input.context context First Second merkle dec root bytes tree H middle parent.point left).trans
      (cutOracle_off names Input.context context First Second merkle dec root bytes tree middle H'
        (parent.child g.batchingIndex_next encode response) right)
  unfold pair
  rw [cut]
  apply RuntimeAdaptiveFS.pair_off (binary := binary) (prime := prime) (P := P) (R := R) (cfg := publicCfg)
    (S := source (tupleAt H' (parent.point : Point).context))
    encode derive coin query c.threshold parent response (typed fallback H) (typed fallback H')
  · intro point notParent notChild
    have agree := same (.inl point) (fun equal => notParent (Sum.inl.inj equal))
      (fun equal => notChild (Sum.inl.inj equal))
    simp only [logicalOracle,agree]

/-- Non-protocol raw inputs have zero algebraic allowance. They remain
available for the separate speculative-query and Merkle accounting. -/
def taggedBudget (point : Tagged) : ℚ :=
  Sum.elim
    (singleBudget c binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg)
    (fun _ => 0) point

include primeGeometry binaryGeometry in
theorem single_mean (fallback : Answer) (point : Tagged) (H : Tagged → Digest × Answer) :
    (∑ answer, singleOf fallback point H answer) ≤
      Fintype.card (Digest × Answer)*
        taggedBudget c binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg point := by
  cases point with
  | inr name => simp only [single,taggedBudget,Sum.elim_inr,sum_const_zero,mul_zero,le_refl]
  | inl point =>
      exact frozenSingle_mean c binary prime P R countBinary countPrime binaryCapacity primeCapacity
        cfg roleFits layout degreeFits rowsFit bitsFit hashPublic decodePublic
        primeShape primeGeometry primeCapacityFits binaryShape binaryGeometry binaryCapacityFits
        (tupleAt H point.context) point fallback (typed fallback H)

theorem pair_mean (fallback : Answer) (parent : Parent) (H : Tagged → Digest × Answer) :
    (∑ response, ∑ first, ∑ second, pairOf fallback parent response H first second) ≤
      (Fintype.card (Digest × Answer) : ℚ)^2*
        pairBudget c binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg := by
  letI : Nonempty Answer := ⟨fallback⟩
  exact frozenPair_mean c binary prime P R countBinary countPrime binaryCapacity primeCapacity
    cfg layout hashPublic decodePublic (tupleAt H (parent.point : Point).context)
    parent (typed fallback H) fallback

include primeGeometry binaryGeometry in
/-- The runtime's actual frontend and joint backend charges, sharing one
query domain and one cut-selected witness pair. All counting and independence
laws follow from the decoded protocol and the stopped execution above. -/
def localProof (fallback : Answer) :
    Composition.LocalCharges Tagged Digest Answer Parent Response where
  parent parent := .inl parent.point
  child parent response := .inl (parent.child g.batchingIndex_next encode response)
  distinct parent response equal := parent.point_ne_child g.batchingIndex_next encode response (Sum.inl.inj equal)
  single := singleOf fallback
  pair := pairOf fallback
  single_nonneg := single_nonneg c binary prime P R countBinary countPrime binaryCapacity primeCapacity
    cfg roleFits layout degreeFits rowsFit bitsFit hashPublic decodePublic primeShape primeCapacityFits
    binaryShape binaryCapacityFits names context merkle dec root bytes tree fallback
  pair_nonneg := pair_nonneg c binary prime P R countBinary countPrime binaryCapacity primeCapacity
    cfg roleFits layout hashPublic decodePublic names context merkle dec root bytes tree fallback
  single_off := single_off c binary prime P R countBinary countPrime binaryCapacity primeCapacity
    cfg roleFits layout degreeFits rowsFit bitsFit hashPublic decodePublic primeShape primeCapacityFits
    binaryShape binaryCapacityFits names context merkle dec root bytes tree fallback
  pair_off := pair_off c binary prime P R countBinary countPrime binaryCapacity primeCapacity
    cfg roleFits layout hashPublic decodePublic names context merkle dec root bytes tree fallback
  singleBudget := taggedBudget c binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg
  pairBudget _ := pairBudget c binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg
  single_mean := single_mean c binary prime P R countBinary countPrime binaryCapacity primeCapacity
    cfg roleFits layout degreeFits rowsFit bitsFit hashPublic decodePublic
    primeShape primeGeometry primeCapacityFits binaryShape binaryGeometry binaryCapacityFits
    names context merkle dec root bytes tree fallback
  pair_mean := pair_mean c binary prime P R countBinary countPrime binaryCapacity primeCapacity
    cfg roleFits layout hashPublic decodePublic names context merkle dec root bytes tree fallback

local notation "proofOf" => localProof c binary prime P R countBinary countPrime binaryCapacity primeCapacity
  cfg roleFits layout degreeFits rowsFit bitsFit hashPublic decodePublic
  primeShape primeGeometry primeCapacityFits binaryShape binaryGeometry binaryCapacityFits
  names context merkle dec root bytes tree

/-- The cache equality exposed directly at the composition interface avoids
unfolding the complete charge record in the concrete runtime instantiation. -/
theorem localProof_single_cache [cacheDecidable : DecidableEq Tagged] (fallback : Answer) (point : Point) (H : Tagged → Digest × Answer)
    (cacheFallback : Digest × Answer) (past rest : List (Tagged × (Digest × Answer)))
    (answer : Digest × Answer)
    (executed : (tree.run H).2 = past ++ ((.inl point),answer)::rest)
    (ancestors : ∀ i : Fin point.rank, (.inl (point.priorPoints i) : Tagged) ∈ past.map Prod.fst) :
    (proofOf fallback).single (.inl point) (Survival.PrefixCache.cache cacheFallback past) answer =
      (proofOf fallback).single (.inl point) H answer :=
  single_cache c binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg
    roleFits layout degreeFits rowsFit bitsFit hashPublic decodePublic
    primeShape primeCapacityFits binaryShape binaryCapacityFits
    names context merkle dec root bytes tree fallback point H cacheFallback past rest answer executed ancestors

section Cover
local instance runtimeLeafInhabited : Inhabited (RuntimeVerifier.Family binary prime P R publicCfg).Leaf := by
  change Inhabited (Joint.Pair.family First Second).Leaf
  infer_instance

variable {Request : Type}
variable (earlier : Request → Replay.Encoding g fields Advice (RuntimeVerifier.Authentication (g := g)) Key
  (RuntimeVerifier.Block (g := g) (fields := fields) (Advice := Advice) (Base := Base))
  (IdealRuntime.Answer binary prime P R countBinary countPrime binaryCapacity primeCapacity))
local notation "Output" => RuntimeAdaptiveVerifier.Output (g := g) (fields := fields)
  (Advice := Advice) (Request := Request)
local notation "Decoded" => RuntimeVerifier.Decoded binary prime P R publicCfg
local notation "encodings" => RuntimeAdaptiveVerifier.encodings binary prime P R publicCfg earlier
local notation "M" => RuntimeAdaptiveVerifier.chain binary prime P R publicCfg earlier

/-- Both decoded field statements are authenticated against the same tuple
from the output's commitment-context cut. Witness selection is consequently
shared by every later frontend and backend check. -/
def authentication (output : Output) (H : Tagged → Digest × Answer) (decoded : Decoded) :=
  ZkJoint.authenticate decoded.statement
    (tupleAt H ((encodings output.request).context output.proof)) decoded.coin
    (RuntimeVerifier.responses binary prime P R publicCfg output.proof) c.cutoff

local notation "auth" => authentication c binary prime P R countBinary countPrime binaryCapacity primeCapacity
  cfg names context merkle dec root bytes tree earlier

variable (layoutCorrect : StatementCompiler.addresses P R binary.cells prime.remaining prime.pads = some layout)

include primeGeometry binaryGeometry layoutCorrect in
/-- Successful decoding and the explained joint opening force one of the
actual local charges whenever the common selected witness does not satisfy
the decoded application. Query order and the final seal are separate strand
properties; no execution or algebraic-cover certificate is assumed here. -/
theorem decoded_cover (fallback : Answer) (output : Output) (H : Tagged → Digest × Answer)
    (decoded : Decoded)
    (decodedCorrect : RuntimeAdaptiveVerifier.decode binary prime P R publicCfg earlier hashPublic decodePublic draw
      output (typed fallback H) = some decoded)
    (verified : let a := auth output H decoded
      JointResponse.Verify First Second a.statement a.oracle a.coin a.response decoded.query)
    (failed : ¬ ∃ witness, (auth output H decoded).context.extract = some witness ∧
      decoded.application.True witness) :
    (proofOf fallback).Covers (rounds := g.roles.length)
      (fun index => .inl ((M).point output (typed fallback H) index)) H := by
  let logical := typed fallback H
  let tuple := tupleAt H ((encodings output.request).context output.proof)
  have covered := RuntimeAdaptiveFS.decoded_charge_cover binary prime P R publicCfg earlier
    hashPublic decodePublic layout c.cutoff (fun _ _ => tuple) (fun _ _ _ _ => rfl)
    (samplers tuple) primeShape primeCapacityFits binaryShape binaryCapacityFits draw
    layoutCorrect primeGeometry binaryGeometry c.threshold output logical decoded decodedCorrect verified failed
  have common index : ((M).point output logical index).context = (encodings output.request).context output.proof := by
    rw [RuntimeAdaptiveVerifier.point_eq]
    exact (encodings output.request).point_context (publicCfg).initialLink output.proof logical index
  rcases covered with ⟨index,bounded,charged⟩ | ⟨index,bounded,parent,response,parentPoint,childPoint,charged⟩
  · refine Or.inl ⟨index,bounded,?_⟩
    change 1 ≤ singleOf fallback (.inl ((M).point output logical index)) H
      (H (.inl ((M).point output logical index)))
    unfold single
    dsimp only
    rw [common index]
    exact charged
  · refine Or.inr ⟨index,bounded,parent,response,congrArg Sum.inl parentPoint,congrArg Sum.inl childPoint,?_⟩
    change 1 ≤ pairOf fallback parent response H (H (.inl parent.point))
      (H (.inl (parent.child g.batchingIndex_next encode response)))
    have parentContext : (parent.point : Point).context = (encodings output.request).context output.proof :=
      (congrArg Input.context parentPoint).trans (common index)
    have batching : (parent.point : Point).role = some .batching := by
      simp only [BackendQueries.Parent.point,Input.role,g.get_batchingIndex]
    have opening : (parent.child g.batchingIndex_next encode response : Point).role = some .opening := by
      change some (g.roles.get ⟨g.batchingIndex.val+1,g.batchingIndex_next⟩) = some .opening
      rw [show (⟨g.batchingIndex.val+1,g.batchingIndex_next⟩ : Fin g.roles.length) = g.openingIndex from
        Fin.ext g.openingIndex_val.symm]
      exact congrArg some g.get_openingIndex
    have first := normalize_role c binary prime P R countBinary countPrime binaryCapacity primeCapacity roleFits
      fallback (H (.inl parent.point)).2 parent.point .batching batching trivial
    have second := normalize_role c binary prime P R countBinary countPrime binaryCapacity primeCapacity roleFits
      fallback (H (.inl (parent.child g.batchingIndex_next encode response))).2
      (parent.child g.batchingIndex_next encode response) .opening opening trivial
    unfold pair
    rw [parentContext]
    change 1 ≤ twoFrozen tuple parent response logical _ _
    change 1 ≤ twoFrozen tuple parent response logical _ _ at charged
    dsimp only [logical,logicalOracle] at charged
    rw [first,second] at charged
    exact charged

end Cover

variable [Fintype Key] [Fintype Base] [Fintype Advice] [∀ side, Fintype (fields side)]

/-- The adjacent backend pair is charged at its parent together with the
rank test. The resulting bound takes one maximum across roles; it does not
allocate a fresh adversarial query budget to every subprotocol or field. -/
theorem localProof_budget_le (fallback : Answer) (point : Tagged) :
    (proofOf fallback).budget point ≤
      Sum.elim (fun _ => 2/((Adapter.Mdoc.binaryOrder-1:ℕ):ℚ)) (fun _ => 0) point := by
  cases point with
  | inr name =>
      simp only [Composition.LocalCharges.budget,localProof,taggedBudget,Sum.elim_inr,
        reduceCtorEq,↓reduceIte,sum_const_zero,add_zero,le_refl]
  | inl point =>
      simp only [Composition.LocalCharges.budget,localProof,taggedBudget,Sum.elim_inl,Sum.inl.injEq]
      have margin : 1999999/(1000000*(Adapter.Mdoc.binaryOrder:ℚ)) ≤
          2/((Adapter.Mdoc.binaryOrder-1:ℕ):ℚ) := by norm_num [Adapter.Mdoc.binaryOrder]
      have parentBound : (pc).rankError+(rc).rankError+pairBudget c binary prime P R
          countBinary countPrime binaryCapacity primeCapacity cfg ≤
          1999999/(1000000*(Adapter.Mdoc.binaryOrder:ℚ)) :=
        c.parameters_parent_budget_le First Second
          (binaryCard c binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg)
          (primeCard c R countPrime)
      have openingBound : GlobalCharges.openingBudget (s := c.s) (n := c.n) (t := c.t)
          c.cutoff c.threshold ≤ 1999999/(1000000*(Adapter.Mdoc.binaryOrder:ℚ)) := by
        change ParameterBounds.openingBudget c.n c.s c.t c.activeCutoff c.binaryCutoff c.primeCutoff ≤ _
        exact c.opening_budget_le
      exact RuntimeAdaptiveFS.point_budget_le (binary := binary) (prime := prime) (P := P) (R := R)
        (cfg := publicCfg) (LB := c.binaryList) (LN := c.primeList)
        encode c.cutoff c.threshold (RuntimeVerifier.encodeResponses_injective binary prime P R publicCfg)
        (pc).toProfileParameters (rc).toProfileParameters
        (pairBudget c binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg)
        (2/((Adapter.Mdoc.binaryOrder-1:ℕ):ℚ))
        (c.round_budget_le cfg.card) (parentBound.trans margin) (openingBound.trans margin)
        (by norm_num [Adapter.Mdoc.binaryOrder]) point

/-- The batching position retains the exact rank and high-response
coefficient, before the old profile theorem rounds it up to the role maximum. -/
theorem batching_budget_eq [budgetDecidable : DecidableEq Tagged] (fallback : Answer) (parent : Parent) :
    (proofOf fallback).budget (.inl parent.point) =
      ParameterBounds.parentBudget c.n c.k c.s c.t c.activeCutoff c.activeList := by
  simp only [Composition.LocalCharges.budget, localProof, taggedBudget, Sum.elim_inl, Sum.inl.injEq]
  rw [BackendOracle.parent_mass, BackendOracle.parentOf_point]
  have appZero : RuntimeAdaptiveCharges.budget (B := B) c.binaryList c.primeList (parent.point : Point) = 0 := by
    simp only [RuntimeAdaptiveCharges.budget, BackendQueries.Parent.point, Input.role,
      g.get_batchingIndex, ApplicationCharging.roundBudget]
  unfold singleBudget RuntimeAdaptiveFS.budget
  rw [appZero]
  simp only [BackendOracle.singleBudget, BackendOracle.parentOf_point, zero_add]
  exact Survival.ProfileBudget.parameters_parent_eq c First Second
    (binaryCard c binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg)
    (primeCard c R countPrime)

/-- Only batching inputs have backend cost in the stopped family. Auxiliary
hash names are left with their entire opaque allowance available. -/
theorem stopped_budget_le [budgetDecidable : DecidableEq Tagged] (fallback : Answer) (allowance : ℚ)
    (parentBound : ParameterBounds.parentBudget c.n c.k c.s c.t c.activeCutoff c.activeList ≤ allowance)
    (point : Tagged) :
    (Survival.StoppedCharges.restrict (proofOf fallback)
      (Survival.RuntimeRoles.marked g.batchingIndex)).budget point ≤
        if Survival.RuntimeRoles.marked g.batchingIndex point && !Survival.RuntimeRoles.auxiliary point
          then allowance else 0 := by
  rw [Survival.StoppedCharges.restrict_budget _ _
    (fun parent => Survival.RuntimeRoles.marked_parent g.batchingIndex parent)]
  cases point with
  | inr name =>
      simp only [Survival.RuntimeRoles.marked, Survival.RuntimeRoles.auxiliary, Bool.not_true,
        Bool.and_false, Bool.false_eq_true, if_false, if_true, Composition.LocalCharges.budget,
        localProof, taggedBudget, Sum.elim_inr, reduceCtorEq, sum_const_zero, add_zero, le_refl]
  | inl point =>
      cases hp : BackendOracle.parentOf (i := g.batchingIndex) point with
      | none => simp only [Survival.RuntimeRoles.marked, hp, Option.isSome_none, Bool.false_eq_true,
          if_false, Bool.false_and, le_refl]
      | some parent =>
          have same := BackendOracle.parentOf_spec hp
          subst point
          simp only [Survival.RuntimeRoles.marked, Survival.RuntimeRoles.auxiliary,
            BackendOracle.parentOf_point, Option.isSome_some, if_true, Bool.not_false, Bool.and_true]
          rw [batching_budget_eq]
          exact parentBound

end Runtime
end LfzkV2.Current.StrandCharges
