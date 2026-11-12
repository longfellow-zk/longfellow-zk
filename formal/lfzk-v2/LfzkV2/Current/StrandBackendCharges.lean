import LfzkV2.Current.StrandLocalCharges
import LfzkV2.Current.Soundness.RuntimeCharges

/-! The physical joint-backend blocks retain exactly the coordinates read by
the actual batching and opening decoders. Normalizing unused ideal factors
preserves the one-answer charges and the linked two-answer event, including
its parent-link check. The existing joint Hahn count is reused unchanged. -/
noncomputable section
namespace LfzkV2.Current.StrandBackendCharges
open Application ApplicationSetup ApplicationOracle RecursivePolygero ProfileAnalysis Finset
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice Base Key B Salt : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable {shared maskBits adviceBits k s n t : ℕ}
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable (binary : BinaryPublic B shared maskBits adviceBits) (prime : PrimePublic N shared)
variable (P : FieldBackend B k s n t) (R : FieldBackend N k s n t)
variable (countBinary countPrime binaryCapacity primeCapacity : ℕ)
local notation "RawB" => IdealRuntime.RawBinary P countBinary
local notation "RawN" => IdealRuntime.RawPrime R countPrime
local notation "Answer" => IdealRuntime.Answer binary prime P R countBinary countPrime binaryCapacity primeCapacity
local notation "Point" => RuntimeVerifier.Point (g := g) (fields := fields)
  (Advice := Advice) (Base := Base) (Key := Key)
local notation "Parent" => BackendQueries.Parent g.roles Key
  (RuntimeVerifier.Block (g := g) (fields := fields) (Advice := Advice) (Base := Base)) Digest g.batchingIndex
local notation "First" => FieldBackend.participant (FieldBackend.indexed P countBinary)
local notation "Second" => FieldBackend.participant (FieldBackend.indexed R countPrime)
local notation "factor" => StrandRoleSampling.factor B N binary.Original prime.Original RawB RawN
  (Fin t ↪ Fin n) binaryCapacity primeCapacity

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

theorem batching_decode_normalize (fallback answer : Answer) :
    coin (StrandSampling.normalize (factor .batching trivial) fallback answer) = coin answer := by
  unfold RuntimeVerifier.batchingDecoder
  apply congrArg
  exact StrandRoleSampling.normalize_component B N binary.Original prime.Original RawB RawN (Fin t ↪ Fin n)
    binaryCapacity primeCapacity .batching fallback answer

omit [DecidableEq B] in
theorem opening_decode_normalize (fallback answer : Answer) :
    query (StrandSampling.normalize (factor .opening trivial) fallback answer) = query answer := by
  apply congrArg OrderedOpening.query
  exact StrandRoleSampling.normalize_component B N binary.Original prime.Original RawB RawN (Fin t ↪ Fin n)
    binaryCapacity primeCapacity .opening fallback answer

variable (derive : BackendQueries.Parent g.roles Key
  (RuntimeVerifier.Block (g := g) (fields := fields) (Advice := Advice) (Base := Base)) Digest g.batchingIndex →
  (Fin g.batchingIndex.val → IdealRuntime.Answer binary prime P R countBinary countPrime binaryCapacity primeCapacity) →
  JointResponse.Statement (P.indexed countBinary).participant (R.indexed countPrime).participant)
variable (cutOracle : (RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key) → Digest ×
    IdealRuntime.Answer binary prime P R countBinary countPrime binaryCapacity primeCapacity) →
  Key → JointResponse.Oracle (P.indexed countBinary).participant (R.indexed countPrime).participant)
variable (cutoff : ℕ × ℕ) (epsilon : ℚ)

/-- A canonical backend preimage determines which physical factor is used.
The statement and commitment cut remain fixed while its answer varies. -/
theorem single_normalize (role : Role) (point : Point) (current : point.role = some role)
    (fits : StrandRoleSampling.Fits binaryCapacity primeCapacity
      (StrandRoleSampling.roleKind binary.degree (prime.circuit.layers+1) role))
    (fallback answer : Answer) (H : Point → Digest × Answer) (link : Digest) :
    BackendOracle.single First Second g.batchingIndex_next encode derive cutOracle coin query cutoff epsilon
      point H (link,StrandSampling.normalize
        (factor (StrandRoleSampling.roleKind binary.degree (prime.circuit.layers+1) role) fits) fallback answer) =
    BackendOracle.single First Second g.batchingIndex_next encode derive cutOracle coin query cutoff epsilon
      point H (link,answer) := by
  unfold BackendOracle.single
  cases parent : BackendOracle.parentOf (i := g.batchingIndex) point with
  | some p =>
      have actual : point.role = some .batching := by
        rw [← BackendOracle.parentOf_spec parent]
        simp only [BackendQueries.Parent.point,Input.role,g.get_batchingIndex]
      have sameRole := Option.some.inj (current.symm.trans actual)
      subst role
      dsimp only
      unfold BackendFS.rank
      apply congrArg
      exact batching_decode_normalize binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg
        fallback answer
  | none =>
      cases child : BackendOracle.childOf First Second g.batchingIndex_next encode point with
      | none => rfl
      | some p =>
          have actual : point.role = some .opening := by
            rw [← BackendOracle.childOf_spec First Second g.batchingIndex_next encode
              (RuntimeVerifier.encodeResponses_injective binary prime P R publicCfg) child]
            change some (g.roles.get ⟨g.batchingIndex.val+1,g.batchingIndex_next⟩) = some .opening
            have index : (⟨g.batchingIndex.val+1,g.batchingIndex_next⟩ : Fin g.roles.length) = g.openingIndex := by
              apply Fin.ext
              exact g.openingIndex_val.symm
            rw [index,g.get_openingIndex]
          have sameRole := Option.some.inj (current.symm.trans actual)
          subst role
          dsimp only
          unfold BackendFS.opening
          apply congrArg
          exact opening_decode_normalize binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg
            fallback answer

/-- The two participant responses share one linked batching/opening event.
Normalization leaves the first digest intact, so it cannot introduce an
extra factor from possible parent links. -/
theorem high_normalize (parent : Parent) (response : Digest × JointResponse.Response First Second)
    (H : Point → Digest × Answer) (fallback : Answer) (first second : Digest × Answer) :
    BackendFS.high First Second derive cutOracle coin query epsilon parent response H
      (first.1,StrandSampling.normalize (factor .batching trivial) fallback first.2)
      (second.1,StrandSampling.normalize (factor .opening trivial) fallback second.2) =
    BackendFS.high First Second derive cutOracle coin query epsilon parent response H first second := by
  unfold BackendFS.high
  rw [batching_decode_normalize binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg,
    opening_decode_normalize binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg]

private def coinSampler : BalancedDecoder Answer (JointResponse.Coin First Second) :=
  BackendChallenges.decoder P R countBinary countPrime
    (RuntimeVerifier.rowPositive binary prime P R publicCfg)
    (IdealRuntime.rawSampler binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg)

private theorem coinSampler_decode :
    (coinSampler binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg).decode = coin := rfl

section Runtime
variable (S : RuntimeCover.Source (g := g) (fields := fields) (Advice := Advice) (Base := Base)
  (Key := Key) (C := IdealRuntime.Answer binary prime P R countBinary countPrime binaryCapacity primeCapacity)
  binary prime (Oracle := JointResponse.Oracle (P.indexed countBinary).participant (R.indexed countPrime).participant))
variable (laws : RuntimeCover.SamplerLaws binary prime P R
  (IdealRuntime.challengePublic (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key) (Salt := Salt)
    binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg) S)
variable (hashPublic : Key → Option (Fin binary.nPublic → Bool))
variable (decodePublic : Base → Option (Fin prime.nPublic → N))
variable (primeShape : FrontendSchedule.Plan N prime.circuit) (primeGeometry : primeShape.frontend = g.prime)
variable (primeFits : primeShape.capacity ≤ laws.primeCapacity)
variable (binaryShape : FrontendSchedule.Plan B binary.template) (binaryGeometry : binaryShape.frontend = g.binary)
variable (binaryFits : binaryShape.capacity ≤ laws.binaryCapacity)
variable (coins : ∀ a : IdealRuntime.Answer binary prime P R countBinary countPrime binaryCapacity primeCapacity,
  S.coins a = a .fingerprints)
local notation "readers" => RuntimeAdaptiveCharges.concreteReaders S laws hashPublic decodePublic
  primeShape primeFits binaryShape binaryFits

include primeGeometry binaryGeometry coins in
/-- The actual runtime's application and backend contributions share the
same normalized explicit answer. Their existing sum is preserved exactly. -/
theorem runtime_single_normalize
    (role : Role) (point : Point) (current : point.role = some role)
    (fits : StrandRoleSampling.Fits binaryCapacity primeCapacity
      (StrandRoleSampling.roleKind binary.degree (prime.circuit.layers+1) role))
    (fallback answer : Answer) (H : Point → Digest × Answer) (link : Digest) :
    Soundness.RuntimeCharges.single laws readers encode derive coin query cutoff epsilon point H
      (link,StrandSampling.normalize
        (factor (StrandRoleSampling.roleKind binary.degree (prime.circuit.layers+1) role) fits) fallback answer) =
    Soundness.RuntimeCharges.single laws readers encode derive coin query cutoff epsilon point H (link,answer) := by
  unfold Soundness.RuntimeCharges.single RuntimeAdaptiveCharges.single
  rw [current]
  exact congrArg₂ (·+·)
    (StrandLocalCharges.application_role_normalize binary prime P R countBinary countPrime binaryCapacity primeCapacity
      cfg S laws hashPublic decodePublic primeShape primeGeometry primeFits binaryShape binaryGeometry binaryFits
      coins role point current fits fallback answer H link)
    (single_normalize binary prime P R countBinary countPrime binaryCapacity primeCapacity
      cfg derive S.oracle cutoff epsilon role point current fits fallback answer H link)

variable (LB LN : ℕ)
variable (binaryListBound : ∀ (point : RuntimeVerifier.Point (g := g) (fields := fields)
  (Advice := Advice) (Base := Base) (Key := Key)) H,
  (S.lists point.context (S.oracle H point.context)).1.card ≤ LB)
variable (primeListBound : ∀ (point : RuntimeVerifier.Point (g := g) (fields := fields)
  (Advice := Advice) (Base := Base) (Key := Key)) H,
  (S.lists point.context (S.oracle H point.context)).2.card ≤ LN)

include primeGeometry binaryGeometry coins binaryListBound primeListBound in
/-- The existing shared-role budget applies to the physical factor. There
is no sum of independent application/backend query bounds. -/
theorem runtime_single_sum
    (pc : ProfileParameters (First).backend) (rc : ProfileParameters (Second).backend) (nonnegative : 0 ≤ epsilon)
    (role : Role) (point : Point) (current : point.role = some role)
    (fits : StrandRoleSampling.Fits binaryCapacity primeCapacity
      (StrandRoleSampling.roleKind binary.degree (prime.circuit.layers+1) role))
    (fallback : Answer) (H : Point → Digest × Answer) :
    (∑ answer : Digest × Answer,
      Soundness.RuntimeCharges.single laws readers encode derive coin query cutoff epsilon point H
        (answer.1,StrandSampling.normalize
          (factor (StrandRoleSampling.roleKind binary.degree (prime.circuit.layers+1) role) fits) fallback answer.2)) ≤
      Fintype.card (Digest × Answer)*Soundness.RuntimeCharges.budget (LB := LB) (LN := LN) encode cutoff epsilon pc rc point := by
  simp_rw [runtime_single_normalize binary prime P R countBinary countPrime binaryCapacity primeCapacity
    cfg derive cutoff epsilon S laws hashPublic decodePublic primeShape primeGeometry primeFits
    binaryShape binaryGeometry binaryFits coins role point current fits fallback]
  exact Soundness.RuntimeCharges.single_sum laws readers encode derive coin query cutoff epsilon binaryListBound primeListBound
    (coinSampler binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg)
    (IdealRuntime.querySampler binary prime P R countBinary countPrime binaryCapacity primeCapacity)
    (coinSampler_decode binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg)
    (IdealRuntime.querySampler_decode binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg)
    pc rc nonnegative point H

/-- The complete response pair is counted jointly. Normalization preserves
the original Hahn budget and its single parent-link test. -/
theorem runtime_pair_sum [Nonempty (IdealRuntime.Answer binary prime P R countBinary countPrime binaryCapacity primeCapacity)]
    (pc : HahnSystemCertificate (First).backend) (rc : ProfileParameters (Second).backend)
    (threshold : pc.threshold ≤ epsilon)
    (active : CodingTheory.UniformFamilyBound n pc.columnCutoff (k+2*s-1) pc.listBound)
    (bound : pc.listBound ≤ Nat.card (First).Carrier)
    (parent : Parent) (H : Point → Digest × Answer) (fallback : Answer) :
    (∑ response, ∑ first : Digest × Answer, ∑ second : Digest × Answer,
      Soundness.RuntimeCharges.pair (S := S) derive coin query epsilon parent response H
        (first.1,StrandSampling.normalize (factor .batching trivial) fallback first.2)
        (second.1,StrandSampling.normalize (factor .opening trivial) fallback second.2)) ≤
      (Fintype.card (Digest × Answer) : ℚ)^2*JointResponse.activeHighBudget First Second pc := by
  change (∑ response, ∑ first : Digest × Answer, ∑ second : Digest × Answer,
    BackendFS.high First Second derive S.oracle coin query epsilon parent response H
      (first.1,StrandSampling.normalize (factor .batching trivial) fallback first.2)
      (second.1,StrandSampling.normalize (factor .opening trivial) fallback second.2)) ≤ _
  simp_rw [high_normalize binary prime P R countBinary countPrime binaryCapacity primeCapacity
    cfg derive S.oracle epsilon parent _ H fallback]
  exact Soundness.RuntimeCharges.pair_sum (binary := binary) (prime := prime) (P := P) (R := R)
    (cfg := publicCfg) (S := S) derive coin query epsilon
    (coinSampler binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg)
    (IdealRuntime.querySampler binary prime P R countBinary countPrime binaryCapacity primeCapacity)
    (coinSampler_decode binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg)
    (IdealRuntime.querySampler_decode binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg)
    pc rc threshold active bound parent H

end Runtime
end LfzkV2.Current.StrandBackendCharges
