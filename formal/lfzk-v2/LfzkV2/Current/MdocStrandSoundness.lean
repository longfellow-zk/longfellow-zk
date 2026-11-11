import LfzkV2.Current.ProtocolProbability
import LfzkV2.Current.StrandProtocol
import LfzkV2.Current.MdocIdentifiers
import LfzkV2.Current.MdocDefaults
import LfzkV2.Current.ProofOutput
import LfzkV2.Current.Parameters.Rate7
import LfzkV2.Current.StrandDomains
import LfzkV2.Current.Soundness.RuntimeRate7

/-! Specialize the strand verifier to the rate-1/7 mdoc configuration.
The adversary submits arbitrary proof bytes. The complete-proof parser is
a pure output map, so malformed proofs are rejected without spending an
oracle query or changing the original query count. -/
noncomputable section
namespace LfzkV2.Current.MdocStrandSoundness
open Application ApplicationSetup Bcs.FiniteProbability Merkle.RandomOracle TranscriptV2
open scoped Classical

variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable (binary : ConcreteSetup.BinaryCircuit B) (prime : ConcreteSetup.PrimeCircuit)
variable (cantor : Module.Basis (Fin 128) (ZMod 2) B) (scalars : MdocRuntime.Scalars B)
variable (ids : MdocIdentifiers.Identifiers) (bounds : MdocIdentifiers.Bounds binary prime)
local notation "c" => FixedRate.Rate7.certificate
local notation "bp" => binary.description
local notation "pp" => prime.description
local notation "nodes" => ConcreteSetup.binaryNodes cantor
local notation "P" => MdocRuntime.binaryBackend bp nodes
local notation "R" => MdocRuntime.primeBackend pp
local notation "g" => MdocRuntime.geometry bp pp binary.plan prime.plan
local notation "repr" => MdocRuntime.representations scalars
local notation "shape" => MdocRuntime.shape bp pp binary.plan prime.plan bounds.inputFits bounds.privateFits (by change 128 < 2^64; decide)
local notation "setup" => MdocIdentifiers.setup binary prime cantor scalars ids bounds
local notation "cfg" => MdocRuntime.configuration bp pp binary.plan prime.plan nodes scalars
  bounds.inputFits bounds.privateFits (by change 128 < 2^64; decide) setup (MdocRuntime.field_card binary.basis)
  (MdocRuntime.polynomialX binary.basis)
local notation "Answer" => MdocRuntime.Answer bp pp binary.plan prime.plan nodes
local notation "cb" => Geometry.affineRows g Side.binary
local notation "cp" => Geometry.affineRows g Side.prime
local notation "bc" => MdocRuntime.binaryCapacity bp binary.plan
local notation "pc" => MdocRuntime.primeCapacity pp prime.plan
local notation "params" => MdocIdentifiers.parameters binary prime cantor scalars ids bounds
local notation "metadata" => ConcreteMetadata.metadata (Advice := MdocAdvice.Value) (C := Answer)
  bp pp shape params setup
local notation "bf" => Nat.le_max_right (BinaryPublic.degree bp) binary.plan.capacity
local notation "primeFits" => Nat.le_max_right ((Layered.Circuit.layers (PrimePublic.circuit pp))+1) prime.plan.capacity
local notation "df" => Nat.le_max_left (BinaryPublic.degree bp) binary.plan.capacity
local notation "rf" => Nat.le_max_left ((Layered.Circuit.layers (PrimePublic.circuit pp))+1) prime.plan.capacity
local notation "Point" => QueryRuntime.Runtime.Point repr shape setup (BinaryPublic.nPublic bp)
local notation "Values" => StrandProtocol.values c bp pp P R cb cp bc pc repr shape setup
local notation "First" => FieldBackend.participant (FieldBackend.indexed P cb)
local notation "Second" => FieldBackend.participant (FieldBackend.indexed R cp)

private instance saltInhabited : Inhabited (Fin (c).n × MerkleNonce) :=
  ⟨⟨⟨0,by decide⟩,fun _ => 0⟩⟩

private instance familyLeafInhabited {k s n t : ℕ} (family : Joint.Family k s n t) : Inhabited family.Leaf :=
  ⟨fun _ => ⟨⟨fun _ _ => 0,fun _ => 0⟩,0⟩⟩

private def fallbackPath :
    StrandMerkleMissingQueries.SelectedPath (n := (c).n) (Salt := Fin (c).n × MerkleNonce)
      (M := (Joint.Pair.family First Second).Leaf) (D := Digest) (Enc := Bytes) where
  I := {⟨0,by decide⟩}
  a := fun _ => default
  pf := ⟨fun column => (column.val,fun _ => 0),fun _ => 0⟩
  root := 0
  column := ⟨0,by decide⟩
  opened := Finset.mem_singleton_self _
  cut := []

abbrev Request := CanonicalRuntime.Request bp shape
abbrev RoundPoint := Point
abbrev RoundValue (point : Point) := Values point

variable {fuel blocks Q : ℕ}
variable (body : Tree Bytes Digest (Request binary prime bounds × Bytes) fuel)
variable (fits : (MdocRuntime.geometry binary.description prime.description binary.plan prime.plan).roles.length < 2^64)
variable (sample : (point : RoundPoint binary prime cantor scalars ids bounds) →
  Tree Strand.Word Digest (Option (RoundValue binary prime cantor scalars ids bounds point)) blocks)

def program := body.map (ProofOutput.decode repr (MdocDefaults.proof g B))

local notation "program" => program binary prime scalars bounds body

abbrev Raw := StrandProtocol.Raw c bp pp P R cb cp bc pc repr shape setup binary.plan prime.plan
  rfl rfl bf primeFits df rf cfg rfl metadata fits sample (by decide) program

local notation "Raw" => MdocStrandSoundness.Raw binary prime cantor scalars ids bounds body fits sample
local notation "rawSHA" => StrandProtocol.rawOracle c bp pp P R cb cp bc pc repr shape setup
  binary.plan prime.plan rfl rfl bf primeFits df rf cfg rfl metadata fits sample (by decide) program
local notation "failure" => StrandProtocol.rawFailure c bp pp P R cb cp bc pc repr shape setup
  binary.plan prime.plan rfl rfl bf primeFits df rf cfg rfl metadata fits sample rfl (by decide) program
def replay := StrandProtocol.verifierReplay c bp pp P R cb cp bc pc repr shape setup
  binary.plan prime.plan rfl rfl bf primeFits df rf cfg rfl metadata sample (by decide)

def observation (G : Raw → Digest) := StrandProtocol.rawObservation c bp pp P R cb cp bc pc repr shape setup
  binary.plan prime.plan rfl rfl bf primeFits df rf cfg rfl metadata fits sample (by decide) program G

def selectedFailure := StrandProtocol.failure c bp pp P R cb cp bc pc repr shape setup
  binary.plan prime.plan rfl rfl bf primeFits df rf cfg rfl metadata sample rfl (by decide)

def verify := StrandProtocol.verify c bp pp P R cb cp bc pc repr shape setup
  binary.plan prime.plan rfl rfl bf primeFits df rf cfg rfl metadata sample rfl (by decide)

theorem observation_verified (G : Raw → Digest) (SHA : Bytes → Digest)
    (replayed : (observation binary prime cantor scalars ids bounds body fits sample G).verifier =
      (replay binary prime cantor scalars ids bounds sample
        (observation binary prime cantor scalars ids bounds body fits sample G).original.1).run SHA)
    (failed : selectedFailure binary prime cantor scalars ids bounds sample
      (observation binary prime cantor scalars ids bounds body fits sample G)) :
    verify binary prime cantor scalars ids bounds sample SHA
      (observation binary prime cantor scalars ids bounds body fits sample G).original.1 = true :=
  StrandProtocol.failure_verified c bp pp P R cb cp bc pc repr shape setup binary.plan prime.plan
    rfl rfl bf primeFits df rf cfg rfl metadata sample rfl (by decide) _ SHA replayed failed

theorem observation_original (G : Raw → Digest) :
    (observation binary prime cantor scalars ids bounds body fits sample G).original = (program).run (rawSHA G) :=
  StrandProtocol.rawObservation_original c bp pp P R cb cp bc pc repr shape setup binary.plan prime.plan
    rfl rfl bf primeFits df rf cfg rfl metadata fits sample (by decide) program G

theorem observation_verifier (G : Raw → Digest) :
    (observation binary prime cantor scalars ids bounds body fits sample G).verifier =
      (replay binary prime cantor scalars ids bounds sample ((program).run (rawSHA G)).1).run (rawSHA G) :=
  StrandProtocol.rawObservation_verifier c bp pp P R cb cp bc pc repr shape setup binary.plan prime.plan
    rfl rfl bf primeFits df rf cfg rfl metadata fits sample (by decide) program G

theorem replay_domain (output : CanonicalRuntime.Output (Advice := MdocAdvice.Value) bp shape) :
    OracleDomain.UsesOnly StrandDomains.protocol (replay binary prime cantor scalars ids bounds sample output) :=
  StrandProtocol.verifierReplay_domain c bp pp P R cb cp bc pc repr shape setup binary.plan prime.plan
    rfl rfl bf primeFits df rf cfg rfl metadata sample (by decide) output

def oracle (G : Raw → Digest) : Bytes → Digest := rawSHA G

def event (G : Raw → Digest) : Prop :=
  (ProofOutput.read («g» := g) repr (body.run (rawSHA G)).1.2).isSome ∧ failure G

variable (bodyFits : ProofBodyBounds.bodyBound (MdocRuntime.representations scalars)
  (MdocRuntime.geometry binary.description prime.description binary.plan prime.plan) ≤ CanonicalPrefix.maxLength)
variable (fiber : RoundPoint binary prime cantor scalars ids bounds → ℕ)
variable (uniform : ∀ point value, (Finset.univ.filter fun stream => ((sample point).run stream).1 = some value).card = fiber point)
variable (queries : ∀ SHA : Bytes → Digest, (seen body SHA).card ≤ Q)

include bodyFits uniform queries in
/-- Leading linear shared-budget soundness, valid for every Q. The proof
uses the common stopped cover and cost directly, independently of W. -/
theorem fixed_setup_linear_ratio_le :
    density (event binary prime cantor scalars ids bounds body fits sample) ≤
      Survival.Rate7.rate*Q + Survival.Rate7.correction Q (g).roles.length := by
  apply query_bound_or_one Q (2^127)
    (density_le_one (event binary prime cantor scalars ids bounds body fits sample))
  · intro budget
    have support (SHA : Bytes → Digest) : (seen program SHA).card ≤ Q := by
      simpa only [MdocStrandSoundness.program,seen,Bcs.TotalOracle.queried,Tree.run_map] using queries SHA
    have bound := StrandProtocol.soundness_linear c bp pp P R cb cp bc pc repr shape setup binary.plan prime.plan
      rfl rfl bf primeFits df rf cfg rfl metadata bodyFits fits sample fiber uniform rfl (by decide) program
      (ConcreteSetup.addresses bp pp nodes ConcreteSetup.primeNodes) (by decide)
      (ConcreteSetup.addresses_eq bp pp nodes ConcreteSetup.primeNodes) support
      (fallbackPath binary prime cantor) (ConcreteMetadata.metadata_challengeIndependent bp pp shape params setup)
      (by intros; rfl) (Survival.Rate7.polygeroFraction*Survival.Rate7.rate)
      (mul_nonneg Survival.Rate7.polygeroFraction_nonneg Survival.Rate7.rate_nonneg)
      (by
        change Survival.Rate7.polygeroFraction*Survival.Rate7.rate ≤ Survival.Rate7.rate
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (Survival.Rate7.polygeroFraction_le.trans (by norm_num : (51/100 : ℚ) ≤ 1))
          Survival.Rate7.rate_nonneg)
      Survival.RuntimeRate7.parent_budget
      (Survival.RuntimeRate7.auxiliary_budget Q budget)
    refine (density_mono (q := failure) (fun _ valid => valid.2)).trans ?_
    apply bound.trans_eq
    rw [Survival.RuntimeRate7.correction_eq]
    rfl
  · intro bounded
    have castBound : (2^127 : ℚ) ≤ Q := by exact_mod_cast bounded
    have leading := mul_le_mul_of_nonneg_left castBound Survival.Rate7.rate_nonneg
    have atCutoff : (1 : ℚ) ≤ Survival.Rate7.rate*(2^127 : ℚ) := by
      norm_num [Survival.Rate7.rate,Survival.Rate7.q]
    have correction : 0 ≤ Survival.Rate7.correction Q (g).roles.length := by
      unfold Survival.Rate7.correction
      positivity
    linarith

include bodyFits uniform queries in
/-- The all-Q leading linear bound for the original runtime failure event. -/
theorem linear_ratio_le :
    density (event binary prime cantor scalars ids bounds body fits sample) ≤
      Survival.Rate7.rate*Q + Survival.Rate7.correction Q (g).roles.length :=
  fixed_setup_linear_ratio_le binary prime cantor scalars ids bounds body fits sample bodyFits fiber uniform queries

include bodyFits uniform queries in
/-- Saturated soundness for the actual rate-1/7 verifier and parser. The
backend and auxiliary bounds are discharged by the concrete runtime profile. -/
theorem fixed_setup_ratio_le (budget : Q < 2^127) :
    density (event binary prime cantor scalars ids bounds body fits sample) ≤
      Survival.Rate7.failureBound Q (g).roles.length := by
  have support (SHA : Bytes → Digest) : (seen program SHA).card ≤ Q := by
    simpa only [MdocStrandSoundness.program,seen,Bcs.TotalOracle.queried,Tree.run_map] using queries SHA
  have bound := StrandProtocol.soundness c bp pp P R cb cp bc pc repr shape setup binary.plan prime.plan
    rfl rfl bf primeFits df rf cfg rfl metadata bodyFits fits sample fiber uniform rfl (by decide) program
    (ConcreteSetup.addresses bp pp nodes ConcreteSetup.primeNodes) (by decide)
    (ConcreteSetup.addresses_eq bp pp nodes ConcreteSetup.primeNodes) support
    (fallbackPath binary prime cantor) (ConcreteMetadata.metadata_challengeIndependent bp pp shape params setup)
    (by intros; rfl) Survival.Rate7.polygeroFraction Survival.Rate7.polygeroFraction_nonneg
    (Survival.Rate7.polygeroFraction_le.trans (by norm_num))
    (Survival.RuntimeRate7.query_budget Q budget) Survival.RuntimeRate7.parent_budget
    (Survival.RuntimeRate7.auxiliary_budget Q budget)
  refine (density_mono (q := failure) (fun _ valid => valid.2)).trans ?_
  apply bound.trans_eq
  rw [Survival.RuntimeRate7.correction_eq, Survival.Rate7.failureBound_eq]
  rfl

include bodyFits uniform queries in
/-- The primary fixed-setup bound uses chronological survival and the
opaque Polygero/hash allowance, with the original runtime failure event. -/
theorem ratio_le (budget : Q < 2^127) :
    density (event binary prime cantor scalars ids bounds body fits sample) ≤
      Survival.Rate7.failureBound Q (g).roles.length :=
  fixed_setup_ratio_le binary prime cantor scalars ids bounds body fits sample bodyFits fiber uniform queries budget

include bodyFits uniform queries in
theorem nonvacuous (budget : Q < 2^127) :
    density (event binary prime cantor scalars ids bounds body fits sample) < 97/100 := by
  exact lt_of_le_of_lt
    ((ratio_le binary prime cantor scalars ids bounds body fits sample bodyFits fiber uniform queries budget).trans
      (Survival.Rate7.failureBound_nonvacuous Q (g).roles.length (Survival.RuntimeRate7.range Q budget) fits))
    (by norm_num)

end LfzkV2.Current.MdocStrandSoundness
