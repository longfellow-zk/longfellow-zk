import LfzkV2.Current.MdocRoundShape
import LfzkV2.Current.MdocStrandSoundness
import LfzkV2.Current.StrandRoutedObserver

/-! Condition the one SHA oracle on its complementary public-setup slice.
The remaining strand and Merkle inputs retain independent uniform answers.
Partial evaluation of the prover preserves its output and filters its
original trace, so no new query budget is introduced. -/
noncomputable section
namespace LfzkV2.Current.MdocStrandOracle
open Application ApplicationSetup TranscriptV2 Merkle.RandomOracle Bcs.FiniteProbability OracleDomain
open scoped Classical

def identifiers (ids : MdocIdentifiers.Identifiers) (outside : Bytes → Digest) : MdocIdentifiers.Identifiers :=
  { ids with hash := outside }

variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable (binary : ConcreteSetup.BinaryCircuit B) (prime : ConcreteSetup.PrimeCircuit)
variable (cantor : Module.Basis (Fin 128) (ZMod 2) B) (scalars : MdocRuntime.Scalars B)
variable (ids : MdocIdentifiers.Identifiers) (bounds : MdocIdentifiers.Bounds binary prime)

omit [Fintype B] [DecidableEq B] in
theorem setup_merge (outside inside : Bytes → Digest) :
    MdocIdentifiers.setup binary prime cantor scalars
        (identifiers ids (SHAOracle.merge StrandDomains.protocol outside inside)) bounds =
      MdocIdentifiers.setup binary prime cantor scalars (identifiers ids outside) bounds := by
  unfold MdocIdentifiers.setup MdocIdentifiers.templateId MdocIdentifiers.binaryContext MdocIdentifiers.primeContext identifiers
  simp only [StrandDomains.adapter_merge,StrandDomains.context_merge,StrandDomains.joint_context_merge]

omit [Fintype B] [DecidableEq B] in
theorem parameters_merge (outside inside : Bytes → Digest) :
    MdocIdentifiers.parameters binary prime cantor scalars
        (identifiers ids (SHAOracle.merge StrandDomains.protocol outside inside)) bounds =
      MdocIdentifiers.parameters binary prime cantor scalars (identifiers ids outside) bounds := by
  unfold MdocIdentifiers.parameters MdocIdentifiers.binaryContext MdocIdentifiers.primeContext identifiers
  simp only [StrandDomains.context_merge]

variable {fuel blocks Q : ℕ}
variable (body : Tree Bytes Digest (MdocStrandSoundness.Request binary prime bounds × Bytes) fuel)
variable (outside : Bytes → Digest)

def residualBody := (StrandRoutedObserver.routed StrandDomains.protocol outside body).map Prod.fst

local notation "residual" => residualBody binary prime bounds body outside

omit [Fintype B] [DecidableEq B] in
theorem residual_output (inside : Bytes → Digest) :
    ((residual).run inside).1 = (body.run (SHAOracle.merge StrandDomains.protocol outside inside)).1 := by
  rw [residualBody,Tree.run_map,StrandRoutedObserver.routed_output]

omit [Fintype B] [DecidableEq B] in
theorem residual_trace (inside : Bytes → Digest) :
    ((residual).run inside).2 =
      ((body.run (SHAOracle.merge StrandDomains.protocol outside inside)).2.filter fun qa =>
        decide (StrandDomains.protocol qa.1)) := by
  rw [residualBody,Tree.run_map,StrandRoutedObserver.routed_trace]

omit [Fintype B] [DecidableEq B] in
theorem residual_domain : UsesOnly StrandDomains.protocol residual :=
  UsesOnly.of_queries _ (StrandRoutedObserver.routed_map_domain StrandDomains.protocol outside body Prod.fst)

variable (queries : ∀ SHA : Bytes → Digest, (seen body SHA).card ≤ Q)

include queries in
omit [Fintype B] [DecidableEq B] in
theorem residual_budget (inside : Bytes → Digest) : (seen residual inside).card ≤ Q := by
  have trace := residual_trace binary prime bounds body outside inside
  change (((residual).run inside).2.map Prod.fst).toFinset.card ≤ Q
  rw [trace]
  refine (Finset.card_le_card ?_).trans (queries (SHAOracle.merge StrandDomains.protocol outside inside))
  intro raw rawPresent
  obtain ⟨qa,qaPresent,qaEq⟩ := List.mem_map.mp (List.mem_toFinset.mp rawPresent)
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨qa,(List.mem_filter.mp qaPresent).1,qaEq⟩)

variable (fits : (MdocRuntime.geometry binary.description prime.description binary.plan prime.plan).roles.length < 2^64)
variable (sample : (point : MdocStrandSoundness.RoundPoint binary prime cantor scalars (identifiers ids outside) bounds) →
  Tree Strand.Word Digest (Option (MdocStrandSoundness.RoundValue binary prime cantor scalars (identifiers ids outside) bounds point)) blocks)
variable (fiber : MdocStrandSoundness.RoundPoint binary prime cantor scalars (identifiers ids outside) bounds → ℕ)
variable (uniform : ∀ point value, (Finset.univ.filter fun stream => ((sample point).run stream).1 = some value).card = fiber point)
variable (bodyFits : ProofBodyBounds.bodyBound (MdocRuntime.representations scalars)
  (MdocRuntime.geometry binary.description prime.description binary.plan prime.plan) ≤ CanonicalPrefix.maxLength)

abbrev Raw := MdocStrandSoundness.Raw binary prime cantor scalars (identifiers ids outside) bounds residual fits sample
local notation "Raw" => MdocStrandOracle.Raw binary prime cantor scalars ids bounds body outside fits sample

def inside (G : Raw → Digest) : Bytes → Digest :=
  MdocStrandSoundness.oracle binary prime cantor scalars (identifiers ids outside) bounds residual fits sample G

local notation "inside" => MdocStrandOracle.inside binary prime cantor scalars ids bounds body outside fits sample

def sha (G : Raw → Digest) : Bytes → Digest := SHAOracle.merge StrandDomains.protocol outside (inside G)
local notation "SHA" => sha binary prime cantor scalars ids bounds body outside fits sample

def observation (G : Raw → Digest) :=
  MdocStrandSoundness.observation binary prime cantor scalars (identifiers ids outside) bounds residual fits sample G

local notation "view" => observation binary prime cantor scalars ids bounds body outside fits sample

theorem submitted_output (G : Raw → Digest) :
    (view G).original.1 = ProofOutput.decode (MdocRuntime.representations scalars)
      (MdocDefaults.proof (MdocRuntime.geometry binary.description prime.description binary.plan prime.plan) B)
      (body.run (SHA G)).1 := by
  have original := congrArg Prod.fst (MdocStrandSoundness.observation_original binary prime cantor scalars
    (identifiers ids outside) bounds residual fits sample G)
  simp only [MdocStrandSoundness.program,Tree.run_map] at original
  exact original.trans (congrArg _ (residual_output binary prime bounds body outside (inside G)))

/-- The extractor's query table is precisely the original table restricted
to the protocol domain. Answers on the fixed setup slice add no evidence. -/
theorem original_trace (G : Raw → Digest) :
    (view G).original.2 = ((body.run (SHA G)).2.filter fun qa => decide (StrandDomains.protocol qa.1)) := by
  have original := congrArg Prod.snd (MdocStrandSoundness.observation_original binary prime cantor scalars
    (identifiers ids outside) bounds residual fits sample G)
  simp only [MdocStrandSoundness.program,Tree.run_map] at original
  exact original.trans (residual_trace binary prime bounds body outside (inside G))

theorem verifier_actual (G : Raw → Digest) :
    (view G).verifier = (MdocStrandSoundness.replay binary prime cantor scalars (identifiers ids outside) bounds
      sample (view G).original.1).run (SHA G) := by
  have original := congrArg Prod.fst (MdocStrandSoundness.observation_original binary prime cantor scalars
    (identifiers ids outside) bounds residual fits sample G)
  have actual := MdocStrandSoundness.observation_verifier binary prime cantor scalars
    (identifiers ids outside) bounds residual fits sample G
  have same := (MdocStrandSoundness.replay_domain binary prime cantor scalars (identifiers ids outside) bounds sample
    (view G).original.1).run_eq (inside G) (SHA G)
      (fun raw member => SHAOracle.merge_inside StrandDomains.protocol outside (inside G) raw member)
  have translated := congrArg (fun out => (MdocStrandSoundness.replay binary prime cantor scalars
    (identifiers ids outside) bounds sample out).run (inside G)) original
  exact (actual.trans translated.symm).trans same.symm

def event (G : Raw → Digest) : Prop :=
  (ProofOutput.read (g := MdocRuntime.geometry binary.description prime.description binary.plan prime.plan)
    (MdocRuntime.representations scalars) (body.run (SHA G)).1.2).isSome ∧
      MdocStrandSoundness.selectedFailure binary prime cantor scalars (identifiers ids outside) bounds sample (view G)

theorem event_eq (G : Raw → Digest) : event binary prime cantor scalars ids bounds body outside fits sample G ↔
    MdocStrandSoundness.event binary prime cantor scalars (identifiers ids outside) bounds residual fits sample G := by
  unfold event MdocStrandSoundness.event
  change
    ((ProofOutput.read (g := MdocRuntime.geometry binary.description prime.description binary.plan prime.plan)
      (MdocRuntime.representations scalars) (body.run (SHA G)).1.2).isSome ∧
        MdocStrandSoundness.selectedFailure binary prime cantor scalars (identifiers ids outside) bounds sample (view G)) ↔
    ((ProofOutput.read (g := MdocRuntime.geometry binary.description prime.description binary.plan prime.plan)
      (MdocRuntime.representations scalars) ((residual).run (inside G)).1.2).isSome ∧
        MdocStrandSoundness.selectedFailure binary prime cantor scalars (identifiers ids outside) bounds sample (view G))
  rw [residual_output binary prime bounds body outside (inside G)]
  rfl

theorem event_verified (G : Raw → Digest) (accepted : event binary prime cantor scalars ids bounds body outside fits sample G) :
    MdocStrandSoundness.verify binary prime cantor scalars (identifiers ids outside) bounds sample (SHA G)
      (view G).original.1 = true :=
  MdocStrandSoundness.observation_verified binary prime cantor scalars (identifiers ids outside) bounds residual fits sample G
    (SHA G) (verifier_actual binary prime cantor scalars ids bounds body outside fits sample G) accepted.2

include queries bodyFits uniform in
theorem linear_ratio_le :
    density (event binary prime cantor scalars ids bounds body outside fits sample) ≤
      LfzkV2.Current.Soundness.Rate7.rate*Q + LfzkV2.Current.Soundness.Rate7.correction Q
        (MdocRuntime.geometry binary.description prime.description binary.plan prime.plan).roles.length := by
  rw [density_congr (event_eq binary prime cantor scalars ids bounds body outside fits sample)]
  exact MdocStrandSoundness.linear_ratio_le binary prime cantor scalars (identifiers ids outside) bounds
    residual fits sample bodyFits fiber uniform (residual_budget binary prime bounds body outside queries)

include queries bodyFits uniform in
theorem ratio_le (budget : Q < 2^127) :
    density (event binary prime cantor scalars ids bounds body outside fits sample) ≤
      LfzkV2.Current.Soundness.Rate7.failureBound Q
        (MdocRuntime.geometry binary.description prime.description binary.plan prime.plan).roles.length := by
  rw [density_congr (event_eq binary prime cantor scalars ids bounds body outside fits sample)]
  exact MdocStrandSoundness.ratio_le binary prime cantor scalars (identifiers ids outside) bounds
    residual fits sample bodyFits fiber uniform (residual_budget binary prime bounds body outside queries) budget

include bodyFits in
/-- Leading linear soundness after averaging the independent complementary
SHA slice and adversary choices, for every Q and the existing extractor. -/
theorem averaged_linear_ratio_le {Omega : Type} [Fintype Omega] [Nonempty Omega]
    (external : Omega → Bytes → Digest)
    (adversary : Omega → Tree Bytes Digest (MdocStrandSoundness.Request binary prime bounds × Bytes) fuel)
    (sampler : (coin : Omega) →
      (point : MdocStrandSoundness.RoundPoint binary prime cantor scalars (identifiers ids (external coin)) bounds) →
      Tree Strand.Word Digest
        (Option (MdocStrandSoundness.RoundValue binary prime cantor scalars (identifiers ids (external coin)) bounds point)) blocks)
    (sampleFiber : (coin : Omega) →
      MdocStrandSoundness.RoundPoint binary prime cantor scalars (identifiers ids (external coin)) bounds → ℕ)
    (balanced : ∀ coin point value,
      (Finset.univ.filter fun stream => ((sampler coin point).run stream).1 = some value).card = sampleFiber coin point)
    (queryBound : ∀ coin oracle, (seen (adversary coin) oracle).card ≤ Q) :
    (∑ coin, density (event binary prime cantor scalars ids bounds (adversary coin) (external coin) fits (sampler coin))) /
        Fintype.card Omega ≤
      LfzkV2.Current.Soundness.Rate7.rate*Q + LfzkV2.Current.Soundness.Rate7.correction Q
        (MdocRuntime.geometry binary.description prime.description binary.plan prime.plan).roles.length := by
  apply mean_le
  intro coin
  exact linear_ratio_le binary prime cantor scalars ids bounds (adversary coin) (external coin)
    (queries := queryBound coin) (fits := fits) (sample := sampler coin) (fiber := sampleFiber coin)
    (uniform := balanced coin) (bodyFits := bodyFits)

include bodyFits in
/-- Saturated soundness after averaging the independent complementary SHA
slice and adversary choices. The event and extractor are the existing runtime ones. -/
theorem averaged_ratio_le {Omega : Type} [Fintype Omega] [Nonempty Omega]
    (external : Omega → Bytes → Digest)
    (adversary : Omega → Tree Bytes Digest (MdocStrandSoundness.Request binary prime bounds × Bytes) fuel)
    (sampler : (coin : Omega) →
      (point : MdocStrandSoundness.RoundPoint binary prime cantor scalars (identifiers ids (external coin)) bounds) →
      Tree Strand.Word Digest
        (Option (MdocStrandSoundness.RoundValue binary prime cantor scalars (identifiers ids (external coin)) bounds point)) blocks)
    (sampleFiber : (coin : Omega) →
      MdocStrandSoundness.RoundPoint binary prime cantor scalars (identifiers ids (external coin)) bounds → ℕ)
    (balanced : ∀ coin point value,
      (Finset.univ.filter fun stream => ((sampler coin point).run stream).1 = some value).card = sampleFiber coin point)
    (queryBound : ∀ coin oracle, (seen (adversary coin) oracle).card ≤ Q) (budget : Q < 2^127) :
    (∑ coin, density (event binary prime cantor scalars ids bounds (adversary coin) (external coin) fits (sampler coin))) /
        Fintype.card Omega ≤
      LfzkV2.Current.Soundness.Rate7.failureBound Q
        (MdocRuntime.geometry binary.description prime.description binary.plan prime.plan).roles.length := by
  apply mean_le
  intro coin
  exact ratio_le binary prime cantor scalars ids bounds (adversary coin) (external coin)
    (queries := queryBound coin) (fits := fits) (sample := sampler coin) (fiber := sampleFiber coin)
    (uniform := balanced coin) (bodyFits := bodyFits) budget

include bodyFits in
/-- Saturated soundness after averaging the independent complementary SHA
slice and adversary choices. The event and extractor are the existing runtime ones. -/
theorem averaged_nonvacuous {Omega : Type} [Fintype Omega] [Nonempty Omega]
    (external : Omega → Bytes → Digest)
    (adversary : Omega → Tree Bytes Digest (MdocStrandSoundness.Request binary prime bounds × Bytes) fuel)
    (sampler : (coin : Omega) →
      (point : MdocStrandSoundness.RoundPoint binary prime cantor scalars (identifiers ids (external coin)) bounds) →
      Tree Strand.Word Digest
        (Option (MdocStrandSoundness.RoundValue binary prime cantor scalars (identifiers ids (external coin)) bounds point)) blocks)
    (sampleFiber : (coin : Omega) →
      MdocStrandSoundness.RoundPoint binary prime cantor scalars (identifiers ids (external coin)) bounds → ℕ)
    (balanced : ∀ coin point value,
      (Finset.univ.filter fun stream => ((sampler coin point).run stream).1 = some value).card = sampleFiber coin point)
    (queryBound : ∀ coin oracle, (seen (adversary coin) oracle).card ≤ Q) (budget : Q < 2^127) :
    (∑ coin, density (event binary prime cantor scalars ids bounds (adversary coin) (external coin) fits (sampler coin))) /
        Fintype.card Omega < 97/100 := by
  have bound := averaged_ratio_le binary prime cantor scalars ids bounds
    (fits := fits) (bodyFits := bodyFits) external adversary sampler sampleFiber balanced queryBound budget
  exact lt_of_le_of_lt (bound.trans (LfzkV2.Current.Soundness.Rate7.failureBound_nonvacuous Q
    (MdocRuntime.geometry binary.description prime.description binary.plan prime.plan).roles.length
    (LfzkV2.Current.Soundness.RuntimeRate7.range Q budget) fits)) (by norm_num)

include bodyFits in
/-- A polynomial consequence for every query budget, including Q = 0. -/
theorem averaged_polynomial_ratio_le {Omega : Type} [Fintype Omega] [Nonempty Omega]
    (external : Omega → Bytes → Digest)
    (adversary : Omega → Tree Bytes Digest (MdocStrandSoundness.Request binary prime bounds × Bytes) fuel)
    (sampler : (coin : Omega) →
      (point : MdocStrandSoundness.RoundPoint binary prime cantor scalars (identifiers ids (external coin)) bounds) →
      Tree Strand.Word Digest
        (Option (MdocStrandSoundness.RoundValue binary prime cantor scalars (identifiers ids (external coin)) bounds point)) blocks)
    (sampleFiber : (coin : Omega) →
      MdocStrandSoundness.RoundPoint binary prime cantor scalars (identifiers ids (external coin)) bounds → ℕ)
    (balanced : ∀ coin point value,
      (Finset.univ.filter fun stream => ((sampler coin point).run stream).1 = some value).card = sampleFiber coin point)
    (queryBound : ∀ coin oracle, (seen (adversary coin) oracle).card ≤ Q) :
    (∑ coin, density (event binary prime cantor scalars ids bounds (adversary coin) (external coin) fits (sampler coin))) /
        Fintype.card Omega ≤
      2*Q*(2 : ℚ)^(-128 : ℤ) +
        (2*(Q : ℚ)^2/(1-(2 : ℚ)^(-128 : ℤ)) +
          (MdocRuntime.geometry binary.description prime.description binary.plan prime.plan).roles.length + 15) *
            (2 : ℚ)^(-256 : ℤ) := by
  apply query_bound_or_one Q (2^127)
    (mean_density_le_one (fun coin =>
      event binary prime cantor scalars ids bounds (adversary coin) (external coin) fits (sampler coin)))
  · intro budget
    have bound := (averaged_ratio_le binary prime cantor scalars ids bounds
      (fits := fits) (bodyFits := bodyFits) external adversary sampler sampleFiber balanced queryBound budget).trans
        (LfzkV2.Current.Soundness.Rate7.failureBound_le_polynomial Q _)
    apply bound.trans_eq
    norm_num [LfzkV2.Current.Soundness.Rate7.q, Adapter.Mdoc.binaryOrder]
    ring
  · intro integerBound
    have rationalBound : (170141183460469231731687303715884105728 : ℚ) ≤ Q := by
      exact_mod_cast integerBound
    have roundsNonnegative : (0 : ℚ) ≤
        (MdocRuntime.geometry binary.description prime.description binary.plan prime.plan).roles.length :=
      Nat.cast_nonneg _
    norm_num [LfzkV2.Current.Soundness.Rate7.q, Adapter.Mdoc.binaryOrder]
    nlinarith only [rationalBound, sq_nonneg (Q : ℚ), roundsNonnegative]

include bodyFits in
/-- Convenient approximation for every Q. The supported compiler shape derives the round bound. -/
theorem averaged_mdoc_approximation {Omega : Type} [Fintype Omega] [Nonempty Omega]
    (external : Omega → Bytes → Digest)
    (adversary : Omega → Tree Bytes Digest (MdocStrandSoundness.Request binary prime bounds × Bytes) fuel)
    (sampler : (coin : Omega) →
      (point : MdocStrandSoundness.RoundPoint binary prime cantor scalars (identifiers ids (external coin)) bounds) →
      Tree Strand.Word Digest
        (Option (MdocStrandSoundness.RoundValue binary prime cantor scalars (identifiers ids (external coin)) bounds point)) blocks)
    (sampleFiber : (coin : Omega) →
      MdocStrandSoundness.RoundPoint binary prime cantor scalars (identifiers ids (external coin)) bounds → ℕ)
    (balanced : ∀ coin point value,
      (Finset.univ.filter fun stream => ((sampler coin point).run stream).1 = some value).card = sampleFiber coin point)
    (queryBound : ∀ coin oracle, (seen (adversary coin) oracle).card ≤ Q)
    (shape : MdocRoundShape.Supported (MdocRuntime.geometry binary.description prime.description binary.plan prime.plan)) :
    (∑ coin, density (event binary prime cantor scalars ids bounds (adversary coin) (external coin) fits (sampler coin))) /
        Fintype.card Omega ≤
      (Q : ℚ)/2^127 + (Q : ℚ)^2/2^257 + 1/2^246 := by
  apply query_bound_or_one Q (2^127)
    (mean_density_le_one (fun coin =>
      event binary prime cantor scalars ids bounds (adversary coin) (external coin) fits (sampler coin)))
  · intro budget
    exact (averaged_ratio_le binary prime cantor scalars ids bounds
      (fits := fits) (bodyFits := bodyFits) external adversary sampler sampleFiber balanced queryBound budget).trans
        (LfzkV2.Current.Soundness.Rate7.mdoc_approximation Q _ (LfzkV2.Current.Soundness.RuntimeRate7.range Q budget)
          (MdocRoundShape.rounds_le _ shape))
  · intro integerBound
    have rationalBound : (170141183460469231731687303715884105728 : ℚ) ≤ Q := by
      exact_mod_cast integerBound
    norm_num [pow_succ]
    nlinarith only [rationalBound, sq_nonneg (Q : ℚ)]

end LfzkV2.Current.MdocStrandOracle
