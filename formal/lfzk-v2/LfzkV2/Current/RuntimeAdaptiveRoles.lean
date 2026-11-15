import LfzkV2.Current.RuntimeAdaptiveCharges
import LfzkV2.Current.RuntimeShape

/-! Actual query roles under any request-family encoding. The schedule is
fixed by the public frontend plans; adaptive public values add no rounds. -/
noncomputable section
namespace LfzkV2.Current.RuntimeAdaptiveRoles
open RuntimeAdaptiveCharges Application ApplicationSetup ApplicationViews ApplicationOracle RuntimeAdaptive RecursivePolygero SumcheckV2
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice Base Key C B Salt Oracle : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B] [Fintype C]
variable {shared maskBits adviceBits k s n t : ℕ}
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable (binary : BinaryPublic B shared maskBits adviceBits) (prime : PrimePublic N shared)
variable (P : FieldBackend B k s n t) (R : FieldBackend N k s n t)
variable (cfg : RuntimeVerifier.Public (g := g) binary prime P R (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key) (C := C) (Salt := Salt))
variable (S : RuntimeSource.Source (g := g) (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key) (C := C) binary prime (Oracle := Oracle))
variable (laws : RuntimeSource.SamplerLaws binary prime P R cfg S)
variable (hashPublic : Key → Option (Fin binary.nPublic → Bool))
variable (decodePublic : RuntimeAdaptive.PublicReader g Base (Fin prime.nPublic → N))
variable (primePlan : FrontendSchedule.Plan N prime.circuit)
variable (primeFits : primePlan.capacity ≤ laws.primeCapacity)
variable (binaryTemplate : FrontendSchedule.Plan B binary.circuit)
variable (binaryFits : binaryTemplate.capacity ≤ laws.binaryCapacity)
local notation "Point" => RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key)
local notation "Generator" => cfg.polynomialX^Adapter.Mdoc.generatorExponent
variable (e : Replay.Encoding g fields Advice (RuntimeVerifier.Authentication (g := g)) Key
  (Base × ProtocolWrites.Fresh g fields Advice) C)
variable (initialLink : Digest)
variable (proof : Replay.Output g fields Advice (RuntimeVerifier.Authentication (g := g)))
variable (H : RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key) → Digest × C)

local notation "Pair" => Selection.Pair B N binary.Original prime.Original

variable (readers : RuntimeAdaptiveCharges.Readers (g := g) (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key) (C := C) binary prime)

omit [Fintype C] in
theorem point_role (i : Fin g.roles.length) :
    ((e.chain initialLink).point proof H i.val).role = some (g.roles.get i) :=
  Input.role_eq_of_rank _ i ((e.chain initialLink).point_rank proof H i.isLt.le)

omit [Fintype C] in
theorem point_role_of_get (i : ℕ) (hi : i < g.roles.length) (role : Role)
    (hget : g.roles[i]? = some role) : ((e.chain initialLink).point proof H i).role = some role := by
  have hrole : g.roles.get ⟨i,hi⟩ = role :=
    Option.some.inj ((List.getElem?_eq_getElem (l := g.roles) hi).symm.trans hget)
  simpa only [hrole] using point_role e initialLink proof H ⟨i,hi⟩

theorem roleCharge_frontend (role : Role) (side : Side) (point : Point)
    (answer : Digest × C) (h : frontendSide role = some side) :
    roleCharge S laws readers role point H answer = match side with
      | .binary => frontendCharge S readers.binaryRead point H answer
      | .prime => primeCharge S laws readers point H answer := by
  cases role with
  | inputAssertions participant entries => cases participant <;> cases h <;> rfl
  | assertions participant stage entries fragments => cases participant <;> cases h <;> rfl
  | sumcheck participant stage round => cases participant <;> cases h <;> rfl
  | terminal participant stage => cases participant <;> cases h <;> rfl
  | combine participant stage entries fragments last => cases participant <;> cases h <;> rfl
  | fingerprint | rowBatching | conversion | packing | batching | opening => cases h

/-- A prime frontend failure is charged at its own boundary, alone or fused
with the rescaling test at the prime frontend's last boundary. -/
theorem primeCharge_of_frontendBad (point : Point) (answer : Digest × C)
    (h : frontendBad S readers.primeRead point H answer.2) :
    primeCharge S laws readers point H answer = 1 := by
  by_cases hlast : LastPrime readers point H
  · rw [primeCharge_last S laws readers point H answer hlast]
    simp [indicator, h]
  · rw [primeCharge_other S laws readers point H answer hlast]
    simp [frontendCharge, indicator, h]

theorem primeCharge_of_rescaleBad (point : Point) (answer : Digest × C)
    (hlast : LastPrime readers point H)
    (h : rescaleBad S readers.rescaleRead laws.rescaleDecoder point H answer.2) :
    primeCharge S laws readers point H answer = 1 := by
  rw [primeCharge_last S laws readers point H answer hlast]
  simp [indicator, h]

theorem prime_single (primeGeometry : primePlan.frontend = g.prime) (query : ℕ)
    (hquery : query < FrontendReplay.slots prime.circuit) (answer : Digest × C) :
    single S laws readers ((e.chain initialLink).point proof H (g.primeStart+query)) H answer =
      primeCharge S laws readers ((e.chain initialLink).point proof H (g.primeStart+query)) H answer := by
  have hslots : FrontendReplay.slots prime.circuit = (g.prime.roles .prime).length := by
    rw [primePlan.slots_eq_roles_length .prime,primeGeometry]
  let i : Fin (g.prime.roles .prime).length := ⟨query,by omega⟩
  have hr := point_role e initialLink proof H (g.primeIndex i)
  change ((e.chain initialLink).point proof H (g.primeStart+query)).role = some (g.roles.get (g.primeIndex i)) at hr
  rw [g.prime_role_get i] at hr
  have hs := RuntimeShape.frontend_side .prime g.prime _ (List.get_mem _ i)
  unfold single
  rw [hr]
  exact roleCharge_frontend binary prime P R cfg S laws H readers _ .prime _ answer hs

/-- Per-proof virtual leaves and adaptive public values preserve the one
fixed binary plan, so they introduce no additional roles or boundaries. -/
theorem binary_single (binaryGeometry : binaryTemplate.frontend = g.binary)
    (bits : Fin binary.nPublic → Bool) (inputs : Fin prime.nPublic → N)
    (packet : AdapterPacket (binaryWithBits binary bits) (primeWithInputs prime inputs) C)
    (query : ℕ) (hquery : query < FrontendReplay.slots (packet.setup Generator).circuit)
    (answer : Digest × C) :
    single S laws readers ((e.chain initialLink).point proof H (g.binaryStart+query)) H answer =
      frontendCharge S readers.binaryRead ((e.chain initialLink).point proof H (g.binaryStart+query)) H answer := by
  let shape : FrontendSchedule.Plan B (packet.setup Generator).circuit := binaryTemplate
  have hslots : FrontendReplay.slots (packet.setup Generator).circuit = (g.binary.roles .binary).length := by
    rw [shape.slots_eq_roles_length .binary]
    exact congrArg (fun frontend => (frontend.roles .binary).length) binaryGeometry
  let i : Fin (g.binary.roles .binary).length := ⟨query,by omega⟩
  have hr := point_role e initialLink proof H (g.binaryIndex i)
  change ((e.chain initialLink).point proof H (g.binaryStart+query)).role = some (g.roles.get (g.binaryIndex i)) at hr
  rw [g.binary_role_get i] at hr
  have hs := RuntimeShape.frontend_side .binary g.binary _ (List.get_mem _ i)
  unfold single
  rw [hr]
  exact roleCharge_frontend binary prime P R cfg S laws H readers _ .binary _ answer hs

/-- The prime frontend's last boundary also carries the rescaling test. -/
theorem rescaling_single (answer : Digest × C) :
    single S laws readers ((e.chain initialLink).point proof H (ApplicationPrefix.rescalingIndex g)) H answer =
      primeCharge S laws readers ((e.chain initialLink).point proof H (ApplicationPrefix.rescalingIndex g)) H answer := by
  have hindex : ApplicationPrefix.rescalingIndex g < g.roles.length := by
    have hlength := g.roles_length
    have hpos := ApplicationPrefix.prime_roles_pos g
    simp only [ApplicationPrefix.rescalingIndex,Geometry.primeStart] at *
    omega
  have hr := point_role_of_get e initialLink proof H _ hindex _ (RuntimeShape.prime_last_get g)
  unfold single
  rw [hr]
  apply roleCharge_frontend binary prime P R cfg S laws H readers _ .prime _ answer
  rcases Frontend.lastRole_cases .prime g.prime with ⟨_,he⟩ | ⟨_,stage,he⟩ <;>
    rw [he] <;> rfl

/-- Every concrete prime view read at the rescaling boundary ends there: it
is the prime frontend's last boundary. -/
theorem lastPrime_concrete (primeGeometry : primePlan.frontend = g.prime) :
    LastPrime (concreteReaders S laws hashPublic decodePublic primePlan primeFits binaryTemplate binaryFits)
      ((e.chain initialLink).point proof H (ApplicationPrefix.rescalingIndex g)) H := by
  have hindex : ApplicationPrefix.rescalingIndex g ≤ g.roles.length := by
    have hlength := g.roles_length
    simp only [ApplicationPrefix.rescalingIndex,Geometry.primeStart] at *
    omega
  have hr := (e.chain initialLink).point_rank proof H hindex
  change Input.rank _ = ApplicationPrefix.rescalingIndex g at hr
  refine ⟨hr,?_⟩
  intro view hview
  simp only [concreteReaders,RuntimeAdaptiveViews.readPrimeView,Option.bind_eq_bind,
    Option.bind_eq_some_iff] at hview
  obtain ⟨values,_,hview⟩ := hview
  unfold ApplicationViews.readPrimeView at hview
  split at hview
  · obtain ⟨payload,_,rfl⟩ := Option.map_eq_some_iff.mp hview
    change _ = g.primeStart+FrontendReplay.slots prime.circuit
    rw [primePlan.slots_eq_roles_length .prime,primeGeometry,hr,
      ← ApplicationPrefix.conversionIndex_eq]
    rfl
  · contradiction

theorem conversion_single (answer : Digest × C) :
    single S laws readers ((e.chain initialLink).point proof H (ApplicationPrefix.conversionIndex g)) H answer =
      indicator (conversionBad S readers.conversionRead laws.conversionDecoder Adapter.Mdoc.groupOrder Adapter.Mdoc.quotientBound
        ((e.chain initialLink).point proof H (ApplicationPrefix.conversionIndex g)) H answer.2) := by
  have hindex : ApplicationPrefix.conversionIndex g < g.roles.length := by
    have hlength := g.roles_length
    simp only [ApplicationPrefix.conversionIndex,Geometry.primeStart] at *
    omega
  have hr := point_role_of_get e initialLink proof H _ hindex _ (RuntimeShape.conversion_get g)
  simp only [single,hr,roleCharge]

theorem packing_single (answer : Digest × C) :
    single S laws readers ((e.chain initialLink).point proof H (ApplicationPrefix.packingIndex g)) H answer =
      indicator (packingBad S readers.packingRead laws.packingDecoder
        ((e.chain initialLink).point proof H (ApplicationPrefix.packingIndex g)) H answer.2) := by
  have nontrivial : g.packingDegree ≠ 1 := by
    rw [cfg.packingDegree]
    exact ne_of_gt binary.degree_gt
  have hindex : ApplicationPrefix.packingIndex g < g.roles.length := by
    have hlength := g.roles_length
    simp only [ApplicationPrefix.packingIndex,Geometry.binaryStart] at *
    omega
  have hr := point_role_of_get e initialLink proof H _ hindex .packing (RuntimeShape.packing_get g nontrivial)
  simp only [single,hr,roleCharge]

theorem fingerprint_single (answer : Digest × C) :
    single S laws readers ((e.chain initialLink).point proof H 0) H answer =
      indicator (S.binarySelection ((e.chain initialLink).point proof H 0) H answer.2) +
      indicator (S.primeSelection ((e.chain initialLink).point proof H 0) H answer.2) := by
  have hindex : 0 < g.roles.length := by rw [g.roles_length]; omega
  have hget : g.roles[0]? = some .fingerprint := by rw [g.roles_eq]; rfl
  have hr := point_role_of_get e initialLink proof H 0 hindex .fingerprint hget
  simp only [single,hr,roleCharge]

end LfzkV2.Current.RuntimeAdaptiveRoles
