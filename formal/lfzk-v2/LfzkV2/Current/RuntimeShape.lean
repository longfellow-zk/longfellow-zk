import LfzkV2.Current.FrontendTopology
import LfzkV2.Current.RuntimeCover

/-! One trusted public binary template determines the schedule and decoder
capacity of every generated adapter instance. Only coefficients depend on
conversion challenges and masked advice; all metadata is retained exactly. -/
noncomputable section
namespace LfzkV2.Current.RuntimeShape
open Application ApplicationSetup ApplicationViews ApplicationOracle RecursivePolygero SumcheckV2

section Transfer
variable {B C : Type} [Field B] [Fintype B] [Algebra (ZMod 2) B] {shared maskBits adviceBits : ℕ}
variable (binary : BinaryPublic B shared maskBits adviceBits)
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable (prime : PrimePublic N shared) (generator : Bˣ)
variable (template : FrontendSchedule.Plan B binary.template)

/-- This is the template's supplied metadata on the actual generated circuit.
It does not replace component identifiers or infer fragment provenance. -/
def binaryPlan (packet : AdapterPacket binary prime C) :
    FrontendSchedule.Plan B (packet.setup generator).circuit :=
  binary.planFromTemplate template (packet.powers generator)
    (generator^(-(Adapter.Mdoc.primeOrder : ℤ))) packet.masked (packet.targets generator)

theorem binaryPlan_frontend (packet : AdapterPacket binary prime C) :
    (binaryPlan binary prime generator template packet).frontend = template.frontend :=
  binary.planFromTemplate_frontend template _ _ _ _

theorem binaryPlan_capacity (packet : AdapterPacket binary prime C) :
    (binaryPlan binary prime generator template packet).capacity = template.capacity :=
  binary.planFromTemplate_capacity template _ _ _ _

end Transfer

section Setup
variable {g : Geometry} {fields : Fields} {Advice Base Key C B Salt Oracle : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B] [Fintype C]
variable {shared maskBits adviceBits k s n t : ℕ}
variable (binary : BinaryPublic B shared maskBits adviceBits)
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable (prime : PrimePublic N shared)
variable (P : FieldBackend B k s n t) (R : FieldBackend N k s n t)
variable (cfg : RuntimeVerifier.Public (g := g) binary prime P R (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key) (C := C) (Salt := Salt))
variable (S : RuntimeCover.Source (g := g) (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key) (C := C) binary prime (Oracle := Oracle))

/-- Fixed samplers, the trusted prime representation and one binary
adapter template suffice. The generated family's schedule and capacity
checks are conclusions of topology preservation, not separate premises. -/
def publicQueries (samplers : RuntimeCover.SamplerLaws binary prime P R cfg S)
    (primePlan : FrontendSchedule.Plan N prime.circuit)
    (primeGeometry : primePlan.frontend = g.prime)
    (primeFits : primePlan.capacity ≤ samplers.primeCapacity)
    (binaryTemplate : FrontendSchedule.Plan B binary.template)
    (binaryGeometry : binaryTemplate.frontend = g.binary)
    (binaryFits : binaryTemplate.capacity ≤ samplers.binaryCapacity) :
    RuntimeCover.PublicQueries binary prime P R cfg S where
  toSamplerLaws := samplers
  primeShape := primePlan
  primeGeometry := primeGeometry
  primeFits := primeFits
  binaryShape := binaryPlan binary prime (cfg.generator^Adapter.Mdoc.generatorExponent) binaryTemplate
  binaryGeometry packet := (binaryPlan_frontend binary prime _ binaryTemplate packet).trans binaryGeometry
  binaryFits packet := by rw [binaryPlan_capacity]; exact binaryFits

end Setup
end LfzkV2.Current.RuntimeShape
