import LfzkV2.Current.RuntimeCover
import LfzkV2.Current.CertifiedProfile

/-! Checked profile data supplies the actual selected-list bounds. The
runtime setup left to the caller consists of trusted circuit representation
and ideal-XOF sampler laws; it contains no coding or bad-event estimate. -/
noncomputable section
namespace LfzkV2.Current.RuntimeParameters
open Application ApplicationSetup ApplicationOracle RecursivePolygero
open scoped Classical

variable (c : CertifiedProfile)
variable {g : Geometry} {fields : Fields} {Advice Base Key C B Salt : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B] [Fintype C]
variable {shared maskBits adviceBits : ℕ}
variable (binary : BinaryPublic B shared maskBits adviceBits)
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable (prime : PrimePublic N shared)
variable (P : FieldBackend B c.k c.s c.n c.t) (R : FieldBackend N c.k c.s c.n c.t)
variable (cfg : RuntimeVerifier.Public (g := g) binary prime P R (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key) (C := C) (Salt := Salt))
variable (layout : StatementCompiler.Addresses P R binary.cells prime.remaining prime.pads)
variable (cutOracle : (RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key) → Digest × C) → Key → JointResponse.Oracle
    (RuntimeVerifier.first binary prime P R cfg).participant
    (RuntimeVerifier.second binary prime P R cfg).participant)
variable (cutOff : ∀ point H H', Bcs.TotalOracle.AgreeOff point H H' →
  cutOracle H point.context = cutOracle H' point.context)
local notation "First" => RuntimeVerifier.first binary prime P R cfg
local notation "Second" => RuntimeVerifier.second binary prime P R cfg
local notation "S" => RuntimeCover.source binary prime P R cfg layout c.cutoff cutOracle cutOff

omit [Fintype C] in
/-- The binary list is the actual projection of committed code candidates.
Projection may merge backend lifts and therefore cannot increase its cap. -/
theorem binary_list_card (key : Key)
    (W : JointResponse.Oracle (First).participant (Second).participant) :
    ((S).lists key W).1.card ≤ c.binaryList :=
  c.binary_projected_card (First).participant W.1
    ((RuntimeCover.selectedParam binary prime P R cfg layout c.cutoff).first.view key)

omit [Fintype C] in
theorem prime_list_card (key : Key)
    (W : JointResponse.Oracle (First).participant (Second).participant) :
    ((S).lists key W).2.card ≤ c.primeList :=
  c.prime_projected_card (Second).participant W.2
    ((RuntimeCover.selectedParam binary prime P R cfg layout c.cutoff).second.view key)

/-- Add the proved coding caps to one public shape/sampling setup. This
constructor carries no caller-supplied list-size or soundness hypothesis. -/
def querySetup (setup : RuntimeCover.PublicQueries binary prime P R cfg (S)) :
    RuntimeCover.QuerySetup binary prime P R cfg (S) c.binaryList c.primeList where
  toPublicQueries := setup
  binaryList_bound := fun point H => binary_list_card c binary prime P R cfg layout cutOracle cutOff
    point.context ((S).oracle H point.context)
  primeList_bound := fun point H => prime_list_card c binary prime P R cfg layout cutOracle cutOff
    point.context ((S).oracle H point.context)

end LfzkV2.Current.RuntimeParameters
