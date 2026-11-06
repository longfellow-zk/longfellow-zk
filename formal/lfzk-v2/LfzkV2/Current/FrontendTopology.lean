import LfzkV2.Current.FrontendSchedule
import LfzkV2.Current.ApplicationSetup

/-! Frontend metadata follows syntax rather than polynomial coefficients.
This relation retains every width, entry count and assertion constructor;
it changes no supplied component identifiers or fragment order. It is used
to transfer one trusted public adapter template to all challenge values. -/
noncomputable section
namespace LfzkV2.Current.FrontendTopology
open SumcheckV2 FrontendSchedule

variable {F : Type}

/-- Equality of circuit grammar and assertion classes. The polynomial tensors
and entry address maps are not identified by this relation. -/
inductive Same : {out input : ℕ} → Layered.Circuit F out input → Layered.Circuit F out input → Type
  | input {n : ℕ} : Same (.input (n := n)) (.input (n := n))
  | entry {out mid input checks : ℕ}
      {firstEntry secondEntry : Layered.Entry (Cube out) (Cube mid) checks}
      {first second : Layered.Circuit F mid input} (tail : Same first second) :
      Same (.entry checks firstEntry first) (.entry checks secondEntry second)
  | layer {out mid input assertions : ℕ}
      {firstBody secondBody : LfzkV2.Native.CircuitLayer (Cube out) (Cube mid) (Fin assertions) F}
      {first second : Layered.Circuit F mid input}
      (classes : ∀ i, isQuadratic (secondBody.assertions i) = isQuadratic (firstBody.assertions i))
      (tail : Same first second) :
      Same (.layer assertions firstBody first) (.layer assertions secondBody second)

namespace Same

/-- Assertion metadata is retained exactly, including the quadratic-first
ordering. Changing coefficients never changes an assertion's constructor. -/
def metadata {out mid assertions : ℕ}
    {first second : LfzkV2.Native.CircuitLayer (Cube out) (Cube mid) (Fin assertions) F}
    (classes : ∀ i, isQuadratic (second.assertions i) = isQuadratic (first.assertions i))
    (original : LayerMetadata first) : LayerMetadata second where
  fragments := original.fragments
  count := original.count
  quadratic_first i := (classes i).trans (original.quadratic_first i)

/-- Transfer the actual supplied metadata; no replacement identifiers or
component ordering are constructed. -/
def plan : {out input : ℕ} → {first second : Layered.Circuit F out input} →
    Same first second → Plan F first → Plan F second
  | _, _, _, _, .input, .input => .input
  | _, _, _, _, .entry .input, .inputEntry entries _ => .inputEntry entries _
  | _, _, _, _, .layer classes next, .layer fragments tail =>
      .layer (metadata classes fragments) (plan next tail)
  | _, _, _, _, .entry (.layer classes next), .entryLayer entries _ fragments tail =>
      .entryLayer entries _ (metadata classes fragments) (plan next tail)

theorem hasLayers {out input : ℕ} {first second : Layered.Circuit F out input}
    (same : Same first second) : FrontendReplay.hasLayers second = FrontendReplay.hasLayers first := by
  induction same with
  | input => rfl
  | entry _ ih => exact ih
  | layer => rfl

theorem frontend {out input : ℕ} {first second : Layered.Circuit F out input}
    (same : Same first second) (original : Plan F first) :
    (same.plan original).frontend = original.frontend := by
  induction original with
  | input => cases same; rfl
  | inputEntry entries entry =>
      cases same with
      | entry tail => cases tail; rfl
  | layer fragments tail ih =>
      cases same with
      | layer classes next =>
          simp only [plan,Plan.frontend,metadata,ih next]
  | entryLayer entries entry fragments tail ih =>
      cases same with
      | entry next =>
          cases next with
          | layer classes rest => simp only [plan,Plan.frontend,metadata,ih rest]

theorem capacityFrom {out input : ℕ} {first second : Layered.Circuit F out input}
    (same : Same first second) (original : Plan F first) (offset : ℕ) :
    (same.plan original).capacityFrom offset = original.capacityFrom offset := by
  induction original generalizing offset with
  | input => cases same; rfl
  | inputEntry entries entry =>
      cases same with
      | entry tail => cases tail; rfl
  | layer fragments tail ih =>
      cases same with
      | layer classes next =>
          simp only [plan,Plan.capacityFrom,next.hasLayers,ih next]
  | entryLayer entries entry fragments tail ih =>
      cases same with
      | entry next =>
          cases next with
          | layer classes rest => simp only [plan,Plan.capacityFrom,rest.hasLayers,ih rest]

theorem capacity {out input : ℕ} {first second : Layered.Circuit F out input}
    (same : Same first second) (original : Plan F first) :
    (same.plan original).capacity = original.capacity := same.capacityFrom original 0

end Same
end LfzkV2.Current.FrontendTopology

namespace LfzkV2.Current.Adapter.Circuit.Fragment
open FrontendTopology SumcheckV2
variable {F : Type} [Field F]

/-- Product-tree reduction has the same public grammar for every set of
coefficient values supplied to its leaf circuit. -/
def reduction_same {d q input : ℕ} (layout : Layout)
    (others : ∀ d q, Extension (F := F) (mid := layout.log d q)
      (layout.flat (half d) (half q))) (shape : Shape d q)
    (first second : Layered.Circuit F (layout.log d q) input) (same : Same first second) :
    Same (reduction layout others shape first) (reduction layout others shape second) := by
  induction shape with
  | root => exact same
  | pair next ih => exact ih _ _ (.layer (fun _ => rfl) same)

/-- Generated adapter coefficients change gate tensors; all assertion
constructors remain the other fragments' fixed constructors. -/
def body_same {d q input final : ℕ} (layout : Layout) (output : Fin 2 ↪ Cube final)
    (shape : Shape d q) (others : Others (F := F) layout d q input final output)
    (sources : Fin d → Cube input) (pads : Fin 2 → Fin q → Cube input)
    (firstPowers secondPowers : Fin 2 → Fin d → Fˣ) (firstBase secondBase : Fˣ)
    (firstMasked secondMasked : Fin 2 → Fin q → Bool) (firstTargets secondTargets : Fin 2 → Fˣ) :
    Same (body layout output shape others sources pads firstPowers firstBase firstMasked firstTargets)
      (body layout output shape others sources pads secondPowers secondBase secondMasked secondTargets) :=
  .layer (fun _ => rfl) (reduction_same layout others.pair shape _ _ (.layer (fun _ => rfl) .input))

def build_same {d q input final out : ℕ} (layout : Layout) (output : Fin 2 ↪ Cube final)
    (shape : Shape d q) (others : Others (F := F) layout d q input final output)
    (carry : Cube out → Option (Cube final))
    (sources : Fin d → Cube input) (pads : Fin 2 → Fin q → Cube input)
    (firstPowers secondPowers : Fin 2 → Fin d → Fˣ) (firstBase secondBase : Fˣ)
    (firstMasked secondMasked : Fin 2 → Fin q → Bool) (firstTargets secondTargets : Fin 2 → Fˣ) :
    Same (build layout output shape others carry sources pads firstPowers firstBase firstMasked firstTargets)
      (build layout output shape others carry sources pads secondPowers secondBase secondMasked secondTargets) :=
  .entry (body_same layout output shape others sources pads firstPowers secondPowers firstBase secondBase
    firstMasked secondMasked firstTargets secondTargets)

def Above.plug_same {out mid input : ℕ} (above : Above F out mid)
    (first second : Layered.Circuit F mid input) (same : Same first second) :
    Same (above.plug first) (above.plug second) := by
  induction above with
  | hole => exact same
  | entry _ _ _ ih => exact .entry (ih _ _ same)
  | layer _ _ _ ih => exact .layer (fun _ => rfl) (ih _ _ same)

end LfzkV2.Current.Adapter.Circuit.Fragment

namespace LfzkV2.Current.ApplicationSetup.BinaryPublic
open SumcheckV2 FrontendTopology FrontendSchedule
variable {B : Type} [Field B] [Algebra (ZMod 2) B] {shared maskBits adviceBits : ℕ}
variable (s : BinaryPublic B shared maskBits adviceBits)

/-- A fixed coefficient choice for public metadata. It is not a verifier
execution or a different circuit claim; only its grammar is reused below. -/
def template : Layered.Circuit B s.upper s.input :=
  s.circuit (fun _ _ => 1) 1 (fun _ _ => false) (fun _ => 1)

/-- The actual generated circuit has the template grammar for all adapter
challenges, advice bits and target values. -/
def same_template (powers : Fin 2 → Fin (shared+maskBits) → Bˣ) (base : Bˣ)
    (masked : Fin 2 → Fin adviceBits → Bool) (targets : Fin 2 → Bˣ) :
    Same s.template (s.circuit powers base masked targets) :=
  s.above.plug_same _ _ (Adapter.Circuit.Fragment.build_same s.layout s.output s.shape s.others
    s.carry s.sources s.advice (fun _ _ => 1) powers 1 base (fun _ _ => false) masked (fun _ => 1) targets)

def planFromTemplate (plan : Plan B s.template)
    (powers : Fin 2 → Fin (shared+maskBits) → Bˣ) (base : Bˣ)
    (masked : Fin 2 → Fin adviceBits → Bool) (targets : Fin 2 → Bˣ) :
    Plan B (s.circuit powers base masked targets) :=
  (s.same_template powers base masked targets).plan plan

theorem planFromTemplate_frontend (plan : Plan B s.template)
    (powers : Fin 2 → Fin (shared+maskBits) → Bˣ) (base : Bˣ)
    (masked : Fin 2 → Fin adviceBits → Bool) (targets : Fin 2 → Bˣ) :
    (s.planFromTemplate plan powers base masked targets).frontend = plan.frontend :=
  (s.same_template powers base masked targets).frontend plan

theorem planFromTemplate_capacity (plan : Plan B s.template)
    (powers : Fin 2 → Fin (shared+maskBits) → Bˣ) (base : Bˣ)
    (masked : Fin 2 → Fin adviceBits → Bool) (targets : Fin 2 → Bˣ) :
    (s.planFromTemplate plan powers base masked targets).capacity = plan.capacity :=
  (s.same_template powers base masked targets).capacity plan

end LfzkV2.Current.ApplicationSetup.BinaryPublic
