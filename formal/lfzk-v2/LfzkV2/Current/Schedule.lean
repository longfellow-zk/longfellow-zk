import Mathlib.Data.List.FinRange
import Mathlib.Tactic

/-! The query schedule of the current MAC-free mdoc verifier. This namespace is
separate from the retained `Layered` checkpoint, whose adapter and transcript
are different. A query here means one `begin_squeeze()`, not one sampled field element.
Public shape and circuit/layout correspondence are parameters of this model. -/
namespace LfzkV2.Current

inductive Side where
  | binary | prime
  deriving DecidableEq, Repr

/-- The tags in `runtime/v2/transcript/src/lib.rs`. Finalization has a separate domain. -/
inductive Domain where
  | output | assertions | sumcheck | terminal | combine | packing | statement
  | batching | opening | rescaling | conversion | rowBatching | fingerprint
  deriving DecidableEq, Repr

def Domain.tag : Domain → Fin 13
  | .output => 0 | .assertions => 1 | .sumcheck => 2 | .terminal => 3
  | .combine => 4 | .packing => 5 | .statement => 6 | .batching => 7
  | .opening => 8 | .rescaling => 9 | .conversion => 10 | .rowBatching => 11
  | .fingerprint => 12

theorem Domain.tag_injective : Function.Injective Domain.tag := by
  intro a b h
  cases a <;> cases b <;> simp_all [tag]

structure Entry where
  circuit : ℕ
  outputs : ℕ
  deriving DecidableEq, Repr

structure Fragment where
  circuit : ℕ
  layer : ℕ
  quadraticAssertions : ℕ
  linearAssertions : ℕ
  deriving DecidableEq, Repr

/-- Only sparse quad fragments are local to a circuit. Rounds act on the one
global wire array, with one shared assertion block per layer. -/
structure Stage where
  entering : List Entry
  fragments : List Fragment
  rounds : ℕ
  deriving DecidableEq, Repr

structure Frontend where
  stages : List Stage
  inputEntries : List Entry
  deriving DecidableEq, Repr

inductive Role where
  | fingerprint
  | inputAssertions (side : Side) (entries : List Entry)
  | assertions (side : Side) (stage : ℕ) (entries : List Entry) (fragments : List Fragment)
  | sumcheck (side : Side) (stage round : ℕ)
  | terminal (side : Side) (stage : ℕ)
  | combine (side : Side) (stage : ℕ) (inputEntries : List Entry)
  | rowBatching
  | rescaling
  | conversion
  | packing
  | batching
  | opening
  deriving DecidableEq, Repr

def Role.domain : Role → Domain
  | .fingerprint => .fingerprint
  | .inputAssertions .. => .assertions
  | .assertions .. => .assertions
  | .sumcheck .. => .sumcheck
  | .terminal .. => .terminal
  | .combine .. => .combine
  | .rowBatching => .rowBatching
  | .rescaling => .rescaling
  | .conversion => .conversion
  | .packing => .packing
  | .batching => .batching
  | .opening => .opening

/-- The participant owning a frontend boundary. Auxiliary and backend
protocol roles have their own dispatch and carry no frontend side. -/
def frontendSide : Role → Option Side
  | .inputAssertions side .. | .assertions side .. | .sumcheck side .. |
      .terminal side .. | .combine side .. => some side
  | _ => none

def Stage.roles (side : Side) (index : ℕ) (s : Stage) (inputEntries : List Entry) : List Role :=
  [.assertions side index s.entering s.fragments] ++
    (List.range s.rounds).map (.sumcheck side index) ++
    [.terminal side index, .combine side index inputEntries]

/-- Circuit outputs are zero assertions at their own stage. Input-only circuits
share the last combine answer; with no stages, one input assertion block remains. -/
def Frontend.roles (side : Side) (f : Frontend) : List Role :=
  if f.stages.isEmpty then [.inputAssertions side f.inputEntries] else
    (List.finRange f.stages.length).flatMap fun i =>
      (f.stages.get i).roles side i.val (if i.val+1 = f.stages.length then f.inputEntries else [])

def Frontend.sumcheckRounds (f : Frontend) : ℕ :=
  ∑ i : Fin f.stages.length, (f.stages.get i).rounds

theorem Stage.roles_length (side : Side) (index : ℕ) (s : Stage) (inputEntries : List Entry) :
    (s.roles side index inputEntries).length = s.rounds + 3 := by
  simp [roles]

theorem Frontend.roles_length (side : Side) (f : Frontend) :
    (f.roles side).length = if f.stages.isEmpty then 1 else
      f.sumcheckRounds + 3*f.stages.length := by
  by_cases h : f.stages.isEmpty
  · simp [roles, h]
  · simp only [roles, h, Bool.false_eq_true, ↓reduceIte, List.length_flatMap, Stage.roles_length,
      ← Fin.sum_univ_def, sumcheckRounds, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    omega

/-- Bind-only operations do not create extra oracle queries. The payloads at
the query itself (round polynomials, H/Z, etc.) are described in `Messages`. -/
inductive Binding where
  | setup
  | fingerprints
  | frontend (side : Side)
  | primeClaim
  | maskedOpening
  | adapterAdvice
  | packingSource
  | packingResponse
  deriving DecidableEq, Repr

inductive Action where
  | bind (binding : Binding)
  | query (role : Role)
  | finalSeal
  deriving DecidableEq, Repr

structure Geometry where
  binary : Frontend
  prime : Frontend
  binaryCells : ℕ
  primeCells : ℕ
  packingDegree : ℕ
  packingPositive : 0 < packingDegree
  rowDimension : ℕ
  maskingDegree : ℕ
  columns : ℕ
  openings : ℕ
  openingsPositive : 0 < openings
  openings_lt : openings < rowDimension
  openings_le : openings ≤ columns
  responseFits : rowDimension + maskingDegree ≤ columns
  productFits : 2 * rowDimension ≤ columns

/-- `binaryCells` and `primeCells` exclude the two dedicated fingerprint
masks. In mdoc the prime projection also excludes the shared bit prefix;
that prefix must be recovered from the selected binary witness. -/
def Geometry.cells (g : Geometry) : Side → ℕ
  | .binary => g.binaryCells
  | .prime => g.primeCells

def Geometry.affineRows (g : Geometry) : Side → ℕ
  | .binary => g.binary.stages.length + (if g.packingDegree = 1 then 1 else 2) + 2
  | .prime => 1 + 2

/-- Every ordinary row reserves `openings` masking coordinates. The two
fingerprint masks are witness cells; Polygero's three row masks are separate. -/
def Geometry.dataRows (g : Geometry) (side : Side) : ℕ :=
  (g.cells side + 2 + (g.rowDimension - g.openings) - 1) /
    (g.rowDimension - g.openings)

def Geometry.batchedRows (g : Geometry) (side : Side) : ℕ := g.dataRows side + 2

def packingActions (degree : ℕ) : List Action :=
  if degree = 1 then [] else
    [.bind .packingSource, .query .packing, .bind .packingResponse]

@[simp] theorem packingActions_one : packingActions 1 = [] := rfl

/-- Verifier chronology, not proof serialization order. In particular the
prime frontend runs before the binary frontend even though the joint typed
participant list, fingerprint vectors and backend samples are binary first. -/
def Geometry.actions (g : Geometry) : List Action :=
  [.bind .setup, .query .fingerprint, .bind .fingerprints, .bind (.frontend .prime)] ++
  (g.prime.roles .prime).map Action.query ++
  [.query .rowBatching, .bind .primeClaim, .query .rescaling,
    .bind .maskedOpening, .query .conversion, .bind .adapterAdvice, .bind (.frontend .binary)] ++
  (g.binary.roles .binary).map Action.query ++ packingActions g.packingDegree ++
  [.query .batching, .query .opening, .finalSeal]

def Action.queryRole : Action → Option Role
  | .query r => some r
  | _ => none

def Geometry.roles (g : Geometry) : List Role := g.actions.filterMap Action.queryRole

/-- The two conversion challenges, all four fingerprint vectors and both
participants' backend samples each belong to their respective single block. -/
theorem Geometry.roles_eq (g : Geometry) :
    g.roles = [.fingerprint] ++ g.prime.roles .prime ++
      [.rowBatching, .rescaling, .conversion] ++ g.binary.roles .binary ++
      (if g.packingDegree = 1 then [] else [.packing]) ++
      [.batching, .opening] := by
  by_cases h : g.packingDegree = 1 <;>
    simp [roles, actions, packingActions, h, Action.queryRole, List.filterMap_map]

/-- Six non-frontend boundaries, plus optional packing. The final seal is
one additional query in its own domain and is deliberately counted separately. -/
theorem Geometry.roles_length (g : Geometry) :
    g.roles.length = (g.prime.roles .prime).length + (g.binary.roles .binary).length +
      (if g.packingDegree = 1 then 0 else 1) + 6 := by
  rw [g.roles_eq]
  by_cases h : g.packingDegree = 1 <;> simp [h] <;> omega

theorem Geometry.last_action (g : Geometry) : g.actions.getLast? = some .finalSeal := by
  simp only [actions, List.getLast?_append]
  rfl

end LfzkV2.Current
