import Mathlib.Algebra.BigOperators.Fin

/-! The query schedule of the current MAC-free mdoc verifier. This namespace is
separate from the retained `Layered` checkpoint, whose adapter and transcript
are different. A query here means one `begin_squeeze()`, not one sampled field element.
Public shape and circuit/layout correspondence are parameters of this model. -/
namespace LfzkV2.Current

inductive Side where
  | binary | prime
  deriving DecidableEq, Repr

/-- Boundary kinds of the challenge schedule. The deployed nodes absorb no
kind: every boundary ends with the same `ROUND` terminator
(`TaggedFormat.wire`). The model keeps the kinds, with distinct tags, to
classify boundaries. -/
inductive Domain where
  | output | assertions | sumcheck | terminal | combine | packing | statement
  | batching | opening | conversion | rowBatching | fingerprint
  deriving DecidableEq, Repr

def Domain.tag : Domain → Fin 13
  | .output => 0 | .assertions => 1 | .sumcheck => 2 | .terminal => 3
  | .combine => 4 | .packing => 5 | .statement => 6 | .batching => 7
  | .opening => 8 | .conversion => 10 | .rowBatching => 11
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

/-- `assertions` is a frontend's opening boundary: the query that closes the
predecessor's messages and draws stage 0's weights (entering outputs, then
quadratic, then linear assertions). A later stage has no boundary of its own
for these weights; the preceding stage's `combine` answer carries them after
alpha, as the last stage's carries the input entries (`last`). The prime
frontend's last boundary also draws the split's nonzero `eta` after them. -/
inductive Role where
  | fingerprint
  | inputAssertions (side : Side) (entries : List Entry)
  | assertions (side : Side) (stage : ℕ) (entries : List Entry) (fragments : List Fragment)
  | sumcheck (side : Side) (stage round : ℕ)
  | terminal (side : Side) (stage : ℕ)
  | combine (side : Side) (stage : ℕ) (entries : List Entry) (fragments : List Fragment) (last : Bool)
  /-- Pure-foreign storage only (`rust/src/runtime/v2/zk/batching.rs`). The mdoc schedule has
  mixed storage, whose layer rows go to Polygero unbatched. -/
  | rowBatching
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

/-- The assertion weights read at stage `i`: its entering outputs and
fragments, or the input entries once `i` is past the last stage. -/
def Frontend.weightsAt (f : Frontend) (i : ℕ) : List Entry × List Fragment :=
  match f.stages[i]? with
  | some stage => (stage.entering, stage.fragments)
  | none => (f.inputEntries, [])

/-- The opening boundary draws stage 0's weights, or the input assertions
of a frontend with no stages. -/
def Frontend.opening (side : Side) (f : Frontend) : Role :=
  match f.stages[0]? with
  | some stage => .assertions side 0 stage.entering stage.fragments
  | none => .inputAssertions side f.inputEntries

/-- A stage's combine answer carries the next stage's weights after alpha. -/
def Stage.roles (side : Side) (index : ℕ) (s : Stage) (next : List Entry × List Fragment)
    (last : Bool) : List Role :=
  (List.range s.rounds).map (.sumcheck side index) ++
    [.terminal side index, .combine side index next.1 next.2 last]

/-- Circuit outputs are zero assertions at their own stage. Input-only circuits
share the last combine answer; with no stages, one input assertion block remains. -/
def Frontend.roles (side : Side) (f : Frontend) : List Role :=
  f.opening side :: (List.finRange f.stages.length).flatMap fun i =>
    (f.stages.get i).roles side i.val (f.weightsAt (i.val+1)) (i.val+1 = f.stages.length)

def Frontend.sumcheckRounds (f : Frontend) : ℕ :=
  ∑ i : Fin f.stages.length, (f.stages.get i).rounds

theorem Stage.roles_length (side : Side) (index : ℕ) (s : Stage) (next : List Entry × List Fragment)
    (last : Bool) : (s.roles side index next last).length = s.rounds + 2 := by
  simp [roles]

/-- One opening boundary, then each stage's rounds, terminal and combine. -/
theorem Frontend.roles_length (side : Side) (f : Frontend) :
    (f.roles side).length = f.sumcheckRounds + 2*f.stages.length + 1 := by
  simp only [roles, List.length_cons, List.length_flatMap, Stage.roles_length, ← Fin.sum_univ_def,
    sumcheckRounds, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]
  omega

theorem Frontend.mem_roles {side : Side} {f : Frontend} {role : Role} (h : role ∈ f.roles side) :
    role = f.opening side ∨ ∃ i : Fin f.stages.length,
      role ∈ (f.stages.get i).roles side i.val (f.weightsAt (i.val+1)) (i.val+1 = f.stages.length) := by
  simp only [roles, List.mem_cons, List.mem_flatMap, List.mem_finRange, true_and] at h
  exact h

/-- The opening boundary is stage 0's assertions, or the input assertions
of a frontend with no stages. -/
theorem Frontend.opening_cases (side : Side) (f : Frontend) :
    (f.stages = [] ∧ f.opening side = .inputAssertions side f.inputEntries) ∨
      ∃ (h : 0 < f.stages.length), f.opening side =
        .assertions side 0 (f.stages.get ⟨0,h⟩).entering (f.stages.get ⟨0,h⟩).fragments := by
  rcases f with ⟨_ | ⟨first, tail⟩, inputs⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨by simp, rfl⟩

theorem Stage.mem_roles {side : Side} {index : ℕ} {s : Stage} {next : List Entry × List Fragment}
    {last : Bool} {role : Role} (h : role ∈ s.roles side index next last) :
    (∃ round < s.rounds, role = .sumcheck side index round) ∨ role = .terminal side index ∨
      role = .combine side index next.1 next.2 last := by
  simp only [roles, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at h
  rcases h with ⟨round, hround, rfl⟩ | rfl | rfl
  · exact Or.inl ⟨round, hround, rfl⟩
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem Frontend.roles_ne_nil (side : Side) (f : Frontend) : f.roles side ≠ [] := by
  simp [roles]

/-- The frontend's last boundary. The prime frontend's also draws `eta`. -/
def Frontend.lastRole (side : Side) (f : Frontend) : Role :=
  (f.roles side).getLast (f.roles_ne_nil side)

private theorem getLast_finRange_flatMap {α : Type} (k : ℕ) (g : Fin (k+1) → List α)
    (h : g (Fin.last k) ≠ []) (hne : (List.finRange (k+1)).flatMap g ≠ []) :
    ((List.finRange (k+1)).flatMap g).getLast hne = (g (Fin.last k)).getLast h := by
  simp only [List.finRange_succ_last, List.flatMap_append, List.flatMap_singleton]
  exact List.getLast_append_of_ne_nil _ h

/-- The last boundary is the last stage's combine, or the opening input
assertions of a frontend with no stages. -/
theorem Frontend.lastRole_cases (side : Side) (f : Frontend) :
    (f.stages = [] ∧ f.lastRole side = .inputAssertions side f.inputEntries) ∨
      (f.stages ≠ [] ∧ ∃ stage, f.lastRole side = .combine side stage f.inputEntries [] true) := by
  rcases f with ⟨_ | ⟨first, rest⟩, inputs⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · apply Or.inr
    refine ⟨List.cons_ne_nil _ _, ?_⟩
    let f : Frontend := ⟨first :: rest, inputs⟩
    have hstage : (f.stages.get (Fin.last rest.length)).roles side rest.length
        (f.weightsAt (rest.length+1)) (rest.length+1 = f.stages.length) ≠ [] := by
      simp [Stage.roles]
    refine ⟨rest.length, ?_⟩
    simp only [lastRole, roles]
    rw [List.getLast_cons (by
      intro hnil
      exact hstage (List.flatMap_eq_nil_iff.mp hnil (Fin.last rest.length) (List.mem_finRange _)))]
    refine (getLast_finRange_flatMap rest.length
      (fun i => (f.stages.get i).roles side i.val (f.weightsAt (i.val+1)) (i.val+1 = f.stages.length))
      hstage _).trans ?_
    simp [Stage.roles, f, weightsAt]

/-- Bind-only operations do not create extra oracle queries. The payloads at
the query itself (round polynomials, H/Z, etc.) are described in `Messages`. -/
inductive Binding where
  | setup
  | fingerprints
  | frontend (side : Side)
  /-- The split claim, reconstructed locally by both roles and never absorbed. -/
  | primeClaim
  | maskedOpening
  | adapterAdvice
  | packingStatement
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

/-- Rows of each Polygero statement. The prime statement has its unbatched
layer rows, the native split row and the two fingerprint rows. -/
def Geometry.affineRows (g : Geometry) : Side → ℕ
  | .binary => g.binary.stages.length + (if g.packingDegree = 1 then 1 else 2) + 2
  | .prime => g.prime.stages.length + 1 + 2

/-- Every ordinary row reserves `openings` masking coordinates. The two
fingerprint masks are witness cells; Polygero's three row masks are separate. -/
def Geometry.dataRows (g : Geometry) (side : Side) : ℕ :=
  (g.cells side + 2 + (g.rowDimension - g.openings) - 1) /
    (g.rowDimension - g.openings)

def Geometry.batchedRows (g : Geometry) (side : Side) : ℕ := g.dataRows side + 2

def packingActions (degree : ℕ) : List Action :=
  if degree = 1 then [] else
    [.bind .packingStatement, .query .packing, .bind .packingResponse]

@[simp] theorem packingActions_one : packingActions 1 = [] := rfl

/-- Verifier chronology, not proof serialization order. In particular the
prime frontend runs before the binary frontend even though the joint typed
participant list, fingerprint vectors and backend samples are binary first. -/
def Geometry.actions (g : Geometry) : List Action :=
  [.bind .setup, .query .fingerprint, .bind .fingerprints, .bind (.frontend .prime)] ++
  (g.prime.roles .prime).map Action.query ++
  [.bind .primeClaim, .bind .maskedOpening, .query .conversion, .bind .adapterAdvice, .bind (.frontend .binary)] ++
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
      [.conversion] ++ g.binary.roles .binary ++
      (if g.packingDegree = 1 then [] else [.packing]) ++
      [.batching, .opening] := by
  by_cases h : g.packingDegree = 1 <;>
    simp [roles, actions, packingActions, h, Action.queryRole, List.filterMap_map]

/-- Four non-frontend boundaries, plus optional packing. The final seal adds
a strand-node hash and a PRF hash and is counted separately. -/
theorem Geometry.roles_length (g : Geometry) :
    g.roles.length = (g.prime.roles .prime).length + (g.binary.roles .binary).length +
      (if g.packingDegree = 1 then 0 else 1) + 4 := by
  rw [g.roles_eq]
  by_cases h : g.packingDegree = 1 <;> simp [h] <;> omega

theorem Geometry.last_action (g : Geometry) : g.actions.getLast? = some .finalSeal := by
  simp only [actions, List.getLast?_append]
  rfl

end LfzkV2.Current
