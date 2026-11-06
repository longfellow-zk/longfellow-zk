import LfzkV2.Current.Messages
import LfzkV2.Layered.Replay

/-! Decode the actual frontend body into the retained algebraic payload.
The public circuit determines every stage width. Entries consume no proof
payload, and a layer consumes exactly one coefficient/cross/claim record.
Wrong stage counts or widths are rejected before reconstruction; callers
supply neither decoded messages nor a semantic correspondence certificate. -/
namespace LfzkV2.Current.FrontendBody
open SumcheckV2

variable {E F : Type}

abbrev StagePayload (E : Type) := (rounds : ℕ) × Current.LayerPayload E rounds

def widths : {out input : ℕ} → Layered.Circuit F out input → List ℕ
  | _, _, .input => []
  | _, _, .entry _ _ rest => widths rest
  | _, _, .layer (mid := mid) _ _ rest => mid :: widths rest

/-- The body already fixes each stage's round count through trusted geometry.
This list view preserves its supplied order and all transmitted field cells. -/
def stages (frontend : Frontend) (body : FrontendPayload E frontend) : List (StagePayload E) :=
  (List.finRange frontend.stages.length).map fun i => ⟨(frontend.stages.get i).rounds,body i⟩

theorem stages_widths (frontend : Frontend) (body : FrontendPayload E frontend) :
    (stages frontend body).map Sigma.fst = frontend.stages.map Stage.rounds := by
  simpa only [stages, List.map_map, Function.comp_def] using
    congrArg (List.map Stage.rounds) (List.map_get_finRange frontend.stages)

def layer (field : E → F) {rounds : ℕ} (body : Current.LayerPayload E rounds) :
    Layered.Replay.LayerPayload F rounds where
  rounds i := ⟨field (body.coefficients i).1,field (body.coefficients i).2⟩
  cross := field body.cross
  claimA := field body.claims.1
  claimB := field body.claims.2

/-- The parser consumes precisely the layers of the public circuit. Zero
layers leave the remaining input untouched; zero-round layers still consume
one cross/claim record. -/
def readFrom (field : E → F) : {out input : ℕ} → (circuit : Layered.Circuit F out input) →
    List (StagePayload E) → Option (Layered.Replay.Payload circuit × List (StagePayload E))
  | _, _, .input, wire => some ((),wire)
  | _, _, .entry _ _ rest, wire => readFrom field rest wire
  | _, _, .layer .., [] => none
  | _, _, .layer (mid := mid) _ _ rest, ⟨rounds,body⟩ :: tail =>
      if h : rounds = mid then
        (readFrom field rest tail).map fun decoded => ((layer field (h ▸ body),decoded.1),decoded.2)
      else none

def read {out input : ℕ} (field : E → F) (circuit : Layered.Circuit F out input)
    (wire : List (StagePayload E)) : Option (Layered.Replay.Payload circuit) :=
  match readFrom field circuit wire with
  | none => none
  | some (payload,[]) => some payload
  | some (_, _ :: _) => none

/-- This is the body-facing entry point. Every input cell comes from the
actual typed `Body.binary` or `Body.prime` frontend payload. -/
def decode {out input : ℕ} (field : E → F) (circuit : Layered.Circuit F out input)
    (frontend : Frontend) (body : FrontendPayload E frontend) :
    Option (Layered.Replay.Payload circuit) := read field circuit (stages frontend body)

/-- Fix the frontend and messages to their actual complete-body fields.
The two branches are only the public participant order. -/
def ofBody {g : Geometry} {fields : Fields} {Advice Authentication : Type} {out input : ℕ}
    (circuit : Layered.Circuit F out input) (body : Body g fields Advice Authentication) :
    (side : Side) → (fields side → F) → Option (Layered.Replay.Payload circuit)
  | .binary, field => decode field circuit g.binary body.binary
  | .prime, field => decode field circuit g.prime body.prime

theorem readFrom_shape {out input : ℕ} (field : E → F) (circuit : Layered.Circuit F out input)
    (wire : List (StagePayload E)) (payload : Layered.Replay.Payload circuit)
    (unused : List (StagePayload E)) (h : readFrom field circuit wire = some (payload,unused)) :
    wire.map Sigma.fst = widths circuit ++ unused.map Sigma.fst := by
  induction circuit generalizing wire unused with
  | input =>
      cases Option.some.inj h
      rfl
  | entry _ _ _ ih => exact ih wire payload unused h
  | @layer out mid input a body rest ih =>
      cases wire with
      | nil => simp only [readFrom] at h; contradiction
      | cons head tail =>
          rcases head with ⟨rounds,head⟩
          by_cases hr : rounds = mid
          · subst rounds
            cases ht : readFrom field rest tail with
            | none => simp only [readFrom, ↓reduceDIte, ht, Option.map_none] at h; contradiction
            | some decoded =>
                simp only [readFrom, ↓reduceDIte, ht, Option.map_some] at h
                cases Option.some.inj h
                simpa only [List.map_cons, widths, List.cons_append] using
                  congrArg (List.cons mid) (ih tail decoded.1 decoded.2 ht)
          · simp only [readFrom, dif_neg hr] at h
            contradiction

/-- Successful decoding certifies the public stage dimensions and consumes
all body records. Malformed dimensions cannot be silently ignored. -/
theorem read_shape {out input : ℕ} (field : E → F) (circuit : Layered.Circuit F out input)
    (wire : List (StagePayload E)) (payload : Layered.Replay.Payload circuit)
    (h : read field circuit wire = some payload) : wire.map Sigma.fst = widths circuit := by
  unfold read at h
  cases hr : readFrom field circuit wire with
  | none => simp only [hr] at h; contradiction
  | some decoded =>
      rcases decoded with ⟨actual,unused⟩
      cases unused with
      | nil =>
        simpa only [List.map_nil, List.append_nil] using readFrom_shape field circuit wire actual [] hr
      | cons head tail => simp only [hr] at h; contradiction

theorem readFrom_complete {out input : ℕ} (field : E → F) (circuit : Layered.Circuit F out input)
    (wire : List (StagePayload E)) (h : wire.map Sigma.fst = widths circuit) :
    ∃ payload, readFrom field circuit wire = some (payload,[]) := by
  induction circuit generalizing wire with
  | input =>
      have hw : wire = [] := List.map_eq_nil_iff.mp h
      subst wire
      exact ⟨(),rfl⟩
  | entry _ _ _ ih => exact ih wire h
  | @layer out mid input a body rest ih =>
      cases wire with
      | nil =>
          simp only [List.map_nil, widths] at h
          cases h
      | cons head tail =>
          rcases head with ⟨rounds,head⟩
          have hh : rounds = mid ∧ tail.map Sigma.fst = widths rest := List.cons.inj h
          obtain ⟨rfl,htail⟩ := hh
          obtain ⟨payload,hpayload⟩ := ih tail htail
          exact ⟨(layer field head,payload), by
            simp only [readFrom, ↓reduceDIte, hpayload, Option.map_some]⟩

/-- Parsing depends only on public layer dimensions. Any field values of
that shape decode, and every successful decode has exactly that shape. -/
theorem read_exists_iff_shape {out input : ℕ} (field : E → F)
    (circuit : Layered.Circuit F out input) (wire : List (StagePayload E)) :
    (∃ payload, read field circuit wire = some payload) ↔ wire.map Sigma.fst = widths circuit := by
  constructor
  · rintro ⟨payload,h⟩
    exact read_shape field circuit wire payload h
  · intro h
    obtain ⟨payload,hpayload⟩ := readFrom_complete field circuit wire h
    exact ⟨payload,by simp only [read, hpayload]⟩

theorem decode_exists_iff_shape {out input : ℕ} (field : E → F)
    (circuit : Layered.Circuit F out input) (frontend : Frontend)
    (body : FrontendPayload E frontend) :
    (∃ payload, decode field circuit frontend body = some payload) ↔
      frontend.stages.map Stage.rounds = widths circuit := by
  simpa only [decode, stages_widths] using read_exists_iff_shape field circuit (stages frontend body)

/-- Flatten a retained payload solely for the inverse law of the parser.
No challenge values or pad cells are serialized by this operation. -/
def write : {out input : ℕ} → (circuit : Layered.Circuit F out input) →
    Layered.Replay.Payload circuit → List (StagePayload F)
  | _, _, .input, _ => []
  | _, _, .entry _ _ rest, payload => write rest payload
  | _, _, .layer (mid := mid) _ _ rest, payload =>
      ⟨mid,⟨fun i => ((payload.1.rounds i).c0,(payload.1.rounds i).c1),
        payload.1.cross,(payload.1.claimA,payload.1.claimB)⟩⟩ :: write rest payload.2

theorem readFrom_write_append {out input : ℕ} (circuit : Layered.Circuit F out input)
    (payload : Layered.Replay.Payload circuit) (tail : List (StagePayload F)) :
    readFrom id circuit (write circuit payload ++ tail) = some (payload,tail) := by
  induction circuit generalizing tail with
  | input => cases payload; rfl
  | entry _ _ _ ih => exact ih payload tail
  | @layer out mid input a body rest ih =>
      simp only [write, List.cons_append, readFrom, ↓reduceDIte, ih payload.2 tail, Option.map_some]
      cases payload with
      | mk head rest =>
          cases head
          rfl

theorem read_write {out input : ℕ} (circuit : Layered.Circuit F out input)
    (payload : Layered.Replay.Payload circuit) : read id circuit (write circuit payload) = some payload := by
  have hr := readFrom_write_append circuit payload []
  simp only [List.append_nil] at hr
  simp only [read, hr]

end LfzkV2.Current.FrontendBody
