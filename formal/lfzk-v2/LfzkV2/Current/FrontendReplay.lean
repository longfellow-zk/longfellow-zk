import LfzkV2.Layered.Schedule

/-! Reconstruct the unchanged affine circuit compiler's messages from the
current grouped query schedule. An entry consumes coordinates of the current
assertion answer, rather than a new oracle answer. Input-only checks extend
the final combine answer after alpha. Empty assertion vectors still have one
layer boundary. This module describes challenge consumption, not a new circuit
representation or an additional verifier acceptance assumption. -/
namespace LfzkV2.Current.FrontendReplay
open SumcheckV2

variable {F Pad C : Type}

def hasLayers : {out input : ℕ} → Layered.Circuit F out input → Bool
  | _, _, .input => false
  | _, _, .entry _ _ rest => hasLayers rest
  | _, _, .layer .. => true

/-- A layer uses one assertion answer, its quadratic rounds, one nonzero
terminal answer and one combine answer. Entry checks introduce no boundaries. -/
def slots : {out input : ℕ} → Layered.Circuit F out input → ℕ
  | _, _, .input => 1
  | _, _, .entry _ _ rest => slots rest
  | _, _, .layer (mid := mid) _ _ rest =>
      mid + 3 + if hasLayers rest then slots rest else 0

theorem slots_positive {out input : ℕ} (circuit : Layered.Circuit F out input) :
    0 < slots circuit := by
  induction circuit with
  | input => simp [slots]
  | entry _ _ _ ih => exact ih
  | layer => simp only [slots]; omega

theorem no_layers {out input : ℕ} (circuit : Layered.Circuit F out input)
    (h : hasLayers circuit = false) : circuit.layers = 0 ∧ circuit.rounds = 0 := by
  induction circuit with
  | input => exact ⟨rfl,rfl⟩
  | entry _ _ _ ih => exact ih h
  | layer => simp [hasLayers] at h

/-- This is the count used by the Rust loop, independent of the number of
entries or quad fragments. It also accounts for an input-only frontend. -/
theorem slots_eq {out input : ℕ} (circuit : Layered.Circuit F out input) :
    slots circuit = if hasLayers circuit then circuit.rounds + 3*circuit.layers else 1 := by
  induction circuit with
  | input => rfl
  | entry _ _ _ ih => exact ih
  | @layer out mid input n body rest ih =>
      by_cases h : hasLayers rest = true
      · simp only [slots, h, ↓reduceIte] at ih ⊢
        simp only [hasLayers, ↓reduceIte, Layered.Circuit.rounds, Layered.Circuit.layers]
        omega
      · have hf : hasLayers rest = false := Bool.eq_false_iff.mpr h
        have hz := no_layers rest hf
        simp [slots, hasLayers, hf, Layered.Circuit.rounds, Layered.Circuit.layers, hz.1, hz.2]

/-- The retained algebra names failure positions separately. This map locates
each position at its actual current query; it is intentionally not injective.
Entering outputs and layer assertions share an index, as do the last combine
and input-only assertions. Counting the old positions as queries is incorrect. -/
def queryIndex : {out input : ℕ} → (circuit : Layered.Circuit F out input) →
    Layered.Replay.LayerRole circuit → ℕ → ℕ
  | _, _, .input, role, _ => Fin.elim0 role
  | _, _, .entry _ _ rest, role, start =>
      match role with
      | .inl _ => start
      | .inr role => queryIndex rest role start
  | _, _, .layer (mid := mid) _ _ rest, role, start =>
      match role with
      | .inl _ => start
      | .inr (.inl i) => start+1+i.val
      | .inr (.inr (.inl _)) => start+1+mid
      | .inr (.inr (.inr (.inl _))) => start+mid+2
      | .inr (.inr (.inr (.inr role))) =>
          queryIndex rest role (if hasLayers rest then start+mid+3 else start+mid+2)

theorem queryIndex_lt {out input : ℕ} (circuit : Layered.Circuit F out input)
    (role : Layered.Replay.LayerRole circuit) (start : ℕ) :
    queryIndex circuit role start < start+slots circuit := by
  induction circuit generalizing start with
  | input => exact Fin.elim0 role
  | entry n e rest ih =>
      cases role with
      | inl _ => have := slots_positive rest; simp only [queryIndex, slots]; omega
      | inr role => exact ih role start
  | @layer out mid input a body rest ih =>
      rcases role with i | i | i | i | role
      · simp only [queryIndex, slots]; omega
      · have := i.isLt; simp only [queryIndex, slots]; omega
      · simp only [queryIndex, slots]; omega
      · simp only [queryIndex, slots]; omega
      · have h := ih role (if hasLayers rest then start+mid+3 else start+mid+2)
        by_cases hr : hasLayers rest = true
        · simpa only [queryIndex, slots, hr, ↓reduceIte, Nat.add_assoc] using h
        · have hf : hasLayers rest = false := Bool.eq_false_iff.mpr hr
          have hz : slots rest = 1 := by rw [slots_eq, hf]; rfl
          simp only [hf, Bool.false_eq_true, ↓reduceIte, hz] at h
          simp only [queryIndex, slots, hf, Bool.false_eq_true, ↓reduceIte]
          omega

theorem queryIndex_ge {out input : ℕ} (circuit : Layered.Circuit F out input)
    (role : Layered.Replay.LayerRole circuit) (start : ℕ) :
    start ≤ queryIndex circuit role start := by
  induction circuit generalizing start with
  | input => exact Fin.elim0 role
  | entry n e rest ih =>
      cases role with
      | inl _ => exact le_refl _
      | inr role => exact ih role start
  | @layer out mid input a body rest ih =>
      rcases role with i | i | i | i | role
      · exact le_refl _
      · simp only [queryIndex]; omega
      · simp only [queryIndex]; omega
      · simp only [queryIndex]; omega
      · have h := ih role (if hasLayers rest then start+mid+3 else start+mid+2)
        simp only [queryIndex]
        split_ifs at h ⊢ <;> omega

variable [Field F]

/-- `decode` reads consecutive full-field coordinates of one boundary answer;
`nonzero` is the nonzero terminal sampler. The finite ideal-answer counting
model supplies their distribution laws separately. An entry and its following
layer deliberately use the same answer with different coordinate offsets. -/
def readFrom (decode : C → ℕ → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F) :
    {out input : ℕ} → (circuit : Layered.Circuit F out input) →
    Layered.Replay.PadPlan (Pad := Pad) circuit → Layered.Replay.Payload circuit →
    (ℕ → C) → ℕ → ℕ → Layered.Circuit.Messages Pad circuit
  | _, _, .input, _, _, _, _, _ => ()
  | _, _, .entry n _ rest, plan, payload, answers, start, offset =>
      (fun i => decode (answers start) (offset+i.val),
        readFrom decode nonzero rest plan payload answers start (offset+n))
  | _, _, .layer (mid := mid) a _ rest, plan, payload, answers, start, offset =>
      let m : Linear.LayerMessages Pad F mid a := {
        roundMessages := payload.1.rounds
        roundPads := plan.1.round
        point i := decode (answers (start+1+i.val)) 0
        beta i := decode (answers start) (offset+i.val)
        cross := payload.1.cross
        scale := (nonzero (answers (start+1+mid))).val
        messageA := payload.1.claimA
        messageB := payload.1.claimB
        padA := plan.1.a, padB := plan.1.b, padAB := plan.1.ab, padD := plan.1.d
        alpha := decode (answers (start+mid+2)) 0 }
      let next := if hasLayers rest then start+mid+3 else start+mid+2
      let nextOffset := if hasLayers rest then 0 else 1
      (m, readFrom decode nonzero rest plan.2 payload.2 answers next nextOffset)

def read (decode : C → ℕ → F) (nonzero : C → Linear.TerminalSampling.Nonzero F)
    {out input : ℕ} (circuit : Layered.Circuit F out input)
    (plan : Layered.Replay.PadPlan (Pad := Pad) circuit) (payload : Layered.Replay.Payload circuit)
    (answers : ℕ → C) : Layered.Circuit.Messages Pad circuit :=
  readFrom decode nonzero circuit plan payload answers 0 0

/-- Frontend reconstruction reads only its actual grouped answers. In
particular, a later backend answer cannot change the statement it authenticates.
The last combine/input-entry sharing is included in the same prefix bound. -/
theorem readFrom_eq_of_prefix (decode : C → ℕ → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F)
    {out input : ℕ} (circuit : Layered.Circuit F out input)
    (plan : Layered.Replay.PadPlan (Pad := Pad) circuit) (payload : Layered.Replay.Payload circuit)
    (first second : ℕ → C) (start offset : ℕ)
    (hanswers : ∀ j, j < start + slots circuit → first j = second j) :
    readFrom decode nonzero circuit plan payload first start offset =
      readFrom decode nonzero circuit plan payload second start offset := by
  induction circuit generalizing start offset with
  | input => rfl
  | entry n e rest ih =>
      have hs := hanswers start (by have := slots_positive rest; simp only [slots]; omega)
      dsimp only [readFrom]
      rw [hs, ih plan payload start (offset+n) hanswers]
  | @layer out mid input a body rest ih =>
      have hs := hanswers start (by simp only [slots]; omega)
      have hp : (fun i : Fin mid => decode (first (start+1+i.val)) 0) =
          (fun i : Fin mid => decode (second (start+1+i.val)) 0) := by
        funext i
        rw [hanswers (start+1+i.val) (by have := i.isLt; simp only [slots]; omega)]
      have ht := hanswers (start+1+mid) (by simp only [slots]; omega)
      have hc := hanswers (start+mid+2) (by simp only [slots]; omega)
      have hr := ih plan.2 payload.2
        (if hasLayers rest then start+mid+3 else start+mid+2)
        (if hasLayers rest then 0 else 1) (by
          intro j hj
          apply hanswers
          by_cases h : hasLayers rest = true
          · simp only [h, ↓reduceIte] at hj
            simp only [slots, h, ↓reduceIte]
            omega
          · have hf : hasLayers rest = false := Bool.eq_false_iff.mpr h
            have hz : slots rest = 1 := by rw [slots_eq, hf]; rfl
            simp only [hf, Bool.false_eq_true, ↓reduceIte, hz] at hj
            simp only [slots, hf, Bool.false_eq_true, ↓reduceIte]
            omega)
      dsimp only [readFrom]
      rw [hs, hp, ht, hc, hr]

/-- Parsing the grouped answers still feeds the actual retained affine
compiler. No additional constraints or product-cell consistency are assumed. -/
theorem constraints_total (decode : C → ℕ → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F)
    {out input : ℕ} (circuit : Layered.Circuit F out input)
    (plan : Layered.Replay.PadPlan (Pad := Pad) circuit) (payload : Layered.Replay.Payload circuit)
    (answers : ℕ → C) :
    ∃ cs, Linear.buildConstraints (circuit.proof (read decode nonzero circuit plan payload answers) 0) =
      some cs :=
  Layered.Replay.constraints_total circuit _ _ _

end LfzkV2.Current.FrontendReplay
