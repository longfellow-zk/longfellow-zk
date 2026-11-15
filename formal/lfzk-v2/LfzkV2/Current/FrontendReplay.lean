import LfzkV2.Layered.Schedule

/-! Reconstruct the unchanged affine circuit compiler's messages from the
current grouped query schedule. An entry consumes coordinates of the current
assertion answer, rather than a new oracle answer. A frontend's first weights
come from its opening answer; every later stage's weights, and the input-only
checks, extend the preceding combine answer after alpha. This module
describes challenge consumption, not a new circuit representation or an
additional verifier acceptance assumption. -/
namespace LfzkV2.Current.FrontendReplay
open SumcheckV2

variable {F Pad C : Type}

def hasLayers : {out input : ℕ} → Layered.Circuit F out input → Bool
  | _, _, .input => false
  | _, _, .entry _ _ rest => hasLayers rest
  | _, _, .layer .. => true

/-- A layer uses its quadratic rounds, one nonzero terminal answer and one
combine answer, which also carries the next weights. The opening answer is
the one extra slot. Entry checks introduce no boundaries. -/
def slots : {out input : ℕ} → Layered.Circuit F out input → ℕ
  | _, _, .input => 1
  | _, _, .entry _ _ rest => slots rest
  | _, _, .layer (mid := mid) _ _ rest => mid + 2 + slots rest

theorem slots_positive {out input : ℕ} (circuit : Layered.Circuit F out input) :
    0 < slots circuit := by
  induction circuit with
  | input => simp [slots]
  | entry _ _ _ ih => exact ih
  | layer => simp only [slots]; omega

/-- The retained algebra names failure positions separately. This map locates
each position at its actual current query; it is intentionally not injective.
Entering outputs and layer assertions share an index, as do a combine and the
next weights or input-only assertions. Counting the old positions as queries is incorrect. -/
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
      | .inr (.inr (.inr (.inr role))) => queryIndex rest role (start+mid+2)

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
      · have := slots_positive rest; simp only [queryIndex, slots]; omega
      · have := i.isLt; have := slots_positive rest; simp only [queryIndex, slots]; omega
      · have := slots_positive rest; simp only [queryIndex, slots]; omega
      · have := slots_positive rest; simp only [queryIndex, slots]; omega
      · have h := ih role (start+mid+2)
        simp only [queryIndex, slots]
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
      · have h := ih role (start+mid+2)
        simp only [queryIndex]
        omega

variable [Field F]

/-- `decode` reads consecutive full-field coordinates of one boundary answer;
`nonzero` is the nonzero terminal sampler. The finite ideal-answer counting
model supplies their distribution laws separately. An entry and its following
layer deliberately use the same answer with different coordinate offsets, and
a layer's tail reads the combine answer after alpha. -/
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
      (m, readFrom decode nonzero rest plan.2 payload.2 answers (start+mid+2) 1)

def read (decode : C → ℕ → F) (nonzero : C → Linear.TerminalSampling.Nonzero F)
    {out input : ℕ} (circuit : Layered.Circuit F out input)
    (plan : Layered.Replay.PadPlan (Pad := Pad) circuit) (payload : Layered.Replay.Payload circuit)
    (answers : ℕ → C) : Layered.Circuit.Messages Pad circuit :=
  readFrom decode nonzero circuit plan payload answers 0 0

/-- Frontend reconstruction reads only its actual grouped answers. In
particular, a later backend answer cannot change the statement it authenticates.
The combine/next-weight sharing is included in the same prefix bound. -/
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
      have hpos := slots_positive rest
      have hs := hanswers start (by simp only [slots]; omega)
      have hp : (fun i : Fin mid => decode (first (start+1+i.val)) 0) =
          (fun i : Fin mid => decode (second (start+1+i.val)) 0) := by
        funext i
        rw [hanswers (start+1+i.val) (by have := i.isLt; simp only [slots]; omega)]
      have ht := hanswers (start+1+mid) (by simp only [slots]; omega)
      have hc := hanswers (start+mid+2) (by simp only [slots]; omega)
      have hr := ih plan.2 payload.2 (start+mid+2) 1 (by
          intro j hj
          apply hanswers
          simp only [slots]
          omega)
      dsimp only [readFrom]
      rw [hs, hp, ht, hc, hr]

/-- The coordinates of the last answer that the reader uses: alpha and the
input-only entries after a layer, or the input-only entries alone. -/
def lastWidth : {out input : ℕ} → Layered.Circuit F out input → ℕ → ℕ
  | _, _, .input, offset => offset
  | _, _, .entry n _ rest, offset => lastWidth rest (offset+n)
  | _, _, .layer _ _ rest, _ => lastWidth rest 1

omit [Field F] in
theorem hasLayers_false_of_slots {out input : ℕ} (circuit : Layered.Circuit F out input)
    (h : slots circuit = 1) : hasLayers circuit = false := by
  induction circuit with
  | input => rfl
  | entry _ _ _ ih => exact ih h
  | layer _ _ rest => have := slots_positive rest; simp only [slots] at h; omega

omit [Field F] in
theorem le_lastWidth {out input : ℕ} (circuit : Layered.Circuit F out input) (offset : ℕ) :
    offset ≤ lastWidth circuit offset ∨ hasLayers circuit = true := by
  induction circuit generalizing offset with
  | input => exact Or.inl le_rfl
  | entry n e rest ih =>
      rcases ih (offset+n) with h | h
      · exact Or.inl (by simp only [lastWidth]; omega)
      · exact Or.inr h
  | layer => exact Or.inr rfl

omit [Field F] in
theorem one_le_lastWidth {out input : ℕ} (circuit : Layered.Circuit F out input) (offset : ℕ)
    (h : 1 ≤ offset) : 1 ≤ lastWidth circuit offset := by
  induction circuit generalizing offset with
  | input => exact h
  | entry n e rest ih => exact ih (offset+n) (by omega)
  | layer _ _ rest ih => exact ih 1 le_rfl

/-- The last answer is read only through its first `lastWidth` full-field
coordinates: it is a combine or an opening answer, never a terminal one.
Changing anything else in that answer, such as the nonzero `eta` it also
carries, leaves the reconstructed messages unchanged. -/
theorem readFrom_eq_of_last_decode (decode : C → ℕ → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F)
    {out input : ℕ} (circuit : Layered.Circuit F out input)
    (plan : Layered.Replay.PadPlan (Pad := Pad) circuit) (payload : Layered.Replay.Payload circuit)
    (first second : ℕ → C) (start offset : ℕ)
    (hanswers : ∀ j, j+1 < start + slots circuit → first j = second j)
    (hdecode : ∀ i < lastWidth circuit offset,
      decode (first (start+slots circuit-1)) i = decode (second (start+slots circuit-1)) i) :
    readFrom decode nonzero circuit plan payload first start offset =
      readFrom decode nonzero circuit plan payload second start offset := by
  induction circuit generalizing start offset with
  | input => rfl
  | entry n e rest ih =>
      have hs : (fun i : Fin n => decode (first start) (offset+i.val)) =
          (fun i : Fin n => decode (second start) (offset+i.val)) := by
        funext i
        by_cases hlast : start+1 < start+slots rest
        · rw [hanswers start (by simp only [slots]; omega)]
        · have hpos := slots_positive rest
          have hone : slots rest = 1 := by omega
          have hrest : hasLayers rest = false := hasLayers_false_of_slots rest hone
          have hw : offset+n ≤ lastWidth rest (offset+n) := by
            rcases le_lastWidth rest (offset+n) with h | h
            · exact h
            · rw [h] at hrest; cases hrest
          have hd := hdecode (offset+i.val) (by simp only [lastWidth]; have := i.isLt; omega)
          simp only [slots, hone] at hd
          simpa using hd
      dsimp only [readFrom]
      rw [hs, ih plan payload start (offset+n) hanswers hdecode]
  | @layer out mid input a body rest ih =>
      have hpos := slots_positive rest
      have hs := hanswers start (by simp only [slots]; omega)
      have hp : (fun i : Fin mid => decode (first (start+1+i.val)) 0) =
          (fun i : Fin mid => decode (second (start+1+i.val)) 0) := by
        funext i
        rw [hanswers (start+1+i.val) (by have := i.isLt; simp only [slots]; omega)]
      have ht := hanswers (start+1+mid) (by simp only [slots]; omega)
      have hc : decode (first (start+mid+2)) 0 = decode (second (start+mid+2)) 0 := by
        by_cases hlast : start+mid+2+1 < start+(mid+2+slots rest)
        · rw [hanswers (start+mid+2) (by simp only [slots]; omega)]
        · have hd := hdecode 0 (by simp only [lastWidth]; exact one_le_lastWidth rest 1 le_rfl)
          have he : start+slots (.layer a body rest)-1 = start+mid+2 := by simp only [slots]; omega
          rw [he] at hd
          exact hd
      have hr := ih plan.2 payload.2 (start+mid+2) 1
        (fun j hj => hanswers j (by simp only [slots]; omega))
        (fun i hi => by
          have hd := hdecode i hi
          have he : start+slots (.layer a body rest)-1 = start+mid+2+slots rest-1 := by
            simp only [slots]; omega
          rw [he] at hd
          exact hd)
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
