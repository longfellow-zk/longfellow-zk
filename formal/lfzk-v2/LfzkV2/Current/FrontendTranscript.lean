import LfzkV2.Current.FrontendCausality

/-! The prover-message part of the grouped frontend transcript.  Assertions
write no polynomial, a quadratic round writes its two coefficients, the
terminal boundary writes the cross coefficient, and combine writes the two
claims.  Entries and fragments never introduce additional message slots.

The reader below reconstructs a payload from those messages.  Its inverse and
prefix lemmas are proved here, rather than supplied as certificates by a
verifier caller.  This is a logical message codec; canonical byte framing is
a separate layer. -/
namespace LfzkV2.Current.FrontendTranscript
open SumcheckV2
open Layered.Replay (LayerRole Message Payload layerMessage)

variable {F : Type} [Field F]

def polynomial : Message F → RoundPoly F
  | .round p => p
  | _ => ⟨0, 0⟩

def cross : Message F → F
  | .cross x => x
  | _ => 0

def claims : Message F → F × F
  | .claims a b => (a, b)
  | _ => (0, 0)

/-- One message per existing boundary.  The empty message has no field bytes;
it does not add a boundary.  Future recursion starts after combine, except
for input-only entries, whose coefficient reads share that combine answer. -/
def writeFrom : {out input : ℕ} → (circuit : Layered.Circuit F out input) →
    Payload circuit → ℕ → ℕ → Message F
  | _, _, .input, _, _, _ => .empty
  | _, _, .entry _ _ rest, payload, start, q => writeFrom rest payload start q
  | _, _, .layer (mid := mid) _ _ rest, payload, start, q =>
      if h : start+1 ≤ q ∧ q < start+1+mid then
        .round (payload.1.rounds ⟨q-(start+1), by omega⟩)
      else if q = start+1+mid then .cross payload.1.cross
      else if q = start+mid+2 then .claims payload.1.claimA payload.1.claimB
      else writeFrom rest payload.2
        (if FrontendReplay.hasLayers rest then start+mid+3 else start+mid+2) q

/-- The payload has only prover messages.  No challenge is recovered from a
message, and reading a payload performs no oracle query. -/
def readFrom : {out input : ℕ} → (circuit : Layered.Circuit F out input) →
    (ℕ → Message F) → ℕ → Payload circuit
  | _, _, .input, _, _ => ()
  | _, _, .entry _ _ rest, wire, start => readFrom rest wire start
  | _, _, .layer (mid := mid) _ _ rest, wire, start =>
      (⟨fun i => polynomial (wire (start+1+i.val)), cross (wire (start+1+mid)),
        (claims (wire (start+mid+2))).1, (claims (wire (start+mid+2))).2⟩,
       readFrom rest wire
        (if FrontendReplay.hasLayers rest then start+mid+3 else start+mid+2))

def write {out input : ℕ} (circuit : Layered.Circuit F out input)
    (payload : Payload circuit) : ℕ → Message F := writeFrom circuit payload 0

def read {out input : ℕ} (circuit : Layered.Circuit F out input)
    (wire : ℕ → Message F) : Payload circuit := readFrom circuit wire 0

theorem readFrom_congr {out input : ℕ} (circuit : Layered.Circuit F out input)
    (first second : ℕ → Message F) (start : ℕ)
    (h : ∀ q, start < q → first q = second q) :
    readFrom circuit first start = readFrom circuit second start := by
  induction circuit generalizing start with
  | input => rfl
  | entry _ _ _ ih => exact ih start h
  | @layer out mid input a body rest ih =>
      have hr : (fun i : Fin mid => polynomial (first (start+1+i.val))) =
          (fun i : Fin mid => polynomial (second (start+1+i.val))) := by
        funext i
        rw [h _ (by omega)]
      have ht := h (start+1+mid) (by omega)
      have hc := h (start+mid+2) (by omega)
      have htail := ih (if FrontendReplay.hasLayers rest then start+mid+3 else start+mid+2)
        (by
          intro q hq
          apply h q
          split_ifs at hq <;> omega)
      dsimp only [readFrom]
      rw [hr, ht, hc, htail]

theorem readFrom_writeFrom {out input : ℕ} (circuit : Layered.Circuit F out input)
    (payload : Payload circuit) (start : ℕ) :
    readFrom circuit (writeFrom circuit payload start) start = payload := by
  induction circuit generalizing start with
  | input => exact Subsingleton.elim _ _
  | entry _ _ _ ih => exact ih payload start
  | @layer out mid input a body rest ih =>
      have hr : (fun i : Fin mid => polynomial
          (writeFrom (.layer a body rest) payload start (start+1+i.val))) = payload.1.rounds := by
        funext i
        have h : start+1 ≤ start+1+i.val ∧ start+1+i.val < start+1+mid := by
          have := i.isLt
          omega
        simp only [writeFrom, dif_pos h, polynomial]
        congr 1
        apply Fin.ext
        change start+1+i.val-(start+1) = i.val
        omega
      have ht : cross (writeFrom (.layer a body rest) payload start (start+1+mid)) =
          payload.1.cross := by
        simp only [writeFrom, lt_self_iff_false, and_false, ↓reduceDIte, ↓reduceIte, cross]
      have hc : claims (writeFrom (.layer a body rest) payload start (start+mid+2)) =
          (payload.1.claimA, payload.1.claimB) := by
        have hround : ¬ (start+1 ≤ start+mid+2 ∧ start+mid+2 < start+1+mid) := by omega
        have hcross : start+mid+2 ≠ start+1+mid := by omega
        simp only [writeFrom, dif_neg hround, hcross, ↓reduceIte, claims]
      let next := if FrontendReplay.hasLayers rest then start+mid+3 else start+mid+2
      have htail : readFrom rest (writeFrom (.layer a body rest) payload start) next = payload.2 := by
        rw [readFrom_congr rest _ (writeFrom rest payload.2 next) next (by
          intro q hq
          have hn : start+mid+2 ≤ next := by dsimp [next]; split_ifs <;> omega
          have hround : ¬ (start+1 ≤ q ∧ q < start+1+mid) := by omega
          have hcross : q ≠ start+1+mid := by omega
          have hcombine : q ≠ start+mid+2 := by omega
          simp only [writeFrom, dif_neg hround, hcross, hcombine, ↓reduceIte]
          rfl)]
        exact ih payload.2 next
      dsimp only [readFrom]
      rw [hr, ht, hc, htail]

theorem read_write {out input : ℕ} (circuit : Layered.Circuit F out input)
    (payload : Payload circuit) : read circuit (write circuit payload) = payload :=
  readFrom_writeFrom circuit payload 0

/-- A single retained algebraic role reads just its own prover message from
the grouped wire.  Earlier roles can therefore be reconstructed from the
actual bound prefix without looking at any future prover bytes. -/
theorem layerMessage_readFrom_congr {out input : ℕ}
    (circuit : Layered.Circuit F out input) (role : LayerRole circuit)
    (first second : ℕ → Message F) (start : ℕ)
    (h : first (FrontendReplay.queryIndex circuit role start) =
      second (FrontendReplay.queryIndex circuit role start)) :
    layerMessage circuit (readFrom circuit first start) role =
      layerMessage circuit (readFrom circuit second start) role := by
  induction circuit generalizing start with
  | input => exact Fin.elim0 role
  | entry _ _ _ ih =>
      cases role with
      | inl _ => rfl
      | inr role => exact ih role start h
  | layer a body rest ih =>
      rcases role with i | i | i | i | role
      · rfl
      · simp only [FrontendReplay.queryIndex] at h
        dsimp only [readFrom, layerMessage]
        rw [h]
      · simp only [FrontendReplay.queryIndex] at h
        dsimp only [readFrom, layerMessage]
        rw [h]
      · simp only [FrontendReplay.queryIndex] at h
        dsimp only [readFrom, layerMessage]
        rw [h]
      · exact ih role _ h

/-- A prefix view is an analysis operation, not another transcript write or
query.  Missing future messages use the ordinary zero defaults above. -/
def boundPrefix (wire : ℕ → Message F) (through : ℕ) : ℕ → Message F :=
  fun q => if q ≤ through then wire q else .empty

theorem layerMessage_prefix {out input : ℕ} (circuit : Layered.Circuit F out input)
    (payload : Payload circuit) (through : ℕ) (role : LayerRole circuit)
    (h : FrontendReplay.queryIndex circuit role 0 ≤ through) :
    layerMessage circuit (read circuit (boundPrefix (write circuit payload) through)) role =
      layerMessage circuit payload role := by
  have hm := layerMessage_readFrom_congr circuit role
    (boundPrefix (write circuit payload) through) (write circuit payload) 0 (if_pos h)
  change layerMessage circuit (read circuit (boundPrefix (write circuit payload) through)) role =
    layerMessage circuit (read circuit (write circuit payload)) role at hm
  simpa only [read_write] using hm

end LfzkV2.Current.FrontendTranscript
