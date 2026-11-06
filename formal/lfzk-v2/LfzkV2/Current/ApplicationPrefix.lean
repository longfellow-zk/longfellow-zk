import LfzkV2.Current.ApplicationSetup
import LfzkV2.Current.FrontendBodyVerifier
import LfzkV2.Current.FrontendSchedule
import LfzkV2.Current.ProtocolWrites

/-! Application reconstruction from bound messages and strict prior answers.
Missing or malformed prover fields are rejected. A successful branch supplies
its frontend payload to the ordinary compiler; it never receives a compiled
system or a semantic correspondence certificate from the caller. -/
noncomputable section
namespace LfzkV2.Current.ApplicationPrefix
open SumcheckV2

namespace Messages
variable {A F : Type}

/-- Finite traversal of required message coordinates. -/
def vector : (n : ℕ) → (Fin n → Option A) → Option (Fin n → A)
  | 0, _ => some Fin.elim0
  | n+1, read => match read 0,vector n (fun i => read i.succ) with
    | some head,some tail => some (Fin.cons head tail)
    | _,_ => none

theorem vector_some (n : ℕ) (read : Fin n → Option A) (values : Fin n → A)
    (h : vector n read = some values) (i : Fin n) : read i = some (values i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      cases hh : read 0 with
      | none => simp only [vector,hh] at h; contradiction
      | some head =>
          cases ht : vector n (fun j => read j.succ) with
          | none => simp only [vector,hh,ht] at h; contradiction
          | some tail =>
              simp only [vector,hh,ht] at h
              cases Option.some.inj h
              refine Fin.cases ?_ (fun j => ?_) i
              · exact hh
              · exact ih (fun j => read j.succ) tail ht j

theorem vector_of_some (n : ℕ) (read : Fin n → Option A) (values : Fin n → A)
    (h : ∀ i, read i = some (values i)) : vector n read = some values := by
  induction n with
  | zero =>
      change some Fin.elim0 = some values
      apply congrArg some
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      have ht := ih (fun i => read i.succ) (fun i => values i.succ) (fun i => h i.succ)
      simp only [vector,h 0,ht]
      congr 1
      funext i
      exact Fin.cases rfl (fun _ => rfl) i

def polynomial : Option (Layered.Replay.Message F) → Option (RoundPoly F)
  | some (.round p) => some p
  | _ => none

def cross : Option (Layered.Replay.Message F) → Option F
  | some (.cross x) => some x
  | _ => none

def claims : Option (Layered.Replay.Message F) → Option (F × F)
  | some (.claims a b) => some (a,b)
  | _ => none

theorem polynomial_some (wire : Option (Layered.Replay.Message F)) (p : RoundPoly F)
    (h : polynomial wire = some p) : wire = some (.round p) := by
  cases wire with
  | none => simp only [polynomial] at h; contradiction
  | some message =>
      cases message <;> simp only [polynomial] at h
      all_goals first | contradiction | cases Option.some.inj h; rfl

theorem cross_some (wire : Option (Layered.Replay.Message F)) (x : F)
    (h : cross wire = some x) : wire = some (.cross x) := by
  cases wire with
  | none => simp only [cross] at h; contradiction
  | some message =>
      cases message <;> simp only [cross] at h
      all_goals first | contradiction | cases Option.some.inj h; rfl

theorem claims_some (wire : Option (Layered.Replay.Message F)) (x : F × F)
    (h : claims wire = some x) : wire = some (.claims x.1 x.2) := by
  cases wire with
  | none => simp only [claims] at h; contradiction
  | some message =>
      cases message <;> simp only [claims] at h
      all_goals first | contradiction | cases Option.some.inj h; rfl

/-- Assertion coefficients introduce no prover payload. Every quadratic
message, terminal cross and masked-claim pair is required at its own bound
position. Scalar layers still require the latter two messages. -/
def readFrom : {out input : ℕ} → (circuit : Layered.Circuit F out input) →
    (ℕ → Option (Layered.Replay.Message F)) → ℕ → Option (Layered.Replay.Payload circuit)
  | _, _, .input, _, _ => some ()
  | _, _, .entry _ _ rest, wire, start => readFrom rest wire start
  | _, _, .layer (mid := mid) _ _ rest, wire, start =>
      match vector mid (fun i => polynomial (wire (start+1+i.val))),
          cross (wire (start+1+mid)),claims (wire (start+mid+2)),
          readFrom rest wire (if FrontendReplay.hasLayers rest then start+mid+3 else start+mid+2) with
      | some rounds,some d,some ab,some tail => some (⟨rounds,d,ab.1,ab.2⟩,tail)
      | _,_,_,_ => none

def read {out input : ℕ} (circuit : Layered.Circuit F out input)
    (wire : ℕ → Option (Layered.Replay.Message F)) : Option (Layered.Replay.Payload circuit) :=
  readFrom circuit wire 0

theorem readFrom_congr {out input : ℕ} (circuit : Layered.Circuit F out input)
    (first second : ℕ → Option (Layered.Replay.Message F)) (start : ℕ)
    (h : ∀ q, start < q → q < start+FrontendReplay.slots circuit → first q = second q) :
    readFrom circuit first start = readFrom circuit second start := by
  induction circuit generalizing start with
  | input => rfl
  | entry _ _ _ ih => exact ih start h
  | @layer out mid input a body rest ih =>
      have hr : (fun i : Fin mid => polynomial (first (start+1+i.val))) =
          (fun i : Fin mid => polynomial (second (start+1+i.val))) := by
        funext i
        rw [h _ (by omega) (by have := i.isLt; simp only [FrontendReplay.slots]; omega)]
      have hd := h (start+1+mid) (by omega) (by simp only [FrontendReplay.slots]; omega)
      have hc := h (start+mid+2) (by omega) (by simp only [FrontendReplay.slots]; omega)
      have ht := ih (if FrontendReplay.hasLayers rest then start+mid+3 else start+mid+2) (by
        intro q hq hupper
        apply h q
        · split_ifs at hq <;> omega
        · by_cases has : FrontendReplay.hasLayers rest = true
          · simp only [has,↓reduceIte] at hupper
            simp only [FrontendReplay.slots,has,↓reduceIte]
            omega
          · have hf : FrontendReplay.hasLayers rest = false := Bool.eq_false_iff.mpr has
            have hz : FrontendReplay.slots rest = 1 := by rw [FrontendReplay.slots_eq,hf]; rfl
            simp only [hf,Bool.false_eq_true,↓reduceIte,hz] at hupper
            simp only [FrontendReplay.slots,hf,Bool.false_eq_true,↓reduceIte]
            omega)
      simp only [readFrom,hr,hd,hc,ht]

theorem readFrom_layer_spec {out mid input assertions : ℕ}
    (body : LfzkV2.Native.CircuitLayer (Cube out) (Cube mid) (Fin assertions) F)
    (rest : Layered.Circuit F mid input) (wire : ℕ → Option (Layered.Replay.Message F)) (start : ℕ)
    (payload : Layered.Replay.Payload (.layer assertions body rest))
    (h : readFrom (.layer assertions body rest) wire start = some payload) :
    vector mid (fun i => polynomial (wire (start+1+i.val))) = some payload.1.rounds ∧
      cross (wire (start+1+mid)) = some payload.1.cross ∧
      claims (wire (start+mid+2)) = some (payload.1.claimA,payload.1.claimB) ∧
      readFrom rest wire (if FrontendReplay.hasLayers rest then start+mid+3 else start+mid+2) = some payload.2 := by
  cases hr : vector mid (fun i => polynomial (wire (start+1+i.val))) with
  | none => simp only [readFrom,hr] at h; contradiction
  | some rounds =>
      cases hd : cross (wire (start+1+mid)) with
      | none => simp only [readFrom,hr,hd] at h; contradiction
      | some d =>
          cases hc : claims (wire (start+mid+2)) with
          | none => simp only [readFrom,hr,hd,hc] at h; contradiction
          | some ab =>
              cases ht : readFrom rest wire
                  (if FrontendReplay.hasLayers rest then start+mid+3 else start+mid+2) with
              | none => simp only [readFrom,hr,hd,hc,ht] at h; contradiction
              | some tail =>
                  simp only [readFrom,hr,hd,hc,ht] at h
                  cases Option.some.inj h
                  exact ⟨rfl,rfl,rfl,rfl⟩

/-- Each required position has one fixed message constructor. Any pointwise
mixture of two successfully parsed streams therefore still parses; its field
values may differ, but no new shape or compiler premise is required. -/
theorem readFrom_mix {out input : ℕ} (circuit : Layered.Circuit F out input)
    (first second : ℕ → Option (Layered.Replay.Message F)) (choose : ℕ → Bool) (start : ℕ)
    (left right : Layered.Replay.Payload circuit)
    (hl : readFrom circuit first start = some left) (hr : readFrom circuit second start = some right) :
    ∃ payload, readFrom circuit (fun q => if choose q then first q else second q) start = some payload := by
  induction circuit generalizing start with
  | input => exact ⟨(),rfl⟩
  | entry _ _ _ ih => exact ih start left right hl hr
  | @layer out mid input a body rest ih =>
      have hs := readFrom_layer_spec body rest first start left hl
      have ht := readFrom_layer_spec body rest second start right hr
      obtain ⟨tail,htail⟩ := ih _ left.2 right.2 hs.2.2.2 ht.2.2.2
      let rounds : Fin mid → RoundPoly F := fun i =>
        if choose (start+1+i.val) then left.1.rounds i else right.1.rounds i
      let d := if choose (start+1+mid) then left.1.cross else right.1.cross
      let ab := if choose (start+mid+2) then (left.1.claimA,left.1.claimB) else (right.1.claimA,right.1.claimB)
      have hrounds : vector mid (fun i => polynomial
          (if choose (start+1+i.val) then first (start+1+i.val) else second (start+1+i.val))) = some rounds := by
        apply vector_of_some
        intro i
        have hleft := vector_some _ _ _ hs.1 i
        have hright := vector_some _ _ _ ht.1 i
        dsimp only [rounds]
        split_ifs with h <;> assumption
      have hd : cross (if choose (start+1+mid) then first (start+1+mid) else second (start+1+mid)) = some d := by
        dsimp only [d]
        split_ifs with h
        · exact hs.2.1
        · exact ht.2.1
      have hab : claims (if choose (start+mid+2) then first (start+mid+2) else second (start+mid+2)) = some ab := by
        dsimp only [ab]
        split_ifs with h
        · exact hs.2.2.1
        · exact ht.2.2.1
      exact ⟨(⟨rounds,d,ab.1,ab.2⟩,tail),by simp only [readFrom,hrounds,hd,hab,htail]⟩

theorem readFrom_writeFrom {out input : ℕ} (circuit : Layered.Circuit F out input)
    (payload : Layered.Replay.Payload circuit) (start : ℕ) :
    readFrom circuit (fun q => some (FrontendTranscript.writeFrom circuit payload start q)) start = some payload := by
  induction circuit generalizing start with
  | input => cases payload; rfl
  | entry _ _ _ ih => exact ih payload start
  | @layer out mid input a body rest ih =>
      have hr : vector mid (fun i => polynomial
          (some (FrontendTranscript.writeFrom (.layer a body rest) payload start (start+1+i.val)))) =
            some payload.1.rounds := by
        apply vector_of_some
        intro i
        have hi : start+1 ≤ start+1+i.val ∧ start+1+i.val < start+1+mid := by have := i.isLt; omega
        simp only [FrontendTranscript.writeFrom,dif_pos hi,polynomial]
        congr 1
        congr 1
        apply Fin.ext
        change start+1+i.val-(start+1) = i.val
        omega
      have hd : cross (some (FrontendTranscript.writeFrom (.layer a body rest) payload start (start+1+mid))) =
          some payload.1.cross := by
        simp only [FrontendTranscript.writeFrom,lt_self_iff_false,and_false,↓reduceDIte,↓reduceIte,cross]
      have hc : claims (some (FrontendTranscript.writeFrom (.layer a body rest) payload start (start+mid+2))) =
          some (payload.1.claimA,payload.1.claimB) := by
        have hi : ¬ (start+1 ≤ start+mid+2 ∧ start+mid+2 < start+1+mid) := by omega
        have hd : start+mid+2 ≠ start+1+mid := by omega
        simp only [FrontendTranscript.writeFrom,dif_neg hi,hd,↓reduceIte,claims]
      let next := if FrontendReplay.hasLayers rest then start+mid+3 else start+mid+2
      have ht : readFrom rest
          (fun q => some (FrontendTranscript.writeFrom (.layer a body rest) payload start q)) next = some payload.2 := by
        rw [readFrom_congr rest _ (fun q => some (FrontendTranscript.writeFrom rest payload.2 next q)) next (by
          intro q hq _
          have hn : start+mid+2 ≤ next := by dsimp only [next]; split_ifs <;> omega
          have hi : ¬ (start+1 ≤ q ∧ q < start+1+mid) := by omega
          have hd : q ≠ start+1+mid := by omega
          have hc : q ≠ start+mid+2 := by omega
          simp only [FrontendTranscript.writeFrom,dif_neg hi,hd,hc,↓reduceIte]
          rfl)]
        exact ih payload.2 next
      dsimp only [next] at ht
      simp only [readFrom,hr,hd,hc,ht]

theorem read_write {out input : ℕ} (circuit : Layered.Circuit F out input)
    (payload : Layered.Replay.Payload circuit) :
    read circuit (fun q => some (FrontendTranscript.write circuit payload q)) = some payload :=
  readFrom_writeFrom circuit payload 0

variable [Field F]

/-- Successful partial decoding agrees with the existing logical message
reader. Zero defaults are therefore irrelevant on every required prover field
of an accepted branch; they are never used to fabricate an application. -/
theorem readFrom_agrees {out input : ℕ} (circuit : Layered.Circuit F out input)
    (wire : ℕ → Option (Layered.Replay.Message F)) (start : ℕ)
    (payload : Layered.Replay.Payload circuit) (h : readFrom circuit wire start = some payload) :
    FrontendTranscript.readFrom circuit (fun q => (wire q).getD .empty) start = payload := by
  induction circuit generalizing start with
  | input => exact Subsingleton.elim _ _
  | entry _ _ _ ih => exact ih start payload h
  | @layer out mid input a body rest ih =>
      cases hr : vector mid (fun i => polynomial (wire (start+1+i.val))) with
      | none => simp only [readFrom,hr] at h; contradiction
      | some rounds =>
          cases hd : cross (wire (start+1+mid)) with
          | none => simp only [readFrom,hr,hd] at h; contradiction
          | some d =>
              cases hc : claims (wire (start+mid+2)) with
              | none => simp only [readFrom,hr,hd,hc] at h; contradiction
              | some ab =>
                  cases ht : readFrom rest wire
                      (if FrontendReplay.hasLayers rest then start+mid+3 else start+mid+2) with
                  | none => simp only [readFrom,hr,hd,hc,ht] at h; contradiction
                  | some tail =>
                      simp only [readFrom,hr,hd,hc,ht] at h
                      cases Option.some.inj h
                      have hrounds : (fun i : Fin mid => FrontendTranscript.polynomial
                          ((wire (start+1+i.val)).getD .empty)) = rounds := by
                        funext i
                        have hw := polynomial_some _ _ (vector_some _ _ _ hr i)
                        simp only [hw,Option.getD_some,FrontendTranscript.polynomial]
                      have hwcross := cross_some _ _ hd
                      have hwclaims := claims_some _ _ hc
                      simp only [FrontendTranscript.readFrom,hrounds,hwcross,hwclaims,
                        Option.getD_some,FrontendTranscript.cross,FrontendTranscript.claims]
                      rw [ih _ tail ht]

end Messages

open ApplicationSetup
variable {g : Geometry} {fields : Fields} {Advice Auth Key Base C B : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable {shared maskBits adviceBits : ℕ}

local notation "Point" => Input g.roles Key (Base × ProtocolWrites.Fresh g fields Advice) Digest
  (Body g fields Advice Auth)

def mapMessage {E G : Type} (field : E → G) : Layered.Replay.Message E → Layered.Replay.Message G
  | .empty => .empty
  | .round p => .round ⟨field p.c0,field p.c1⟩
  | .cross x => .cross (field x)
  | .claims a b => .claims (field a) (field b)

/-- A message is obtained only from the recorded block at its actual
frontend position. An unavailable block remains missing, rather than being
replaced by a message from the complete proof. -/
def wire {F : Type} (point : Point) (side : Side) (field : fields side → F) (start q : ℕ) :
    Option (Layered.Replay.Message F) :=
  point.readAt (start+q) (fun block => some (mapMessage field (block.2.frontend side)))

def strictAnswer (point : Point) (past : Fin point.rank → C) (q : ℕ) : Option C :=
  if h : q < point.rank then some (past ⟨q,h⟩) else none

/-- Future entries of this total tape are irrelevant to the frontend
compiler. The reader below first checks that every frontend slot is strict
past; its remaining protocol challenges are read with `strictAnswer`. -/
def answerTape (point : Point) (past : Fin point.rank → C) (fallback : C) (start q : ℕ) : C :=
  (strictAnswer point past (start+q)).getD fallback

theorem answerTape_eq (point : Point) (past : Fin point.rank → C) (fallback : C)
    (start q : ℕ) (h : start+q < point.rank) :
    answerTape point past fallback start q = past ⟨start+q,h⟩ := by
  simp only [answerTape,strictAnswer,dif_pos h,Option.getD_some]

/-- Retain only this frontend's answer window. Later adapter/backend answers
cannot change the extensional packet even though the compiler never reads
them. This makes the same completed frontend identical at later prefixes. -/
def frontendTape (point : Point) (past : Fin point.rank → C) (fallback : C)
    (start slots q : ℕ) : C :=
  if q < slots then answerTape point past fallback start q else fallback

theorem read_frontendTape {F Pad : Type} [Field F] {out input : ℕ}
    (circuit : Layered.Circuit F out input) (plan : Layered.Replay.PadPlan (Pad := Pad) circuit)
    (payload : Layered.Replay.Payload circuit) (decode : C → ℕ → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F)
    (point : Point) (past : Fin point.rank → C) (fallback : C) (start : ℕ) :
    FrontendReplay.read decode nonzero circuit plan payload
        (frontendTape point past fallback start (FrontendReplay.slots circuit)) =
      FrontendReplay.read decode nonzero circuit plan payload (answerTape point past fallback start) := by
  apply FrontendReplay.readFrom_eq_of_prefix
  intro q hq
  have hq' : q < FrontendReplay.slots circuit := by simpa only [Nat.zero_add] using hq
  simp only [frontendTape,if_pos hq']

theorem constraints_frontendTape {F Pad : Type} [Field F] {out input : ℕ}
    (circuit : Layered.Circuit F out input) (plan : Layered.Replay.PadPlan (Pad := Pad) circuit)
    (payload : Layered.Replay.Payload circuit) (decode : C → ℕ → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F)
    (point : Point) (past : Fin point.rank → C) (fallback : C) (start : ℕ) :
    FrontendVerifier.constraints circuit plan payload decode nonzero
        (frontendTape point past fallback start (FrontendReplay.slots circuit)) =
      FrontendVerifier.constraints circuit plan payload decode nonzero (answerTape point past fallback start) := by
  unfold FrontendVerifier.constraints
  rw [read_frontendTape]

def rowBatchingIndex (g : Geometry) : ℕ := g.primeStart+(g.prime.roles .prime).length
def rescalingIndex (g : Geometry) : ℕ := rowBatchingIndex g+1
def conversionIndex (g : Geometry) : ℕ := rowBatchingIndex g+2
def packingIndex (g : Geometry) : ℕ := g.binaryStart+(g.binary.roles .binary).length

/-- Compile the prime rows from the complete bound prime message window,
then sample their row-combination coefficients from the one prime-batch
answer. No rows, claim or compiler-success proof are supplied by the caller. -/
def readPrime (n : PrimePublic (ZMod Adapter.Mdoc.primeOrder) shared)
    (field : fields .prime → ZMod Adapter.Mdoc.primeOrder)
    (decode : C → ℕ → ZMod Adapter.Mdoc.primeOrder)
    (nonzero : C → Linear.TerminalSampling.Nonzero (ZMod Adapter.Mdoc.primeOrder))
    (fallback : C) (point : Point) (past : Fin point.rank → C) : Option (PrimeData n C) :=
  if g.primeStart+FrontendReplay.slots n.circuit ≤ point.rank then do
    let payload ← Messages.read n.circuit (wire point .prime field g.primeStart)
    let batching ← strictAnswer point past (rowBatchingIndex g)
    some {
      payload := payload
      decode := decode
      nonzero := nonzero
      answers := frontendTape point past fallback g.primeStart (FrontendReplay.slots n.circuit)
      rho := fun i => decode batching i.val }
  else none

/-- The binary circuit is generated from the reconstructed prime claim and
the actual adapter exchange. Both conversion challenges come from the same
answer through the fixed two-coordinate decoder. Packing response cells are
backend data; they are never binary field-valued circuit inputs. -/
def readBinary (s : BinaryPublic B shared maskBits adviceBits)
    {n : PrimePublic (ZMod Adapter.Mdoc.primeOrder) shared} (prime : PrimeData n C)
    (generator : Bˣ) (hdegree : g.packingDegree = s.degree)
    (binaryField : fields .binary → B) (primeField : fields .prime → ZMod Adapter.Mdoc.primeOrder)
    (decode : C → ℕ → B) (nonzero : C → Linear.TerminalSampling.Nonzero B)
    (rescale : C → Linear.TerminalSampling.Nonzero (ZMod Adapter.Mdoc.primeOrder))
    (convert : C → Fin 2 → Linear.TerminalSampling.Nonzero (ZMod Adapter.Mdoc.primeOrder))
    (advice : Advice → Option (Fin 2 → Fin adviceBits → Bool))
    (fallback : C) (point : Point) (past : Fin point.rank → C) :
    Option (BinaryData s prime generator) := do
  let scale ← strictAnswer point past (rescalingIndex g)
  let conversion ← strictAnswer point past (conversionIndex g)
  let mu ← point.readAt (conversionIndex g) (fun block => block.2.mu.map primeField)
  let rawAdvice ← point.readAt g.binaryStart (fun block => block.2.advice)
  let masked ← advice rawAdvice
  let U ← point.readAt (packingIndex g) (fun block => block.2.packingU)
  let packing ← strictAnswer point past (packingIndex g)
  let A ← point.readAt g.batchingIndex.val (fun block => block.2.packingA.map binaryField)
  let eta := (rescale scale).val
  let alpha := convert conversion
  let powers := fun tree i => generator^((alpha tree).val*(Handoff.weights prime.claim.sharedWeights eta i)).val
  let targets := fun tree => generator^((alpha tree).val*mu).val
  let circuit := s.circuit powers (generator^(-(Adapter.Mdoc.primeOrder : ℤ))) masked targets
  if g.binaryStart+FrontendReplay.slots circuit ≤ point.rank then
    let payload ← Messages.read circuit (wire point .binary binaryField g.binaryStart)
    some {
      eta := eta
      mu := mu
      alpha := alpha
      masked := masked
      payload := payload
      decode := decode
      nonzero := nonzero
      answers := frontendTape point past fallback g.binaryStart (FrontendReplay.slots circuit)
      U := fun i => binaryField (U (Fin.cast hdegree.symm i))
      delta := fun i => decode packing i.val
      A := A }
  else none

/-- The final runtime application decoder. All message/challenge parsing
precedes the actual primitive-generator and packing trace checks. Rejected
branches stay `none`; no certified-System fallback is used. -/
def decodeChecked (s : BinaryPublic B shared maskBits adviceBits)
    (n : PrimePublic (ZMod Adapter.Mdoc.primeOrder) shared)
    (hcard : Fintype.card B = Adapter.Mdoc.binaryOrder) (x : Bˣ)
    (bound : 2^adviceBits ≤ Adapter.Mdoc.quotientBound) (hdegree : g.packingDegree = s.degree)
    (binaryField : fields .binary → B) (primeField : fields .prime → ZMod Adapter.Mdoc.primeOrder)
    (binaryDecode : C → ℕ → B) (binaryNonzero : C → Linear.TerminalSampling.Nonzero B)
    (primeDecode : C → ℕ → ZMod Adapter.Mdoc.primeOrder)
    (primeNonzero : C → Linear.TerminalSampling.Nonzero (ZMod Adapter.Mdoc.primeOrder))
    (convert : C → Fin 2 → Linear.TerminalSampling.Nonzero (ZMod Adapter.Mdoc.primeOrder))
    (advice : Advice → Option (Fin 2 → Fin adviceBits → Bool))
    (fallback : C) (point : Point) (past : Fin point.rank → C) := do
  let prime ← readPrime n primeField primeDecode primeNonzero fallback point past
  let binary ← readBinary s prime (x^Adapter.Mdoc.generatorExponent) hdegree binaryField primeField
    binaryDecode binaryNonzero primeNonzero convert advice fallback point past
  ApplicationSetup.decodeChecked s n prime hcard x bound binary

theorem readPrime_spec (n : PrimePublic (ZMod Adapter.Mdoc.primeOrder) shared)
    (field : fields .prime → ZMod Adapter.Mdoc.primeOrder)
    (decode : C → ℕ → ZMod Adapter.Mdoc.primeOrder)
    (nonzero : C → Linear.TerminalSampling.Nonzero (ZMod Adapter.Mdoc.primeOrder))
    (fallback : C) (point : Point) (past : Fin point.rank → C) (data : PrimeData n C)
    (h : readPrime n field decode nonzero fallback point past = some data) :
    g.primeStart+FrontendReplay.slots n.circuit ≤ point.rank ∧
      Messages.read n.circuit (wire point .prime field g.primeStart) = some data.payload ∧
      data.decode = decode ∧ data.nonzero = nonzero ∧
      data.answers = frontendTape point past fallback g.primeStart (FrontendReplay.slots n.circuit) ∧
      ∃ batching, strictAnswer point past (rowBatchingIndex g) = some batching ∧
        data.rho = fun i => decode batching i.val := by
  unfold readPrime at h
  split at h
  · rename_i hslots
    simp only [PrimePublic.setup,Option.bind_eq_bind,Option.bind_eq_some_iff] at h
    obtain ⟨payload,hpayload,batching,hbatching,hresult⟩ := h
    cases Option.some.inj hresult
    exact ⟨hslots,hpayload,rfl,rfl,rfl,batching,hbatching,rfl⟩
  · contradiction

omit [DecidableEq B] in
theorem readBinary_spec (s : BinaryPublic B shared maskBits adviceBits)
    {n : PrimePublic (ZMod Adapter.Mdoc.primeOrder) shared} (prime : PrimeData n C)
    (generator : Bˣ) (hdegree : g.packingDegree = s.degree)
    (binaryField : fields .binary → B) (primeField : fields .prime → ZMod Adapter.Mdoc.primeOrder)
    (decode : C → ℕ → B) (nonzero : C → Linear.TerminalSampling.Nonzero B)
    (rescale : C → Linear.TerminalSampling.Nonzero (ZMod Adapter.Mdoc.primeOrder))
    (convert : C → Fin 2 → Linear.TerminalSampling.Nonzero (ZMod Adapter.Mdoc.primeOrder))
    (advice : Advice → Option (Fin 2 → Fin adviceBits → Bool))
    (fallback : C) (point : Point) (past : Fin point.rank → C) (data : BinaryData s prime generator)
    (h : readBinary s prime generator hdegree binaryField primeField decode nonzero rescale convert advice
      fallback point past = some data) :
    g.binaryStart+FrontendReplay.slots data.setup.circuit ≤ point.rank ∧
      (∃ scale, strictAnswer point past (rescalingIndex g) = some scale ∧ data.eta = (rescale scale).val) ∧
      (∃ conversion, strictAnswer point past (conversionIndex g) = some conversion ∧ data.alpha = convert conversion) ∧
      point.readAt (conversionIndex g) (fun block => block.2.mu.map primeField) = some data.mu ∧
      (∃ raw, point.readAt g.binaryStart (fun block => block.2.advice) = some raw ∧ advice raw = some data.masked) ∧
      (∃ U, point.readAt (packingIndex g) (fun block => block.2.packingU) = some U ∧
        data.U = fun i => binaryField (U (Fin.cast hdegree.symm i))) ∧
      (∃ packing, strictAnswer point past (packingIndex g) = some packing ∧ data.delta = fun i => decode packing i.val) ∧
      point.readAt g.batchingIndex.val (fun block => block.2.packingA.map binaryField) = some data.A ∧
      Messages.read data.setup.circuit (wire point .binary binaryField g.binaryStart) = some data.payload ∧
      data.decode = decode ∧ data.nonzero = nonzero ∧
      data.answers = frontendTape point past fallback g.binaryStart (FrontendReplay.slots data.setup.circuit) := by
  unfold readBinary at h
  simp only [Option.bind_eq_bind,Option.bind_eq_some_iff] at h
  obtain ⟨scale,hscale,conversion,hconversion,mu,hmu,rawAdvice,hadvice,masked,hmasked,
    U,hU,packing,hpacking,A,hA,h⟩ := h
  split at h
  · rename_i hslots
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨payload,hpayload,hresult⟩ := h
    cases Option.some.inj hresult
    exact ⟨hslots,⟨scale,hscale,rfl⟩,⟨conversion,hconversion,rfl⟩,hmu,
      ⟨rawAdvice,hadvice,hmasked⟩,⟨U,hU,rfl⟩,⟨packing,hpacking,rfl⟩,hA,hpayload,rfl,rfl,rfl⟩
  · contradiction

/-- Complete successful decoding exposes the two parsed frontend records
and the actual runtime generator/trace checks. These are conclusions of the
reader, not extra acceptance or correspondence premises. -/
theorem decodeChecked_spec (s : BinaryPublic B shared maskBits adviceBits)
    (n : PrimePublic (ZMod Adapter.Mdoc.primeOrder) shared)
    (hcard : Fintype.card B = Adapter.Mdoc.binaryOrder) (x : Bˣ)
    (bound : 2^adviceBits ≤ Adapter.Mdoc.quotientBound) (hdegree : g.packingDegree = s.degree)
    (binaryField : fields .binary → B) (primeField : fields .prime → ZMod Adapter.Mdoc.primeOrder)
    (binaryDecode : C → ℕ → B) (binaryNonzero : C → Linear.TerminalSampling.Nonzero B)
    (primeDecode : C → ℕ → ZMod Adapter.Mdoc.primeOrder)
    (primeNonzero : C → Linear.TerminalSampling.Nonzero (ZMod Adapter.Mdoc.primeOrder))
    (convert : C → Fin 2 → Linear.TerminalSampling.Nonzero (ZMod Adapter.Mdoc.primeOrder))
    (advice : Advice → Option (Fin 2 → Fin adviceBits → Bool))
    (fallback : C) (point : Point) (past : Fin point.rank → C) (system)
    (h : decodeChecked s n hcard x bound hdegree binaryField primeField binaryDecode binaryNonzero
      primeDecode primeNonzero convert advice fallback point past = some system) :
    ∃ prime binary,
      readPrime n primeField primeDecode primeNonzero fallback point past = some prime ∧
      readBinary s prime (x^Adapter.Mdoc.generatorExponent) hdegree binaryField primeField
        binaryDecode binaryNonzero primeNonzero convert advice fallback point past = some binary ∧
      ApplicationSetup.decodeChecked s n prime hcard x bound binary = some system := by
  simp only [decodeChecked,Option.bind_eq_bind,Option.bind_eq_some_iff] at h
  obtain ⟨prime,hprime,binary,hbinary,hcheck⟩ := h
  exact ⟨prime,binary,hprime,hbinary,hcheck⟩

theorem prime_payload_agrees (n : PrimePublic (ZMod Adapter.Mdoc.primeOrder) shared)
    (field : fields .prime → ZMod Adapter.Mdoc.primeOrder)
    (decode : C → ℕ → ZMod Adapter.Mdoc.primeOrder)
    (nonzero : C → Linear.TerminalSampling.Nonzero (ZMod Adapter.Mdoc.primeOrder))
    (fallback : C) (point : Point) (past : Fin point.rank → C) (data : PrimeData n C)
    (h : readPrime n field decode nonzero fallback point past = some data) :
    FrontendTranscript.read n.circuit
      (fun q => (wire point .prime field g.primeStart q).getD .empty) = data.payload :=
  Messages.readFrom_agrees n.circuit _ 0 data.payload
    (readPrime_spec n field decode nonzero fallback point past data h).2.1

omit [DecidableEq B] in
theorem binary_payload_agrees (s : BinaryPublic B shared maskBits adviceBits)
    {n : PrimePublic (ZMod Adapter.Mdoc.primeOrder) shared} (prime : PrimeData n C)
    (generator : Bˣ) (hdegree : g.packingDegree = s.degree)
    (binaryField : fields .binary → B) (primeField : fields .prime → ZMod Adapter.Mdoc.primeOrder)
    (decode : C → ℕ → B) (nonzero : C → Linear.TerminalSampling.Nonzero B)
    (rescale : C → Linear.TerminalSampling.Nonzero (ZMod Adapter.Mdoc.primeOrder))
    (convert : C → Fin 2 → Linear.TerminalSampling.Nonzero (ZMod Adapter.Mdoc.primeOrder))
    (advice : Advice → Option (Fin 2 → Fin adviceBits → Bool))
    (fallback : C) (point : Point) (past : Fin point.rank → C) (data : BinaryData s prime generator)
    (h : readBinary s prime generator hdegree binaryField primeField decode nonzero rescale convert advice
      fallback point past = some data) :
    FrontendTranscript.read data.setup.circuit
      (fun q => (wire point .binary binaryField g.binaryStart q).getD .empty) = data.payload := by
  have hp := readBinary_spec s prime generator hdegree binaryField primeField decode nonzero
    rescale convert advice fallback point past data h
  exact Messages.readFrom_agrees data.setup.circuit _ 0 data.payload hp.2.2.2.2.2.2.2.2.1

/-- The complete reader uses only its fixed preimage and strict ancestors.
Changing this boundary's answer cannot change the reconstructed system. -/
theorem decodeChecked_off (s : BinaryPublic B shared maskBits adviceBits)
    (n : PrimePublic (ZMod Adapter.Mdoc.primeOrder) shared)
    (hcard : Fintype.card B = Adapter.Mdoc.binaryOrder) (x : Bˣ)
    (bound : 2^adviceBits ≤ Adapter.Mdoc.quotientBound) (hdegree : g.packingDegree = s.degree)
    (binaryField : fields .binary → B) (primeField : fields .prime → ZMod Adapter.Mdoc.primeOrder)
    (binaryDecode : C → ℕ → B) (binaryNonzero : C → Linear.TerminalSampling.Nonzero B)
    (primeDecode : C → ℕ → ZMod Adapter.Mdoc.primeOrder)
    (primeNonzero : C → Linear.TerminalSampling.Nonzero (ZMod Adapter.Mdoc.primeOrder))
    (convert : C → Fin 2 → Linear.TerminalSampling.Nonzero (ZMod Adapter.Mdoc.primeOrder))
    (advice : Advice → Option (Fin 2 → Fin adviceBits → Bool))
    (fallback : C) (point : Point) (H H' : Point → Digest × C)
    (h : Bcs.TotalOracle.AgreeOff point H H') :
    decodeChecked s n hcard x bound hdegree binaryField primeField binaryDecode binaryNonzero
        primeDecode primeNonzero convert advice fallback point (point.priorAnswers H) =
      decodeChecked s n hcard x bound hdegree binaryField primeField binaryDecode binaryNonzero
        primeDecode primeNonzero convert advice fallback point (point.priorAnswers H') := by
  rw [point.priorAnswers_off h]

end LfzkV2.Current.ApplicationPrefix
