import LfzkV2.Current.ApplicationViews

/-! Actual replay supplies the partial frontend views used by query-local
charging. Only already-bound prover messages are retained; future messages
are completed by the parser's fixed zero stream. -/
noncomputable section
namespace LfzkV2.Current.ApplicationViews
open ApplicationSetup WitnessSelection SumcheckV2

section LocalTransfer
open ApplicationOracle ApplicationCharging
variable {roles : List Role} {Key Block Link Body C Oracle B N IB IN F Pad : Type}
variable [Field B] [Field N] [DecidableEq B] [DecidableEq N] [Fintype IB] [Fintype IN]
variable [Field F] [Fintype F] [DecidableEq F] [Fintype C]
variable (S : SelectionSource roles Key Block Link Body C Oracle B N IB IN)

/-- A parsed local view charges the actual frontend failure once its bound
message prefix and selected cells are identified. No future messages or
future oracle answers participate in this transfer. -/
theorem frontendBad_of_prefix
    (read : (point : Input roles Key Block Link Body) → (Fin point.rank → C) →
      Option (FrontendView F Pad (Selection.Pair B N IB IN) (Input roles Key Block Link Body) C))
    (point : Input roles Key Block Link Body) (H : Input roles Key Block Link Body → Link × C)
    (answer : C) (view : FrontendView F Pad (Selection.Pair B N IB IN)
      (Input roles Key Block Link Body) C)
    (hread : read point (point.priorAnswers H) = some view)
    (w : Selection.Pair B N IB IN)
    (actualPayload : Layered.Replay.Payload view.data.circuit) (actualAnswers : ℕ → C)
    (hstart : view.data.start ≤ point.rank)
    (hselected : S.selected point H = some w)
    (hanswers : ∀ j, j ≤ point.rank-view.data.start → actualAnswers j =
      point.answersWith H answer view.data.fallback (view.data.start+j))
    (hmessages : ∀ role, FrontendReplay.queryIndex view.data.circuit role 0 ≤ point.rank-view.data.start →
      Layered.Replay.layerMessage view.data.circuit actualPayload role =
        Layered.Replay.layerMessage view.data.circuit (view.data.payload point) role)
    (hbad : FrontendReplay.BadAt view.data.decode view.data.nonzero view.data.circuit view.data.plan
      actualPayload actualAnswers (view.data.inputs w) (view.data.pads w) (point.rank-view.data.start)) :
    frontendBad S read point H answer := by
  rw [frontendBad,hread]
  refine ⟨hstart,?_⟩
  exact SelectedFrontendOracle.bad_of_prefix S.lists S.coins S.responses S.oracle
    view.data.circuit view.data.plan view.data.payload view.data.inputs view.data.pads
    view.data.decode view.data.nonzero view.data.start view.data.fallback point H answer
    w actualPayload actualAnswers hselected hanswers hmessages hbad

end LocalTransfer

section AnswerTransfer
variable {g : Geometry} {fields : Fields} {Advice Auth Key Base C : Type}
local notation "Point" => Input g.roles Key (Base × ProtocolWrites.Fresh g fields Advice) Digest
  (Body g fields Advice Auth)

/-- A completed frontend tape contains exactly the actual earlier answers,
including the answer at the current local test. Its future entries are not
needed to identify that test. -/
theorem frontendTape_eq_answersWith
    (e : Replay.Encoding g fields Advice Auth Key (Base × ProtocolWrites.Fresh g fields Advice) C)
    (initialLink : Digest) (proof : Replay.Output g fields Advice Auth) (H : Point → Digest × C)
    (current later start slots : ℕ) (hc : current ≤ g.roles.length) (hl : later ≤ g.roles.length)
    (hstart : start ≤ current) (hcl : current < later) (hslot : current-start < slots)
    (fallback : C) (j : ℕ) (hj : j ≤ current-start) :
    ApplicationPrefix.frontendTape ((e.chain initialLink).point proof H later)
        (((e.chain initialLink).point proof H later).priorAnswers H) fallback start slots j =
      ((e.chain initialLink).point proof H current).answersWith H
        (H ((e.chain initialLink).point proof H current)).2 fallback (start+j) := by
  have hrank := (e.chain initialLink).point_rank proof H hl
  change Input.rank _ = later at hrank
  have hlt : start+j < ((e.chain initialLink).point proof H later).rank := by rw [hrank]; omega
  rw [ApplicationPrefix.frontendTape,if_pos (show j < slots by omega),
    ApplicationPrefix.answerTape_eq _ _ _ _ _ hlt]
  change (H (((e.chain initialLink).point proof H later).priorPoints ⟨start+j,hlt⟩)).2 = _
  rw [e.point_priorPoints initialLink proof H later hl ⟨start+j,by omega⟩]
  exact (e.point_answersWith initialLink proof H current (start+j) hc (by omega) fallback).symm

end AnswerTransfer

variable {g : Geometry} {fields : Fields} {Advice Auth Key Base C B : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B] [Fintype C]
variable {shared maskBits adviceBits : ℕ}
local notation "N" => ZMod Adapter.Mdoc.primeOrder
local notation "Point" => Input g.roles Key (Base × ProtocolWrites.Fresh g fields Advice) Digest
  (Body g fields Advice Auth)

omit [Fintype B] in
theorem primeView_from_late
    (e : Replay.Encoding g fields Advice Auth Key (Base × ProtocolWrites.Fresh g fields Advice) C)
    (s : BinaryPublic B shared maskBits adviceBits) (n : PrimePublic N shared)
    (shape : FrontendSchedule.Plan N n.circuit) (capacity : ℕ)
    (decode : C → ℕ → N) (nonzero : C → Linear.TerminalSampling.Nonzero N)
    (decoder : FrontendReplay.Decoder capacity decode nonzero) (hcapacity : shape.capacity ≤ capacity)
    (field : fields .prime → N) (fallback : C)
    (initialLink : Digest) (proof : Replay.Output g fields Advice Auth) (H : Point → Digest × C)
    (current later : ℕ) (hc : current ≤ g.roles.length) (hl : later ≤ g.roles.length)
    (hstart : g.primeStart ≤ current) (hcl : current ≤ later)
    (hfit : g.primeStart+FrontendReplay.slots n.circuit ≤ g.roles.length)
    (payload : Layered.Replay.Payload n.circuit)
    (hparsed : ApplicationPrefix.Messages.read n.circuit
      (ApplicationPrefix.wire ((e.chain initialLink).point proof H later) .prime field g.primeStart) = some payload) :
    ∃ early, readPrimeView s n shape capacity decode nonzero decoder hcapacity field fallback
        ((e.chain initialLink).point proof H current)
        (((e.chain initialLink).point proof H current).priorAnswers H) =
          some (primeViewOfPayload s n shape capacity decode nonzero decoder hcapacity fallback early) ∧
      ∀ role, FrontendReplay.queryIndex n.circuit role 0 ≤ current-g.primeStart →
        Layered.Replay.layerMessage n.circuit early role = Layered.Replay.layerMessage n.circuit payload role := by
  obtain ⟨early,hearly,hmessages⟩ := partial_from_late e .prime field n.circuit initialLink proof H
    current later g.primeStart hc hl hstart hcl hfit payload hparsed
  have hrank := (e.chain initialLink).point_rank proof H hc
  change Input.rank _ = current at hrank
  refine ⟨early,?_,hmessages⟩
  simp only [readPrimeView,hrank,if_pos hstart,hearly,Option.map_some]

theorem binaryView_from_late
    (e : Replay.Encoding g fields Advice Auth Key (Base × ProtocolWrites.Fresh g fields Advice) C)
    (s : BinaryPublic B shared maskBits adviceBits) (n : PrimePublic N shared)
    (generator : Bˣ) (capacity : ℕ)
    (shape : (packet : AdapterPacket s n C) → FrontendSchedule.Plan B (packet.setup generator).circuit)
    (decode : C → ℕ → B) (nonzero : C → Linear.TerminalSampling.Nonzero B)
    (decoder : FrontendReplay.Decoder capacity decode nonzero)
    (hcapacity : ∀ packet, (shape packet).capacity ≤ capacity)
    (binaryField : fields .binary → B) (primeField : fields .prime → N)
    (primeDecode : C → ℕ → N) (primeNonzero : C → Linear.TerminalSampling.Nonzero N)
    (convert : C → Fin 2 → Linear.TerminalSampling.Nonzero N)
    (advice : Advice → Option (Fin 2 → Fin adviceBits → Bool)) (fallback : C)
    (initialLink : Digest) (proof : Replay.Output g fields Advice Auth) (H : Point → Digest × C)
    (current later : ℕ) (hc : current ≤ g.roles.length) (hl : later ≤ g.roles.length)
    (hstart : g.binaryStart ≤ current) (hcl : current ≤ later) (packet : AdapterPacket s n C)
    (hadapter : readAdapter s n primeField primeDecode primeNonzero convert advice fallback
      ((e.chain initialLink).point proof H current)
      (((e.chain initialLink).point proof H current).priorAnswers H) = some packet)
    (hfit : g.binaryStart+FrontendReplay.slots (packet.setup generator).circuit ≤ g.roles.length)
    (payload : Layered.Replay.Payload (packet.setup generator).circuit)
    (hparsed : ApplicationPrefix.Messages.read (packet.setup generator).circuit
      (ApplicationPrefix.wire ((e.chain initialLink).point proof H later) .binary binaryField g.binaryStart) = some payload) :
    ∃ early, readBinaryView s n generator capacity shape decode nonzero decoder hcapacity binaryField primeField
        primeDecode primeNonzero convert advice fallback
        ((e.chain initialLink).point proof H current)
        (((e.chain initialLink).point proof H current).priorAnswers H) =
          some (binaryViewOfPayload s n generator packet (shape packet) capacity decode nonzero decoder
            (hcapacity packet) fallback early) ∧
      ∀ role, FrontendReplay.queryIndex (packet.setup generator).circuit role 0 ≤ current-g.binaryStart →
        Layered.Replay.layerMessage (packet.setup generator).circuit early role =
          Layered.Replay.layerMessage (packet.setup generator).circuit payload role := by
  obtain ⟨early,hearly,hmessages⟩ := partial_from_late e .binary binaryField (packet.setup generator).circuit
    initialLink proof H current later g.binaryStart hc hl hstart hcl hfit payload hparsed
  have hrank := (e.chain initialLink).point_rank proof H hc
  change Input.rank _ = current at hrank
  refine ⟨early,?_,hmessages⟩
  simp only [readBinaryView,hrank,if_pos hstart,hadapter,Option.bind_eq_bind,Option.bind_some,hearly]

end LfzkV2.Current.ApplicationViews
