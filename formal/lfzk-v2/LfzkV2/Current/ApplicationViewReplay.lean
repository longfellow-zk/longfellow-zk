import LfzkV2.Current.ApplicationViews

/-! Completed application packets are stable along actual verifier replay.
Earlier reads recover the same bound blocks and oracle answers at every later
prefix. The bounded frontend tape matters here: answers outside its public
window are absent from the packet, even after later rounds have finished. -/
noncomputable section
namespace LfzkV2.Current.ApplicationViewReplay
open SumcheckV2 ApplicationSetup

variable {g : Geometry} {fields : Fields} {Advice Auth Key Base C : Type}
local notation "Point" => Replay.Point g fields Advice Auth Key
  (Base × ProtocolWrites.Fresh g fields Advice)
variable (e : Replay.Encoding g fields Advice Auth Key
  (Base × ProtocolWrites.Fresh g fields Advice) C)
variable (initialLink : Digest) (proof : Replay.Output g fields Advice Auth)

/-- A strict-past read returns the actual answer at that earlier boundary. -/
theorem strictAnswer_replay (H : Point → Digest × C) (n q : ℕ) (hn : n ≤ g.roles.length) (hq : q < n) :
    ApplicationPrefix.strictAnswer ((e.chain initialLink).point proof H n)
      (((e.chain initialLink).point proof H n).priorAnswers H) q =
      some (H ((e.chain initialLink).point proof H q)).2 := by
  have hr := (e.chain initialLink).point_rank proof H hn
  change Input.rank _ = n at hr
  unfold ApplicationPrefix.strictAnswer
  rw [dif_pos (by rw [hr]; exact hq)]
  congr 1
  exact congrArg (fun p => (H p).2)
    (e.point_priorPoints initialLink proof H n hn ⟨q,hq⟩)

theorem strictAnswer_replay_eq (H : Point → Digest × C) (n m q : ℕ)
    (hn : n ≤ g.roles.length) (hm : m ≤ g.roles.length) (hqn : q < n) (hqm : q < m) :
    ApplicationPrefix.strictAnswer ((e.chain initialLink).point proof H n)
        (((e.chain initialLink).point proof H n).priorAnswers H) q =
      ApplicationPrefix.strictAnswer ((e.chain initialLink).point proof H m)
        (((e.chain initialLink).point proof H m).priorAnswers H) q := by
  rw [strictAnswer_replay e initialLink proof H n q hn hqn,
    strictAnswer_replay e initialLink proof H m q hm hqm]

/-- Once a frontend's complete window is in the strict past, its entire
bounded answer tape is identical at every later prefix. -/
theorem frontendTape_replay_eq (H : Point → Digest × C) (fallback : C) (n m start slots : ℕ)
    (hn : n ≤ g.roles.length) (hm : m ≤ g.roles.length)
    (hwn : start+slots ≤ n) (hwm : start+slots ≤ m) :
    ApplicationPrefix.frontendTape ((e.chain initialLink).point proof H n)
        (((e.chain initialLink).point proof H n).priorAnswers H) fallback start slots =
      ApplicationPrefix.frontendTape ((e.chain initialLink).point proof H m)
        (((e.chain initialLink).point proof H m).priorAnswers H) fallback start slots := by
  funext q
  by_cases hq : q < slots
  · simp only [ApplicationPrefix.frontendTape,if_pos hq,ApplicationPrefix.answerTape]
    rw [strictAnswer_replay_eq e initialLink proof H n m (start+q) hn hm (by omega) (by omega)]
  · simp only [ApplicationPrefix.frontendTape,if_neg hq]

/-- Completed prover-message parsing is independent of the later prefix.
The parser only inspects the frontend's public message window. -/
theorem messages_replay_eq {F : Type} {out input : ℕ}
    (side : Side) (field : fields side → F) (circuit : Layered.Circuit F out input)
    (H : Point → Digest × C) (n m start : ℕ) (hn : n ≤ g.roles.length) (hm : m ≤ g.roles.length)
    (hwn : start+FrontendReplay.slots circuit ≤ n)
    (hwm : start+FrontendReplay.slots circuit ≤ m) :
    ApplicationPrefix.Messages.read circuit
        (ApplicationPrefix.wire ((e.chain initialLink).point proof H n) side field start) =
      ApplicationPrefix.Messages.read circuit
        (ApplicationPrefix.wire ((e.chain initialLink).point proof H m) side field start) := by
  apply ApplicationPrefix.Messages.readFrom_congr
  intro q _ hq
  exact ApplicationViews.wire_replay_eq e side field initialLink proof H n m start q hn hm
    (by omega) (by omega) (by omega)

/-- Auxiliary writes, like conversion targets and masked advice, are also
recovered from the same recorded block at every later prefix. -/
theorem readAt_replay_eq {X : Type} (H : Point → Digest × C) (read : Base × ProtocolWrites.Fresh g fields Advice → Option X)
    (n m q : ℕ) (hn : n ≤ g.roles.length) (hm : m ≤ g.roles.length)
    (hq : q < g.roles.length) (hqn : q ≤ n) (hqm : q ≤ m) :
    ((e.chain initialLink).point proof H n).readAt q read =
      ((e.chain initialLink).point proof H m).readAt q read := by
  rw [e.readAt_replay initialLink proof H n hn ⟨q,hq⟩ hqn,
    e.readAt_replay initialLink proof H m hm ⟨q,hq⟩ hqm]

section Prime
variable {shared : ℕ}
variable (prime : PrimePublic (ZMod Adapter.Mdoc.primeOrder) shared)
variable (field : fields .prime → ZMod Adapter.Mdoc.primeOrder)
variable (decode : C → ℕ → ZMod Adapter.Mdoc.primeOrder)
variable (nonzero : C → Linear.TerminalSampling.Nonzero (ZMod Adapter.Mdoc.primeOrder))
variable (fallback : C)

/-- Once the prime message window is in the past, the actual prime data and
its split claim are identical at every later replay prefix. -/
theorem readPrime_replay_eq (H : Point → Digest × C) (n m : ℕ)
    (hn : n ≤ g.roles.length) (hm : m ≤ g.roles.length)
    (hwn : g.primeStart+FrontendReplay.slots prime.circuit ≤ n)
    (hwm : g.primeStart+FrontendReplay.slots prime.circuit ≤ m) :
    ApplicationPrefix.readPrime prime field decode nonzero fallback
        ((e.chain initialLink).point proof H n)
        (((e.chain initialLink).point proof H n).priorAnswers H) =
      ApplicationPrefix.readPrime prime field decode nonzero fallback
        ((e.chain initialLink).point proof H m)
        (((e.chain initialLink).point proof H m).priorAnswers H) := by
  have hrn := (e.chain initialLink).point_rank proof H hn
  have hrm := (e.chain initialLink).point_rank proof H hm
  change Input.rank _ = n at hrn
  change Input.rank _ = m at hrm
  unfold ApplicationPrefix.readPrime
  rw [if_pos (by rw [hrn]; exact hwn),if_pos (by rw [hrm]; exact hwm)]
  rw [messages_replay_eq e initialLink proof .prime field prime.circuit H n m g.primeStart hn hm hwn hwm,
    frontendTape_replay_eq e initialLink proof H fallback n m g.primeStart
      (FrontendReplay.slots prime.circuit) hn hm hwn hwm]

/-- A late successful read supplies the identical prime data at every
earlier boundary after the prime frontend. -/
theorem readPrime_from_late (H : Point → Digest × C) (n m : ℕ)
    (hn : n ≤ g.roles.length) (hm : m ≤ g.roles.length)
    (hwn : g.primeStart+FrontendReplay.slots prime.circuit ≤ n)
    (hwm : g.primeStart+FrontendReplay.slots prime.circuit ≤ m)
    (data : PrimeData prime C)
    (hlate : ApplicationPrefix.readPrime prime field decode nonzero fallback
      ((e.chain initialLink).point proof H m)
      (((e.chain initialLink).point proof H m).priorAnswers H) = some data) :
    ApplicationPrefix.readPrime prime field decode nonzero fallback
        ((e.chain initialLink).point proof H n)
        (((e.chain initialLink).point proof H n).priorAnswers H) = some data :=
  (readPrime_replay_eq e initialLink proof prime field decode nonzero fallback H n m hn hm
    hwn hwm).trans hlate

end Prime

section Adapter
variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable {shared maskBits adviceBits : ℕ}
variable (binary : BinaryPublic B shared maskBits adviceBits)
variable (prime : PrimePublic (ZMod Adapter.Mdoc.primeOrder) shared)
variable (field : fields .prime → ZMod Adapter.Mdoc.primeOrder)
variable (decode : C → ℕ → ZMod Adapter.Mdoc.primeOrder)
variable (nonzero : C → Linear.TerminalSampling.Nonzero (ZMod Adapter.Mdoc.primeOrder))
variable (convert : C → Fin 2 → Linear.TerminalSampling.Nonzero (ZMod Adapter.Mdoc.primeOrder))
variable (advice : Advice → Option (Fin 2 → Fin adviceBits → Bool)) (fallback : C)

omit [DecidableEq B] in
/-- A successful full binary decode contains exactly the earlier adapter
packet. Its future frontend and packing fields play no role in this projection. -/
theorem readAdapter_of_readBinary (point : Point) (past : Fin point.rank → C)
    (primeData : PrimeData prime C) (generator : Bˣ)
    (degree : g.packingDegree = binary.degree)
    (binaryField : fields .binary → B) (binaryDecode : C → ℕ → B)
    (binaryNonzero : C → Linear.TerminalSampling.Nonzero B)
    (binaryData : BinaryData binary primeData generator)
    (hprime : ApplicationPrefix.readPrime prime field decode nonzero fallback point past = some primeData)
    (hbinary : ApplicationPrefix.readBinary binary primeData generator degree binaryField field
      binaryDecode binaryNonzero nonzero convert advice fallback point past = some binaryData) :
    ApplicationViews.readAdapter binary prime field decode nonzero convert advice fallback point past =
      some ⟨primeData,binaryData.eta,binaryData.mu,binaryData.alpha,binaryData.masked⟩ := by
  have hs := ApplicationPrefix.readBinary_spec binary primeData generator degree binaryField field
    binaryDecode binaryNonzero nonzero convert advice fallback point past binaryData hbinary
  obtain ⟨scale,hscale,heta⟩ := hs.2.1
  obtain ⟨conversion,hconversion,halpha⟩ := hs.2.2.1
  obtain ⟨raw,hraw,hmasked⟩ := hs.2.2.2.2.1
  unfold ApplicationViews.readAdapter
  rw [hprime,hscale,hconversion,hs.2.2.2.1,hraw]
  simp only [Option.bind_eq_bind,Option.bind_some,hmasked,heta,halpha]

omit [Fintype B] [DecidableEq B] in
/-- The circuit-generating packet is fixed as soon as conversion and masked
advice are bound. Later binary sumcheck and packing rounds cannot change it. -/
theorem readAdapter_replay_eq (H : Point → Digest × C) (n m : ℕ)
    (hn : n ≤ g.roles.length) (hm : m ≤ g.roles.length)
    (hwn : g.primeStart+FrontendReplay.slots prime.circuit ≤ n)
    (hwm : g.primeStart+FrontendReplay.slots prime.circuit ≤ m)
    (hcn : ApplicationPrefix.conversionIndex g < n)
    (hcm : ApplicationPrefix.conversionIndex g < m)
    (han : g.binaryStart ≤ n) (ham : g.binaryStart ≤ m) :
    ApplicationViews.readAdapter binary prime field decode nonzero convert advice fallback
        ((e.chain initialLink).point proof H n)
        (((e.chain initialLink).point proof H n).priorAnswers H) =
      ApplicationViews.readAdapter binary prime field decode nonzero convert advice fallback
        ((e.chain initialLink).point proof H m)
        (((e.chain initialLink).point proof H m).priorAnswers H) := by
  have hsn : ApplicationPrefix.rescalingIndex g < n := by
    unfold ApplicationPrefix.conversionIndex at hcn
    omega
  have hsm : ApplicationPrefix.rescalingIndex g < m := by
    unfold ApplicationPrefix.conversionIndex at hcm
    omega
  have hab : g.binaryStart < g.roles.length := by
    have hlength := g.roles_length
    unfold Geometry.binaryStart
    omega
  unfold ApplicationViews.readAdapter
  rw [readPrime_replay_eq e initialLink proof prime field decode nonzero fallback H n m hn hm hwn hwm,
    strictAnswer_replay_eq e initialLink proof H n m (ApplicationPrefix.rescalingIndex g) hn hm hsn hsm,
    strictAnswer_replay_eq e initialLink proof H n m (ApplicationPrefix.conversionIndex g) hn hm hcn hcm,
    readAt_replay_eq e initialLink proof H
      (fun block => block.2.mu.map field) n m (ApplicationPrefix.conversionIndex g)
      hn hm (by omega) (by omega) (by omega),
    readAt_replay_eq e initialLink proof H
      (fun block => block.2.advice) n m g.binaryStart hn hm hab han ham]

omit [DecidableEq B] in
/-- A late full binary parse supplies the actual earlier circuit-generating
packet, without a separately assumed earlier parse or System equality. -/
theorem readAdapter_from_late (H : Point → Digest × C) (n m : ℕ)
    (hn : n ≤ g.roles.length) (hm : m ≤ g.roles.length)
    (hwn : g.primeStart+FrontendReplay.slots prime.circuit ≤ n)
    (hwm : g.primeStart+FrontendReplay.slots prime.circuit ≤ m)
    (hcn : ApplicationPrefix.conversionIndex g < n)
    (hcm : ApplicationPrefix.conversionIndex g < m)
    (han : g.binaryStart ≤ n) (ham : g.binaryStart ≤ m)
    (primeData : PrimeData prime C) (generator : Bˣ)
    (degree : g.packingDegree = binary.degree)
    (binaryField : fields .binary → B) (binaryDecode : C → ℕ → B)
    (binaryNonzero : C → Linear.TerminalSampling.Nonzero B)
    (binaryData : BinaryData binary primeData generator)
    (hprime : ApplicationPrefix.readPrime prime field decode nonzero fallback
      ((e.chain initialLink).point proof H m)
      (((e.chain initialLink).point proof H m).priorAnswers H) = some primeData)
    (hbinary : ApplicationPrefix.readBinary binary primeData generator degree binaryField field
      binaryDecode binaryNonzero nonzero convert advice fallback
      ((e.chain initialLink).point proof H m)
      (((e.chain initialLink).point proof H m).priorAnswers H) = some binaryData) :
    ApplicationViews.readAdapter binary prime field decode nonzero convert advice fallback
        ((e.chain initialLink).point proof H n)
        (((e.chain initialLink).point proof H n).priorAnswers H) =
      some ⟨primeData,binaryData.eta,binaryData.mu,binaryData.alpha,binaryData.masked⟩ :=
  (readAdapter_replay_eq e initialLink proof binary prime field decode nonzero convert advice fallback
    H n m hn hm hwn hwm hcn hcm han ham).trans
    (readAdapter_of_readBinary binary prime field decode nonzero convert advice fallback _ _ primeData
      generator degree binaryField binaryDecode binaryNonzero binaryData hprime hbinary)

omit [DecidableEq B] in
/-- Packing reads the same completed binary frontend that was reconstructed
at the late batching prefix. Its earlier packet needs neither delta nor A. -/
theorem readBinaryPacket_from_late (H : Point → Digest × C) (n m : ℕ)
    (hn : n ≤ g.roles.length) (hm : m ≤ g.roles.length)
    (hwn : g.primeStart+FrontendReplay.slots prime.circuit ≤ n)
    (hwm : g.primeStart+FrontendReplay.slots prime.circuit ≤ m)
    (hcn : ApplicationPrefix.conversionIndex g < n)
    (hcm : ApplicationPrefix.conversionIndex g < m)
    (han : g.binaryStart ≤ n) (ham : g.binaryStart ≤ m)
    (primeData : PrimeData prime C) (generator : Bˣ)
    (degree : g.packingDegree = binary.degree)
    (binaryField : fields .binary → B) (binaryDecode : C → ℕ → B)
    (binaryNonzero : C → Linear.TerminalSampling.Nonzero B)
    (binaryData : BinaryData binary primeData generator)
    (hbinaryWindow : g.binaryStart+FrontendReplay.slots binaryData.setup.circuit ≤ n)
    (hprime : ApplicationPrefix.readPrime prime field decode nonzero fallback
      ((e.chain initialLink).point proof H m)
      (((e.chain initialLink).point proof H m).priorAnswers H) = some primeData)
    (hbinary : ApplicationPrefix.readBinary binary primeData generator degree binaryField field
      binaryDecode binaryNonzero nonzero convert advice fallback
      ((e.chain initialLink).point proof H m)
      (((e.chain initialLink).point proof H m).priorAnswers H) = some binaryData) :
    ApplicationViews.readBinaryPacket binary prime generator binaryField field decode nonzero convert advice fallback
        ((e.chain initialLink).point proof H n)
        (((e.chain initialLink).point proof H n).priorAnswers H) =
      some { adapter := ⟨primeData,binaryData.eta,binaryData.mu,binaryData.alpha,binaryData.masked⟩
             payload := binaryData.payload,answers := binaryData.answers } := by
  have hadapter := readAdapter_from_late e initialLink proof binary prime field decode nonzero convert advice
    fallback H n m hn hm hwn hwm hcn hcm han ham primeData generator degree binaryField
    binaryDecode binaryNonzero binaryData hprime hbinary
  have hs := ApplicationPrefix.readBinary_spec binary primeData generator degree binaryField field
    binaryDecode binaryNonzero nonzero convert advice fallback _ _ binaryData hbinary
  have hrn := (e.chain initialLink).point_rank proof H hn
  have hrm := (e.chain initialLink).point_rank proof H hm
  change Input.rank _ = n at hrn
  change Input.rank _ = m at hrm
  have hlateWindow : g.binaryStart+FrontendReplay.slots binaryData.setup.circuit ≤ m := by
    simpa only [hrm] using hs.1
  have hmessages := messages_replay_eq e initialLink proof .binary binaryField binaryData.setup.circuit H
    n m g.binaryStart hn hm hbinaryWindow hlateWindow
  have htape := frontendTape_replay_eq e initialLink proof H fallback n m g.binaryStart
    (FrontendReplay.slots binaryData.setup.circuit) hn hm hbinaryWindow hlateWindow
  unfold ApplicationViews.readBinaryPacket
  rw [hadapter]
  simp only [Option.bind_eq_bind,Option.bind_some]
  erw [if_pos (show g.binaryStart+FrontendReplay.slots binaryData.setup.circuit ≤
    ((e.chain initialLink).point proof H n).rank by rw [hrn]; exact hbinaryWindow)]
  erw [hmessages,hs.2.2.2.2.2.2.2.2.1,htape,← hs.2.2.2.2.2.2.2.2.2.2.2]
  rfl

omit [DecidableEq B] in
/-- The packing packet is the source equation of the parsed frontend plus
the already-bound U vector. Its construction never needs delta or A. -/
theorem readPackingPacket_of_readBinaryPacket (primeData : PrimeData prime C) (generator : Bˣ)
    (degree : g.packingDegree = binary.degree)
    (binaryField : fields .binary → B) (binaryDecode : C → ℕ → B)
    (binaryNonzero : C → Linear.TerminalSampling.Nonzero B)
    (binaryData : BinaryData binary primeData generator)
    (point : Point) (past : Fin point.rank → C)
    (hpacket : ApplicationViews.readBinaryPacket binary prime generator binaryField field decode nonzero
      convert advice fallback point past =
        some { adapter := ⟨primeData,binaryData.eta,binaryData.mu,binaryData.alpha,binaryData.masked⟩
               payload := binaryData.payload,answers := binaryData.answers })
    (hdecode : binaryData.decode = binaryDecode) (hnonzero : binaryData.nonzero = binaryNonzero)
    (U : Fin g.packingDegree → fields .binary)
    (hreadU : point.readAt (ApplicationPrefix.packingIndex g) (fun block => block.2.packingU) = some U)
    (hU : binaryData.U = fun i => binaryField (U (Fin.cast degree.symm i))) :
    ApplicationViews.readPackingPacket binary prime generator degree binaryField field binaryDecode binaryNonzero
        decode nonzero convert advice fallback point past =
      some { source := binaryData.frontend.source, values := ApplicationViews.binaryValues binary prime
             U := binaryData.U } := by
  unfold ApplicationViews.readPackingPacket
  rw [hpacket]
  simp only [Option.bind_eq_bind,Option.bind_some,hreadU]
  rw [← hdecode,← hnonzero,← hU]
  rfl

end Adapter
end LfzkV2.Current.ApplicationViewReplay
