import LfzkV2.Current.ApplicationPrefix
import LfzkV2.Current.ApplicationCharging

/-! Query-local application views. A frontend view carries only the circuit,
its public pad plan, bound message prefix and ideal samplers; it requires no
whole application System, full-proof replay or compiled-row certificate.
Unavailable packets are rejected and contribute zero local charge. -/
noncomputable section
namespace LfzkV2.Current.ApplicationViews
open Application ApplicationOracle ApplicationCharging RecursivePolygero Counting
open SumcheckV2 Finset
open scoped Classical

/-- Local frontend data with its public shape/sampling checks. Payload
getters may retain only the current prefix; no future proof or answer tape is
part of this record. -/
structure FrontendView (F Pad Witness Point C : Type) [Field F] [Fintype F] [DecidableEq F] [Fintype C] where
  data : FrontendData F Pad Witness Point C
  capacity : ℕ
  decoder : FrontendReplay.Decoder capacity data.decode data.nonzero
  coalesced : FrontendReplay.Coalesced data.circuit
  fits : FrontendReplay.Fits capacity data.circuit 0

section Frontend
variable {roles : List Role} {Key Block Link Body C Oracle B N IB IN F Pad : Type}
variable [Field B] [Field N] [DecidableEq B] [DecidableEq N] [Fintype IB] [Fintype IN]
variable [Field F] [Fintype F] [DecidableEq F] [Fintype C]
variable (S : SelectionSource roles Key Block Link Body C Oracle B N IB IN)

local notation "Point" => Input roles Key Block Link Body
local notation "View" => FrontendView F Pad (Selection.Pair B N IB IN) (Input roles Key Block Link Body) C

namespace FrontendView

def bad (view : View) (point : Point) (H : Point → Link × C) (answer : C) : Prop :=
  view.data.bad S point H answer

theorem bad_off (view : View) (point : Point) (H H' : Point → Link × C)
    (h : Bcs.TotalOracle.AgreeOff point H H') (answer : C) :
    view.bad S point H answer ↔ view.bad S point H' answer := by
  unfold bad FrontendData.bad
  rw [SelectedFrontendOracle.bad_off S.lists S.coins S.responses S.oracle S.oracle_off
    view.data.circuit view.data.plan view.data.payload view.data.inputs view.data.pads view.data.decode
    view.data.nonzero view.data.start view.data.fallback point H H' h answer]

theorem bad_card_mul_le (view : View) (point : Point) (H : Point → Link × C) :
    (univ.filter (view.bad S point H)).card * (Fintype.card F-1) ≤ 2*Fintype.card C := by
  by_cases hs : view.data.start ≤ point.rank
  · simpa only [bad,FrontendData.bad,hs,true_and] using
      SelectedFrontendOracle.bad_card_mul_le S.lists S.coins S.responses S.oracle
        view.data.circuit view.data.plan view.data.payload view.data.inputs view.data.pads
        view.data.decode view.data.nonzero view.decoder view.data.start view.data.fallback
        point H hs view.coalesced view.fits
  · simp [bad,FrontendData.bad,hs]

end FrontendView

variable (read : (point : Input roles Key Block Link Body) → (Fin point.rank → C) →
  Option (FrontendView F Pad (Selection.Pair B N IB IN) (Input roles Key Block Link Body) C))

/-- A missing or malformed packet is a rejected branch, with no artificial
frontend execution used to fill its place. -/
def frontendBad (point : Point) (H : Point → Link × C) (answer : C) : Prop :=
  match read point (point.priorAnswers H) with
  | none => False
  | some view => view.bad S point H answer

def frontendCharge (point : Point) (H : Point → Link × C) (answer : Link × C) : ℚ :=
  indicator (frontendBad S read point H answer.2)

theorem frontendBad_off (point : Point) (H H' : Point → Link × C)
    (h : Bcs.TotalOracle.AgreeOff point H H') (answer : C) :
    frontendBad S read point H answer ↔ frontendBad S read point H' answer := by
  unfold frontendBad
  rw [point.priorAnswers_off h]
  cases read point (point.priorAnswers H') with
  | none => rfl
  | some view => exact view.bad_off S point H H' h answer

theorem frontendBad_card_mul_le (point : Point) (H : Point → Link × C) :
    (univ.filter (frontendBad S read point H)).card * (Fintype.card F-1) ≤ 2*Fintype.card C := by
  unfold frontendBad
  cases read point (point.priorAnswers H) with
  | none => simp
  | some view => exact view.bad_card_mul_le S point H

theorem frontendCharge_nonneg (point : Point) (H : Point → Link × C) (answer : Link × C) :
    0 ≤ frontendCharge S read point H answer := by
  unfold frontendCharge indicator
  split_ifs <;> norm_num

theorem frontendCharge_off (point : Point) (H H' : Point → Link × C)
    (h : Bcs.TotalOracle.AgreeOff point H H') (answer : Link × C) :
    frontendCharge S read point H answer = frontendCharge S read point H' answer := by
  unfold frontendCharge
  rw [frontendBad_off S read point H H' h answer.2]

theorem frontendCharge_sum [Fintype Link] (point : Point) (H : Point → Link × C) :
    (∑ answer,frontendCharge S read point H answer) ≤
      Fintype.card (Link × C)*(2/((Fintype.card F-1 : ℕ) : ℚ)) := by
  exact indicator_link_sum_le (frontendBad S read point H) 2 (Fintype.card F-1)
    (Nat.sub_pos_of_lt Fintype.one_lt_card) (frontendBad_card_mul_le S read point H)

end Frontend

section OptionalPackets
variable {roles : List Role} {Key Block Link Body C Oracle B N IB IN D : Type}
variable [Field B] [Field N] [Fintype B] [Fintype N] [DecidableEq B] [DecidableEq N]
  [Fintype IB] [Fintype IN] [Fintype C]
variable (S : SelectionSource roles Key Block Link Body C Oracle B N IB IN)
local notation "Point" => Input roles Key Block Link Body
local notation "Pair" => Selection.Pair B N IB IN

def optionBad (bad : D → Pair → C → Prop) : Option D → Pair → C → Prop
  | none,_,_ => False
  | some packet,w,answer => bad packet w answer

def packetBad (read : (point : Input roles Key Block Link Body) → (Fin point.rank → C) → Option D)
    (bad : D → Pair → C → Prop) := S.test read (optionBad bad)

omit [Fintype B] [Fintype N] [Fintype C] in
theorem packetBad_off
    (read : (point : Input roles Key Block Link Body) → (Fin point.rank → C) → Option D)
    (bad : D → Pair → C → Prop) (point : Point) (H H' : Point → Link × C)
    (h : Bcs.TotalOracle.AgreeOff point H H') (answer : C) :
    packetBad S read bad point H answer ↔ packetBad S read bad point H' answer :=
  S.test_off read _ point H H' h answer

omit [Fintype B] [Fintype N] in
theorem packetBad_card_mul_le
    (read : (point : Input roles Key Block Link Body) → (Fin point.rank → C) → Option D)
    (bad : D → Pair → C → Prop) (point : Point) (H : Point → Link × C)
    (numerator denominator : ℕ)
    (hlocal : ∀ packet w, (univ.filter (bad packet w)).card*denominator ≤ numerator*Fintype.card C) :
    (univ.filter (packetBad S read bad point H)).card*denominator ≤ numerator*Fintype.card C := by
  apply S.test_card_mul_le read (optionBad bad) point H numerator denominator
  intro packet w
  cases packet with
  | none => simp [optionBad]
  | some packet => exact hlocal packet w

def packetCharge
    (read : (point : Input roles Key Block Link Body) → (Fin point.rank → C) → Option D)
    (bad : D → Pair → C → Prop) (point : Point) (H : Point → Link × C) (answer : Link × C) : ℚ :=
  indicator (packetBad S read bad point H answer.2)

omit [Fintype B] [Fintype N] [Fintype C] in
theorem packetCharge_off
    (read : (point : Input roles Key Block Link Body) → (Fin point.rank → C) → Option D)
    (bad : D → Pair → C → Prop) (point : Point) (H H' : Point → Link × C)
    (h : Bcs.TotalOracle.AgreeOff point H H') (answer : Link × C) :
    packetCharge S read bad point H answer = packetCharge S read bad point H' answer := by
  unfold packetCharge
  rw [packetBad_off S read bad point H H' h answer.2]

def batchBad {Slot : Type}
    (read : (point : Input roles Key Block Link Body) → (Fin point.rank → C) →
      Option (BatchPacket N Slot Pair C)) := packetBad S read (fun packet w answer => packet.bad w answer)

omit [Fintype B] in
theorem batchBad_card_mul_le {Slot : Type}
    (read : (point : Input roles Key Block Link Body) → (Fin point.rank → C) →
      Option (BatchPacket N Slot Pair C)) (point : Point) (H : Point → Link × C) :
    (univ.filter (batchBad S read point H)).card*Fintype.card N ≤ Fintype.card C := by
  simpa only [batchBad,one_mul] using packetBad_card_mul_le S read
    (fun packet w answer => packet.bad w answer) point H 1 (Fintype.card N)
    (fun packet w => by simpa only [one_mul] using packet.bad_card_mul_le w)

def rescaleBad {Shared Other : Type} [Fintype Shared] [Fintype Other]
    (read : (point : Input roles Key Block Link Body) → (Fin point.rank → C) → Option (RescaleData N Shared Other Pair))
    (decoder : BalancedDecoder C (Linear.TerminalSampling.Nonzero N)) :=
  packetBad S read (fun packet w answer => packet.bad w (decoder.decode answer))

omit [Fintype B] in
theorem rescaleBad_card_mul_le {Shared Other : Type} [Fintype Shared] [Fintype Other]
    (read : (point : Input roles Key Block Link Body) → (Fin point.rank → C) → Option (RescaleData N Shared Other Pair))
    (decoder : BalancedDecoder C (Linear.TerminalSampling.Nonzero N)) (point : Point) (H : Point → Link × C) :
    (univ.filter (rescaleBad S read decoder point H)).card*(Fintype.card N-1) ≤ Fintype.card C := by
  simpa only [rescaleBad,one_mul] using packetBad_card_mul_le S read
    (fun packet w answer => packet.bad w (decoder.decode answer)) point H 1 (Fintype.card N-1)
    (fun packet w => by simpa only [one_mul] using packet.bad_card_mul_le w decoder)

def conversionBad {p bits : ℕ} [Fact p.Prime]
    (read : (point : Input roles Key Block Link Body) → (Fin point.rank → C) → Option (ConversionData p bits Pair))
    (decoder : BalancedDecoder C (Linear.TerminalSampling.Nonzero (ZMod p) ×
      Linear.TerminalSampling.Nonzero (ZMod p))) (M K : ℕ) :=
  packetBad S read (fun packet w answer => packet.bad M K w (decoder.decode answer))

omit [Fintype B] [Fintype N] in
theorem conversionBad_card_mul_le {p bits M K : ℕ} [Fact p.Prime]
    (read : (point : Input roles Key Block Link Body) → (Fin point.rank → C) → Option (ConversionData p bits Pair))
    (decoder : BalancedDecoder C (Linear.TerminalSampling.Nonzero (ZMod p) ×
      Linear.TerminalSampling.Nonzero (ZMod p))) (hM : 0 < M) (hbits : bits ≤ K)
    (point : Point) (H : Point → Link × C) :
    (univ.filter (conversionBad S read decoder M K point H)).card*(p-1)^2 ≤
      (2*(K*p/M)+1)^2*Fintype.card C := by
  exact packetBad_card_mul_le S read _ point H _ _ (fun packet w => packet.bad_card_mul_le w hM hbits decoder)

def packingBad {KField F I J Slot : Type} [Field KField] [Fintype KField] [Field F] [Fintype F]
    [Algebra KField F] [Fintype I] [DecidableEq I] [Fintype J]
    (read : (point : Input roles Key Block Link Body) → (Fin point.rank → C) →
      Option (PackingData KField F I J Slot Pair)) (decoder : BalancedDecoder C (I → F)) :=
  packetBad S read (fun packet w answer => packet.bad w (decoder.decode answer))

omit [Fintype B] [Fintype N] in
theorem packingBad_card_mul_le {KField F I J Slot : Type} [Field KField] [Fintype KField] [Field F] [Fintype F]
    [DecidableEq F] [Algebra KField F] [Fintype I] [DecidableEq I] [Fintype J]
    (read : (point : Input roles Key Block Link Body) → (Fin point.rank → C) →
      Option (PackingData KField F I J Slot Pair)) (decoder : BalancedDecoder C (I → F))
    (point : Point) (H : Point → Link × C) :
    (univ.filter (packingBad S read decoder point H)).card*Fintype.card F ≤ Fintype.card C := by
  simpa only [packingBad,one_mul] using packetBad_card_mul_le S read
    (fun packet w answer => packet.bad w (decoder.decode answer)) point H 1 (Fintype.card F)
    (fun packet w => by simpa only [one_mul] using packet.bad_card_mul_le w decoder)

end OptionalPackets

namespace PartialMessages
variable {F : Type} [Field F] {out input : ℕ}

/-- Only unavailable future prover messages receive typed zero values.
Required past or current messages are left untouched, so missing or malformed
bound messages still make the partial parser reject. -/
def filledWire (circuit : Layered.Circuit F out input)
    (wire : ℕ → Option (Layered.Replay.Message F)) (through q : ℕ) :
    Option (Layered.Replay.Message F) :=
  if q ≤ through then wire q else
    some (FrontendTranscript.write circuit (FrontendBody.zeroPayload circuit) q)

def read (circuit : Layered.Circuit F out input)
    (wire : ℕ → Option (Layered.Replay.Message F)) (through : ℕ) :
    Option (Layered.Replay.Payload circuit) :=
  ApplicationPrefix.Messages.read circuit (filledWire circuit wire through)

theorem exists_of_complete (circuit : Layered.Circuit F out input)
    (wire : ℕ → Option (Layered.Replay.Message F)) (through : ℕ)
    (complete : Layered.Replay.Payload circuit)
    (h : ApplicationPrefix.Messages.read circuit wire = some complete) :
    ∃ payload, read circuit wire through = some payload := by
  have hm := ApplicationPrefix.Messages.readFrom_mix circuit wire
    (fun q => some (FrontendTranscript.write circuit (FrontendBody.zeroPayload circuit) q))
    (fun q => decide (q ≤ through)) 0 complete (FrontendBody.zeroPayload circuit) h
    (ApplicationPrefix.Messages.read_write circuit (FrontendBody.zeroPayload circuit))
  change ∃ payload, ApplicationPrefix.Messages.readFrom circuit
    (fun q => if q ≤ through then wire q else
      some (FrontendTranscript.write circuit (FrontendBody.zeroPayload circuit) q)) 0 = some payload
  simpa only [decide_eq_true_eq] using hm

theorem exists_of_late (circuit : Layered.Circuit F out input)
    (early late : ℕ → Option (Layered.Replay.Message F)) (through : ℕ)
    (complete : Layered.Replay.Payload circuit)
    (hlate : ApplicationPrefix.Messages.read circuit late = some complete)
    (hprefix : ∀ q, q < FrontendReplay.slots circuit → q ≤ through → early q = late q) :
    ∃ payload, read circuit early through = some payload := by
  obtain ⟨payload,hpayload⟩ := exists_of_complete circuit late through complete hlate
  refine ⟨payload,?_⟩
  change ApplicationPrefix.Messages.readFrom circuit (filledWire circuit early through) 0 = some payload
  rw [ApplicationPrefix.Messages.readFrom_congr circuit _ (filledWire circuit late through) 0 (by
    intro q _ hq
    have hq' : q < FrontendReplay.slots circuit := by simpa only [Nat.zero_add] using hq
    by_cases h : q ≤ through
    · simp only [filledWire,if_pos h,hprefix q hq' h]
    · simp only [filledWire,if_neg h])]
  exact hpayload

/-- A successful partial decode preserves every already-bound message.
Future zero completion changes no local test whose message has been written. -/
theorem message_eq (circuit : Layered.Circuit F out input)
    (wire : ℕ → Option (Layered.Replay.Message F)) (through : ℕ)
    (payload : Layered.Replay.Payload circuit) (h : read circuit wire through = some payload)
    (role : Layered.Replay.LayerRole circuit)
    (hrole : FrontendReplay.queryIndex circuit role 0 ≤ through) :
    Layered.Replay.layerMessage circuit payload role =
      Layered.Replay.layerMessage circuit
        (FrontendTranscript.read circuit (fun q => (wire q).getD .empty)) role := by
  have hp := ApplicationPrefix.Messages.readFrom_agrees circuit
    (filledWire circuit wire through) 0 payload h
  have hm := FrontendTranscript.layerMessage_readFrom_congr circuit role
    (fun q => (filledWire circuit wire through q).getD .empty)
    (fun q => (wire q).getD .empty) 0
    (by simp only [filledWire,if_pos hrole])
  rw [hp] at hm
  exact hm

end PartialMessages

section Replay
variable {g : Geometry} {fields : Fields} {Advice Auth Key Base C : Type}
local notation "Point" => Replay.Point g fields Advice Auth Key (Base × ProtocolWrites.Fresh g fields Advice)
variable (e : Replay.Encoding g fields Advice Auth Key (Base × ProtocolWrites.Fresh g fields Advice) C)

/-- Earlier message reads agree at any two actual replay prefixes. This
uses recorded blocks and strict prior answers; it requires no caller-supplied
equality between a proof payload and a reconstructed message. -/
theorem wire_replay_eq {F : Type} (side : Side) (field : fields side → F)
    (initialLink : Digest) (proof : Replay.Output g fields Advice Auth) (H : Point → Digest × C)
    (n m start q : ℕ) (hn : n ≤ g.roles.length) (hm : m ≤ g.roles.length)
    (hq : start+q < g.roles.length) (hqn : start+q ≤ n) (hqm : start+q ≤ m) :
    ApplicationPrefix.wire ((e.chain initialLink).point proof H n) side field start q =
      ApplicationPrefix.wire ((e.chain initialLink).point proof H m) side field start q := by
  unfold ApplicationPrefix.wire
  rw [e.readAt_replay initialLink proof H n hn ⟨start+q,hq⟩ hqn,
    e.readAt_replay initialLink proof H m hm ⟨start+q,hq⟩ hqm]

/-- A late complete frontend and an earlier partial view expose identical
messages through the current round. Only public window arithmetic and the
two actual successful parse results are needed. -/
theorem partial_message_from_late {F : Type} [Field F] {out input : ℕ}
    (side : Side) (field : fields side → F) (circuit : Layered.Circuit F out input)
    (initialLink : Digest) (proof : Replay.Output g fields Advice Auth) (H : Point → Digest × C)
    (n m start : ℕ) (hn : n ≤ g.roles.length) (hm : m ≤ g.roles.length)
    (hstart : start ≤ n) (hnm : n ≤ m) (hfit : start+FrontendReplay.slots circuit ≤ g.roles.length)
    (early late : Layered.Replay.Payload circuit)
    (hearly : PartialMessages.read circuit
      (ApplicationPrefix.wire ((e.chain initialLink).point proof H n) side field start) (n-start) = some early)
    (hlate : ApplicationPrefix.Messages.read circuit
      (ApplicationPrefix.wire ((e.chain initialLink).point proof H m) side field start) = some late)
    (role : Layered.Replay.LayerRole circuit) (hrole : FrontendReplay.queryIndex circuit role 0 ≤ n-start) :
    Layered.Replay.layerMessage circuit early role = Layered.Replay.layerMessage circuit late role := by
  have he := PartialMessages.message_eq circuit _ (n-start) early hearly role hrole
  have hl := ApplicationPrefix.Messages.readFrom_agrees circuit _ 0 late hlate
  have hwire := wire_replay_eq e side field initialLink proof H n m start
    (FrontendReplay.queryIndex circuit role 0) hn hm
    (by have h := FrontendReplay.queryIndex_lt circuit role 0; omega)
    (by omega) (by omega)
  have hx := FrontendTranscript.layerMessage_readFrom_congr circuit role
    (fun q => (ApplicationPrefix.wire ((e.chain initialLink).point proof H n) side field start q).getD .empty)
    (fun q => (ApplicationPrefix.wire ((e.chain initialLink).point proof H m) side field start q).getD .empty)
    0 (congrArg (fun x => x.getD .empty) hwire)
  exact he.trans (hx.trans (congrArg (fun p => Layered.Replay.layerMessage circuit p role) hl))

/-- Accepted complete messages guarantee that every earlier frontend view
parses. The witness and all past-message equalities are derived here, rather
than supplied as an accepted-path correspondence certificate. -/
theorem partial_from_late {F : Type} [Field F] {out input : ℕ}
    (side : Side) (field : fields side → F) (circuit : Layered.Circuit F out input)
    (initialLink : Digest) (proof : Replay.Output g fields Advice Auth) (H : Point → Digest × C)
    (n m start : ℕ) (hn : n ≤ g.roles.length) (hm : m ≤ g.roles.length)
    (hstart : start ≤ n) (hnm : n ≤ m) (hfit : start+FrontendReplay.slots circuit ≤ g.roles.length)
    (late : Layered.Replay.Payload circuit)
    (hlate : ApplicationPrefix.Messages.read circuit
      (ApplicationPrefix.wire ((e.chain initialLink).point proof H m) side field start) = some late) :
    ∃ early, PartialMessages.read circuit
        (ApplicationPrefix.wire ((e.chain initialLink).point proof H n) side field start) (n-start) = some early ∧
      ∀ role, FrontendReplay.queryIndex circuit role 0 ≤ n-start →
        Layered.Replay.layerMessage circuit early role = Layered.Replay.layerMessage circuit late role := by
  obtain ⟨early,hearly⟩ := PartialMessages.exists_of_late circuit _ _ (n-start) late hlate (by
    intro q hq hbound
    exact wire_replay_eq e side field initialLink proof H n m start q hn hm (by omega) (by omega) (by omega))
  exact ⟨early,hearly,fun role hrole =>
    partial_message_from_late e side field circuit initialLink proof H n m start hn hm hstart hnm hfit
      early late hearly hlate role hrole⟩

end Replay

section Concrete
open ApplicationSetup WitnessSelection
variable {g : Geometry} {fields : Fields} {Advice Auth Key Base C B : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B] [Fintype C]
variable {shared maskBits adviceBits : ℕ}
local notation "N" => ZMod Adapter.Mdoc.primeOrder
local notation "Point" => Input g.roles Key (Base × ProtocolWrites.Fresh g fields Advice) Digest
  (Body g fields Advice Auth)

def binaryValues (s : BinaryPublic B shared maskBits adviceBits)
    (n : PrimePublic N shared) (w : Selection.Pair B N s.Original n.Original) : s.Slot → B :=
  FingerprintRows.realize (CellLayout.selected s.cells) w.1

def primeValues (s : BinaryPublic B shared maskBits adviceBits)
    (n : PrimePublic N shared) (w : Selection.Pair B N s.Original n.Original) : n.Other ⊕ Unit → N :=
  FingerprintRows.realize (CellLayout.Prime.layout n.remaining n.pads) w.2

def primeFullValues (s : BinaryPublic B shared maskBits adviceBits)
    (n : PrimePublic N shared) (w : Selection.Pair B N s.Original n.Original) : Fin shared ⊕ n.Other → N :=
  Sum.elim (fun i => if s.sharedValues w.1 i then 1 else 0) (fun i => primeValues s n w (.inl i))

def primeInputs (s : BinaryPublic B shared maskBits adviceBits)
    (n : PrimePublic N shared) (w : Selection.Pair B N s.Original n.Original) : Cube n.input → N :=
  circuitInputs n.inputIndex n.publicInputs (CellLayout.Prime.input shared n.remaining n.pads)
    (primeFullValues s n w)

private theorem buildFrom_length {F Pad : Type} [Field F] (claim : PadExpression Pad F)
    (transcripts : List (Linear.LayerTranscript Pad F)) (constraints : Linear.Constraints Pad F)
    (h : Linear.buildFrom claim transcripts = some constraints) :
    constraints.layers.length = transcripts.length := by
  induction transcripts generalizing claim constraints with
  | nil => cases Option.some.inj h; rfl
  | cons head tail ih =>
      cases hr : (LfzkV2.Native.subtractConstant claim head.constant).rounds head.rounds head.challenges with
      | none => simp only [Linear.buildFrom,hr] at h; contradiction
      | some terminal =>
          cases ht : Linear.buildFrom head.nextClaim tail with
          | none => simp only [Linear.buildFrom,hr,ht] at h; contradiction
          | some rest =>
              simp only [Linear.buildFrom,hr,ht,Option.pure_def] at h
              cases Option.some.inj h
              exact congrArg (·+1) (ih _ rest ht)

private theorem circuit_proof_length {F Pad : Type} [Field F] {out input : ℕ}
    (circuit : Layered.Circuit F out input) (messages : Layered.Circuit.Messages Pad circuit)
    (weights : Cube out → F) : (circuit.proof messages weights).length = circuit.layers := by
  induction circuit with
  | input => rfl
  | entry _ _ _ ih => exact ih messages.2 _
  | layer _ _ _ ih =>
      simp only [Layered.Circuit.proof,Layered.Circuit.layers,List.length_cons]
      rw [ih messages.2 _]
      omega

omit [Fintype C] in
/-- Prime batching has one row per ordinary layer plus its input row.
The sampler dimension is thus public and bounded, independently of prover
messages, challenges or the number of quad fragments. -/
theorem prime_rows_length {F Slot Pad : Type} [Field F]
    (setup : FrontendVerifier.PrimeSetup F Slot Pad)
    (payload : Layered.Replay.Payload setup.circuit) (decode : C → ℕ → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F) (answers : ℕ → C) :
    (setup.prepare payload decode nonzero answers).rows.length = setup.circuit.layers+1 := by
  have hc := buildFrom_length zeroClaim
    (setup.circuit.proof (FrontendReplay.read decode nonzero setup.circuit setup.plan payload answers) 0)
    (FrontendVerifier.constraints setup.circuit setup.plan payload decode nonzero answers)
    (FrontendVerifier.constraints_built setup.circuit setup.plan payload decode nonzero answers)
  rw [circuit_proof_length] at hc
  simpa only [Frontend.Prime.rows,FrontendVerifier.PrimeSetup.prepare,Linear.compile,
    List.length_append,List.length_map,List.length_singleton] using congrArg (·+1) hc

structure PrimePacket (n : PrimePublic N shared) (C : Type) where
  payload : Layered.Replay.Payload n.circuit
  answers : ℕ → C

namespace PrimePacket
variable {n : PrimePublic N shared}
def frontend (packet : PrimePacket n C) (decode : C → ℕ → N)
    (nonzero : C → Linear.TerminalSampling.Nonzero N) :=
  n.setup.prepare packet.payload decode nonzero packet.answers
end PrimePacket

/-- The completed prime frontend before its row-batching challenge. No
rho value is invented merely to construct this packet. -/
def readPrimePacket (n : PrimePublic N shared) (field : fields .prime → N)
    (fallback : C) (point : Point) (past : Fin point.rank → C) : Option (PrimePacket n C) :=
  if g.primeStart+FrontendReplay.slots n.circuit ≤ point.rank then do
    let payload ← ApplicationPrefix.Messages.read n.circuit (ApplicationPrefix.wire point .prime field g.primeStart)
    some ⟨payload,ApplicationPrefix.frontendTape point past fallback g.primeStart (FrontendReplay.slots n.circuit)⟩
  else none

def readBatchPacket (s : BinaryPublic B shared maskBits adviceBits) (n : PrimePublic N shared)
    (decode : C → ℕ → N) (nonzero : C → Linear.TerminalSampling.Nonzero N)
    (decoder : BalancedDecoder C (Fin (n.circuit.layers+1) → N))
    (field : fields .prime → N) (fallback : C) (point : Point) (past : Fin point.rank → C) :
    Option (BatchPacket N (Fin shared ⊕ n.Other) (Selection.Pair B N s.Original n.Original) C) := do
  let packet ← readPrimePacket n field fallback point past
  let frontend := packet.frontend decode nonzero
  some {
    data := ⟨frontend.rows,primeFullValues s n⟩
    decoder := (prime_rows_length n.setup packet.payload decode nonzero packet.answers).symm ▸ decoder }

/-- Prime local tests need no adapter or binary frontend execution. Shared
input bits and prime pad cells are reconstructed directly from the selected
commitment pair using fixed public layouts. -/
def primeViewOfPayload (s : BinaryPublic B shared maskBits adviceBits) (n : PrimePublic N shared)
    (shape : FrontendSchedule.Plan N n.circuit) (capacity : ℕ)
    (decode : C → ℕ → N) (nonzero : C → Linear.TerminalSampling.Nonzero N)
    (decoder : FrontendReplay.Decoder capacity decode nonzero) (hcapacity : shape.capacity ≤ capacity)
    (fallback : C) (payload : Layered.Replay.Payload n.circuit) :
    FrontendView N (Fin n.pads) (Selection.Pair B N s.Original n.Original) Point C where
  data := {
    out := n.out,input := n.input,circuit := n.circuit
    plan := n.setup.plan
    payload := fun _ => payload
    inputs := primeInputs s n
    pads := fun w i => primeFullValues s n w (.inr (CellLayout.Prime.pad n.remaining n.pads i))
    decode := decode,nonzero := nonzero,start := g.primeStart,fallback := fallback }
  capacity := capacity
  decoder := decoder
  coalesced := shape.coalesced
  fits := shape.fits_of_capacityFrom_le 0 capacity hcapacity

def readPrimeView (s : BinaryPublic B shared maskBits adviceBits) (n : PrimePublic N shared)
    (shape : FrontendSchedule.Plan N n.circuit) (capacity : ℕ)
    (decode : C → ℕ → N) (nonzero : C → Linear.TerminalSampling.Nonzero N)
    (decoder : FrontendReplay.Decoder capacity decode nonzero) (hcapacity : shape.capacity ≤ capacity)
    (field : fields .prime → N) (fallback : C) (point : Point) (_past : Fin point.rank → C) :
    Option (FrontendView N (Fin n.pads) (Selection.Pair B N s.Original n.Original) Point C) :=
  if g.primeStart ≤ point.rank then
    (PartialMessages.read n.circuit (ApplicationPrefix.wire point .prime field g.primeStart)
      (point.rank-g.primeStart)).map (primeViewOfPayload s n shape capacity decode nonzero decoder hcapacity fallback)
  else none

/-- Only data already needed to generate the binary circuit is present.
Packing U, delta and A are deliberately absent from this packet. -/
structure AdapterPacket (s : BinaryPublic B shared maskBits adviceBits)
    (n : PrimePublic N shared) (C : Type) where
  prime : PrimeData n C
  eta : N
  mu : N
  alpha : Fin 2 → Linear.TerminalSampling.Nonzero N
  masked : Fin 2 → Fin adviceBits → Bool

namespace AdapterPacket
variable {s : BinaryPublic B shared maskBits adviceBits} {n : PrimePublic N shared}
variable (packet : AdapterPacket s n C) (generator : Bˣ)

def powers (tree : Fin 2) (i : Fin (shared+maskBits)) : Bˣ :=
  generator^((packet.alpha tree).val*(Handoff.weights packet.prime.claim.sharedWeights packet.eta i)).val
def targets (tree : Fin 2) : Bˣ := generator^((packet.alpha tree).val*packet.mu).val
def setup := s.setup (packet.powers generator) (generator^(-(Adapter.Mdoc.primeOrder : ℤ)))
  packet.masked (packet.targets generator)

end AdapterPacket

def readAdapter (s : BinaryPublic B shared maskBits adviceBits) (n : PrimePublic N shared)
    (primeField : fields .prime → N) (primeDecode : C → ℕ → N)
    (primeNonzero : C → Linear.TerminalSampling.Nonzero N)
    (convert : C → Fin 2 → Linear.TerminalSampling.Nonzero N)
    (advice : Advice → Option (Fin 2 → Fin adviceBits → Bool))
    (fallback : C) (point : Point) (past : Fin point.rank → C) : Option (AdapterPacket s n C) := do
  let prime ← ApplicationPrefix.readPrime n primeField primeDecode primeNonzero fallback point past
  let scale ← ApplicationPrefix.strictAnswer point past (ApplicationPrefix.rescalingIndex g)
  let conversion ← ApplicationPrefix.strictAnswer point past (ApplicationPrefix.conversionIndex g)
  let mu ← point.readAt (ApplicationPrefix.conversionIndex g) (fun block => block.2.mu.map primeField)
  let rawAdvice ← point.readAt g.binaryStart (fun block => block.2.advice)
  let masked ← advice rawAdvice
  some ⟨prime,(primeNonzero scale).val,mu,convert conversion,masked⟩

def readRescalePacket (s : BinaryPublic B shared maskBits adviceBits) (n : PrimePublic N shared)
    (primeField : fields .prime → N) (primeDecode : C → ℕ → N)
    (primeNonzero : C → Linear.TerminalSampling.Nonzero N)
    (fallback : C) (point : Point) (past : Fin point.rank → C) :
    Option (RescaleData N (Fin shared) n.Other (Selection.Pair B N s.Original n.Original)) := do
  let prime ← ApplicationPrefix.readPrime n primeField primeDecode primeNonzero fallback point past
  some {
    claim := prime.claim
    shared := fun w i => if s.sharedValues w.1 i then 1 else 0
    other := fun w i => primeValues s n w (.inl i)
    binaryMask := fun w => Handoff.binaryMask (s.mask w.1)
    primeMask := fun w => primeValues s n w (.inr ()) }

/-- The conversion target is already bound, while both conversion
challenges are still the explicit current answer. Masked advice is future
and is not read merely to populate an irrelevant packet field. -/
def readConversionPacket (s : BinaryPublic B shared maskBits adviceBits) (n : PrimePublic N shared)
    (primeField : fields .prime → N) (primeDecode : C → ℕ → N)
    (primeNonzero : C → Linear.TerminalSampling.Nonzero N)
    (fallback : C) (point : Point) (past : Fin point.rank → C) :
    Option (ConversionData Adapter.Mdoc.primeOrder (shared+maskBits)
      (Selection.Pair B N s.Original n.Original)) := do
  let prime ← ApplicationPrefix.readPrime n primeField primeDecode primeNonzero fallback point past
  let scale ← ApplicationPrefix.strictAnswer point past (ApplicationPrefix.rescalingIndex g)
  let mu ← point.readAt (ApplicationPrefix.conversionIndex g) (fun block => block.2.mu.map primeField)
  some {
    weights := Handoff.weights prime.claim.sharedWeights (primeNonzero scale).val
    values := fun w => Handoff.values (s.sharedValues w.1) (s.mask w.1)
    target := mu }

/-- A completed binary frontend before its packing challenge. It has no
packing response fields, which are not yet needed by this packet. -/
structure BinaryPacket (s : BinaryPublic B shared maskBits adviceBits)
    (n : PrimePublic N shared) (C : Type) (generator : Bˣ) where
  adapter : AdapterPacket s n C
  payload : Layered.Replay.Payload (adapter.setup generator).circuit
  answers : ℕ → C

namespace BinaryPacket
variable {s : BinaryPublic B shared maskBits adviceBits} {n : PrimePublic N shared} {generator : Bˣ}

def source (packet : BinaryPacket s n C generator) (decode : C → ℕ → B)
    (nonzero : C → Linear.TerminalSampling.Nonzero B) :
    LfzkV2.Packed.Statement (ZMod 2) B (Fin s.degree) (Fin s.words) s.Slot :=
  let setup := packet.adapter.setup generator
  let messages := FrontendReplay.read decode nonzero setup.circuit setup.plan packet.payload packet.answers
  let constraints := FrontendVerifier.constraints setup.circuit setup.plan packet.payload decode nonzero packet.answers
  s.packing.withSource s.packedIndex constraints.inputClaim setup.coordinate
    (fun i => setup.circuit.inputWeights messages 0 (s.inputIndex (.inl i))) setup.publicInputs
    (fun i => setup.circuit.inputWeights messages 0 (s.inputIndex (.inr i)))

end BinaryPacket

def readBinaryPacket (s : BinaryPublic B shared maskBits adviceBits) (n : PrimePublic N shared)
    (generator : Bˣ) (binaryField : fields .binary → B) (primeField : fields .prime → N)
    (primeDecode : C → ℕ → N) (primeNonzero : C → Linear.TerminalSampling.Nonzero N)
    (convert : C → Fin 2 → Linear.TerminalSampling.Nonzero N)
    (advice : Advice → Option (Fin 2 → Fin adviceBits → Bool))
    (fallback : C) (point : Point) (past : Fin point.rank → C) :
    Option (BinaryPacket s n C generator) := do
  let adapter ← readAdapter s n primeField primeDecode primeNonzero convert advice fallback point past
  let circuit := (adapter.setup generator).circuit
  if g.binaryStart+FrontendReplay.slots circuit ≤ point.rank then
    let payload ← ApplicationPrefix.Messages.read circuit
      (ApplicationPrefix.wire point .binary binaryField g.binaryStart)
    some ⟨adapter,payload,ApplicationPrefix.frontendTape point past fallback g.binaryStart (FrontendReplay.slots circuit)⟩
  else none

/-- U is bound before the packing challenge. Neither the challenge delta
nor the later scalar A is read while preparing this one-query test. -/
def readPackingPacket (s : BinaryPublic B shared maskBits adviceBits) (n : PrimePublic N shared)
    (generator : Bˣ) (hdegree : g.packingDegree = s.degree)
    (binaryField : fields .binary → B) (primeField : fields .prime → N)
    (decode : C → ℕ → B) (nonzero : C → Linear.TerminalSampling.Nonzero B)
    (primeDecode : C → ℕ → N) (primeNonzero : C → Linear.TerminalSampling.Nonzero N)
    (convert : C → Fin 2 → Linear.TerminalSampling.Nonzero N)
    (advice : Advice → Option (Fin 2 → Fin adviceBits → Bool))
    (fallback : C) (point : Point) (past : Fin point.rank → C) :
    Option (PackingData (ZMod 2) B (Fin s.degree) (Fin s.words) s.Slot
      (Selection.Pair B N s.Original n.Original)) := do
  let packet ← readBinaryPacket s n generator binaryField primeField primeDecode primeNonzero
    convert advice fallback point past
  let U ← point.readAt (ApplicationPrefix.packingIndex g) (fun block => block.2.packingU)
  some {
    source := packet.source decode nonzero
    values := binaryValues s n
    U := fun i => binaryField (U (Fin.cast hdegree.symm i)) }

def binaryViewOfPayload (s : BinaryPublic B shared maskBits adviceBits) (n : PrimePublic N shared)
    (generator : Bˣ) (packet : AdapterPacket s n C)
    (shape : FrontendSchedule.Plan B (packet.setup generator).circuit) (capacity : ℕ)
    (decode : C → ℕ → B) (nonzero : C → Linear.TerminalSampling.Nonzero B)
    (decoder : FrontendReplay.Decoder capacity decode nonzero) (hcapacity : shape.capacity ≤ capacity)
    (fallback : C) (payload : Layered.Replay.Payload (packet.setup generator).circuit) :
    FrontendView B s.Pad (Selection.Pair B N s.Original n.Original) Point C where
  data := {
    out := (packet.setup generator).out,input := (packet.setup generator).input
    circuit := (packet.setup generator).circuit,plan := (packet.setup generator).plan
    payload := fun _ => payload
    inputs := fun w => s.inputs (binaryValues s n w)
    pads := fun w i => binaryValues s n w (CellLayout.Binary.pad s.words s.degree s.pads i)
    decode := decode,nonzero := nonzero,start := g.binaryStart,fallback := fallback }
  capacity := capacity
  decoder := decoder
  coalesced := shape.coalesced
  fits := shape.fits_of_capacityFrom_le 0 capacity hcapacity

/-- Once conversion and masked advice are bound, the generated binary
circuit has a local view even though its packing response is still future.
Only its current message prefix is parsed. -/
def readBinaryView (s : BinaryPublic B shared maskBits adviceBits) (n : PrimePublic N shared)
    (generator : Bˣ) (capacity : ℕ)
    (shape : (packet : AdapterPacket s n C) → FrontendSchedule.Plan B (packet.setup generator).circuit)
    (decode : C → ℕ → B) (nonzero : C → Linear.TerminalSampling.Nonzero B)
    (decoder : FrontendReplay.Decoder capacity decode nonzero)
    (hcapacity : ∀ packet, (shape packet).capacity ≤ capacity)
    (binaryField : fields .binary → B) (primeField : fields .prime → N)
    (primeDecode : C → ℕ → N) (primeNonzero : C → Linear.TerminalSampling.Nonzero N)
    (convert : C → Fin 2 → Linear.TerminalSampling.Nonzero N)
    (advice : Advice → Option (Fin 2 → Fin adviceBits → Bool))
    (fallback : C) (point : Point) (past : Fin point.rank → C) :
    Option (FrontendView B s.Pad (Selection.Pair B N s.Original n.Original) Point C) := do
  if g.binaryStart ≤ point.rank then
    let packet ← readAdapter s n primeField primeDecode primeNonzero convert advice fallback point past
    let setup := packet.setup generator
    let payload ← PartialMessages.read setup.circuit
      (ApplicationPrefix.wire point .binary binaryField g.binaryStart) (point.rank-g.binaryStart)
    some (binaryViewOfPayload s n generator packet (shape packet) capacity decode nonzero decoder (hcapacity packet) fallback payload)
  else none

end Concrete

end LfzkV2.Current.ApplicationViews
