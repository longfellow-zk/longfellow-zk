import LfzkV2.Current.ApplicationCover
import LfzkV2.Current.BalancedDecoder
import LfzkV2.Current.SelectionReplay

/-! Query-local tests for the non-layered parts of the current application.
All data readers receive only the fixed preimage and its strict ancestors.
The candidate answer is explicit.  The tests below are the actual fingerprint,
row-batching, rescaling, conversion and packing predicates, with their existing
algebraic counts lifted to the full raw answer alphabet. -/
noncomputable section
namespace LfzkV2.Current.ApplicationOracle
open Finset WitnessSelection SumcheckV2 DualPacking.ArtinSchreier
open scoped Classical

variable {roles : List Role} {Key Block Link Body C Oracle B N IB IN : Type}
variable [Field B] [Field N] [Fintype B] [Fintype N] [DecidableEq B] [DecidableEq N]
  [Fintype IB] [Fintype IN]

local notation "Point" => Input roles Key Block Link Body
local notation "Pair" => Selection.Pair B N IB IN

/-- The concrete early-selection replay interface.  On an accepted path the
response reader is instantiated by the already-bound fingerprint response
prefix, not by a later mutable statement. -/
structure SelectionSource (roles : List Role) (Key Block Link Body C Oracle B N IB IN : Type)
    [Field B] [Field N] [DecidableEq B] [DecidableEq N] [Fintype IB] [Fintype IN] where
  lists : Key → Oracle → Finset (WitnessSelection.Candidate B IB) ×
    Finset (WitnessSelection.Candidate N IN)
  coins : C → Coins B IB × Coins N IN
  responses : Input roles Key Block Link Body → (B × B) × (N × N)
  oracle : (Input roles Key Block Link Body → Link × C) → Key → Oracle
  oracle_off : ∀ point H H', Bcs.TotalOracle.AgreeOff point H H' →
    oracle H point.context = oracle H' point.context

namespace SelectionSource
variable (S : SelectionSource roles Key Block Link Body C Oracle B N IB IN)

def selected (point : Point) (H : Point → Link × C) : Option Pair :=
  Selection.atPoint S.lists S.coins S.responses S.oracle point H

omit [Fintype B] [Fintype N] in
theorem selected_off (point : Point) (H H' : Point → Link × C)
    (h : Bcs.TotalOracle.AgreeOff point H H') : S.selected point H = S.selected point H' := by
  exact Selection.atPoint_off S.lists S.coins S.responses S.oracle S.oracle_off point H H' h

/-- This wrapper fixes the selected pair and strict-prefix data before
testing an explicit current answer.  The concrete tests below instantiate
`bad` with the existing algebraic predicates. -/
def test {D : Type} (read : (point : Point) → (Fin point.rank → C) → D)
    (bad : D → Pair → C → Prop) (point : Point) (H : Point → Link × C) (answer : C) : Prop :=
  ∃ w, S.selected point H = some w ∧ bad (read point (point.priorAnswers H)) w answer

omit [Fintype B] [Fintype N] in
theorem test_off {D : Type} (read : (point : Point) → (Fin point.rank → C) → D)
    (bad : D → Pair → C → Prop) (point : Point) (H H' : Point → Link × C)
    (h : Bcs.TotalOracle.AgreeOff point H H') (answer : C) :
    S.test read bad point H answer ↔ S.test read bad point H' answer := by
  unfold test
  rw [S.selected_off point H H' h, point.priorAnswers_off h]

def binarySelection (point : Point) (H : Point → Link × C) (answer : C) : Prop :=
  (S.coins answer).1 ∈ badCoins (S.lists point.context (S.oracle H point.context)).1

def primeSelection (point : Point) (H : Point → Link × C) (answer : C) : Prop :=
  (S.coins answer).2 ∈ badCoins (S.lists point.context (S.oracle H point.context)).2

omit [Fintype N] in
theorem binarySelection_off (point : Point) (H H' : Point → Link × C)
    (h : Bcs.TotalOracle.AgreeOff point H H') (answer : C) :
    S.binarySelection point H answer ↔ S.binarySelection point H' answer := by
  unfold binarySelection
  rw [S.oracle_off point H H' h]

omit [Fintype B] in
theorem primeSelection_off (point : Point) (H H' : Point → Link × C)
    (h : Bcs.TotalOracle.AgreeOff point H H') (answer : C) :
    S.primeSelection point H answer ↔ S.primeSelection point H' answer := by
  unfold primeSelection
  rw [S.oracle_off point H H' h]

omit [Fintype N] in
theorem binarySelection_card_mul_le [Fintype C] [Fintype (Coins B IB)]
    (decoder : BalancedDecoder C (Coins B IB))
    (hagrees : ∀ c, decoder.decode c = (S.coins c).1)
    (point : Point) (H : Point → Link × C) :
    (univ.filter (S.binarySelection point H)).card * Fintype.card B^2 ≤
      (S.lists point.context (S.oracle H point.context)).1.card.choose 2 * Fintype.card C := by
  let candidates := (S.lists point.context (S.oracle H point.context)).1
  have hcard : Fintype.card (Coins B IB) = Fintype.card B^Fintype.card IB *
      Fintype.card B^Fintype.card IB := by
    simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun] using
      Fintype.card_congr (show Coins B IB ≃
        Fin (Fintype.card (IB → B)) × Fin (Fintype.card (IB → B)) from
        Equiv.prodCongr (Fintype.equivFin (IB → B)) (Fintype.equivFin (IB → B)))
  have hlocal : (univ.filter fun a => a ∈ badCoins candidates).card * Fintype.card B^2 ≤
      candidates.card.choose 2 * Fintype.card (Coins B IB) := by
    simpa [hcard] using list_collision_card_mul_le candidates
  have h := decoder.bad_card_mul_le (fun a => a ∈ badCoins candidates)
    (candidates.card.choose 2) (Fintype.card B^2) (by
      convert! hlocal using 1
      congr 2
      ext a
      simp)
  convert h using 1
  congr 2
  ext c
  simp only [mem_filter]
  rw [hagrees]
  rfl

omit [Fintype B] in
theorem primeSelection_card_mul_le [Fintype C] [Fintype (Coins N IN)]
    (decoder : BalancedDecoder C (Coins N IN))
    (hagrees : ∀ c, decoder.decode c = (S.coins c).2)
    (point : Point) (H : Point → Link × C) :
    (univ.filter (S.primeSelection point H)).card * Fintype.card N^2 ≤
      (S.lists point.context (S.oracle H point.context)).2.card.choose 2 * Fintype.card C := by
  let candidates := (S.lists point.context (S.oracle H point.context)).2
  have hcard : Fintype.card (Coins N IN) = Fintype.card N^Fintype.card IN *
      Fintype.card N^Fintype.card IN := by
    simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun] using
      Fintype.card_congr (show Coins N IN ≃
        Fin (Fintype.card (IN → N)) × Fin (Fintype.card (IN → N)) from
        Equiv.prodCongr (Fintype.equivFin (IN → N)) (Fintype.equivFin (IN → N)))
  have hlocal : (univ.filter fun a => a ∈ badCoins candidates).card * Fintype.card N^2 ≤
      candidates.card.choose 2 * Fintype.card (Coins N IN) := by
    simpa [hcard] using list_collision_card_mul_le candidates
  have h := decoder.bad_card_mul_le (fun a => a ∈ badCoins candidates)
    (candidates.card.choose 2) (Fintype.card N^2) (by
      convert! hlocal using 1
      congr 2
      ext a
      simp)
  convert h using 1
  congr 2
  ext c
  simp only [mem_filter]
  rw [hagrees]
  rfl

end SelectionSource

variable {W Raw : Type} [Fintype Raw]

/-- An option-valued extractor selects at most one witness.  There is no
enumeration of possible witnesses and no candidate-list multiplier here. -/
theorem selected_card_mul_le (selected : Option W) (bad : W → Raw → Prop)
    (numerator denominator : ℕ)
    (hlocal : ∀ w, (univ.filter (bad w)).card * denominator ≤ numerator * Fintype.card Raw) :
    (univ.filter fun raw => ∃ w, selected = some w ∧ bad w raw).card * denominator ≤
      numerator * Fintype.card Raw := by
  cases selected with
  | none => simp
  | some w => simpa only [Option.some.injEq, exists_eq_left'] using hlocal w

variable {F Slot Shared Other I J KField : Type} [Field F] [Fintype F] [DecidableEq F]

structure BatchData (F Slot W : Type) [Field F] where
  rows : List (LinearRow Slot F)
  values : W → Slot → F

def BatchData.bad (d : BatchData F Slot W) (w : W) (rho : Fin d.rows.length → F) : Prop :=
  Prime.BatchBad (fun i => (d.rows.get i).eval (d.values w)) rho

theorem BatchData.bad_card_mul_le (d : BatchData F Slot W) (w : W)
    (decoder : BalancedDecoder Raw (Fin d.rows.length → F)) :
    (univ.filter fun raw => d.bad w (decoder.decode raw)).card * Fintype.card F ≤
      Fintype.card Raw := by
  have hlocal := Prime.batch_bad_card_mul_le (fun i => (d.rows.get i).eval (d.values w))
  simpa only [one_mul] using decoder.bad_card_mul_le (d.bad w) 1 (Fintype.card F)
    (by simpa [BatchData.bad] using hlocal)

/-- One actual prime-row packet and its matching ideal sampler. A finite
raw answer cannot support samplers for arbitrarily long unrelated row lists;
the decoder is therefore bundled with the rows that this query uses. -/
structure BatchPacket (F Slot W Raw : Type) [Field F] [Fintype F] [Fintype Raw] where
  data : BatchData F Slot W
  decoder : BalancedDecoder Raw (Fin data.rows.length → F)

namespace BatchPacket

def bad (packet : BatchPacket F Slot W Raw) (w : W) (answer : Raw) : Prop :=
  packet.data.bad w (packet.decoder.decode answer)

/-- Retarget only along equality of the actual decoded packet data. This
does not ask for a decoder on any additional row dimension. -/
def decoderAt (packet : BatchPacket F Slot W Raw) {data : BatchData F Slot W}
    (h : packet.data = data) : BalancedDecoder Raw (Fin data.rows.length → F) :=
  h ▸ packet.decoder

omit [DecidableEq F] in
theorem bad_eq (packet : BatchPacket F Slot W Raw) {data : BatchData F Slot W}
    (h : packet.data = data) (w : W) (answer : Raw) :
    packet.bad w answer = data.bad w ((packet.decoderAt h).decode answer) := by
  cases h
  rfl

theorem bad_card_mul_le (packet : BatchPacket F Slot W Raw) (w : W) :
    (univ.filter (packet.bad w)).card * Fintype.card F ≤ Fintype.card Raw :=
  packet.data.bad_card_mul_le w packet.decoder

end BatchPacket

structure RescaleData (F Shared Other W : Type) [Field F] where
  claim : Prime.Claim Shared Other F
  shared : W → Shared → F
  other : W → Other → F
  binaryMask : W → F
  primeMask : W → F

def RescaleData.bad [Fintype Shared] [Fintype Other]
    (d : RescaleData F Shared Other W) (w : W) (eta : Linear.TerminalSampling.Nonzero F) : Prop :=
  Prime.RescalingBad (d.claim.residual (d.shared w) (d.other w))
    (d.binaryMask w - d.primeMask w) eta.val

theorem RescaleData.bad_card_mul_le [Fintype Shared] [Fintype Other]
    (d : RescaleData F Shared Other W) (w : W)
    (decoder : BalancedDecoder Raw (Linear.TerminalSampling.Nonzero F)) :
    (univ.filter fun raw => d.bad w (decoder.decode raw)).card * (Fintype.card F-1) ≤
      Fintype.card Raw := by
  apply (decoder.bad_card_mul_le (d.bad w) 1 (Fintype.card F-1) ?_).trans_eq (one_mul _)
  simpa only [RescaleData.bad, Linear.TerminalSampling.nonzero_card, one_mul] using
    Nat.mul_le_mul_right (Fintype.card F-1)
      (Prime.rescaling_bad_card (d.claim.residual (d.shared w) (d.other w))
        (d.binaryMask w-d.primeMask w))

variable {p bits M K : ℕ} [Fact p.Prime]

structure ConversionData (p bits : ℕ) (W : Type) [Fact p.Prime] where
  weights : Fin bits → ZMod p
  values : W → Fin bits → Bool
  target : ZMod p

def ConversionData.bad (d : ConversionData p bits W) (M K : ℕ) (w : W)
    (alpha : Linear.TerminalSampling.Nonzero (ZMod p) ×
      Linear.TerminalSampling.Nonzero (ZMod p)) : Prop :=
  Adapter.residual d.weights (d.values w) d.target ≠ 0 ∧
    Adapter.Bad d.weights (d.values w) d.target M K alpha.1 ∧
    Adapter.Bad d.weights (d.values w) d.target M K alpha.2

theorem ConversionData.bad_card_mul_le (d : ConversionData p bits W) (w : W)
    (hM : 0 < M) (hbits : bits ≤ K)
    (decoder : BalancedDecoder Raw (Linear.TerminalSampling.Nonzero (ZMod p) ×
      Linear.TerminalSampling.Nonzero (ZMod p))) :
    (univ.filter fun raw => d.bad M K w (decoder.decode raw)).card * (p-1)^2 ≤
      (2*(K*p/M)+1)^2 * Fintype.card Raw := by
  apply decoder.bad_card_mul_le
  by_cases hfalse : Adapter.residual d.weights (d.values w) d.target ≠ 0
  · simpa [ConversionData.bad, hfalse, Fintype.card_prod,
      Linear.TerminalSampling.nonzero_card, ZMod.card, sq] using
      Nat.mul_le_mul_right ((p-1)*(p-1)) (Adapter.two_bad_card d.weights (d.values w) d.target hM hbits hfalse)
  · simp [ConversionData.bad, hfalse]

variable [Field KField] [Fintype KField] [Algebra KField F]
  [Fintype I] [DecidableEq I] [Fintype J]

structure PackingData (KField F I J Slot W : Type)
    [Field KField] [Fintype KField] [Field F] [Fintype F]
    [Algebra KField F] [Fintype I] [DecidableEq I] [Fintype J] where
  source : Packed.Statement KField F I J Slot
  values : W → Slot → F
  U : I → F

def PackingData.bad (d : PackingData KField F I J Slot W) (w : W) (delta : I → F) : Prop :=
  d.source.Bad (d.values w) d.U delta

theorem PackingData.bad_card_mul_le (d : PackingData KField F I J Slot W) (w : W)
    (decoder : BalancedDecoder Raw (I → F)) :
    (univ.filter fun raw => d.bad w (decoder.decode raw)).card * Fintype.card F ≤
      Fintype.card Raw := by
  apply (decoder.bad_card_mul_le (d.bad w) 1 (Fintype.card F) ?_).trans_eq (one_mul _)
  have hdim : 1 ≤ Fintype.card I := Fintype.card_pos_iff.mpr ⟨d.source.pivot⟩
  calc
    _ ≤ Fintype.card F^(Fintype.card I-1) * Fintype.card F :=
      Nat.mul_le_mul_right _ (d.source.bad_card_le (d.values w) d.U)
    _ = _ := by rw [← pow_succ, Nat.sub_add_cancel hdim]; simp

namespace SelectionSource
variable [Fintype C]
variable (S : SelectionSource roles Key Block Link Body C Oracle B N IB IN)

omit [Fintype B] [Fintype N] in
theorem test_card_mul_le {D : Type}
    (read : (point : Point) → (Fin point.rank → C) → D)
    (bad : D → Pair → C → Prop) (point : Point) (H : Point → Link × C)
    (numerator denominator : ℕ)
    (hlocal : ∀ d w, (univ.filter (bad d w)).card * denominator ≤
      numerator * Fintype.card C) :
    (univ.filter (S.test read bad point H)).card * denominator ≤
      numerator * Fintype.card C := by
  simpa only [test] using selected_card_mul_le (S.selected point H)
    (bad (read point (point.priorAnswers H))) numerator denominator
    (hlocal (read point (point.priorAnswers H)))

def rowBatching
    (read : (point : Point) → (Fin point.rank → C) → BatchPacket N Slot Pair C) :=
  S.test read (fun packet w answer => packet.bad w answer)

omit [Fintype B] in
theorem rowBatching_off
    (read : (point : Point) → (Fin point.rank → C) → BatchPacket N Slot Pair C)
    (point : Point) (H H' : Point → Link × C)
    (h : Bcs.TotalOracle.AgreeOff point H H') (answer : C) :
    S.rowBatching read point H answer ↔ S.rowBatching read point H' answer :=
  S.test_off read _ point H H' h answer

omit [Fintype B] in
theorem rowBatching_card_mul_le
    (read : (point : Point) → (Fin point.rank → C) → BatchPacket N Slot Pair C)
    (point : Point) (H : Point → Link × C) :
    (univ.filter (S.rowBatching read point H)).card * Fintype.card N ≤
      Fintype.card C := by
  simpa only [rowBatching, one_mul] using S.test_card_mul_le read
    (fun packet w answer => packet.bad w answer) point H 1 (Fintype.card N)
    (fun packet w => by simpa only [one_mul] using packet.bad_card_mul_le w)

def rescale [Fintype Shared] [Fintype Other]
    (read : (point : Point) → (Fin point.rank → C) → RescaleData N Shared Other Pair)
    (decoder : BalancedDecoder C (Linear.TerminalSampling.Nonzero N)) :=
  S.test read (fun d w answer => d.bad w (decoder.decode answer))

omit [Fintype B] in
theorem rescale_off [Fintype Shared] [Fintype Other]
    (read : (point : Point) → (Fin point.rank → C) → RescaleData N Shared Other Pair)
    (decoder : BalancedDecoder C (Linear.TerminalSampling.Nonzero N))
    (point : Point) (H H' : Point → Link × C)
    (h : Bcs.TotalOracle.AgreeOff point H H') (answer : C) :
    S.rescale read decoder point H answer ↔ S.rescale read decoder point H' answer :=
  S.test_off read _ point H H' h answer

omit [Fintype B] in
theorem rescale_card_mul_le [Fintype Shared] [Fintype Other]
    (read : (point : Point) → (Fin point.rank → C) → RescaleData N Shared Other Pair)
    (decoder : BalancedDecoder C (Linear.TerminalSampling.Nonzero N))
    (point : Point) (H : Point → Link × C) :
    (univ.filter (S.rescale read decoder point H)).card * (Fintype.card N-1) ≤
      Fintype.card C := by
  simpa only [rescale, one_mul] using S.test_card_mul_le read
    (fun d w answer => d.bad w (decoder.decode answer)) point H 1 (Fintype.card N-1)
    (fun d w => by simpa only [one_mul] using d.bad_card_mul_le w decoder)

def conversion
    (read : (point : Point) → (Fin point.rank → C) → ConversionData p bits Pair)
    (decoder : BalancedDecoder C (Linear.TerminalSampling.Nonzero (ZMod p) ×
      Linear.TerminalSampling.Nonzero (ZMod p))) (M K : ℕ) :=
  S.test read (fun d w answer => d.bad M K w (decoder.decode answer))

omit [Fintype B] [Fintype N] in
theorem conversion_off
    (read : (point : Point) → (Fin point.rank → C) → ConversionData p bits Pair)
    (decoder : BalancedDecoder C (Linear.TerminalSampling.Nonzero (ZMod p) ×
      Linear.TerminalSampling.Nonzero (ZMod p)))
    (point : Point) (H H' : Point → Link × C)
    (h : Bcs.TotalOracle.AgreeOff point H H') (answer : C) :
    S.conversion read decoder M K point H answer ↔ S.conversion read decoder M K point H' answer :=
  S.test_off read _ point H H' h answer

omit [Fintype B] [Fintype N] in
theorem conversion_card_mul_le
    (read : (point : Point) → (Fin point.rank → C) → ConversionData p bits Pair)
    (decoder : BalancedDecoder C (Linear.TerminalSampling.Nonzero (ZMod p) ×
      Linear.TerminalSampling.Nonzero (ZMod p)))
    (hM : 0 < M) (hbits : bits ≤ K) (point : Point) (H : Point → Link × C) :
    (univ.filter (S.conversion read decoder M K point H)).card * (p-1)^2 ≤
      (2*(K*p/M)+1)^2 * Fintype.card C := by
  exact S.test_card_mul_le read (fun d w answer => d.bad M K w (decoder.decode answer))
    point H _ _ (fun d w => d.bad_card_mul_le w hM hbits decoder)

variable [Algebra KField B]

def packing
    (read : (point : Point) → (Fin point.rank → C) → PackingData KField B I J Slot Pair)
    (decoder : BalancedDecoder C (I → B)) :=
  S.test read (fun d w answer => d.bad w (decoder.decode answer))

omit [Fintype N] in
theorem packing_off
    (read : (point : Point) → (Fin point.rank → C) → PackingData KField B I J Slot Pair)
    (decoder : BalancedDecoder C (I → B))
    (point : Point) (H H' : Point → Link × C)
    (h : Bcs.TotalOracle.AgreeOff point H H') (answer : C) :
    S.packing read decoder point H answer ↔ S.packing read decoder point H' answer :=
  S.test_off read _ point H H' h answer

omit [Fintype N] in
theorem packing_card_mul_le
    (read : (point : Point) → (Fin point.rank → C) → PackingData KField B I J Slot Pair)
    (decoder : BalancedDecoder C (I → B)) (point : Point) (H : Point → Link × C) :
    (univ.filter (S.packing read decoder point H)).card * Fintype.card B ≤
      Fintype.card C := by
  simpa only [packing, one_mul] using S.test_card_mul_le read
    (fun d w answer => d.bad w (decoder.decode answer)) point H 1 (Fintype.card B)
    (fun d w => by simpa only [one_mul] using d.bad_card_mul_le w decoder)

end SelectionSource
end LfzkV2.Current.ApplicationOracle

namespace LfzkV2.Current.Application.System
open ApplicationOracle SumcheckV2

variable {B I J SlotB PadB Other PadN IB IN CB CN : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
  [Fintype I] [DecidableEq I] [Fintype J] [Fintype Other]
  [Fintype IB] [Fintype IN] [DecidableEq IB] [DecidableEq IN]
variable {p shared maskBits M K : ℕ} [Fact p.Prime]
variable (A : System B I J SlotB PadB Other PadN IB IN CB CN p shared maskBits M K)

/-- These are the exact local algebraic data obtained from the application
compiler.  Query-prefix readers are checked against these records along the
accepted replay; the records themselves contain no oracle access. -/
def batchData : BatchData (ZMod p) (Fin shared ⊕ Other) A.Pair where
  rows := A.prime.rows
  values := A.fullPrimeRead

def rescaleData : RescaleData (ZMod p) (Fin shared) Other A.Pair where
  claim := A.claim
  shared := fun w i => if A.sharedValues w.1 i then 1 else 0
  other := A.other
  binaryMask := fun w => Handoff.binaryMask (A.mask w.1)
  primeMask := A.primeMask

def conversionData : ConversionData p (shared+maskBits) A.Pair where
  weights := Handoff.weights A.claim.sharedWeights A.eta
  values := fun w => Handoff.values (A.sharedValues w.1) (A.mask w.1)
  target := A.mu

def packingData : PackingData (ZMod 2) B I J SlotB A.Pair where
  source := A.binary.source
  values := A.binaryRead
  U := A.binary.U

/-- Both adapter challenges are one sampled pair.  This representation is
identical to the two-coordinate function used by the algebraic handoff. -/
theorem conversionData_bad_iff (w : A.Pair) :
    A.conversionData.bad M K w (A.alpha 0,A.alpha 1) ↔
      Handoff.ConversionBad A.claim.sharedWeights A.eta A.mu
        (A.sharedValues w.1) (A.mask w.1) M K A.alpha := by
  constructor
  · rintro ⟨hf,h0,h1⟩
    refine ⟨hf,fun j => ?_⟩
    fin_cases j
    · exact h0
    · exact h1
  · rintro ⟨hf,h⟩
    exact ⟨hf,h 0,h 1⟩

end LfzkV2.Current.Application.System
