import LfzkV2.Current.RuntimeSource
import LfzkV2.Current.ApplicationViewReplay

/-! Adaptive public values with fixed circuit topology. Early query contexts
contain only data already bound at that point. Prime public values are read
from the prime-start block, before its challenge, rather than being added
retroactively to the fingerprint context. -/
noncomputable section
namespace LfzkV2.Current.RuntimeAdaptive
open Application ApplicationSetup ApplicationViews ApplicationOracle RecursivePolygero SumcheckV2
open scoped Classical

section FamilyReplay
variable {g : Geometry} {fields : Fields} {Advice Auth Key Block C Request : Type}

/-- The adversary may choose its public request together with its proof.
Only the encoding of that chosen request determines the actual replay. -/
structure Output where
  request : Request
  proof : Replay.Output g fields Advice Auth

instance [Fintype Request] [Fintype (Replay.Output g fields Advice Auth)] :
    Fintype (Output (g := g) (fields := fields) (Advice := Advice) (Auth := Auth) (Request := Request)) := by
  apply Fintype.ofInjective (fun output => (output.request,output.proof))
  intro first second h
  cases first
  cases second
  cases h
  rfl

variable (encodings : Request → Replay.Encoding g fields Advice Auth Key Block C)
variable (initialLink : Digest)

/-- A family shares one query domain and one public topology. Public data
is written at the same boundaries as in the selected member's runtime. -/
def chain : TranscriptV2.Chain (Replay.Point g fields Advice Auth Key Block) Digest C
    (Output (g := g) (fields := fields) (Advice := Advice) (Auth := Auth) (Request := Request))
    g.roles.length where
  parent := Input.parent
  claimed := Input.claimed initialLink
  State := Replay.State g fields Advice Auth Key Block C
  rank := Input.rank
  initial output := (encodings output.request).initial output.proof
  input := Replay.State.point
  advance output _ state answer := (encodings output.request).advance output.proof state answer
  initial_rank output := (encodings output.request).stateAt_rank output.proof 0 (Nat.zero_le _)
    ((encodings output.request).context output.proof) Fin.elim0
  advance_rank output := (encodings output.request).advance_rank output.proof
  advance_parent output := (encodings output.request).advance_parent output.proof
  advance_link output i state answer h :=
    (encodings output.request).advance_link output.proof i state answer h initialLink
  finalSeal output := output.proof.finalSeal

/-- Selecting a member is not a union bound. This identity merely locates
its actual path in the one common-domain adaptive experiment. -/
theorem replay_eq (output : Output (g := g) (fields := fields) (Advice := Advice)
    (Auth := Auth) (Request := Request))
    (H : Replay.Point g fields Advice Auth Key Block → Digest × C) (n : ℕ) :
    (chain encodings initialLink).replay output H n =
      ((encodings output.request).chain initialLink).replay output.proof H n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [TranscriptV2.Chain.replay]
      split_ifs
      · rw [ih]
        rfl
      · exact ih

theorem point_eq (output : Output (g := g) (fields := fields) (Advice := Advice)
    (Auth := Auth) (Request := Request))
    (H : Replay.Point g fields Advice Auth Key Block → Digest × C) (n : ℕ) :
    (chain encodings initialLink).point output H n =
      ((encodings output.request).chain initialLink).point output.proof H n := by
  exact congrArg Replay.State.point (replay_eq encodings initialLink output H n)

end FamilyReplay

section PublicValues
variable {N : Type} [Field N] {shared : ℕ}

def primeWithInputs (prime : PrimePublic N shared) (inputs : Fin prime.nPublic → N) :
    PrimePublic N shared := { prime with publicInputs := inputs }

@[simp] theorem primeWithInputs_circuit (prime : PrimePublic N shared) (inputs : Fin prime.nPublic → N) :
    (primeWithInputs prime inputs).circuit = prime.circuit := rfl

@[simp] theorem primeWithInputs_pads (prime : PrimePublic N shared) (inputs : Fin prime.nPublic → N) :
    (primeWithInputs prime inputs).pads = prime.pads := rfl

section Binary
variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable {maskBits adviceBits : ℕ}

def binaryWithBits (binary : BinaryPublic B shared maskBits adviceBits)
    (bits : Fin binary.nPublic → Bool) : BinaryPublic B shared maskBits adviceBits :=
  { binary with publicBits := bits }

omit [Fintype B] [DecidableEq B] in
@[simp] theorem binaryWithBits_cells (binary : BinaryPublic B shared maskBits adviceBits)
    (bits : Fin binary.nPublic → Bool) : (binaryWithBits binary bits).cells = binary.cells := rfl

end Binary
end PublicValues

/-- Where the signature circuit's public inputs are read from a bound
history: the node at `index`, which is bound no later than the prime
frontend's first boundary, decoded by `read`. A format whose statement
carries every public input reads them from the first node. -/
structure PublicReader (g : Geometry) (Base X : Type) where
  index : ℕ
  index_le : index ≤ g.primeStart
  read : Base → Option X

section PrimeViews
variable {g : Geometry} {fields : Fields} {Advice Auth Key Base C B Oracle : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B] [Fintype C]
variable {shared maskBits adviceBits : ℕ}
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable (binary : BinaryPublic B shared maskBits adviceBits) (prime : PrimePublic N shared)
local notation "Point" => Replay.Point g fields Advice Auth Key (Base × ProtocolWrites.Fresh g fields Advice)

/-- Public prime inputs become available exactly when that block is bound.
Reading this value does not consult the candidate answer at the current query. -/
def primePublic (decodePublic : PublicReader g Base (Fin prime.nPublic → N)) (point : Point) :
    Option (Fin prime.nPublic → N) :=
  point.readAt decodePublic.index (fun block => decodePublic.read block.1)

variable (shape : FrontendSchedule.Plan N prime.circuit) (capacity : ℕ)
variable (decode : C → ℕ → N) (nonzero : C → Linear.TerminalSampling.Nonzero N)
variable (decoder : FrontendReplay.Decoder capacity decode nonzero)
variable (fits : shape.capacity ≤ capacity) (field : fields .prime → N) (fallback : C)
variable (decodePublic : PublicReader g Base (Fin prime.nPublic → N))

/-- The circuit, addresses, samplers and capacities remain public constants.
Only the public field values come from the actual current-or-earlier prefix. -/
def primeRead (point : Point) (past : Fin point.rank → C) :
    Option (FrontendView N (Fin prime.pads) (Selection.Pair B N binary.Original prime.Original) Point C) := do
  let publicInputs ← primePublic prime decodePublic point
  readPrimeView binary (primeWithInputs prime publicInputs) shape capacity decode nonzero decoder fits
    field fallback point past

variable (S : SelectionSource g.roles Key (Base × ProtocolWrites.Fresh g fields Advice) Digest
  (Body g fields Advice Auth) C Oracle B N binary.Original prime.Original)

omit [Fintype B] in
/-- The same local sumcheck bound applies after an adversary chooses its
public values. The charged query fixes those values through its preimage. -/
theorem primeCharge_sum (point : Point) (H : Point → Digest × C) :
    (∑ answer, frontendCharge S
      (primeRead binary prime shape capacity decode nonzero decoder fits field fallback decodePublic)
      point H answer) ≤ Fintype.card (Digest × C)*(2/((Fintype.card N-1 : ℕ):ℚ)) :=
  frontendCharge_sum S _ point H

variable (e : Replay.Encoding g fields Advice Auth Key (Base × ProtocolWrites.Fresh g fields Advice) C)

omit [Fintype C] in
/-- Once bound, the same public values are recovered at every later prefix.
In particular they need not occur in the earlier fingerprint query at all. -/
theorem primePublic_replay_eq (initialLink : Digest) (proof : Replay.Output g fields Advice Auth)
    (H : Point → Digest × C) (n m : ℕ) (hn : n ≤ g.roles.length) (hm : m ≤ g.roles.length)
    (hstart : g.primeStart < g.roles.length) (hpn : g.primeStart ≤ n) (hpm : g.primeStart ≤ m) :
    primePublic prime decodePublic ((e.chain initialLink).point proof H n) =
      primePublic prime decodePublic ((e.chain initialLink).point proof H m) :=
  ApplicationViewReplay.readAt_replay_eq e initialLink proof H (fun block => decodePublic.read block.1)
    n m decodePublic.index hn hm (lt_of_le_of_lt decodePublic.index_le hstart)
    (decodePublic.index_le.trans hpn) (decodePublic.index_le.trans hpm)

end PrimeViews
section ApplicationReader
variable {g : Geometry} {fields : Fields} {Advice Base Key C B Salt : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable {shared maskBits adviceBits k s n t : ℕ}
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable (binary : BinaryPublic B shared maskBits adviceBits) (prime : PrimePublic N shared)
variable (P : FieldBackend B k s n t) (R : FieldBackend N k s n t)
variable (cfg : RuntimeVerifier.Public (g := g) binary prime P R (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key) (C := C) (Salt := Salt))
variable (hashPublic : Key → Option (Fin binary.nPublic → Bool))
variable (decodePublic : PublicReader g Base (Fin prime.nPublic → N))
local notation "Point" => RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key)
local notation "System" => RuntimeVerifier.System binary prime (C := C)
local notation "First" => RuntimeVerifier.first binary prime P R cfg
local notation "Second" => RuntimeVerifier.second binary prime P R cfg

/-- Both public vectors are obtained from bound data. No complete public
request is added to a query that has not yet written it. The application
compiler remains the concrete checked constructor used by the fixed reader. -/
def application (point : Point) (past : Fin point.rank → C) : Option System := do
  let bits ← hashPublic point.context
  let inputs ← primePublic prime decodePublic point
  ApplicationPrefix.decodeChecked (binaryWithBits binary bits) (primeWithInputs prime inputs)
    cfg.card cfg.polynomialX cfg.quotientBound cfg.packingDegree cfg.binaryField cfg.primeField
    cfg.binaryDecode cfg.binaryNonzero cfg.primeDecode cfg.primeNonzero cfg.conversion cfg.advice
    cfg.fallback point past

/-- Successful adaptive reconstruction exposes actual parsed public values
and the same checked frontend/adapter constructor; it is not a certificate. -/
theorem application_spec (point : Point) (past : Fin point.rank → C) (A : System)
    (h : application binary prime P R cfg hashPublic decodePublic point past = some A) :
    ∃ (bits : Fin binary.nPublic → Bool) (inputs : Fin prime.nPublic → N),
      hashPublic point.context = some bits ∧ primePublic prime decodePublic point = some inputs ∧
      ApplicationPrefix.decodeChecked (binaryWithBits binary bits) (primeWithInputs prime inputs)
        cfg.card cfg.polynomialX cfg.quotientBound cfg.packingDegree cfg.binaryField cfg.primeField
        cfg.binaryDecode cfg.binaryNonzero cfg.primeDecode cfg.primeNonzero cfg.conversion cfg.advice
        cfg.fallback point past = some A := by
  simp only [application,Option.bind_eq_bind,Option.bind_eq_some_iff] at h
  obtain ⟨bits,hbits,inputs,hinputs,hread⟩ := h
  exact ⟨bits,inputs,hbits,hinputs,hread⟩

/-- The one global adaptive backend statement depends only on its bound
preimage and strict earlier answers. Its physical maps and equation order are
constructed by the same numerical checks as the fixed runtime decoder. -/
def statementAt (point : Point) (past : Fin point.rank → C) :
    Option (Σ A : System, StatementData A First Second) := do
  let A ← application binary prime P R cfg hashPublic decodePublic point past
  let layout ← StatementCompiler.addresses P R binary.cells prime.remaining prime.pads
  let fingerprint ← ApplicationPrefix.strictAnswer point past 0
  let targets ← point.readAt g.primeStart (fun block => block.2.fingerprints)
  let data ← StatementCompiler.compile P R A layout cfg.countBinary cfg.countPrime
    (cfg.fingerprintBinary fingerprint) (cfg.fingerprintPrime fingerprint)
    (cfg.binaryField targets.1.1,cfg.binaryField targets.1.2)
    (cfg.primeField targets.2.1,cfg.primeField targets.2.2)
  pure ⟨A,data⟩

end ApplicationReader
end LfzkV2.Current.RuntimeAdaptive
