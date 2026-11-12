import LfzkV2.Current.RuntimeAdaptiveVerifier

/-! Public-vector readback identifies the application checked on an accepted
path with the caller's request. The algebraic system is still reconstructed
by the runtime decoder; it is never supplied as a correctness certificate. -/
noncomputable section
namespace LfzkV2.Current.RequestedApplication
open Application ApplicationSetup ApplicationViews RuntimeAdaptive
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice Base Key C B Salt : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable {shared maskBits adviceBits k s n t : ℕ}
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable (binary : BinaryPublic B shared maskBits adviceBits) (prime : PrimePublic N shared)
variable (P : FieldBackend B k s n t)
variable (R : FieldBackend N k s n t)
variable (cfg : RuntimeVerifier.Public (g := g) binary prime P R (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key) (C := C) (Salt := Salt))
variable (hashPublic : Key → Option (Fin binary.nPublic → Bool))
variable (decodePublic : Base → Option (Fin prime.nPublic → N))
local notation "Point" => RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key)
local notation "System" => RuntimeVerifier.System binary prime (C := C)

/-- Once both actual prefix readers recover the request, the adaptive
application reader is exactly the ordinary constructor for those values. -/
theorem application_eq (point : Point) (past : Fin point.rank → C)
    (bits : Fin binary.nPublic → Bool) (inputs : Fin prime.nPublic → N)
    (hbits : hashPublic point.context = some bits)
    (hinputs : RuntimeAdaptive.primePublic prime decodePublic point = some inputs) :
    RuntimeAdaptive.application binary prime P R cfg hashPublic decodePublic point past =
      ApplicationPrefix.decodeChecked (binaryWithBits binary bits) (primeWithInputs prime inputs)
        cfg.card cfg.generator cfg.quotientBound cfg.packingDegree cfg.binaryField cfg.primeField
        cfg.binaryDecode cfg.binaryNonzero cfg.primeDecode cfg.primeNonzero cfg.conversion cfg.advice
        cfg.fallback point past := by
  simp only [RuntimeAdaptive.application,Option.bind_eq_bind,hbits,hinputs,Option.bind_some]

/-- The successful checked constructor preserves the requested public
vectors in both circuit input arrays. In particular the prime shared values
come from the same selected binary witness, not a second committed copy. -/
theorem checked_true
    (bits : Fin binary.nPublic → Bool) (inputs : Fin prime.nPublic → N)
    (nd : PrimeData (primeWithInputs prime inputs) C)
    (bd : BinaryData (binaryWithBits binary bits) nd (cfg.generator^Adapter.Mdoc.generatorExponent))
    (A : System)
    (h : ApplicationSetup.decodeChecked (binaryWithBits binary bits) (primeWithInputs prime inputs)
      nd cfg.card cfg.generator cfg.quotientBound bd = some A)
    (w : Selection.Pair B N binary.Original prime.Original) (htrue : A.True w) :
    bd.setup.circuit.Satisfies ((binaryWithBits binary bits).inputs
      (binaryValues (binaryWithBits binary bits) (primeWithInputs prime inputs) w)) ∧
    prime.circuit.Satisfies
      (primeInputs (binaryWithBits binary bits) (primeWithInputs prime inputs) w) := by
  unfold ApplicationSetup.decodeChecked at h
  split at h
  · unfold ApplicationSetup.decode at h
    split at h
    · cases Option.some.inj h
      exact htrue
    · contradiction
  · contradiction

/-- The extracted pair satisfies the two circuits at the requested public
values. Generated adapter coefficients are those reconstructed from this
very prefix and its preceding answers. No alternate witness is selected. -/
theorem true_at_request (point : Point) (past : Fin point.rank → C)
    (bits : Fin binary.nPublic → Bool) (inputs : Fin prime.nPublic → N)
    (hbits : hashPublic point.context = some bits)
    (hinputs : RuntimeAdaptive.primePublic prime decodePublic point = some inputs)
    (A : System)
    (hA : RuntimeAdaptive.application binary prime P R cfg hashPublic decodePublic point past = some A)
    (w : Selection.Pair B N binary.Original prime.Original) (htrue : A.True w) :
    ∃ (nd : PrimeData (primeWithInputs prime inputs) C)
      (bd : BinaryData (binaryWithBits binary bits) nd (cfg.generator^Adapter.Mdoc.generatorExponent)),
      ApplicationPrefix.readPrime (primeWithInputs prime inputs) cfg.primeField cfg.primeDecode
        cfg.primeNonzero cfg.fallback point past = some nd ∧
      ApplicationPrefix.readBinary (binaryWithBits binary bits) nd
        (cfg.generator^Adapter.Mdoc.generatorExponent) cfg.packingDegree cfg.binaryField cfg.primeField
        cfg.binaryDecode cfg.binaryNonzero cfg.primeNonzero cfg.conversion cfg.advice cfg.fallback
        point past = some bd ∧
      bd.setup.circuit.Satisfies ((binaryWithBits binary bits).inputs
        (binaryValues (binaryWithBits binary bits) (primeWithInputs prime inputs) w)) ∧
      prime.circuit.Satisfies
        (primeInputs (binaryWithBits binary bits) (primeWithInputs prime inputs) w) := by
  rw [application_eq binary prime P R cfg hashPublic decodePublic point past bits inputs hbits hinputs] at hA
  obtain ⟨nd,bd,hprime,hbinary,hchecked⟩ := ApplicationPrefix.decodeChecked_spec
    (binaryWithBits binary bits) (primeWithInputs prime inputs) cfg.card cfg.generator cfg.quotientBound
    cfg.packingDegree cfg.binaryField cfg.primeField cfg.binaryDecode cfg.binaryNonzero
    cfg.primeDecode cfg.primeNonzero cfg.conversion cfg.advice cfg.fallback point past A hA
  exact ⟨nd,bd,hprime,hbinary,checked_true binary prime P R cfg bits inputs nd bd A hchecked w htrue⟩

end LfzkV2.Current.RequestedApplication
