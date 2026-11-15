import LfzkV2.Current.WireBlocks
import LfzkV2.Current.PublicRequest
import LfzkV2.Current.RuntimeAdaptiveVerifier

/-! The request and output types of the deployed format, named by its
public shape alone. -/
namespace LfzkV2.Current.CanonicalRequest

variable {g : Geometry} {fields : Fields} {Advice : Type}

/-- The public request a proof answers: the session, the hash circuit's
public bits and the signature circuit's public inputs. -/
abbrev Request (shape : WireBlocks.Shape g fields) (publicCount : ℕ) :=
  PublicRequest publicCount shape.primePublic (fields .prime)

abbrev Output := Replay.Output g fields Advice (OpeningBody.Authentication g)

end LfzkV2.Current.CanonicalRequest

namespace LfzkV2.Current.CanonicalRuntime
variable {g : Geometry} {fields : Fields} {Advice B : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B] {shared maskBits adviceBits : ℕ}

/-- Runtime outputs for requests of the deployed format, named by its
public shape alone; equal to `FormatOutput binary fmt` for the deployed format. -/
abbrev Output (binary : ApplicationSetup.BinaryPublic B shared maskBits adviceBits)
    (shape : WireBlocks.Shape g fields) :=
  RuntimeAdaptiveVerifier.Output (g := g) (fields := fields) (Advice := Advice)
    (Request := CanonicalRequest.Request shape binary.nPublic)

end LfzkV2.Current.CanonicalRuntime
