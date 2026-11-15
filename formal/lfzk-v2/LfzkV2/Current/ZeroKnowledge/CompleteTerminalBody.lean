import LfzkV2.Current.OpeningBody

/-! Terminal replacement changes only backend payloads, opened rows and
Merkle authentication. These record identities do not depend on an oracle,
transcript replay, or a circuit execution. -/
namespace LfzkV2.Current.ZeroKnowledge.CompleteTerminal
variable {g : Geometry} {fields : Fields} {Advice : Type}

def fill (body terminal : Body g fields Advice (OpeningBody.Authentication g)) :=
  { body with binaryBackend := terminal.binaryBackend
              primeBackend := terminal.primeBackend
              authentication := terminal.authentication }

end LfzkV2.Current.ZeroKnowledge.CompleteTerminal
