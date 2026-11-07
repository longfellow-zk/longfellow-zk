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

theorem fill_fill (body earlier terminal : Body g fields Advice (OpeningBody.Authentication g)) :
    fill (fill body earlier) terminal = fill body terminal := rfl

theorem fill_idempotent (body terminal : Body g fields Advice (OpeningBody.Authentication g)) :
    fill body (fill body terminal) = fill body terminal := rfl

/-- Replacing a commitment by its stored value leaves the complete body
unchanged. The same record fact is shared by real and simulated backends. -/
theorem commitment_eq (body : Body g fields Advice (OpeningBody.Authentication g)) (value : Digest)
    (same : body.commitment = value) : {body with commitment := value} = body := by
  cases body
  cases same
  rfl

end LfzkV2.Current.ZeroKnowledge.CompleteTerminal
