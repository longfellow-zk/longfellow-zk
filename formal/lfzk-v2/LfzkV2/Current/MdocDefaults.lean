import LfzkV2.Current.MdocRuntime

/-! A fixed value for the rejected-parse branch of the finite proof-output
experiment. It is not an accepting proof or a verifier fallback: the event
separately requires successful complete-proof parsing before verification. -/
namespace LfzkV2.Current.MdocDefaults

private instance {B : Type} [Zero B] (side : Side) : Zero (MdocRuntime.fields B side) := by
  cases side <;> dsimp only [MdocRuntime.fields,MdocRuntime.Prime] <;> infer_instance

def digest : Digest := fun _ => 0

def layer {F : Type} [Zero F] (rounds : ℕ) : LayerPayload F rounds :=
  ⟨fun _ => (0,0),0,(0,0)⟩

def response {F : Type} [Zero F] (g : Geometry) : Response g F :=
  ⟨fun _ => 0,fun _ => 0⟩

def packing {F : Type} [Zero F] (degree : ℕ) : PackingPayload F degree := by
  by_cases h : degree = 1
  · exact (show PackingPayload F degree from h ▸ ())
  · exact (show PackingPayload F degree from by
      rw [PackingPayload,if_neg h]
      exact (fun _ => 0,0))

def authentication (g : Geometry) : OpeningBody.Authentication g where
  context := digest
  nonce := fun _ _ => 0
  frontierLength := ⟨0,Nat.zero_lt_succ _⟩
  frontier := Fin.elim0

/-- The malformed-output normalizer has no caller-chosen default proof.
All scalar cells, authentication data and the final seal are fixed zero. -/
def proof (g : Geometry) (B : Type) [Zero B] :
    Proof g (MdocRuntime.fields B) MdocAdvice.Value (OpeningBody.Authentication g) where
  body := {
    commitment := digest
    fingerprints := ((0,0),(0,0))
    mu := 0
    advice := 0
    binary := fun i => layer (g.binary.stages.get i).rounds
    prime := fun i => layer (g.prime.stages.get i).rounds
    packing := packing g.packingDegree
    binaryBackend := ⟨response g,fun _ _ => 0⟩
    primeBackend := ⟨response g,fun _ _ => 0⟩
    authentication := authentication g }
  finalSeal := digest

@[simp] theorem proof_finalSeal (g : Geometry) (B : Type) [Zero B] :
    (proof g B).finalSeal = digest := rfl

@[simp] theorem proof_frontierLength (g : Geometry) (B : Type) [Zero B] :
    (proof g B).body.authentication.frontierLength.val = 0 := rfl

end LfzkV2.Current.MdocDefaults
