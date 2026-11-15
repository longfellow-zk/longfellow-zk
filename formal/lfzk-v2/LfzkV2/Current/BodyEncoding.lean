import LfzkV2.Current.Replay

/-! A replay encoding computed from the proof body alone, so that the final
seal cannot reach any ordinary boundary. -/
namespace LfzkV2.Current.ProofBodyReplay
section Current
variable {g : Geometry} {fields : Fields} {Advice Authentication Context Block C : Type}

/-- Encoding from the public body has no access to the future final seal.
This is a constructor, not a supplied independence or privacy certificate. -/
structure BodyEncoding where
  context : Body g fields Advice Authentication → Context
  block : Body g fields Advice Authentication →
    (i : Fin g.roles.length) → (Fin i.val → C) → Block

def BodyEncoding.encoding (e : BodyEncoding (g := g) (fields := fields)
    (Advice := Advice) (Authentication := Authentication) (Context := Context)
    (Block := Block) (C := C)) : Replay.Encoding g fields Advice Authentication Context Block C where
  context proof := e.context proof.body
  block proof := e.block proof.body

variable (e : BodyEncoding (g := g) (fields := fields) (Advice := Advice)
  (Authentication := Authentication) (Context := Context) (Block := Block) (C := C))

theorem replay_same_body (initial : Digest)
    (first second : Proof g fields Advice Authentication)
    (same : first.body = second.body)
    (H : Replay.Point g fields Advice Authentication Context Block → Digest × C) (index : ℕ) :
    (e.encoding.chain initial).replay first H index =
      (e.encoding.chain initial).replay second H index := by
  rcases first with ⟨body,firstSeal⟩
  rcases second with ⟨otherBody,secondSeal⟩
  cases same
  induction index with
  | zero => rfl
  | succ index ih =>
      by_cases inside : index < g.roles.length
      · simp only [TranscriptV2.Chain.replay, dif_pos inside]
        rw [ih]
        generalize (e.encoding.chain initial).replay ⟨body,secondSeal⟩ H index = state
        rcases state with ⟨point,answers⟩
        cases point <;> rfl
      · simpa only [TranscriptV2.Chain.replay, dif_neg inside] using ih


end Current
end LfzkV2.Current.ProofBodyReplay
