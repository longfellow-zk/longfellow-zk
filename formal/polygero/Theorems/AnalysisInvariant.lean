import polygero.Theorems.WireExtraction

/-! Hahn changes only the certified counting bound. The protocol, wire verifier,
message order and local decoder are shared. The conversion lemmas are defined alongside the extractor and error definitions.
These remaining equalities show that even changing Hahn certificates leaves the
transmitted protocol and recursive extractor unchanged.
-/

namespace RecursivePolygero.Protocol.HahnProfileProof
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {I : Instance F} {protocol : Protocol I}
variable {p₁ p₂ : HahnSystemCertificate I}

/-- Changing the packing certificate never changes the transcript extractor. -/
theorem runTranscript_independent (r₁ : protocol.HahnProfileProof p₁)
    (r₂ : protocol.HahnProfileProof p₂) :
    ∀ (σ : I.layer.Statement) (W : I.layer.Oracle) (transcript : protocol.chain.Transcript),
      r₁.runTranscript σ W transcript = r₂.runTranscript σ W transcript := by
  induction r₁ with
  | terminal p => cases r₂; intros; rfl
  | step p rest ih =>
    cases r₂ with
    | step p₂ rest₂ =>
      intro σ W transcript
      simp only [runTranscript, family]
      rw [ih rest₂]
      split <;> rfl

/-- A numerically improved certificate leaves witness extraction unchanged. -/
theorem extractWitness_independent (r₁ : protocol.HahnProfileProof p₁)
    (r₂ : protocol.HahnProfileProof p₂)
    (σ : I.layer.Statement) (W : I.layer.Oracle)
    (messages : Strategy protocol.chain) (coins : protocol.chain.Coins) :
    r₁.extractWitness σ W messages coins = r₂.extractWitness σ W messages coins := by
  unfold extractWitness extract extractTranscript
  by_cases h : executionVerify protocol.chain σ W messages coins = true
  · simp only [h, ↓reduceIte, Option.bind_some]
    rw [r₁.runTranscript_independent r₂]
    rfl
  · simp [h]

/-- The same invariance holds after expanding the paper's physical wire oracle. -/
theorem wireExtract_independent (r₁ : protocol.HahnProfileProof p₁)
    (r₂ : protocol.HahnProfileProof p₂) (masks : Bool)
    (σ : I.layer.Statement) (W : I.WireOracle masks)
    (messages : protocol.WireStrategy) (coins : protocol.chain.Coins) :
    r₁.wireExtract masks σ W messages coins = r₂.wireExtract masks σ W messages coins :=
  r₁.extractWitness_independent r₂ σ _ _ coins

end RecursivePolygero.Protocol.HahnProfileProof
