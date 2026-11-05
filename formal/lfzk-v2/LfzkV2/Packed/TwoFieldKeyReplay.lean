import LfzkV2.Packed.TwoFieldReplay
import Bcs.VerifierQuery
import Merkle.TwoOracle

/-! Raw proofs carry messages and tags, while the verifier recomputes the
shared MAC multiplier after both roots. This replay derives the annotation
used by the fixed-input transcript model. -/

namespace LfzkV2.Packed.TwoFieldReplay

open RecursivePolygero Bcs.TotalOracle Merkle.RandomOracle

variable {F₁ F₂ Key C Public Out Enc D : Type}
variable [Field F₁] [Fintype F₁] [DecidableEq F₁]
variable [Field F₂] [Fintype F₂] [DecidableEq F₂] [Fintype C]
variable {out₁ input₁ out₂ input₂ N tA TM : ℕ}
variable {circuit₁ : Native.Circuit F₁ out₁ input₁} {I₁ : Instance F₁}
variable {circuit₂ : Native.Circuit F₂ out₂ input₂} {I₂ : Instance F₂}
variable (S₁ : CompiledSide F₁ C (Context Key C Public) circuit₁ I₁)
variable (S₂ : CompiledSide F₂ C S₁.Selected circuit₂ I₂)

/-- The direct side's unused scalar annotation is set to zero by its codec.
Allowing it here is a conservative extension of the raw verifier model. -/
structure RawProof where
  key : Key
  publicData : Public
  dataOne : S₁.Data
  scalarOne : F₁
  responseOne : I₁.layer.Payload
  dataTwo : S₂.Data
  scalarTwo : F₂
  responseTwo : I₂.layer.Payload

def annotate (raw : RawProof S₁ S₂) (answer : C) : Proof S₁ S₂ :=
  let first : S₁.Selected :=
    ((((raw.key,answer,raw.publicData),raw.dataOne),raw.scalarOne),raw.responseOne)
  (((first,raw.dataTwo),raw.scalarTwo),raw.responseTwo)

def rawKey (raw : RawProof S₁ S₂) : Key := raw.key

def preparedProof (proofOf : Out → RawProof S₁ S₂) (result : Out × C) : Proof S₁ S₂ :=
  annotate S₁ S₂ (proofOf result.1) result.2

theorem preparedProof_key_input (proofOf : Out → RawProof S₁ S₂) (out : Out) (c : C) :
    hashInput S₁ S₂ (preparedProof S₁ S₂ proofOf (out,c)) 0 =
      .inl (rawKey S₁ S₂ (proofOf out)) := rfl

def prepareBody (body : TwoOracleTree Enc D (Domain S₁ S₂) C Out tA N)
    (proofOf : Out → RawProof S₁ S₂) :
    TwoOracleTree Enc D (Domain S₁ S₂) C (Out × C) tA (1+N) :=
  body.bindRight fun out => Tree.query (.inl (rawKey S₁ S₂ (proofOf out)))
    (fun c => Tree.done (out,c))

theorem prepareBody_fixLeft [DecidableEq Enc]
    (body : TwoOracleTree Enc D (Domain S₁ S₂) C Out tA N)
    (proofOf : Out → RawProof S₁ S₂) (mt : Fin TM → D) (dflt : D) (seen : List Enc) :
    TwoOracleTree.fixLeft mt dflt (prepareBody S₁ S₂ body proofOf) seen =
      VerifierQuery.prepare (TwoOracleTree.fixLeft mt dflt body seen)
        (fun out => .inl (rawKey S₁ S₂ (proofOf out))) := by
  rw [prepareBody,TwoOracleTree.fixLeft_bindRight]
  rfl

/-- Coherence follows from replay even when the prover never queried the key. -/
theorem preparedProof_coherent (tree : Tree (Domain S₁ S₂) C Out N)
    (proofOf : Out → RawProof S₁ S₂) (H : Domain S₁ S₂ → C) :
    let result := ((VerifierQuery.prepare tree
      (fun out => .inl (rawKey S₁ S₂ (proofOf out)))).run H).1
    let proof := preparedProof S₁ S₂ proofOf result
    (context S₁ S₂ proof).2.1 = H (.inl (context S₁ S₂ proof).1) := by
  rw [VerifierQuery.prepare_output]
  rfl

end LfzkV2.Packed.TwoFieldReplay
