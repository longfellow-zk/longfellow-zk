import LfzkV2.Joint.Replay
import Bcs.VerifierQuery
import Merkle.TwoOracle

/-! Raw proofs contain no claimed MAC challenge. The verifier queries the
point fixed by the joint commitment, then annotates the two frontend inputs
with that answer for the mathematical replay. -/

namespace LfzkV2.Joint.Replay

open RecursivePolygero Bcs.TotalOracle Merkle.RandomOracle

variable {F₁ F₂ Key C Public Out Enc D : Type}
variable [Field F₁] [Fintype F₁] [DecidableEq F₁]
variable [Field F₂] [Fintype F₂] [DecidableEq F₂] [Fintype C]
variable {out₁ input₁ out₂ input₂ N tA TM : ℕ}
variable {circuit₁ : Native.Circuit F₁ out₁ input₁} {I₁ : Instance F₁}
variable {circuit₂ : Native.Circuit F₂ out₂ input₂} {I₂ : Instance F₂}
variable (S₁ : Linear.Runtime.CompiledSide F₁ C (Context Key C Public) circuit₁ I₁)
variable (S₂ : Linear.Runtime.CompiledSide F₂ C (Side.Frontend S₁) circuit₂ I₂)

def macPoint (key : Key) : Domain S₁ S₂ :=
  Transcript.pointAt key (fun _ => .empty) ⟨0,by unfold slots; omega⟩

theorem hashInput_zero (proof : Proof S₁ S₂) :
    hashInput S₁ S₂ proof 0 = macPoint S₁ S₂ (context S₁ S₂ proof).1 := by
  rw [hashInput, dif_pos (by unfold slots; omega)]
  apply Transcript.at_eq_of_message_prefix
  intro j hj
  change j ≤ 0 at hj
  have heq : j = 0 := by omega
  subst j
  simp only [messages, if_true]

/-- The unused degree-one packing scalar is allowed as an annotation here;
the concrete codec always sets it to zero. -/
structure RawProof where
  key : Key
  publicData : Public
  dataOne : S₁.Data
  scalarOne : F₁
  dataTwo : S₂.Data
  scalarTwo : F₂
  responseOne : I₁.layer.Payload
  responseTwo : I₂.layer.Payload

def annotate (raw : RawProof S₁ S₂) (answer : C) : Proof S₁ S₂ :=
  let first : Side.Frontend S₁ := (((raw.key,answer,raw.publicData),raw.dataOne),raw.scalarOne)
  ((((first,raw.dataTwo),raw.scalarTwo)),raw.responseOne,raw.responseTwo)

def preparedProof (proofOf : Out → RawProof S₁ S₂) (result : Out × C) : Proof S₁ S₂ :=
  annotate S₁ S₂ (proofOf result.1) result.2

theorem preparedProof_key_input (proofOf : Out → RawProof S₁ S₂) (out : Out) (c : C) :
    hashInput S₁ S₂ (preparedProof S₁ S₂ proofOf (out,c)) 0 =
      macPoint S₁ S₂ (proofOf out).key := hashInput_zero S₁ S₂ _

def prepareBody (body : TwoOracleTree Enc D (Domain S₁ S₂) C Out tA N)
    (proofOf : Out → RawProof S₁ S₂) :
    TwoOracleTree Enc D (Domain S₁ S₂) C (Out × C) tA (1+N) :=
  body.bindRight fun out => Tree.query (macPoint S₁ S₂ (proofOf out).key)
    (fun c => Tree.done (out,c))

theorem prepareBody_fixLeft [DecidableEq Enc]
    (body : TwoOracleTree Enc D (Domain S₁ S₂) C Out tA N)
    (proofOf : Out → RawProof S₁ S₂) (mt : Fin TM → D) (dflt : D) (seen : List Enc) :
    TwoOracleTree.fixLeft mt dflt (prepareBody S₁ S₂ body proofOf) seen =
      VerifierQuery.prepare (TwoOracleTree.fixLeft mt dflt body seen)
        (fun out => macPoint S₁ S₂ (proofOf out).key) := by
  rw [prepareBody,TwoOracleTree.fixLeft_bindRight]
  rfl

theorem preparedProof_coherent (tree : Tree (Domain S₁ S₂) C Out N)
    (proofOf : Out → RawProof S₁ S₂) (H : Domain S₁ S₂ → C) :
    let result := ((VerifierQuery.prepare tree
      (fun out => macPoint S₁ S₂ (proofOf out).key)).run H).1
    let proof := preparedProof S₁ S₂ proofOf result
    (context S₁ S₂ proof).2.1 = H (hashInput S₁ S₂ proof 0) := by
  rw [VerifierQuery.prepare_output]
  dsimp only
  rw [hashInput_zero]
  rfl

end LfzkV2.Joint.Replay
