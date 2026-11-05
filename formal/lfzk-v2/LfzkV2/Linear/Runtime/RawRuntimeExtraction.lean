import LfzkV2.Linear.Runtime.RawExtraction
import LfzkV2.Linear.Runtime.RuntimeSecurity

/-! The current packed runtime's authenticated raw-proof endpoint. Both
commitment roots precede the shared MAC challenge; the hash side then has
one packing stage and the signature side is direct. This certificate models
the linear-only backend at commit 21cb029. It includes no supplied-key coherence
premise and covers every pair of prover-query budgets. -/

namespace LfzkV2.Linear.Runtime.RawRuntimeExtraction

open Finset RecursivePolygero Merkle Merkle.MH Merkle.RandomOracle TwoFieldReplay
open scoped Classical

set_option maxRecDepth 100000

variable {F₁ F₂ Key C Public Out Enc D Salt₁ Salt₂ Fmac : Type}
variable [Field F₁] [Fintype F₁] [DecidableEq F₁]
variable [Field F₂] [Fintype F₂] [DecidableEq F₂]
variable [Fintype C] [DecidableEq Enc] [Inhabited D]
variable [Field Fmac] [Fintype Fmac] [DecidableEq Fmac]
variable {out₁ input₁ out₂ input₂ blocks tA N TM : ℕ}
variable {circuit₁ : Native.Circuit F₁ out₁ input₁} {I₁ : Instance F₁}
variable {circuit₂ : Native.Circuit F₂ out₂ input₂} {I₂ : Instance F₂}
variable (S₁ : CompiledSide F₁ C (Context Key C Public) circuit₁ I₁)
variable (S₂ : CompiledSide F₂ C S₁.Selected circuit₂ I₂)
variable (cert₁ : S₁.Profiled LfzkV2.Packed.RuntimeProfiles.Hash.profile)
variable (cert₂ : S₂.Profiled LfzkV2.Packed.RuntimeProfiles.Signature.profile)
variable [Inhabited Salt₁] [Inhabited Salt₂]
variable [DecidableEq (Domain S₁ S₂)]
variable (M : MacData C Fmac (Counting.tupleCounts I₁).Index (Counting.tupleCounts I₂).Index blocks)
variable (codec₁ : Codec Salt₁ (MerkleCompiler.Leaf F₁ I₁.nw I₁.nq) D Enc)
variable (codec₂ : Codec Salt₂ (MerkleCompiler.Leaf F₂ I₂.nw I₂.nq) D Enc)
variable (claimOf₁ : Out → OpeningClaim I₁.n Salt₁ (MerkleCompiler.Leaf F₁ I₁.nw I₁.nq) D)
variable (claimOf₂ : Out → OpeningClaim I₂.n Salt₂ (MerkleCompiler.Leaf F₂ I₂.nw I₂.nq) D)
variable (ht₁ : 0 < I₁.t) (ht₂ : 0 < I₂.t)
variable (body : TwoOracleTree Enc D (Domain S₁ S₂) C Out tA N)
variable (proofOf : Out → RawProof S₁ S₂)
variable (dec₁ : RoleDecoders codec₁) (dec₂ : RoleDecoders codec₂) (rootOf₁ rootOf₂ : Key → D)
variable [Fintype Key] [Fintype Public] [Fintype D] [DecidableEq Key] [DecidableEq D]
variable [Inhabited (MerkleCompiler.Leaf F₁ I₁.nw I₁.nq)]
variable [Inhabited (MerkleCompiler.Leaf F₂ I₂.nw I₂.nq)]
variable [Fintype S₁.Data] [Fintype S₂.Data]

variable (hpacked₁ : S₁.packed = true) (hpacked₂ : S₂.packed = false)
variable (hpacking : S₁.packingBudget = (S₁.sampling.fieldFiber : ℚ)*S₁.bound)
variable (hfield₁ : 2^128 ≤ Fintype.card F₁) (hfield₂ : 2^255 ≤ Fintype.card F₂)
variable (hmac : 2^128 ≤ Fintype.card Fmac) (hDigest : Fintype.card D = 2^256)
variable (hout₁ : out₁ ≤ 5) (hout₂ : out₂ ≤ 3)
variable (hfront₁ : out₁+circuit₁.sharpLayerBudget ≤ 593)
variable (hfront₂ : out₂+circuit₂.sharpLayerBudget ≤ 565)
variable (hlayers₁ : circuit₁.layers ≤ 20) (hlayers₂ : circuit₂.layers ≤ 21)
variable (tag : Public → Fin blocks → Fmac)
variable (hrowOne : ∀ (ctx : Context Key C Public) W g, S₁.Good ctx W g →
  M.macOne g (M.decode ctx.2.1) = tag ctx.2.2)
variable (hrowTwo : ∀ (ctx : S₁.Selected) W g, S₂.Good ctx W g →
  M.macTwo g (M.decode (S₁.context ctx).2.1) = tag (S₁.context ctx).2.2)
variable (hspace : 2*I₂.n+2*I₁.n+tA ≤ TM)

include cert₁ cert₂ hpacked₁ hpacked₂ hpacking hfield₁ hfield₂ hmac hDigest
  hout₁ hout₂ hfront₁ hfront₂ hlayers₁ hlayers₂ tag hrowOne hrowTwo hspace

/-- Exact finite bound for the authenticated acceptance/extraction-failure
event, including the verifier's one additional MAC-key lookup. -/
theorem probability_bound :
    RawExtraction.probability (TM := TM) S₁ S₂ M
      codec₁ codec₂ claimOf₁ claimOf₂ ht₁ ht₂ body proofOf dec₁ dec₂ rootOf₁ rootOf₂ ≤
      (1+N : ℕ)*RuntimeCost.coefficient+RuntimeCost.constant+
        2*(Bcs.AdaptiveCommit.adaptiveNumerator 11648 tA
          (1+S₁.slots+S₂.slots+(1+N)) : ℚ)/(2^256 : ℚ) := by
  letI : Nonempty C := ⟨S₁.dflt⟩
  let K := TwoFieldCommitmentFS.setup S₁ S₂ (prepareBody S₁ S₂ body proofOf)
    (preparedProof S₁ S₂ proofOf) S₁.dflt
  let proof : Proof S₁ S₂ := preparedProof S₁ S₂ proofOf
    (K.proof (fun _ : Fin TM => default) (fun _ => S₁.dflt))
  have hc := RuntimeCost.error_le S₁ S₂ cert₁ cert₂ hpacked₁ hpacked₂ hpacking
    hfield₁ hfield₂ hmac hout₁ hout₂ hfront₁ hfront₂ hlayers₁ hlayers₂ M (1+N) proof
  have hp := RawExtraction.probability_le S₁ S₂ M codec₁ codec₂ claimOf₁ claimOf₂
    ht₁ ht₂ body proofOf dec₁ dec₂ rootOf₁ rootOf₂ tag hrowOne hrowTwo hspace
  have hn : 2*I₂.n+2*I₁.n = 11648 := by rw [cert₁.geometry.n,cert₂.geometry.n]; rfl
  rw [hn,hDigest] at hp
  push_cast at hc hp ⊢
  exact hp.trans (add_le_add hc le_rfl)

/-- Unit-offset 116-bit work-normalized extraction for the complete packed
native transcript. N counts only the prover's transcript queries, and tA
counts its Merkle queries. -/
theorem extraction_116 :
    RawExtraction.probability (TM := TM) S₁ S₂ M
      codec₁ codec₂ claimOf₁ claimOf₂ ht₁ ht₂ body proofOf dec₁ dec₂ rootOf₁ rootOf₂ ≤
      (1+N+tA : ℚ)/(2^116 : ℚ) := by
  have hn : 2*I₂.n+2*I₁.n = 11648 := by rw [cert₁.geometry.n,cert₂.geometry.n]; rfl
  by_cases hsmall : tA < 8
  · have h := RawExtraction.probability_small_merkle S₁ S₂ M codec₁ codec₂
      claimOf₁ claimOf₂ ht₁ ht₂ body proofOf dec₁ dec₂ rootOf₁ rootOf₂
      (by rw [cert₁.geometry.n]; decide) hsmall hspace
    rw [hn,hDigest] at h
    have hnum : 2*tA*tA+(11648+tA)*(2*tA+1) ≤ 174923 := by
      calc
        _ ≤ 2*7*7+(11648+7)*(2*7+1) := by gcongr <;> omega
        _ = 174923 := rfl
    calc
      _ ≤ (2*tA*tA+(11648+tA)*(2*tA+1) : ℕ)/(2^256 : ℚ) := by
        simpa only [Nat.cast_pow,Nat.cast_ofNat] using h
      _ ≤ 174923/(2^256 : ℚ) := by gcongr; exact_mod_cast hnum
      _ ≤ 1/(2^116 : ℚ) := by norm_num
      _ ≤ (1+N+tA : ℚ)/(2^116 : ℚ) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg _
        have ht : (0 : ℚ) ≤ tA := Nat.cast_nonneg _
        linarith
  · apply RuntimeSecurity.tsec_116_of_merkle_ge
      (RawExtraction.probability_le_one S₁ S₂ M codec₁ codec₂ claimOf₁ claimOf₂
        ht₁ ht₂ body proofOf dec₁ dec₂ rootOf₁ rootOf₂)
      (L := 1+S₁.slots+S₂.slots) ?_ (by omega)
    · exact probability_bound S₁ S₂ cert₁ cert₂ M codec₁ codec₂ claimOf₁ claimOf₂
        ht₁ ht₂ body proofOf dec₁ dec₂ rootOf₁ rootOf₂ hpacked₁ hpacked₂ hpacking
        hfield₁ hfield₂ hmac hDigest hout₁ hout₂ hfront₁ hfront₂ hlayers₁ hlayers₂ tag hrowOne hrowTwo hspace
    · simpa [CompiledSide.slots,hpacked₁,hpacked₂,Replay.packingSlots] using
        RuntimeSecurity.slots_le circuit₁ circuit₂ hfront₁ hfront₂ hlayers₁ hlayers₂

end LfzkV2.Linear.Runtime.RawRuntimeExtraction
