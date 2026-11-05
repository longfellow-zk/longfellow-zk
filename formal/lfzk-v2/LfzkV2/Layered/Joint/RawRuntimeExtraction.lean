import LfzkV2.Layered.Joint.RawExtraction
import LfzkV2.Layered.Joint.RuntimeCost
import LfzkV2.Joint.RuntimeSecurity
import LfzkV2.Layered.Sizes

/-! Full authenticated mdoc extraction for the quad-fragment Rust checkpoint: the packed binary
frontend, direct prime-field frontend, linear terminal and backend, retained
MAC, and one tuple commitment with shared column queries. -/

namespace LfzkV2.Layered.Joint.RawRuntimeExtraction

open Finset RecursivePolygero LigeroFamily Merkle Merkle.MH Merkle.RandomOracle Replay
open LfzkV2.Joint (Participant)
open scoped Classical

set_option maxRecDepth 100000

variable {k s n t out₁ input₁ out₂ input₂ tA N TM blocks : ℕ}
variable (P₁ P₂ : Participant k s n t)
variable {Key C Public Out Enc D Salt Fmac : Type}
variable [Fintype C] [Field Fmac] [Fintype Fmac] [DecidableEq Fmac]
variable {circuit₁ : Layered.Circuit P₁.Carrier out₁ input₁}
variable {circuit₂ : Layered.Circuit P₂.Carrier out₂ input₂}
variable (S₁ : Layered.Runtime.CompiledSide P₁.Carrier C (Context Key C Public) circuit₁ P₁.backend)
variable (S₂ : Layered.Runtime.CompiledSide P₂.Carrier C (Side.Frontend S₁) circuit₂ P₂.backend)
variable (M : MacData C Fmac (Counting.tupleCounts P₁.backend).Index
  (Counting.tupleCounts P₂.backend).Index blocks)
variable (decodeQuery : C → QuerySet n t)
variable [DecidableEq Enc] [Inhabited D] [Inhabited Salt]
variable [Fintype Key] [Fintype Public] [Fintype D] [DecidableEq Key] [DecidableEq D]
variable [Inhabited (Pair.family P₁ P₂).Leaf] [Fintype S₁.Data] [Fintype S₂.Data]
variable [DecidableEq (Domain S₁ S₂)]
variable (codec : Codec Salt (Pair.family P₁ P₂).Leaf D Enc)
variable (claimOf : Out → OpeningClaim n Salt (Pair.family P₁ P₂).Leaf D)
variable (ht : 0 < t) (body : TwoOracleTree Enc D (Domain S₁ S₂) C Out tA N)
variable (proofOf : Out → RawProof S₁ S₂) (dec : RoleDecoders codec) (rootOf : Key → D)

variable (cert₁ : S₁.Profiled LfzkV2.Packed.RuntimeProfiles.Hash.profile)
variable (cert₂ : S₂.Profiled LfzkV2.Packed.RuntimeProfiles.Signature.profile)
variable (hpacked₁ : S₁.packed = true) (hpacked₂ : S₂.packed = false)
variable (hpacking : S₁.packingBudget = (S₁.sampling.fieldFiber : ℚ)*S₁.bound)
variable (hfield₁ : 2^128 ≤ Fintype.card P₁.Carrier) (hfield₂ : 2^255 ≤ Fintype.card P₂.Carrier)
variable (hmac : 2^128 ≤ Fintype.card Fmac) (hDigest : Fintype.card D = 2^256)
variable (hfront₁ : circuit₁.ordinaryBudget ≤ 593)
variable (hfront₂ : circuit₂.ordinaryBudget ≤ 565)
variable (hlayers₁ : circuit₁.layers ≤ 20) (hlayers₂ : circuit₂.layers ≤ 21)
variable (hqueryOne : ∀ c, S₁.decodeQuery c = P₁.localQuery (decodeQuery c))
variable (hqueryTwo : ∀ c, S₂.decodeQuery c = P₂.localQuery (decodeQuery c))
variable (tag : Public → Fin blocks → Fmac)
variable (hrowOne : ∀ (ctx : Context Key C Public) W g, S₁.Good ctx W g →
  M.macOne g (M.decode ctx.2.1) = tag ctx.2.2)
variable (hrowTwo : ∀ (ctx : Side.Frontend S₁) W g, S₂.Good ctx W g →
  M.macTwo g (M.decode ctx.1.1.2.1) = tag ctx.1.1.2.2)
variable (hspace : 2*n+tA ≤ TM)

include cert₁ cert₂ hpacked₁ hpacked₂ hpacking hfield₁ hfield₂ hmac hDigest
  hfront₁ hfront₂ hlayers₁ hlayers₂ hqueryOne hqueryTwo tag hrowOne hrowTwo hspace

/-- Exact finite bound. The coefficient 1384 is the sum 925+459 of the
per-field shared-query residual bounds. The one-tree Merkle term appears once. -/
theorem probability_bound :
    RawExtraction.probability (TM := TM) P₁ P₂ S₁ S₂ M decodeQuery codec claimOf ht
      body proofOf dec rootOf ≤
      (1+N : ℕ)*RuntimeCost.coefficient+RuntimeCost.constant+
        (Bcs.AdaptiveCommit.adaptiveNumerator 5824 tA
          (slots S₁ S₂+(1+N)) : ℚ)/(2^256 : ℚ) := by
  letI : Nonempty C := ⟨S₁.dflt⟩
  have hc := RuntimeCost.error_le S₁ S₂ cert₁ cert₂ hpacked₁ hpacked₂ hpacking
    hfield₁ hfield₂ hmac hfront₁ hfront₂ hlayers₁ hlayers₂ M (1+N)
  have hp := RawExtraction.probability_le P₁ P₂ S₁ S₂ M decodeQuery codec claimOf ht
    body proofOf dec rootOf hqueryOne hqueryTwo tag hrowOne hrowTwo hspace
  have hn : n = 2912 := P₁.columns.symm.trans cert₁.geometry.n
  have hn2 : 2*n = 5824 := by omega
  rw [hn2,hDigest] at hp
  push_cast at hc hp ⊢
  exact hp.trans (add_le_add hc le_rfl)

/-- Unit-offset 116-bit work-normalized extraction for the actual joint
runtime. N and tA count the prover's transcript and Merkle queries. The
verifier's MAC replay query is included, not assumed to have been made. -/
theorem extraction_116 :
    RawExtraction.probability (TM := TM) P₁ P₂ S₁ S₂ M decodeQuery codec claimOf ht
      body proofOf dec rootOf ≤ (1+N+tA : ℚ)/(2^116 : ℚ) := by
  have hn : n = 2912 := P₁.columns.symm.trans cert₁.geometry.n
  by_cases hsmall : tA < 8
  · have h := RawExtraction.probability_small_merkle P₁ P₂ S₁ S₂ M decodeQuery codec claimOf ht
      body proofOf dec rootOf (by rw [hn]; decide) hsmall hspace
    have hn2 : 2*n = 5824 := by omega
    rw [hn2,hDigest] at h
    have hnum : 2*tA*tA+(5824+tA)*(2*tA+1) ≤ 87563 := by
      calc
        _ ≤ 2*7*7+(5824+7)*(2*7+1) := by gcongr <;> omega
        _ = 87563 := rfl
    calc
      _ ≤ (2*tA*tA+(5824+tA)*(2*tA+1) : ℕ)/(2^256 : ℚ) := by
        simpa only [Nat.cast_pow,Nat.cast_ofNat] using h
      _ ≤ 87563/(2^256 : ℚ) := by gcongr; exact_mod_cast hnum
      _ ≤ 1/(2^116 : ℚ) := by norm_num
      _ ≤ (1+N+tA : ℚ)/(2^116 : ℚ) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg _
        have ht : (0 : ℚ) ≤ tA := Nat.cast_nonneg _
        linarith
  · apply LfzkV2.Joint.RuntimeSecurity.tsec_116_of_merkle_ge
      (RawExtraction.probability_le_one P₁ P₂ S₁ S₂ M decodeQuery codec claimOf ht
        body proofOf dec rootOf) (L := slots S₁ S₂) ?_ (by omega)
    · exact probability_bound P₁ P₂ S₁ S₂ M decodeQuery codec claimOf ht body proofOf dec rootOf
        cert₁ cert₂ hpacked₁ hpacked₂ hpacking hfield₁ hfield₂ hmac hDigest
        hfront₁ hfront₂ hlayers₁ hlayers₂ hqueryOne hqueryTwo tag hrowOne hrowTwo hspace
    · have hs₁ := Layered.Replay.slots_le circuit₁
      have hs₂ := Layered.Replay.slots_le circuit₂
      simp [slots, backendStart, secondStart, Side.steps,
        hpacked₁, hpacked₂, Layered.Runtime.Replay.packingSlots]
      omega

end LfzkV2.Layered.Joint.RawRuntimeExtraction
