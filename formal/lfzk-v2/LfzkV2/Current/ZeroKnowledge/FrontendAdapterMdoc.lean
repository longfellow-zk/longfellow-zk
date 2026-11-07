import LfzkV2.Current.ZeroKnowledge.FrontendAdapter

/-! Current mdoc specialization: 768 shared bits, one canonical 256-bit
copy of the prime hiding scalar, and two ten-bit quotients. All public
adapter outputs can be sampled without a witness. The inverse uses that
witness only to recover the already committed scalar and OTP coordinates. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.Adapter.Mdoc
open SumcheckV2
open scoped Classical

abbrev P := ZMod Current.Adapter.Mdoc.primeOrder
abbrev Alphas := P → Fin 2 → {r : P // r ≠ 0}

theorem maskCapacity : Current.Adapter.Mdoc.primeOrder ≤ 2^256 := by
  norm_num [Current.Adapter.Mdoc.primeOrder]

def sharedSum (weights : Fin 768 → P) (values : Fin 768 → Bool) : P :=
  ∑ i, weights i * (if values i then 1 else 0)

def offset (weights : Fin 768 → P) (values : Fin 768 → Bool) (eta : P) : P :=
  eta*sharedSum weights values

def recoverMask (weights : Fin 768 → P) (values : Fin 768 → Bool) (eta mu : P) : P :=
  mu-offset weights values eta

theorem recoverMask_mu (weights : Fin 768 → P) (values : Fin 768 → Bool) (eta mask : P) :
    recoverMask weights values eta (offset weights values eta+mask) = mask := by
  simp [recoverMask,add_comm]

def values (weights : Fin 768 → P) (shared : Fin 768 → Bool) (eta mu : P) : Fin 1024 → Bool :=
  Handoff.values shared (canonicalMask maskCapacity (recoverMask weights shared eta mu))

def weights (sharedWeights : Fin 768 → P) (eta : P) : Fin 1024 → P :=
  Handoff.weights (maskBits := 256) sharedWeights eta

theorem residual_zero (sharedWeights : Fin 768 → P) (shared : Fin 768 → Bool) (eta mu : P) :
    Current.Adapter.residual (weights sharedWeights eta) (values sharedWeights shared eta mu) mu = 0 := by
  rw [weights,values,Handoff.residual_eq,canonicalMask_value]
  simp only [recoverMask,offset,sharedSum]
  ring

def quotients (sharedWeights : Fin 768 → P) (shared : Fin 768 → Bool) (eta : P)
    (alpha : Alphas) (mu : P) : Fin 2 → Fin (2^10) := fun tree =>
  honestQuotient (weights sharedWeights eta) (values sharedWeights shared eta mu)
    (alpha mu tree).val (by decide) (by decide)

def advice (sharedWeights : Fin 768 → P) (shared : Fin 768 → Bool) (eta : P)
    (alpha : Alphas) (mu : P) : MdocAdvice.Value :=
  AdapterBits.packedQuotients (quotients sharedWeights shared eta alpha mu)

theorem advice_at (sharedWeights : Fin 768 → P) (shared : Fin 768 → Bool) (eta : P)
    (alpha : Alphas) (mu : P) :
    advice sharedWeights shared eta alpha mu =
      advice sharedWeights shared eta (fun _ => alpha mu) mu := rfl

theorem quotients_runtime (sharedWeights : Fin 768 → P) (shared : Fin 768 → Bool) (eta : P)
    (alpha : Alphas) (mu : P) (tree : Fin 2) :
    let sum := Current.Adapter.scaledSum (weights sharedWeights eta)
      (values sharedWeights shared eta mu) (alpha mu tree).val
    let target := ((alpha mu tree).val*mu).val
    target ≤ sum ∧ (sum-target) % Current.Adapter.Mdoc.primeOrder = 0 ∧
      (sum-target) / Current.Adapter.Mdoc.primeOrder =
        (quotients sharedWeights shared eta alpha mu tree).val :=
  honestQuotient_runtime _ _ _ _ (by decide) (by decide) (residual_zero _ _ _ _)

def coupling (sharedWeights : Fin 768 → P) (shared : Fin 768 → Bool) (eta : P) (alpha : Alphas) :
    (P × Fin (2^24)) ≃ ((P × MdocAdvice.Value) × Fin 16) :=
  rawMuAdviceEquiv (offset sharedWeights shared eta) (advice sharedWeights shared eta alpha)

theorem coupling_mu (sharedWeights : Fin 768 → P) (shared : Fin 768 → Bool) (eta : P)
    (alpha : Alphas) (mask : P) (otp : Fin (2^24)) :
    (coupling sharedWeights shared eta alpha (mask,otp)).1.1 =
      eta*sharedSum sharedWeights shared+mask := rfl

theorem coupling_bits (sharedWeights : Fin 768 → P) (shared : Fin 768 → Bool) (eta : P)
    (alpha : Alphas) (mask : P) (otp : Fin (2^24)) (tree : Fin 2) (i : Fin 10) :
    let mu := offset sharedWeights shared eta+mask
    MdocAdvice.bits (coupling sharedWeights shared eta alpha (mask,otp)).1.2 tree i =
      Bool.xor ((quotients sharedWeights shared eta alpha mu tree).val.testBit i.val)
        (otp.val.testBit (10*tree.val+i.val)) := by
  have h := muAdviceEquiv_bits (offset sharedWeights shared eta)
    (advice sharedWeights shared eta alpha) mask (AdapterBits.rawOtpEquiv otp).1 tree i
  rw [show ∀ mu, advice sharedWeights shared eta alpha mu =
      AdapterBits.packedQuotients (quotients sharedWeights shared eta alpha mu) from fun _ => rfl,
    AdapterBits.packedQuotients_bits,AdapterBits.rawOtp_bits] at h
  exact h

def simulate (coins : (P × MdocAdvice.Value) × Fin 16) : P × MdocAdvice.Value := coins.1

theorem sameDistribution {Observed : Type} [DecidableEq Observed]
    (sharedWeights : Fin 768 → P) (shared : Fin 768 → Bool) (eta : P) (alpha : Alphas)
    (observe : P × MdocAdvice.Value → Observed) :
    LigeroFamily.SameDistribution
      (fun tape => observe (coupling sharedWeights shared eta alpha tape).1)
      (fun coins => observe (simulate coins)) :=
  rawMuAdvice_sameDistribution _ _ observe

end LfzkV2.Current.ZeroKnowledge.Frontend.Adapter.Mdoc
