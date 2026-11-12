import LfzkV2.Current.WitnessInputs
import LfzkV2.Current.HashCircuit

/-! Ordinary witness truth and static hash-circuit noninterference.
`HashValid` checks one reference assignment of the reserved inputs. The
separate circuit property `HashNoninterference` states that changing masks,
OTP bits and generated adapter parameters cannot change the ordinary hash
checks, uniformly over public inputs and private values. It derives the
`UniformHashValid` fact consumed by coin-change proofs. An arbitrary trusted
`BinaryCircuit` topology does not imply this static read-dependency property.
-/
noncomputable section
namespace LfzkV2.Current.MdocWitness
open Application ApplicationSetup ConcreteSetup SumcheckV2
open scoped Classical
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

variable {B : Type} [Field B] [Algebra (ZMod 2) B]

/-- Non-adapter checks at one assignment of the reserved inputs and publicBits
adapter parameters. This predicate assumes no generated product equation. -/
def HashAt (binary : BinaryCircuit B) (original : Fin binary.nPrivate → Bool)
    (mask : Fin 256 → Bool) (otp : Fin 2 → Fin 10 → Bool)
    (powers : Fin 2 → Fin 1024 → Bˣ) (base : Bˣ)
    (masked : Fin 2 → Fin 10 → Bool) (targets : Fin 2 → Bˣ) : Prop :=
  HashCircuit.Checks binary.description.layout binary.description.output binary.description.shape binary.description.others
      binary.description.carry binary.description.above binary.description.sources binary.description.advice
      powers base masked targets
      (Current.Adapter.Circuit.bitValue ∘ WitnessInputs.bits binary
        (WitnessInputs.privateValues binary original mask otp))

/-- Ordinary witness truth at one fixed reference assignment. The separate
static noninterference property transports it to the protocol's random masks. -/
def HashValid (binary : BinaryCircuit B) (original : Fin binary.nPrivate → Bool) : Prop :=
  HashAt binary original (fun _ => false) (fun _ _ => false)
    (fun _ _ => 1) 1 (fun _ _ => false) (fun _ => 1)

/-- A property of the trusted circuit, independent of any chosen witness:
reserved masks, OTP bits and generated adapter parameters cannot change its
ordinary hash checks. Public inputs are quantified, so the property survives
installing an adaptively selected request. Arbitrary `Others`/`Above` topology
does not imply this restriction; the circuit supplier must establish it. -/
def HashNoninterference (binary : BinaryCircuit B) : Prop :=
  ∀ (publicBits : Fin binary.nPublic → Bool) (original : Fin binary.nPrivate → Bool)
    (mask : Fin 256 → Bool) (otp : Fin 2 → Fin 10 → Bool)
    (powers : Fin 2 → Fin 1024 → Bˣ) (base : Bˣ)
    (masked : Fin 2 → Fin 10 → Bool) (targets : Fin 2 → Bˣ),
    HashValid { binary with publicBits := publicBits } original ↔
      HashAt { binary with publicBits := publicBits } original mask otp powers base masked targets

/-- The uniform fact consumed by the coin-change proof is a consequence of
ordinary witness truth and static circuit noninterference. -/
def UniformHashValid (binary : BinaryCircuit B) (original : Fin binary.nPrivate → Bool) : Prop :=
  ∀ mask otp powers base masked targets, HashAt binary original mask otp powers base masked targets

theorem HashNoninterference.with_publicBits {binary : BinaryCircuit B}
    (independent : HashNoninterference binary) (publicBits : Fin binary.nPublic → Bool) :
    HashNoninterference { binary with publicBits := publicBits } := by
  intro next original mask otp powers base masked targets
  exact independent next original mask otp powers base masked targets

theorem uniformHashValid_of_valid {binary : BinaryCircuit B}
    (independent : HashNoninterference binary) (original : Fin binary.nPrivate → Bool)
    (valid : HashValid binary original) : UniformHashValid binary original := by
  intro mask otp powers base masked targets
  exact (independent binary.publicBits original mask otp powers base masked targets).mp valid

theorem UniformHashValid.reference {binary : BinaryCircuit B}
    {original : Fin binary.nPrivate → Bool} (valid : UniformHashValid binary original) :
    HashValid binary original := valid _ _ _ _ _ _

theorem private_prefix (binary : BinaryCircuit B) (original : Fin binary.nPrivate → Bool)
    (mask : Fin 256 → Bool) (otp : Fin 2 → Fin 10 → Bool) (i : Fin binary.nPrivate)
    (before : i.val < binary.nPrivate-276) :
    WitnessInputs.privateValues binary original mask otp i = original i :=
  dif_pos before


end LfzkV2.Current.MdocWitness
