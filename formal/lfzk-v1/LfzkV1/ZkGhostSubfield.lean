import LfzkV1.ZkGhostTwoField
import LfzkV1.V7SubfieldPadding

/-!
# Exact ghost arithmetic with subfield-restricted core padding

The selected rows' padding belongs to the image of the small field. The
other padding and the three dedicated masks retain their full support.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace LfzkV1.ZkGhostSubfield

open LigeroFamily Ligero.V1
open LfzkV1.ZkAdaptiveV1 LfzkV1.CompiledLongfellowZk LfzkV1.Mac
open LfzkV1.CompiledLongfellowZkTwoField
open LfzkV1.ZkGhostSimulator
open LigeroFamily.ReedSolomon

section Domain

variable {K F : Type} [Field K] [Field F] {r w n : ℕ}
variable (emb : K →+* F) (large : Domain F r w n)
variable (pointSupported : ∀ i, large.point i ∈ Set.range emb)

/-- Lift any subfield-valued evaluation domain without imposing a canonical
numbering or basis on the small field. -/
noncomputable def preimageDomain : Domain K r w n where
  point i := Classical.choose (pointSupported i)
  injective := fun {i j} h => large.injective
    ((Classical.choose_spec (pointSupported i)).symm.trans
      ((congrArg emb h).trans (Classical.choose_spec (pointSupported j))))

theorem preimageDomain_map (i : Position r w n) :
    large.point i = emb ((preimageDomain emb large pointSupported).point i) :=
  (Classical.choose_spec (pointSupported i)).symm

end Domain

section Side

variable {K F E : Type} [Field K] [Field F] [Fintype F] [DecidableEq F]
  [Fintype E] [DecidableEq E]
variable {r w n nw nq reps : ℕ}
variable {Salt D Enc Coin LQ Ctx Wit Blind Tr RO : Type}
variable (P : Side F r w n nw nq reps E Salt D Enc Coin LQ Ctx Wit Blind Tr RO)
variable (emb : K →+* F)
variable (selected : (block : CoreBlock) → Fin (block.rowCount nw nq) → Prop)

/-- The part of the sampler support that is smaller than the ambient field. -/
def support (ρ : Tape P.C nw nq reps) : Prop :=
  ∀ block j, selected block j → ∀ i, ρ.corePadding block j i ∈ Set.range emb

variable (small : Domain K r w n) (large : Domain F r w n)
variable (domainMap : ∀ i, large.point i = emb (small.point i))
variable (baseEq : P.C.base = evaluationSpace large (r + w))

private theorem translateCorePadding_roundtrip (q : QuerySet n r)
    (a b : Fin w → F) (pad : Fin r → F) :
    translateCorePadding P.C q b a (translateCorePadding P.C q a b pad) = pad :=
  (translateCorePaddingEquiv P.C q a b).symm_apply_apply pad

include domainMap baseEq in
/-- The real and simulated tape satisfy exactly the same support restriction.
The witness must lie in the small field at every selected row. -/
theorem sideCoinsEquiv_support_iff (κ : Ctx) (wit : Wit) (Gr : RO) (c i : Coin)
    (valid : P.FE.Valid wit κ)
    (hwit : ∀ b block j, selected block j → ∀ k, P.FE.msgs wit b block j k ∈ Set.range emb)
    (x : Blind × Tape P.C nw nq reps) :
    support P emb selected ((sideCoinsEquiv P κ wit Gr c i valid x).2) ↔
      support P emb selected x.2 := by
  let y := sideCoinsEquiv P κ wit Gr c i valid x
  let query := P.dec₂ i
  have hpad (block : CoreBlock) (j : Fin (block.rowCount nw nq)) :
      y.2.corePadding block j =
        translateCorePadding P.C query (P.FE.msgs wit x.1 block j) 0
          (x.2.corePadding block j) := rfl
  have hzero : ∀ k : Fin w, (0 : Fin w → F) k ∈ Set.range emb :=
    fun _ => ⟨0, map_zero emb⟩
  constructor
  · intro hy block j hj
    have hrec := V7SubfieldPadding.translateCorePadding_mem_range emb small large domainMap P.C
      baseEq query 0 (P.FE.msgs wit x.1 block j) (y.2.corePadding block j)
      hzero (hwit x.1 block j hj) (hy block j hj)
    rwa [hpad, translateCorePadding_roundtrip] at hrec
  · intro hx block j hj
    change ∀ k, y.2.corePadding block j k ∈ Set.range emb
    rw [hpad]
    exact V7SubfieldPadding.translateCorePadding_mem_range emb small large domainMap P.C
      baseEq query (P.FE.msgs wit x.1 block j) 0 (x.2.corePadding block j)
      (hwit x.1 block j hj) hzero (hx block j hj)

end Side

section RestrictedProducts

variable {A B C S T : Type}

/-- Allow both tape factors to range over supported values only. -/
private def jointSubtype (p : S → Prop) (q : T → Prop) :
    A × (B × {x : S // p x}) × (C × {x : T // q x}) ≃
      {x : A × (B × S) × (C × T) // p x.2.1.2 ∧ q x.2.2.2} where
  toFun x := ⟨(x.1, (x.2.1.1, x.2.1.2.val), x.2.2.1, x.2.2.2.val),
    x.2.1.2.property, x.2.2.2.property⟩
  invFun x := (x.val.1, (x.val.2.1.1, ⟨x.val.2.1.2, x.property.1⟩), x.val.2.2.1,
    ⟨x.val.2.2.2, x.property.2⟩)
  left_inv _ := rfl
  right_inv _ := rfl

end RestrictedProducts

section Joint

variable {F₁ E₁ F₂ E₂ : Type} [Field F₁] [Fintype F₁] [DecidableEq F₁] [Fintype E₁]
  [DecidableEq E₁] [Field F₂] [Fintype F₂] [DecidableEq F₂] [Fintype E₂] [DecidableEq E₂]
variable {r₁ w₁ n₁ nw₁ nq₁ reps₁ r₂ w₂ n₂ nw₂ nq₂ reps₂ : ℕ}
variable {Salt D Enc₁ Enc₂ Coin₁ Coin₂ LQ₁ LQ₂ Ctx₁ Ctx₂ Wit₁ Wit₂ B₁ B₂ Tr₁ Tr₂ RO₁ RO₂ : Type}
variable [DecidableEq LQ₁] [DecidableEq LQ₂]
variable {Fmac : Type} [Field Fmac] {nblk : ℕ}
variable (P₁ : Side F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ E₁ Salt D Enc₁ Coin₁ LQ₁ Ctx₁ Wit₁ B₁ Tr₁ RO₁)
variable (P₂ : Side F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂ E₂ Salt D Enc₂ Coin₂ LQ₂ Ctx₂ Wit₂ B₂ Tr₂ RO₂)
variable (ctx₁ : D → D → Fmac → Tag Fmac nblk → Ctx₁)
variable (ctx₂ : D → D → Fmac → Tag Fmac nblk → LProof F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ Salt D Tr₁ Coin₁ →
  Ctx₂)
variable (Gav : D × D → Fmac)
variable (s₁ : FixedSide n₁ Salt D Coin₁ LQ₁ RO₁) (s₂ : FixedSide n₂ Salt D Coin₂ LQ₂ RO₂)
variable (wit₁ : Tag Fmac nblk → Wit₁) (wit₂ : Tag Fmac nblk → Wit₂) (msg : Fin nblk → Fmac)
variable (p : Tape P₁.C nw₁ nq₁ reps₁ → Prop) (q : Tape P₂.C nw₂ nq₂ reps₂ → Prop)

local notation "Real" => Tag Fmac nblk × (B₁ × Subtype p) × (B₂ × Subtype q)
local notation "Sim" => Tag Fmac nblk × (Tr₁ × Subtype p) × (Tr₂ × Subtype q)

/-- Forget the support proofs, preserving all arithmetic coins. -/
def forgetSupport {A B C S T : Type} {p : S → Prop} {q : T → Prop}
    (x : A × (B × Subtype p) × (C × Subtype q)) : A × (B × S) × (C × T) :=
  (x.1, (x.2.1.1, x.2.1.2.val), x.2.2.1, x.2.2.2.val)

/-- The support restriction is stable at every context and valid witness
that can occur for the fixed challenge coins. -/
def Stable (P : Side F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ E₁ Salt D Enc₁ Coin₁ LQ₁ Ctx₁ Wit₁ B₁ Tr₁ RO₁)
    (s : FixedSide n₁ Salt D Coin₁ LQ₁ RO₁) (wit : Tag Fmac nblk → Wit₁)
    (p : Tape P.C nw₁ nq₁ reps₁ → Prop) : Prop :=
  ∀ (ap : Tag Fmac nblk) κ (valid : P.FE.Valid (wit ap) κ) x,
    p ((sideCoinsEquiv P κ (wit ap) s.round s.challenge s.query valid x).2) ↔ p x.2

theorem stable_of_subfield {K : Type} [Field K] (emb : K →+* F₁)
    (selected : (block : CoreBlock) → Fin (block.rowCount nw₁ nq₁) → Prop)
    (small : Domain K r₁ w₁ n₁) (large : Domain F₁ r₁ w₁ n₁)
    (domainMap : ∀ i, large.point i = emb (small.point i))
    (baseEq : P₁.C.base = evaluationSpace large (r₁ + w₁))
    (hwit : ∀ ap b block j, selected block j → ∀ k,
      P₁.FE.msgs (wit₁ ap) b block j k ∈ Set.range emb) :
    Stable P₁ s₁ wit₁ (support P₁ emb selected) :=
  fun ap κ valid x => sideCoinsEquiv_support_iff P₁ emb selected small large domainMap baseEq κ
    (wit₁ ap) s₁.round s₁.challenge s₁.query valid (hwit ap) x

theorem stable_unrestricted : Stable P₁ s₁ wit₁ (fun _ => True) :=
  fun _ _ _ _ => Iff.rfl

theorem stable_of_points_supported {K : Type} [Field K] (emb : K →+* F₁)
    (selected : (block : CoreBlock) → Fin (block.rowCount nw₁ nq₁) → Prop)
    (large : Domain F₁ r₁ w₁ n₁) (pointSupported : ∀ i, large.point i ∈ Set.range emb)
    (baseEq : P₁.C.base = evaluationSpace large (r₁ + w₁))
    (hwit : ∀ ap b block j, selected block j → ∀ k,
      P₁.FE.msgs (wit₁ ap) b block j k ∈ Set.range emb) :
    Stable P₁ s₁ wit₁ (support P₁ emb selected) :=
  stable_of_subfield P₁ s₁ wit₁ emb selected (preimageDomain emb large pointSupported) large
    (preimageDomain_map emb large pointSupported) baseEq hwit

variable
  (hvalid₁ : ∀ ap root₁ root₂ av, P₁.FE.Valid (wit₁ ap) (ctx₁ root₁ root₂ av (macTag av ap msg)))
  (hvalid₂ : ∀ ap root₁ root₂ av p₁,
    P₂.FE.Valid (wit₂ ap) (ctx₂ root₁ root₂ av (macTag av ap msg) p₁))
  (hp : Stable P₁ s₁ wit₁ p) (hq : Stable P₂ s₂ wit₂ q)

local notation "ordinary" => jointCoinsEquiv P₁ P₂ ctx₁ ctx₂ Gav s₁ s₂ wit₁ wit₂ msg hvalid₁ hvalid₂

/-- Restrict the joint arithmetic bijection to the product of supported
side tapes. Both sides keep the same independent support factors. -/
noncomputable def jointCoinsEquivRestricted : (Real) ≃ (Sim) :=
  let e := ordinary
  (jointSubtype p q).trans ((e.subtypeEquiv (fun x =>
    (show p (e x).2.1.2 ↔ p x.2.1.2 from hp _ _ _ x.2.1).symm.and
      (show q (e x).2.2.2 ↔ q x.2.2.2 from hq _ _ _ x.2.2).symm)).trans (jointSubtype p q).symm)

local notation "restricted" => jointCoinsEquivRestricted P₁ P₂ ctx₁ ctx₂ Gav s₁ s₂ wit₁ wit₂ msg p q
   hvalid₁ hvalid₂ hp hq

private theorem forget_jointCoinsEquivRestricted (x : Real) :
    forgetSupport (restricted x) = ordinary (forgetSupport x) := rfl

include hvalid₁ hvalid₂ hp hq in
/-- Exact joint arithmetic simulation on supported tapes for arbitrary
postprocessing, including the ghost oracle's programmed openings. -/
theorem joint_simulation_restricted [Fintype Fmac] [Fintype B₁] [Fintype B₂]
    [Fintype Tr₁] [Fintype Tr₂] [Fintype (Subtype p)] [Fintype (Subtype q)]
    {V : Type} (observe : JointView P₁ P₂ (Fmac := Fmac) (nblk := nblk) → V) :
    StatClose 0
      (fun x : Real => observe (honestJoint P₁ P₂ ctx₁ ctx₂ Gav s₁ s₂ wit₁ wit₂ msg (forgetSupport x)))
      (fun x : Sim => observe (simJoint P₁ P₂ ctx₁ ctx₂ Gav s₁ s₂ (forgetSupport x))) := by
  refine statClose_of_equiv_pointwise _ _ restricted (fun x => ?_)
  rw [forget_jointCoinsEquivRestricted P₁ P₂ ctx₁ ctx₂ Gav s₁ s₂ wit₁ wit₂ msg p q
    hvalid₁ hvalid₂ hp hq x]
  exact congrArg observe (simJoint_jointCoinsEquiv P₁ P₂ ctx₁ ctx₂ Gav s₁ s₂ wit₁ wit₂ msg
    hvalid₁ hvalid₂ (forgetSupport x)).symm

section Experiment

open LfzkV1.ZkGhostTwoField

variable [Inhabited D]
variable {Q : ℕ} {V : Type}
variable (dist : TwoDistinguisher F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂
  Salt D Enc₁ Enc₂ Tr₁ Tr₂ Coin₁ Coin₂ LQ₁ LQ₂ RO₁ RO₂ Fmac nblk V Q)

local notation "Outer" => OuterCoins n₁ n₂ Salt D Enc₁ Enc₂ Fmac RO₁ LQ₁ Coin₁ RO₂ LQ₂ Coin₂

variable [Fintype Salt] [Fintype D] [DecidableEq D]
  [DecidableEq Enc₁] [DecidableEq Enc₂] [Fintype Enc₁] [Fintype Enc₂]
  [Fintype LQ₁] [Fintype LQ₂] [Fintype Coin₁] [Fintype Coin₂] [Fintype RO₁] [Fintype RO₂]
  [Fintype Fmac] [Fintype B₁] [Fintype B₂] [Fintype Tr₁] [Fintype Tr₂]
  [Fintype (Subtype p)] [Fintype (Subtype q)]

include hvalid₁ hvalid₂ in
/-- Mix the exact supported arithmetic law over all outer samples
in the two-field ghost experiments. -/
theorem ghost_simulation_restricted
    (hp' : ∀ side, Stable P₁ side wit₁ p) (hq' : ∀ side, Stable P₂ side wit₂ q) :
    StatClose 0
      (fun x : Real × Outer => ghostHonestExp P₁ P₂ ctx₁ ctx₂ dist wit₁ wit₂ msg
        (forgetSupport x.1, x.2))
      (fun x : Sim × Outer => ghostSimExp P₁ P₂ ctx₁ ctx₂ dist (forgetSupport x.1, x.2)) := by
  refine statClose_mix_equiv le_rfl _ _ (Equiv.prodComm Outer (Real)) (Equiv.prodComm Outer (Sim)) ?_
  rintro ⟨g, m⟩
  let sides := ghostSides P₁ P₂ g m
  exact joint_simulation_restricted P₁ P₂ ctx₁ ctx₂ g.1 sides.1 sides.2 wit₁ wit₂ msg p q
    hvalid₁ hvalid₂ (hp' sides.1) (hq' sides.2) (observe P₁ P₂ dist m.2.1 m.2.2)

end Experiment

end Joint

end LfzkV1.ZkGhostSubfield
