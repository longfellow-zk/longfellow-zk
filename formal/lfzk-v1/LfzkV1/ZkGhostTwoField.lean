import LfzkV1.ZkGhostSimulator
import LfzkV1.JointMerkleNonceV7
import Mathlib.Data.Finset.Sum

/-!
# The two-field experiment with independently sampled Merkle leaf labels

The only Merkle oracle calls counted in the error budget are the observer's
queries after it receives both proofs and all challenge functions. A single
query tree interleaves both typed Merkle oracles.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace LfzkV1.ZkGhostTwoField

open Finset Merkle.MH Merkle.RandomOracle
open LigeroFamily LigeroFamily.ZeroKnowledge
open LfzkV1.ZkAdaptiveV1 LfzkV1.CompiledLongfellowZk
  LfzkV1.CompiledLongfellowZkTwoField LfzkV1.JointMerkleHidingV7 LfzkV1.ZkGhostSimulator
open LfzkV1.CompiledLigeroZk (statClose_comp_equiv_left)

variable {F₁ E₁ F₂ E₂ : Type} [Field F₁] [Fintype F₁] [DecidableEq F₁] [Fintype E₁]
  [DecidableEq E₁] [Field F₂] [Fintype F₂] [DecidableEq F₂] [Fintype E₂] [DecidableEq E₂]
variable {r₁ w₁ n₁ nw₁ nq₁ reps₁ r₂ w₂ n₂ nw₂ nq₂ reps₂ : ℕ}
variable {Salt D Enc₁ Enc₂ Coin₁ Coin₂ LQ₁ LQ₂ Ctx₁ Ctx₂ Wit₁ Wit₂ B₁ B₂ Tr₁ Tr₂ RO₁ RO₂ : Type}
variable [Inhabited D] [DecidableEq LQ₁] [DecidableEq LQ₂]
variable {Fmac : Type} [Field Fmac] {nblk Q : ℕ} {V : Type}

variable (P₁ : Side F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ E₁ Salt D Enc₁ Coin₁ LQ₁ Ctx₁ Wit₁ B₁ Tr₁ RO₁)
variable (P₂ : Side F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂ E₂ Salt D Enc₂ Coin₂ LQ₂ Ctx₂ Wit₂ B₂ Tr₂ RO₂)
variable (ctx₁ : D → D → Fmac → Tag Fmac nblk → Ctx₁)
variable (ctx₂ : D → D → Fmac → Tag Fmac nblk → LProof F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ Salt D Tr₁ Coin₁ →
  Ctx₂)
variable (dist : TwoDistinguisher F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂
  Salt D Enc₁ Enc₂ Tr₁ Tr₂ Coin₁ Coin₂ LQ₁ LQ₂ RO₁ RO₂ Fmac nblk V Q)

abbrev Index (n₁ n₂ : ℕ) := Fin n₁ ⊕ Fin n₂
abbrev Schedule (RO LQ Coin : Type) := RO × (LQ → Coin) × Coin × Coin

abbrev ChallengeCoins (D Fmac RO₁ LQ₁ Coin₁ RO₂ LQ₂ Coin₂ : Type) :=
  (D × D → Fmac) × Schedule RO₁ LQ₁ Coin₁ × Schedule RO₂ LQ₂ Coin₂

abbrev MerkleCoins (n₁ n₂ : ℕ) (Salt D Enc₁ Enc₂ : Type) :=
  (Index n₁ n₂ → Salt) × (Enc₁ ⊕ Enc₂ → D) × (Index n₁ n₂ → D)

abbrev HonestTape :=
  Tag Fmac nblk × (B₁ × Tape P₁.C nw₁ nq₁ reps₁) × (B₂ × Tape P₂.C nw₂ nq₂ reps₂)

abbrev SimTape :=
  Tag Fmac nblk × (Tr₁ × Tape P₁.C nw₁ nq₁ reps₁) × (Tr₂ × Tape P₂.C nw₂ nq₂ reps₂)

variable (wit₁ : Tag Fmac nblk → Wit₁) (wit₂ : Tag Fmac nblk → Wit₂) (msg : Fin nblk → Fmac)

noncomputable def payloads (x : HonestTape P₁ P₂ (Fmac := Fmac) (nblk := nblk)) :
    (Fin n₁ → Col F₁ nw₁ nq₁ reps₁) × (Fin n₂ → Col F₂ nw₂ nq₂ reps₂) :=
  (colsOf (v1Oracle (P₁.FE.msgs (wit₁ x.1) x.2.1.1) x.2.1.2),
   colsOf (v1Oracle (P₂.FE.msgs (wit₂ x.1) x.2.2.1) x.2.2.2))

def separateColumns (x : HonestTape P₁ P₂ (Fmac := Fmac) (nblk := nblk)) : Prop :=
  Function.Injective (payloads P₁ P₂ wit₁ wit₂ x).1 ∧
    Function.Injective (payloads P₁ P₂ wit₁ wit₂ x).2

private def fixedSide {n : ℕ} {Coin LQ RO : Type} (g : Schedule RO LQ Coin)
    (values : ℕ → D) (salts : Fin n → Salt) : FixedSide n Salt D Coin LQ RO :=
  ⟨values, salts, g.1, g.2.1, g.2.2.1, g.2.2.2⟩

abbrev View := JointView P₁ P₂ (Fmac := Fmac) (nblk := nblk)

/-- Programs only addresses in the disclosed opening. This definition also
gives a total oracle on simulator coins that happen to repeat an open address. -/
noncomputable def disclosedOracle (H : Enc₁ ⊕ Enc₂ → D) (leaves : Index n₁ n₂ → D)
    (v : View P₁ P₂ (Fmac := Fmac) (nblk := nblk)) : Enc₁ ⊕ Enc₂ → D :=
  let p₁ := v.1.2.1
  let p₂ := v.1.2.2
  let opened := p₁.query.coordinates.disjSum p₂.query.coordinates
  let key (i : opened) : Enc₁ ⊕ Enc₂ := match i with
    | ⟨.inl j, hj⟩ =>
        let k : p₁.query.coordinates := ⟨j, inl_mem_disjSum.mp hj⟩
        .inl (P₁.Cod.leafEnc (p₁.merkleOpening.nonce k, p₁.opening k))
    | ⟨.inr j, hj⟩ =>
        let k : p₂.query.coordinates := ⟨j, inr_mem_disjSum.mp hj⟩
        .inr (P₂.Cod.leafEnc (p₂.merkleOpening.nonce k, p₂.opening k))
  program key (fun _ => True) H (leaves ∘ Subtype.val)

noncomputable def observe (H : Enc₁ ⊕ Enc₂ → D) (leaves : Index n₁ n₂ → D)
    (v : View P₁ P₂ (Fmac := Fmac) (nblk := nblk)) : V :=
  ((dist v.1 v.2).run (disclosedOracle P₁ P₂ H leaves v)).1

noncomputable def observerAtLabels (g : ChallengeCoins D Fmac RO₁ LQ₁ Coin₁ RO₂ LQ₂ Coin₂)
    (x : HonestTape P₁ P₂ (Fmac := Fmac) (nblk := nblk))
    (s : Index n₁ n₂ → Salt) (v₁ v₂ : ℕ → D) : Merkle.RandomOracle.Tree (Enc₁ ⊕ Enc₂) D V Q :=
  let v := honestJoint P₁ P₂ ctx₁ ctx₂ g.1 (fixedSide g.2.1 v₁ (s ∘ Sum.inl))
    (fixedSide g.2.2 v₂ (s ∘ Sum.inr)) wit₁ wit₂ msg x
  dist v.1 v.2

noncomputable def eagerProgrammedCore (g : ChallengeCoins D Fmac RO₁ LQ₁ Coin₁ RO₂ LQ₂ Coin₂)
    (x : HonestTape P₁ P₂ (Fmac := Fmac) (nblk := nblk))
    (s : Index n₁ n₂ → Salt) (H : Enc₁ ⊕ Enc₂ → D) : V :=
  let cols := payloads P₁ P₂ wit₁ wit₂ x
  let v₁ := commitLabels (P₁.Cod.withOracle (H ∘ Sum.inl)) n₁ (s ∘ Sum.inl) cols.1
  let v₂ := commitLabels (P₂.Cod.withOracle (H ∘ Sum.inr)) n₂ (s ∘ Sum.inr) cols.2
  ((observerAtLabels P₁ P₂ ctx₁ ctx₂ dist wit₁ wit₂ msg g x s v₁ v₂).run H).1

/-- Both sides' fixed coins, using the same sampled labels for the proof and observer. -/
def ghostSides (g : ChallengeCoins D Fmac RO₁ LQ₁ Coin₁ RO₂ LQ₂ Coin₂)
    (m : MerkleCoins n₁ n₂ Salt D Enc₁ Enc₂) :
    FixedSide n₁ Salt D Coin₁ LQ₁ RO₁ × FixedSide n₂ Salt D Coin₂ LQ₂ RO₂ :=
  (fixedSide g.2.1 (labels P₁.Cod (m.2.1 ∘ Sum.inl) (m.2.2 ∘ Sum.inl)) (m.1 ∘ Sum.inl),
   fixedSide g.2.2 (labels P₂.Cod (m.2.1 ∘ Sum.inr) (m.2.2 ∘ Sum.inr)) (m.1 ∘ Sum.inr))

noncomputable def ghostHonestCore (g : ChallengeCoins D Fmac RO₁ LQ₁ Coin₁ RO₂ LQ₂ Coin₂)
    (x : HonestTape P₁ P₂ (Fmac := Fmac) (nblk := nblk))
    (m : MerkleCoins n₁ n₂ Salt D Enc₁ Enc₂) : V :=
  let sides := ghostSides P₁ P₂ g m
  observe P₁ P₂ dist m.2.1 m.2.2 (honestJoint P₁ P₂ ctx₁ ctx₂ g.1 sides.1 sides.2 wit₁ wit₂ msg x)

noncomputable def ghostSimCore (g : ChallengeCoins D Fmac RO₁ LQ₁ Coin₁ RO₂ LQ₂ Coin₂)
    (x : SimTape P₁ P₂ (Fmac := Fmac) (nblk := nblk))
    (m : MerkleCoins n₁ n₂ Salt D Enc₁ Enc₂) : V :=
  let sides := ghostSides P₁ P₂ g m
  observe P₁ P₂ dist m.2.1 m.2.2 (simJoint P₁ P₂ ctx₁ ctx₂ g.1 sides.1 sides.2 x)


private theorem honestProof_salt_congr {F E Salt D Enc Coin LQ Ctx Wit B Tr RO : Type}
    [Field F] [Fintype E] {r w n nw nq reps : ℕ}
    (P : Side F r w n nw nq reps E Salt D Enc Coin LQ Ctx Wit B Tr RO) (κ : Ctx)
    (wit : Wit) (ρ : Tape P.C nw nq reps) (b : B) (salt salt' : Fin n → Salt)
    (Gr : RO) (c i : Coin) (vals : ℕ → D)
    (h : ∀ j ∈ (P.dec₂ i).coordinates, salt j = salt' j) :
    honestProof P κ wit ρ b salt Gr c i vals = honestProof P κ wit ρ b salt' Gr c i vals := by
  dsimp only [honestProof, ZkGhostProgramming.honestProofAt]
  congr
  funext j
  exact h j.val j.property

section Fixed

variable (g : ChallengeCoins D Fmac RO₁ LQ₁ Coin₁ RO₂ LQ₂ Coin₂)
variable (x : HonestTape P₁ P₂ (Fmac := Fmac) (nblk := nblk))
variable (H : Enc₁ ⊕ Enc₂ → D) (leaves : Index n₁ n₂ → D)

private def disclosed : Finset (Index n₁ n₂) :=
  (P₁.dec₂ g.2.1.2.2.2).coordinates.disjSum (P₂.dec₂ g.2.2.2.2.2).coordinates

private noncomputable def ghostView (s : Index n₁ n₂ → Salt) :
    View P₁ P₂ (Fmac := Fmac) (nblk := nblk) :=
  let sides := ghostSides P₁ P₂ g (s, H, leaves)
  honestJoint P₁ P₂ ctx₁ ctx₂ g.1 sides.1 sides.2 wit₁ wit₂ msg x

private theorem ghostView_salt_congr (s s' : Index n₁ n₂ → Salt)
    (h : ∀ i ∈ disclosed P₁ P₂ g, s i = s' i) :
    ghostView P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg g x H leaves s =
      ghostView P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg g x H leaves s' := by
  dsimp [ghostView, ghostSides, fixedSide, honestJoint]
  have h₁ : ∀ j ∈ (P₁.dec₂ g.2.1.2.2.2).coordinates, (s ∘ Sum.inl) j = (s' ∘ Sum.inl) j :=
    fun j hj => h (.inl j) (inl_mem_disjSum.mpr hj)
  have h₂ : ∀ j ∈ (P₂.dec₂ g.2.2.2.2.2).coordinates, (s ∘ Sum.inr) j = (s' ∘ Sum.inr) j :=
    fun j hj => h (.inr j) (inr_mem_disjSum.mpr hj)
  simp only [honestProof_salt_congr P₁ _ _ _ _ _ _ _ _ _ _ h₁,
    honestProof_salt_congr P₂ _ _ _ _ _ _ _ _ _ _ h₂]

private theorem disclosedOracle_ghostView (s : Index n₁ n₂ → Salt) :
    disclosedOracle P₁ P₂ H leaves (ghostView P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg g x H leaves s) =
      let cols := payloads P₁ P₂ wit₁ wit₂ x
      openedOracle (leafAddress P₁.Cod P₂.Cod cols.1 cols.2) (disclosed P₁ P₂ g) H leaves
        (fun j => s j.val) := by
  unfold disclosedOracle openedOracle
  refine congrArg (fun key : disclosed P₁ P₂ g → Enc₁ ⊕ Enc₂ =>
    program key (fun _ => True) H (leaves ∘ Subtype.val)) ?_
  funext j
  rcases j with ⟨i | i, hi⟩ <;> rfl

/-- The coupling at fixed arithmetic tapes. On tapes with distinct columns
the only error is hitting an unopened salt in the ghost observer's trace. -/
private theorem fixed_hiding [Fintype Salt] [Nonempty Salt]
    (leaf₁ : Function.Injective P₁.Cod.leafEnc) (leaf₂ : Function.Injective P₂.Cod.leafEnc)
    (node₁ : ∀ children sm, P₁.Cod.nodeEnc children ≠ P₁.Cod.leafEnc sm)
    (node₂ : ∀ children sm, P₂.Cod.nodeEnc children ≠ P₂.Cod.leafEnc sm)
    (distinct : separateColumns P₁ P₂ wit₁ wit₂ x) :
    StatClose ((Q : ℚ) / Fintype.card Salt)
      (fun s : Index n₁ n₂ → Salt =>
        let cols := payloads P₁ P₂ wit₁ wit₂ x
        let address := fun i => leafAddress P₁.Cod P₂.Cod cols.1 cols.2 i (s i)
        eagerProgrammedCore P₁ P₂ ctx₁ ctx₂ dist wit₁ wit₂ msg g x s
          (swapEquiv address (H, leaves)).1)
      (fun s : Index n₁ n₂ → Salt =>
        ghostHonestCore P₁ P₂ ctx₁ ctx₂ dist wit₁ wit₂ msg g x (s, H, leaves)) := by
  classical
  letI : DecidableEq (Index n₁ n₂) := instDecidableEqSum
  let cols := payloads P₁ P₂ wit₁ wit₂ x
  let address := leafAddress P₁.Cod P₂.Cod cols.1 cols.2
  let opened := disclosed P₁ P₂ g
  let view := ghostView P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg g x H leaves
  let fill (revealed : opened → Salt) (i : Index n₁ n₂) :=
    if hi : i ∈ opened then revealed ⟨i, hi⟩ else Classical.choice (inferInstance : Nonempty Salt)
  let observer (revealed : opened → Salt) :=
    let v := view (fill revealed)
    dist v.1 v.2
  have hi : Function.Injective (Function.uncurry address) :=
    leafAddress_injective _ _ _ _ leaf₁ leaf₂ distinct.1 distinct.2
  have htree (s : Index n₁ n₂ → Salt) :
      observer (fun i => s i.val) = dist (view s).1 (view s).2 := by
    have hv := ghostView_salt_congr P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg g x H leaves
      (fill fun i => s i.val) s (fun i hs => by simp [fill, opened, hs])
    exact congrArg (fun v : View P₁ P₂ (Fmac := Fmac) (nblk := nblk) => dist v.1 v.2) hv
  have h := statClose_map Prod.fst
    (fixed_observer_close opened address hi H leaves observer)
  intro test
  specialize h test
  have real_eq (s : Index n₁ n₂ → Salt) :
      ((observer (fun i => s i.val)).run (swapEquiv (fun i => address i (s i)) (H, leaves)).1).1 =
        eagerProgrammedCore P₁ P₂ ctx₁ ctx₂ dist wit₁ wit₂ msg g x s
          (swapEquiv (fun i => address i (s i)) (H, leaves)).1 := by
    have hn : Function.Injective (fun i => address i (s i)) :=
      fun i j he => congrArg Prod.fst (@hi (i, s i) (j, s j) he)
    obtain ⟨hl, hr⟩ := coupled_labels_eq P₁.Cod P₂.Cod s cols.1 cols.2 H leaves node₁ node₂ hn
    rw [htree]
    dsimp only [eagerProgrammedCore, observerAtLabels, view, ghostView, ghostSides, Prod.fst, Prod.snd]
    change _ = _
    rw [hl, hr]
  have sim_eq (s : Index n₁ n₂ → Salt) :
      ((observer (fun i => s i.val)).run (openedOracle address opened H leaves (fun i => s i.val))).1 =
        ghostHonestCore P₁ P₂ ctx₁ ctx₂ dist wit₁ wit₂ msg g x (s, H, leaves) := by
    rw [htree, ← disclosedOracle_ghostView P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg g x H leaves]
    rfl
  simpa only [Function.comp_def, real_eq, sim_eq] using h

end Fixed


abbrev OuterCoins (n₁ n₂ : ℕ) (Salt D Enc₁ Enc₂ Fmac RO₁ LQ₁ Coin₁ RO₂ LQ₂ Coin₂ : Type) :=
  ChallengeCoins D Fmac RO₁ LQ₁ Coin₁ RO₂ LQ₂ Coin₂ × MerkleCoins n₁ n₂ Salt D Enc₁ Enc₂

section Bound

local notation "Outer" => OuterCoins n₁ n₂ Salt D Enc₁ Enc₂ Fmac RO₁ LQ₁ Coin₁ RO₂ LQ₂ Coin₂
local notation "Honest" => HonestTape P₁ P₂ (Fmac := Fmac) (nblk := nblk)
local notation "Simulated" => SimTape P₁ P₂ (Fmac := Fmac) (nblk := nblk)

noncomputable def eagerProgrammedExp (ω : Honest × Outer) : V :=
  eagerProgrammedCore P₁ P₂ ctx₁ ctx₂ dist wit₁ wit₂ msg ω.2.1 ω.1 ω.2.2.1 ω.2.2.2.1

noncomputable def ghostHonestExp (ω : Honest × Outer) : V :=
  ghostHonestCore P₁ P₂ ctx₁ ctx₂ dist wit₁ wit₂ msg ω.2.1 ω.1 ω.2.2

noncomputable def ghostSimExp (ω : Simulated × Outer) : V :=
  ghostSimCore P₁ P₂ ctx₁ ctx₂ dist ω.2.1 ω.1 ω.2.2

private def groupSalt (G S H Y : Type) : (G × H × Y) × S ≃ G × S × H × Y where
  toFun ω := (ω.1.1, ω.2, ω.1.2)
  invFun ω := ((ω.1, ω.2.2), ω.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable def swapOuter (x : Honest) : Outer ≃ Outer :=
  let cols := payloads P₁ P₂ wit₁ wit₂ x
  (Equiv.refl _).prodCongr <| Equiv.prodCongrRight fun salts =>
    swapEquiv (fun i => leafAddress P₁.Cod P₂.Cod cols.1 cols.2 i (salts i))

variable [Fintype Salt] [Nonempty Salt] [Fintype D] [DecidableEq D]
  [DecidableEq Enc₁] [DecidableEq Enc₂] [Fintype Enc₁] [Fintype Enc₂]
  [Fintype LQ₁] [Fintype LQ₂] [Fintype Coin₁] [Fintype Coin₂] [Fintype RO₁] [Fintype RO₂]
  [Fintype Fmac] [Fintype B₁] [Fintype B₂] [Fintype Tr₁] [Fintype Tr₂]

/-- The single joint hiding charge for any finite sampler of the honest
arithmetic coins. The duplicate payload probability is charged once. -/
theorem joint_hiding_sampled {X : Type} [Fintype X] (draw : X → Honest)
    (leaf₁ : Function.Injective P₁.Cod.leafEnc) (leaf₂ : Function.Injective P₂.Cod.leafEnc)
    (node₁ : ∀ children sm, P₁.Cod.nodeEnc children ≠ P₁.Cod.leafEnc sm)
    (node₂ : ∀ children sm, P₂.Cod.nodeEnc children ≠ P₂.Cod.leafEnc sm) :
    StatClose ((Q : ℚ) / Fintype.card Salt +
        probOf draw (fun x => ¬ separateColumns P₁ P₂ wit₁ wit₂ x))
      (fun p : X × Outer => eagerProgrammedExp P₁ P₂ ctx₁ ctx₂ dist wit₁ wit₂ msg (draw p.1, p.2))
      (fun p : X × Outer => ghostHonestExp P₁ P₂ ctx₁ ctx₂ dist wit₁ wit₂ msg (draw p.1, p.2)) := by
  apply statClose_mix_bad (separateColumns P₁ P₂ wit₁ wit₂ ∘ draw) _ (by positivity)
    (fun x o => eagerProgrammedExp P₁ P₂ ctx₁ ctx₂ dist wit₁ wit₂ msg (draw x, o))
    (fun x o => ghostHonestExp P₁ P₂ ctx₁ ctx₂ dist wit₁ wit₂ msg (draw x, o))
  intro a distinct
  let x := draw a
  let e := swapOuter P₁ P₂ wit₁ wit₂ x
  apply (statClose_comp_equiv_left _ _ e).mp
  refine statClose_mix_equiv (by positivity) _ _ (groupSalt _ _ _ _) (groupSalt _ _ _ _) ?_
  rintro ⟨g, H, leaves⟩
  exact fixed_hiding P₁ P₂ ctx₁ ctx₂ dist wit₁ wit₂ msg g x H leaves leaf₁ leaf₂ node₁ node₂ distinct

end Bound

end LfzkV1.ZkGhostTwoField
