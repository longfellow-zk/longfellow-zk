import TranscriptV2.StrandOracle

/-! Exact finite-sampler disintegration. A balanced challenge projection
can be represented by its challenge and independent residual coins while
retaining the entire original answer. In particular rejected/unused bytes
are reconstructed; they are not asserted independent in their original
representation. A partial rejection sampler is padded only on its failure
branch; successful runtime samples and all original bytes are unchanged. -/
noncomputable section
namespace TranscriptV2.StrandSampling
open Finset
open scoped Classical

variable {Coins Value Parent : Type} [Fintype Coins]

/-- Extra mathematical coins are read only when the real sampler failed.
The protocol still rejects that branch. This permits uniform-coordinate
counting without asserting an impossible total prime-field projection from
a fixed number of binary bits. -/
def complete (decode : Coins → Option Value) (coins : Coins × Value) : Value :=
  (decode coins.1).getD coins.2

omit [Fintype Coins] in
theorem complete_success (decode : Coins → Option Value) (coins : Coins) (value fallback : Value)
    (success : decode coins = some value) : complete decode (coins,fallback) = value := by
  simp only [complete,success,Option.getD_some]

/-- Equal successful fibers suffice: the failure branch is given an
independent uniform dummy value, while retaining its complete original input. -/
theorem complete_fiber [Fintype Value] (decode : Coins → Option Value) (fiber : ℕ)
    (uniform : ∀ value, (univ.filter fun coins => decode coins = some value).card = fiber)
    (value : Value) :
    (univ.filter fun coins : Coins × Value => complete decode coins = value).card =
      fiber*Fintype.card Value + (univ.filter fun coins => decode coins = none).card := by
  let accepted := univ.filter fun coins => decode coins = some value
  let failed := univ.filter fun coins => decode coins = none
  have sets : (univ.filter fun coins : Coins × Value => complete decode coins = value) =
      (accepted ×ˢ univ) ∪ (failed ×ˢ {value}) := by
    ext coins
    simp only [accepted,failed,mem_union,mem_product,mem_filter,mem_univ,mem_singleton,true_and,and_true]
    cases result : decode coins.1 with
    | none => simp [complete,result]
    | some output => simp [complete,result]
  have separate : Disjoint (accepted ×ˢ (univ : Finset Value)) (failed ×ˢ {value}) := by
    apply disjoint_left.mpr
    intro coins first second
    have good := (mem_filter.mp (mem_product.mp first).1).2
    have missing := (mem_filter.mp (mem_product.mp second).1).2
    rw [missing] at good
    contradiction
  rw [sets,card_union_of_disjoint separate,card_product,card_product,card_univ,card_singleton,mul_one]
  rw [show accepted.card = fiber from uniform value]

/-- Equal fibers are exactly the finite uniform-projection law. The residual
coordinate is a reindexing of the full answer, not a second PRF generator. -/
def answerEquiv (decode : Coins → Value) (fiber : ℕ)
    (uniform : ∀ value, Fintype.card {coins // decode coins = value} = fiber) :
    Coins ≃ Value × Fin fiber :=
  (Equiv.sigmaFiberEquiv decode).symm.trans
    (Equiv.sigmaEquivProdOfEquiv fun value => Fintype.equivFinOfCardEq (uniform value))

@[simp] theorem answerEquiv_value (decode : Coins → Value) (fiber : ℕ)
    (uniform : ∀ value, Fintype.card {coins // decode coins = value} = fiber) (coins : Coins) :
    (answerEquiv decode fiber uniform coins).1 = decode coins := rfl

/-- Fixing both coordinates recovers every raw byte of the oracle answer. -/
theorem answer_reconstruct (decode : Coins → Value) (fiber : ℕ)
    (uniform : ∀ value, Fintype.card {coins // decode coins = value} = fiber) (coins : Coins) :
    (answerEquiv decode fiber uniform).symm
      (decode coins,(answerEquiv decode fiber uniform coins).2) = coins :=
  (answerEquiv decode fiber uniform).symm_apply_apply coins

def oracleEquiv (decode : Coins → Value) (fiber : ℕ)
    (uniform : ∀ value, Fintype.card {coins // decode coins = value} = fiber) :
    (Parent → Coins) ≃ (Parent → Value) × (Parent → Fin fiber) where
  toFun H := (fun p => (answerEquiv decode fiber uniform (H p)).1,
    fun p => (answerEquiv decode fiber uniform (H p)).2)
  invFun pair p := (answerEquiv decode fiber uniform).symm (pair.1 p,pair.2 p)
  left_inv H := by
    funext p
    exact (answerEquiv decode fiber uniform).symm_apply_apply (H p)
  right_inv pair := by
    apply Prod.ext
    · funext p
      exact congrArg Prod.fst ((answerEquiv decode fiber uniform).apply_symm_apply (pair.1 p,pair.2 p))
    · funext p
      exact congrArg Prod.snd ((answerEquiv decode fiber uniform).apply_symm_apply (pair.1 p,pair.2 p))

/-- Independent residual oracle coins are derived by an equivalence of
uniform tables. They are not a strengthened sampler/oracle hypothesis. -/
theorem oracle_ratio_eq [Fintype Parent] [Fintype Value] (decode : Coins → Value) (fiber : ℕ)
    (uniform : ∀ value, Fintype.card {coins // decode coins = value} = fiber)
    (event : (Parent → Value) × (Parent → Fin fiber) → Prop) :
    ((univ.filter fun H => event (oracleEquiv decode fiber uniform H)).card : ℚ) /
        Fintype.card (Parent → Coins) =
      ((univ.filter event).card : ℚ) /
        Fintype.card ((Parent → Value) × (Parent → Fin fiber)) := by
  have hc : (univ.filter fun H => event (oracleEquiv decode fiber uniform H)).card =
      (univ.filter event).card := Finset.card_equiv (oracleEquiv decode fiber uniform) (fun _ => by simp)
  rw [hc,Fintype.card_congr (oracleEquiv decode fiber uniform)]

end TranscriptV2.StrandSampling
