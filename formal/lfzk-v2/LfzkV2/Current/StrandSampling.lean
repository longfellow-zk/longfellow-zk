import LfzkV2.Current.BalancedDecoder
import TranscriptV2.StrandSampling
import TranscriptV2.StrandVerifier

/-! Connect the accepted uniform-rejection-sampler assumption to the local
runtime bounds. Independent analysis coins complete failed samples and supply
unused ideal role factors. Physical reads retain their original failure or
successful joint block; those analysis coins cannot change acceptance. -/
noncomputable section
namespace LfzkV2.Current.StrandSampling
open Finset
open scoped Classical

variable {Coins Value : Type} [Fintype Coins] [Fintype Value]

def completedDecoder (decode : Coins → Option Value) (fiber : ℕ)
    (uniform : ∀ value, (univ.filter fun coins => decode coins = some value).card = fiber) :
    BalancedDecoder (Coins × Value) Value :=
  BalancedDecoder.of_fibers (TranscriptV2.StrandSampling.complete decode)
    (fiber*Fintype.card Value + (univ.filter fun coins => decode coins = none).card)
    (TranscriptV2.StrandSampling.complete_fiber decode fiber uniform)

/-- The ideal coordinate equals the actual value on every accepting read.
No assumption is made about discarded bytes being independent of that value. -/
theorem completedDecoder_agrees (decode : Coins → Option Value) (fiber : ℕ)
    (uniform : ∀ value, (univ.filter fun coins => decode coins = some value).card = fiber)
    (coins : Coins) (value fallback : Value) (accepted : decode coins = some value) :
    (completedDecoder decode fiber uniform).decode (coins,fallback) = value :=
  TranscriptV2.StrandSampling.complete_success decode coins value fallback accepted

/-- Completing a partial sampler with an independent fallback leaves one
raw-stream-sized residual fiber per value. Its size is independent of the
field, the round's block width, and the rejection probability. -/
theorem completed_fiber [Nonempty Value] (decode : Coins → Option Value) (fiber : ℕ)
    (uniform : ∀ value, (univ.filter fun coins => decode coins = some value).card = fiber)
    (value : Value) :
    (univ.filter fun coins : Coins × Value => TranscriptV2.StrandSampling.complete decode coins = value).card =
      Fintype.card Coins := by
  rw [TranscriptV2.StrandSampling.complete_fiber decode fiber uniform]
  have balanced := (completedDecoder decode fiber uniform).balanced
  simp only [Fintype.card_prod] at balanced
  exact Nat.eq_of_mul_eq_mul_right (Fintype.card_pos : 0 < Fintype.card Value) balanced

variable {Answer Unused : Type} [Nonempty Value]

/-- Auxiliary queries have no protocol sampler. Their ideal coordinate is
unused padding, and the residual coordinate retains the original raw row. -/
def auxiliaryEquiv : (Coins × Answer) ≃ Answer × Fin (Fintype.card Coins) :=
  (Equiv.prodComm Coins Answer).trans
    (Equiv.prodCongr (Equiv.refl Answer) (Fintype.equivFin Coins))

/-- Project the whole block read by this round into the existing common
answer alphabet. Unused role coordinates are independent analysis coins;
they are not extra PRF reads. The inverse retains every original raw byte.
`Value` must be the joint block, not separate marginal samplers. -/
def componentEquiv (factor : Answer ≃ Value × Unused) (decode : Coins → Option Value) (fiber : ℕ)
    (uniform : ∀ value, (univ.filter fun coins => decode coins = some value).card = fiber) :
    (Coins × Answer) ≃ Answer × Fin (Fintype.card Coins) :=
  let split := TranscriptV2.StrandSampling.answerEquiv (TranscriptV2.StrandSampling.complete decode)
    (Fintype.card Coins) (fun value => by
      simpa only [Fintype.card_subtype] using completed_fiber decode fiber uniform value)
  (Equiv.prodCongr (Equiv.refl Coins) factor).trans
    ((Equiv.prodAssoc Coins Value Unused).symm.trans
      ((Equiv.prodCongr split (Equiv.refl Unused)).trans
        ((Equiv.prodAssoc Value (Fin (Fintype.card Coins)) Unused).trans
          ((Equiv.prodCongr (Equiv.refl Value) (Equiv.prodComm (Fin (Fintype.card Coins)) Unused)).trans
            ((Equiv.prodAssoc Value Unused (Fin (Fintype.card Coins))).symm.trans
              (Equiv.prodCongr factor.symm (Equiv.refl _)))))))

theorem componentEquiv_apply (factor : Answer ≃ Value × Unused) (decode : Coins → Option Value) (fiber : ℕ)
    (uniform : ∀ value, (univ.filter fun coins => decode coins = some value).card = fiber)
    (coins : Coins) (padding : Answer) :
    (componentEquiv factor decode fiber uniform (coins,padding)).1 =
      factor.symm (TranscriptV2.StrandSampling.complete decode (coins,(factor padding).1),(factor padding).2) := rfl

/-- Successful runtime reads retain exactly their decoded joint block.
Unused factors are unchanged, including all coordinates for other roles. -/
theorem componentEquiv_success (factor : Answer ≃ Value × Unused) (decode : Coins → Option Value) (fiber : ℕ)
    (uniform : ∀ value, (univ.filter fun coins => decode coins = some value).card = fiber)
    (coins : Coins) (value : Value) (padding : Answer) (accepted : decode coins = some value) :
    factor (componentEquiv factor decode fiber uniform (coins,padding)).1 = (value,(factor padding).2) := by
  rw [componentEquiv_apply,Equiv.apply_symm_apply,
    TranscriptV2.StrandSampling.complete_success decode coins value (factor padding).1 accepted]

/-- In the reindexed execution, every successful physical sampler gives
the ideal role value. Failure padding cannot turn a rejecting read into an
accepting one; the complete verifier must still check sampler success. -/
theorem componentEquiv_inverse_success (factor : Answer ≃ Value × Unused)
    (decode : Coins → Option Value) (fiber : ℕ)
    (uniform : ∀ value, (univ.filter fun coins => decode coins = some value).card = fiber)
    (challenge : Answer) (residual : Fin (Fintype.card Coins)) (value : Value)
    (accepted : decode ((componentEquiv factor decode fiber uniform).symm (challenge,residual)).1 = some value) :
    (factor challenge).1 = value := by
  let input := (componentEquiv factor decode fiber uniform).symm (challenge,residual)
  have same := componentEquiv_success factor decode fiber uniform input.1 value input.2 accepted
  change factor (componentEquiv factor decode fiber uniform input).1 = _ at same
  rw [show componentEquiv factor decode fiber uniform input = (challenge,residual) from
    (componentEquiv factor decode fiber uniform).apply_symm_apply _] at same
  exact congrArg Prod.fst same

section Reads
open Merkle.RandomOracle
variable {Index Block : Type} {fuel : ℕ}

/-- A physical round supplies only its own joint block. Coordinates for
other roles are placeholders in the common verifier alphabet, not additional
samples. Their fixed values do not stand in for a failed physical read. -/
def normalize (factor : Answer ≃ Value × Unused) (fallback answer : Answer) : Answer :=
  factor.symm ((factor answer).1,(factor fallback).2)

omit [Fintype Value] [Nonempty Value] in
theorem normalize_value (factor : Answer ≃ Value × Unused) (fallback answer : Answer) :
    (factor (normalize factor fallback answer)).1 = (factor answer).1 := by
  simp only [normalize,Equiv.apply_symm_apply]

/-- The physical reader preserves failure and embeds successful values in
the runtime's common alphabet. Its raw query trace is unchanged. -/
def read (factor : Answer ≃ Value × Unused) (fallback : Answer)
    (sampler : Tree Index Block (Option Value) fuel) : Tree Index Block (Option Answer) fuel :=
  sampler.map (Option.map fun value => factor.symm (value,(factor fallback).2))

omit [Fintype Value] [Nonempty Value] in
theorem read_trace (factor : Answer ≃ Value × Unused) (fallback : Answer)
    (sampler : Tree Index Block (Option Value) fuel) (stream : Index → Block) :
    ((read factor fallback sampler).run stream).2 = (sampler.run stream).2 := by
  rw [read,Tree.run_map]

omit [Fintype Value] [Nonempty Value] in
theorem read_failed (factor : Answer ≃ Value × Unused) (fallback : Answer)
    (sampler : Tree Index Block (Option Value) fuel) (stream : Index → Block) :
    ((read factor fallback sampler).run stream).1 = none ↔ (sampler.run stream).1 = none := by
  simp only [read,Tree.run_map,Option.map_eq_none_iff]

/-- Reindexing retains every raw block. On success the physical reader
equals the normalized ideal answer; its other role coordinates are never
mistaken for physically generated randomness. -/
theorem read_inverse_success [Fintype Index] [Fintype Block]
    (factor : Answer ≃ Value × Unused) (fallback : Answer)
    (sampler : Tree Index Block (Option Value) fuel) (fiber : ℕ)
    (uniform : ∀ value, (univ.filter fun stream => (sampler.run stream).1 = some value).card = fiber)
    (challenge : Answer) (residual : Fin (Fintype.card (Index → Block)))
    (value : Value)
    (success : (sampler.run
      ((componentEquiv factor (fun stream => (sampler.run stream).1) fiber uniform).symm
        (challenge,residual)).1).1 = some value) :
    ((read factor fallback sampler).run
      ((componentEquiv factor (fun stream => (sampler.run stream).1) fiber uniform).symm
        (challenge,residual)).1).1 = some (normalize factor fallback challenge) := by
  have same := componentEquiv_inverse_success factor (fun stream => (sampler.run stream).1)
    fiber uniform challenge residual value success
  simp only [read,Tree.run_map,success,Option.map_some,normalize,same]

end Reads

section Oracles
open Merkle.RandomOracle
variable {Point Link Raw Challenge Residual Out : Type}

/-- Each ordinary query selects its own joint role sampler. Reindexing its
whole answer preserves the node digest and all remaining raw randomness.
The resulting two oracle tables are independent product coordinates, not
additional protocol oracles. The split may depend on the bound query input,
but cannot depend on that query's answer. -/
def oracleEquiv (split : Point → Raw ≃ Challenge × Residual) :
    (Point → Link × Raw) ≃ (Point → Link × Challenge) × (Point → Residual) where
  toFun H := (fun point => ((H point).1,(split point (H point).2).1),
    fun point => (split point (H point).2).2)
  invFun pair point := ((pair.1 point).1,(split point).symm ((pair.1 point).2,pair.2 point))
  left_inv H := by
    funext point
    exact Prod.ext rfl ((split point).symm_apply_apply (H point).2)
  right_inv pair := by
    apply Prod.ext
    · funext point
      exact Prod.ext rfl (congrArg Prod.fst ((split point).apply_symm_apply ((pair.1 point).2,pair.2 point)))
    · funext point
      exact congrArg Prod.snd ((split point).apply_symm_apply ((pair.1 point).2,pair.2 point))

theorem oracleEquiv_link (split : Point → Raw ≃ Challenge × Residual)
    (H : Point → Link × Raw) (point : Point) :
    (((oracleEquiv split) H).1 point).1 = (H point).1 := rfl

/-- The actual query program receives its reconstructed raw answer. In
particular it can still inspect rejected and unused bytes. Fixing the
residual table leaves an ordinary adaptive program over uniform challenges. -/
def reindex (split : Point → Raw ≃ Challenge × Residual) (residual : Point → Residual) :
    {fuel : ℕ} → Tree Point (Link × Raw) Out fuel → Tree Point (Link × Challenge) Out fuel
  | _, .done out => .done out
  | _, .query point next => .query point fun answer =>
      reindex split residual (next (answer.1,(split point).symm (answer.2,residual point)))

/-- Output equality applies to arbitrary retained observations, including
raw traces and extraction cuts. Query names and their order are unchanged. -/
theorem reindex_run (split : Point → Raw ≃ Challenge × Residual) (residual : Point → Residual)
    {fuel : ℕ} (tree : Tree Point (Link × Raw) Out fuel) (H : Point → Link × Challenge) :
    ((reindex split residual tree).run H).1 = (tree.run ((oracleEquiv split).symm (H,residual))).1 ∧
      ((reindex split residual tree).run H).2.map Prod.fst =
        (tree.run ((oracleEquiv split).symm (H,residual))).2.map Prod.fst := by
  induction tree with
  | done out => exact ⟨rfl,rfl⟩
  | query point next ih =>
      have later := ih ((H point).1,(split point).symm ((H point).2,residual point))
      exact ⟨later.1,congrArg (List.cons point) later.2⟩

theorem reindex_seen [DecidableEq Point] (split : Point → Raw ≃ Challenge × Residual)
    (residual : Point → Residual) {fuel : ℕ} (tree : Tree Point (Link × Raw) Out fuel)
    (H : Point → Link × Challenge) :
    TranscriptV2.seen (reindex split residual tree) H =
      TranscriptV2.seen tree ((oracleEquiv split).symm (H,residual)) := by
  exact congrArg List.toFinset (reindex_run split residual tree H).2

theorem reindex_firstOfTwo [DecidableEq Point] (split : Point → Raw ≃ Challenge × Residual)
    (residual : Point → Residual) {fuel : ℕ} (tree : Tree Point (Link × Raw) Out fuel)
    (H : Point → Link × Challenge) (parent child : Point) :
    Bcs.TotalOracle.firstOfTwo (reindex split residual tree) H parent child =
      Bcs.TotalOracle.firstOfTwo tree ((oracleEquiv split).symm (H,residual)) parent child := by
  induction tree with
  | done out => rfl
  | query point next ih =>
      simp only [reindex,Bcs.TotalOracle.firstOfTwo]
      split_ifs <;> first | rfl | exact ih _

/-- A bijection of full oracle tables proves the joint observation law.
It retains correlations between the raw program, its cut and verifier
replay; uniformity of individual field samples alone would not suffice. -/
theorem oracle_law [Fintype Point] [Fintype Link] [Fintype Raw] [Fintype Challenge] [Fintype Residual]
    (split : Point → Raw ≃ Challenge × Residual) (event : (Point → Link × Raw) → Prop) :
    Bcs.FiniteProbability.density event =
      Bcs.FiniteProbability.density (fun pair => event ((oracleEquiv split).symm pair)) :=
  (Bcs.FiniteProbability.density_equiv (oracleEquiv split).symm event).symm

end Oracles

section Tagged
variable {P Aux : Type} {Values Remainders : P → Type}
variable [∀ point, Fintype (Values point)] [∀ point, Nonempty (Values point)]
variable (factor : (point : P) → Answer ≃ Values point × Remainders point)
variable (decode : (point : P) → Coins → Option (Values point)) (fiber : P → ℕ)
variable (uniform : ∀ point value,
  (univ.filter fun coins => decode point coins = some value).card = fiber point)

/-- Typed addresses expose their own joint challenge block. Auxiliary
addresses retain their complete physical row in the residual coordinate;
their independent ideal coordinate is never consumed by a protocol. -/
def taggedEquiv : P ⊕ Aux → (Coins × Answer) ≃ Answer × Fin (Fintype.card Coins)
  | .inl point => componentEquiv (factor point) (decode point) (fiber point) (uniform point)
  | .inr _ => auxiliaryEquiv

theorem taggedEquiv_typed (point : P) :
    taggedEquiv (Aux := Aux) factor decode fiber uniform (.inl point) =
      componentEquiv (factor point) (decode point) (fiber point) (uniform point) := rfl

theorem taggedEquiv_auxiliary (aux : Aux) :
    taggedEquiv factor decode fiber uniform (.inr aux) =
      auxiliaryEquiv (Coins := Coins) (Answer := Answer) := rfl

/-- An accepted physical block equals its ideal role coordinate. This
applies after conditioning on any residual table, including one retaining
all the prover's otherwise unused raw bytes. -/
theorem taggedEquiv_inverse_success (point : P) (challenge : Answer)
    (residual : Fin (Fintype.card Coins)) (value : Values point)
    (accepted : decode point
      ((taggedEquiv (Aux := Aux) factor decode fiber uniform (.inl point)).symm
        (challenge,residual)).1 = some value) :
    (factor point challenge).1 = value :=
  componentEquiv_inverse_success (factor point) (decode point) (fiber point) (uniform point)
    challenge residual value accepted

end Tagged

section Physical
open Merkle.RandomOracle TranscriptV2
variable {P : Type} {Values Remainders : P → Type} {blocks : ℕ}
variable (history : P → Strand.History) (fallback : Answer)
variable (factor : (point : P) → Answer ≃ Values point × Remainders point)
variable (sampler : (point : P) → Tree Strand.Word Strand.Digest (Option (Values point)) blocks)

/-- Every round uses its own joint decoder, possibly with a different
field or block width. Once its actual PRF row has been identified by the
strand coupling, an accepting read supplies exactly the ideal role value.
The row equality is a separate deterministic coupling lemma; uniformity
alone would not justify replacing a stream reserved by an early query. -/
theorem oracle_on_success (SHA : Strand.Oracle) (point : P)
    [Fintype (Values point)] [Nonempty (Values point)] (fiber : ℕ)
    (uniform : ∀ value,
      (univ.filter fun stream => ((sampler point).run stream).1 = some value).card = fiber)
    (challenge : Answer) (residual : Fin (Fintype.card (Strand.Word → Strand.Digest)))
    (stream : (fun counter => SHA (Strand.Input.prf (history point).id (SHA (history point).input.encode) counter).encode) =
      ((componentEquiv (factor point) (fun stream => ((sampler point).run stream).1) fiber uniform).symm
        (challenge,residual)).1)
    (success : StrandVerifier.sampled history (fun p => read (factor p) fallback (sampler p)) SHA point) :
    StrandVerifier.oracle history (fun p => read (factor p) fallback (sampler p)) fallback SHA point =
      (SHA (history point).input.encode,normalize (factor point) fallback challenge) := by
  let row := ((componentEquiv (factor point) (fun stream => ((sampler point).run stream).1)
    fiber uniform).symm (challenge,residual)).1
  cases result : ((sampler point).run row).1 with
  | none =>
      simp only [StrandVerifier.sampled,read,Tree.run_map,stream] at success
      change (((sampler point).run row).1.map _).isSome at success
      simp only [result,Option.map_none,Option.isSome_none,Bool.false_eq_true] at success
  | some value =>
      have same := componentEquiv_inverse_success (Coins := Strand.Word → Strand.Digest)
        (factor point) (fun stream => ((sampler point).run stream).1)
        fiber uniform challenge residual value result
      apply Prod.ext
      · exact StrandVerifier.oracle_node history _ fallback SHA point
      · rw [StrandVerifier.oracle_challenge,stream]
        simp only [read,Tree.run_map]
        change (((sampler point).run row).1.map _).getD fallback = _
        simp only [result,Option.map_some,Option.getD_some,normalize,same]

end Physical

end LfzkV2.Current.StrandSampling
