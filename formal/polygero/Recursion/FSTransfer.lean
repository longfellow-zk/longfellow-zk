import polygero.Recursion.ProbabilityBound
import polygero.Local.Incidence
import Bcs.FootprintCharging

/-!
# Two-level random-target transfer and its finite-ROM lifting

The local theorem retains the target-family quantifier. The child oracle
can depend on the parent challenge, but is fixed before the parent query.
The resulting child envelope is averaged over the parent query and child
challenge jointly; no union over child witness tuples is taken.

The FS theorem allows arbitrary adaptive queries, including reverse order.
It requires an explicit incidence bound for the local certificates sharing
each hash point. The interactive theorem alone does not provide that bound.
No concrete Polygero hash serialization or numerical FS rate is asserted here.
-/

namespace RecursivePolygero.FiatShamir

open Finset Counting ProfileAnalysis
open Bcs.TotalOracle.Footprint
open scoped Classical

def transfer (epsilon rate : ℚ) : ℚ := epsilon + (1 - epsilon) * rate

def twoError (parent child : ℚ) : ℚ := parent + (1 - parent) * child

theorem transfer_comp (parent child rate : ℚ) :
    transfer child (transfer parent rate) = transfer (twoError parent child) rate := by
  unfold transfer twoError
  ring

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {I : Instance F} (child : Child I)
variable (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)

/-- Parent challenges precede the child commitment; parent queries follow it.
The envelope is uniform over the terminal response chosen after the child
challenge. The inherited target is indexed by a fixed child witness. -/
noncomputable def twoLevelEnvelope
    (sigma : I.layer.Statement) (W : I.layer.Oracle)
    (childOracle : I.layer.Coin → child.instance.layer.Oracle)
    (D : (tupleCounts I).Index → Prop)
    (a : I.layer.Coin) (q : I.layer.Query) (b : child.instance.layer.Coin) : ℚ :=
  localEnvelope child.instance cp.toProfileParameters
    (child.link.statement sigma W a q) (childOracle a) cp.threshold
    (Protocol.ProfileProof.inducedFamily (child := child) sigma W a D q) b

/-- Each fixed child witness induces a parent-query target of bounded
frequency. Quantifying before selecting the child witness is essential. -/
theorem induced_target_frequency_le
    (sigma : I.layer.Statement) (W : I.layer.Oracle)
    (D : (tupleCounts I).Index → Prop) (a : I.layer.Coin)
    (g : (tupleCounts child.instance).Index) :
    mean (fun q => indicator (Protocol.ProfileProof.inducedFamily
      (child := child) sigma W a D q g)) ≤
        localEnvelope I p.toProfileParameters sigma W p.threshold D a := by
  rw [Protocol.ProfileProof.inducedFamily_frequency]
  unfold indicator
  split_ifs with hout
  · rw [one_mul]
    exact response_fraction_le_envelope I p.toProfileParameters sigma W p.threshold
      p.columnFloor_le p.threshold_lt_one.le D a _ hout
  · rw [zero_mul]
    exact (localEnvelope_bounds I p.toProfileParameters sigma W p.threshold
      p.threshold_nonneg p.threshold_lt_one.le D a).1

/-- The seam lemma: parent query and child challenge are jointly averaged.
The child commitment is fixed throughout that average. -/
theorem seam_envelope_mean_le
    (sigma : I.layer.Statement) (W : I.layer.Oracle)
    (childOracle : I.layer.Coin → child.instance.layer.Oracle)
    (D : (tupleCounts I).Index → Prop) (a : I.layer.Coin) :
    mean (fun q => mean (twoLevelEnvelope child cp sigma W childOracle D a q)) ≤
      transfer cp.error (localEnvelope I p.toProfileParameters sigma W p.threshold D a) := by
  let E := Protocol.ProfileProof.inducedFamily (child := child) sigma W a D
  let rate := localEnvelope I p.toProfileParameters sigma W p.threshold D a
  have hb := localEnvelope_bounds I p.toProfileParameters sigma W p.threshold
    p.threshold_nonneg p.threshold_lt_one.le D a
  exact localEnvelope_mean_of_hahn child.instance cp
    (fun q => child.link.statement sigma W a q) (childOracle a) rate hb.1 hb.2 E
    (induced_target_frequency_le child p sigma W D a)

/-- Selection-safe seam transfer. The child system family may depend on
the parent challenge and the chosen child commitment, but must be fixed
before the parent query and child challenge are sampled. -/
theorem seam_incidence_mean_le
    (sigma : I.layer.Statement) (W : I.layer.Oracle)
    (childOracle : I.layer.Coin → child.instance.layer.Oracle)
    (D : (tupleCounts I).Index → Prop) (a : I.layer.Coin)
    (T : Finset (systems child.instance.domain child.instance.primary_le (childOracle a)))
    (hT : T.card ≤ Nat.card F) :
    mean (fun q => mean (localIncidence child.instance cp
      (child.link.statement sigma W a q) (childOracle a) T
      (Protocol.ProfileProof.inducedFamily (child := child) sigma W a D q))) ≤
        transfer cp.error (localEnvelope I p.toProfileParameters sigma W p.threshold D a) := by
  have hb := localEnvelope_bounds I p.toProfileParameters sigma W p.threshold
    p.threshold_nonneg p.threshold_lt_one.le D a
  exact localIncidence_mean_of_hahn child.instance cp
    (fun q => child.link.statement sigma W a q) (childOracle a) T hT _ hb.1 hb.2
    (Protocol.ProfileProof.inducedFamily (child := child) sigma W a D)
    (induced_target_frequency_le child p sigma W D a)

/-- Two-level transfer for summed excess incidences, with the same affine
error as the interactive maximum. This is the local budget usable by an
FS charging argument when a fixed small family covers all charged systems. -/
theorem twoLevel_incidence_mean_le
    {Z : Type} [Fintype Z] [Nonempty Z]
    (sigma : Z → I.layer.Statement) (W : I.layer.Oracle)
    (childOracle : Z → I.layer.Coin → child.instance.layer.Oracle)
    (D : Z → (tupleCounts I).Index → Prop) (rate : ℚ)
    (hr0 : 0 ≤ rate) (hr1 : rate ≤ 1)
    (hD : ∀ g, mean (fun z => indicator (D z g)) ≤ rate)
    (T : ∀ z a, Finset (systems child.instance.domain child.instance.primary_le (childOracle z a)))
    (hT : ∀ z a, (T z a).card ≤ Nat.card F) :
    mean (fun z => mean (fun a => mean (fun q => mean (localIncidence child.instance cp
      (child.link.statement (sigma z) W a q) (childOracle z a) (T z a)
      (Protocol.ProfileProof.inducedFamily (child := child) (sigma z) W a (D z) q))))) ≤
        transfer (twoError p.error cp.error) rate := by
  have hs := mean_mono (fun z => mean_mono (fun a =>
    seam_incidence_mean_le child p cp (sigma z) W (childOracle z) (D z) a (T z a) (hT z a)))
  simp only [transfer, mean_add, mean_const, mean_mul_left] at hs
  have hp := localEnvelope_mean_of_hahn I p sigma W rate hr0 hr1 D hD
  have hm := mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr cp.error_lt_one.le)
  unfold transfer twoError
  nlinarith only [hs, hm]

/-- Two local errors compose by the affine random-target transfer law,
already at the response-independent envelope, before any terminal strategy
is selected. External target randomness may also affect the statement and
the child commitment policy, but not the fixed parent oracle. -/
theorem twoLevel_envelope_mean_le
    {Z : Type} [Fintype Z] [Nonempty Z]
    (sigma : Z → I.layer.Statement) (W : I.layer.Oracle)
    (childOracle : Z → I.layer.Coin → child.instance.layer.Oracle)
    (D : Z → (tupleCounts I).Index → Prop) (rate : ℚ)
    (hr0 : 0 ≤ rate) (hr1 : rate ≤ 1)
    (hD : ∀ g, mean (fun z => indicator (D z g)) ≤ rate) :
    mean (fun z => mean (fun a => mean (fun q =>
      mean (twoLevelEnvelope child cp (sigma z) W (childOracle z) (D z) a q)))) ≤
      transfer (twoError p.error cp.error) rate := by
  have hs := mean_mono (fun z => mean_mono (fun a =>
    seam_envelope_mean_le child p cp (sigma z) W (childOracle z) (D z) a))
  simp only [transfer, mean_add, mean_const, mean_mul_left] at hs
  have hp := localEnvelope_mean_of_hahn I p sigma W rate hr0 hr1 D hD
  have hm := mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr cp.error_lt_one.le)
  unfold transfer twoError
  nlinarith only [hs, hm]

/-- A fixed terminal payload is dominated by the seam envelope, including
child extraction failure and hits on the inherited parent target. -/
theorem terminal_response_mean_le
    (sigma : I.layer.Statement) (W : I.layer.Oracle)
    (childOracle : I.layer.Coin → child.instance.layer.Oracle)
    (D : (tupleCounts I).Index → Prop)
    (a : I.layer.Coin) (q : I.layer.Query) (b : child.instance.layer.Coin)
    (payload : child.instance.layer.Payload) :
    mean (fun t : child.instance.layer.Query => indicator
      (child.instance.layer.verify (child.link.statement sigma W a q) (childOracle a) b payload t ∧
        outputHit (Protocol.ProfileProof.inducedFamily (child := child) sigma W a D q)
          (scanRecoverAt child.instance (child.link.statement sigma W a q) (childOracle a) b payload))) ≤
      twoLevelEnvelope child cp sigma W childOracle D a q b :=
  family_response_mean child.instance cp.toProfileParameters _ _ cp.threshold
    cp.columnFloor_le cp.threshold_lt_one.le _ b payload

/-- The exact two-invocation proof used by the local-to-ROM adapter. -/
noncomputable def twoProof : (Protocol.step child (.terminal child.instance)).HahnProfileProof p :=
  .step p (.terminal cp)

omit [Fintype F] [DecidableEq F] in
theorem twoProof_error : (twoProof child p cp).error = twoError p.error cp.error := rfl

/-- The finite interactive local bound, retaining arbitrary random targets.
This is a consequence of the existing recursive extraction theorem, not a
new soundness assumption on the adversary. -/
theorem twoLevel_randomTarget_le
    {Z : Type} [Fintype Z] [Nonempty Z]
    (sigma : Z → I.layer.Statement) (W : I.layer.Oracle)
    (messages : Z → Strategy (Protocol.step child (.terminal child.instance)).chain)
    (D : Z → (tupleCounts I).Index → Prop) (rate : ℚ)
    (hr0 : 0 ≤ rate) (hr1 : rate ≤ 1)
    (hD : ∀ g, mean (fun z => indicator (D z g)) ≤ rate) :
    mean (fun z => (twoProof child p cp).familyProbability (sigma z) W (messages z) (D z)) ≤
      transfer (twoError p.error cp.error) rate :=
  (twoProof child p cp).randomTargetProbability_le sigma W messages D rate hr0 hr1 hD

/-- A local candidate carries a nonanticipating two-level execution on the
coordinates held out by its footprint. The equivalence is a model bridge:
it must not be silently assumed for a biased fixed-bit challenge decoder.
All data may depend on the complementary oracle. -/
structure LocalModel (Z : Type) [Fintype Z] [Nonempty Z]
    (Q C : Type) [Fintype Q] [DecidableEq Q] [Fintype C]
    (support : Finset Q) (rate : ℚ) where
  sigma : (Outside support → C) → Z → I.layer.Statement
  oracle : (Outside support → C) → I.layer.Oracle
  messages : (Outside support → C) → Z →
    Strategy (Protocol.step child (.terminal child.instance)).chain
  target : (Outside support → C) → Z → (tupleCounts I).Index → Prop
  target_frequency : ∀ off g, mean (fun z => indicator (target off z g)) ≤ rate
  coins : (Inside support → C) ≃
    (Z × (Protocol.step child (.terminal child.instance)).chain.Coins)

variable {child}

noncomputable def LocalModel.weight
    {Z Q C : Type} [Fintype Z] [Nonempty Z] [Fintype Q] [DecidableEq Q] [Fintype C]
    {support : Finset Q} {rate : ℚ}
    (model : LocalModel child Z Q C support rate) (H : Q → C) : ℚ :=
  let off : Outside support → C := fun z => H z.1
  let tape := model.coins (fun z => H z.1)
  indicator (executionVerify (Protocol.step child (.terminal child.instance)).chain
      (model.sigma off tape.1) (model.oracle off) (model.messages off tape.1) tape.2 = true ∧
    outputHit (model.target off tape.1)
      ((twoProof child p cp).run (model.sigma off tape.1) (model.oracle off)
        (model.messages off tape.1) tape.2))

theorem LocalModel.weight_nonneg
    {Z Q C : Type} [Fintype Z] [Nonempty Z] [Fintype Q] [DecidableEq Q] [Fintype C]
    {support : Finset Q} {rate : ℚ}
    (model : LocalModel child Z Q C support rate) (H : Q → C) :
    0 ≤ model.weight p cp H := indicator_nonneg _

theorem LocalModel.local_bound
    {Z Q C : Type} [Fintype Z] [Nonempty Z] [Fintype Q] [DecidableEq Q] [Fintype C]
    {support : Finset Q} {rate : ℚ}
    (model : LocalModel child Z Q C support rate) (hr0 : 0 ≤ rate) (hr1 : rate ≤ 1)
    (off : Outside support → C) :
    average (fun on => model.weight p cp ((split support).symm (on, off))) ≤
      transfer (twoError p.error cp.error) rate := by
  let f := fun tape : Z × (Protocol.step child (.terminal child.instance)).chain.Coins =>
    indicator (executionVerify (Protocol.step child (.terminal child.instance)).chain
        (model.sigma off tape.1) (model.oracle off) (model.messages off tape.1) tape.2 = true ∧
      outputHit (model.target off tape.1)
        ((twoProof child p cp).run (model.sigma off tape.1) (model.oracle off)
          (model.messages off tape.1) tape.2))
  have he (on : Inside support → C) :
      model.weight p cp ((split support).symm (on, off)) = f (model.coins on) := by
    have ho := congrArg Prod.snd ((split (C := C) support).apply_symm_apply (on, off))
    have hi := congrArg Prod.fst ((split (C := C) support).apply_symm_apply (on, off))
    change (fun z : Outside support => (split support).symm (on, off) z.1) = off at ho
    change (fun z : Inside support => (split support).symm (on, off) z.1) = on at hi
    simp only [LocalModel.weight, ho, hi]
    rw [ho]
  simp_rw [he]
  have hs := Fintype.sum_equiv model.coins (fun on => f (model.coins on)) f (by intro on; rfl)
  unfold average
  rw [hs, Fintype.card_congr model.coins]
  change mean f ≤ _
  rw [mean_prod]
  exact twoLevel_randomTarget_le child p cp (model.sigma off) (model.oracle off)
    (model.messages off) (model.target off) rate hr0 hr1 (model.target_frequency off)

variable (child)

/-- Two-level FS random-target transfer with explicit query-incidence
budgets. `hquery` and `hfinal` are deterministic combinatorial obligations;
neither assumes the desired probability bound. No witness-list factor is
introduced by the local Polygero proof. Any FS branching cost is visible in
these two incidence hypotheses.

The event may choose its candidate using the entire adversarial execution.
Every local candidate must reproduce it on a full unit-weight event, and
its footprint must contain the designated verifier lookup. -/
theorem twoLevel_fs_transfer
    {Z Q C Candidate Out : Type} [Fintype Z] [Nonempty Z]
    [Fintype Q] [DecidableEq Q] [Fintype C] [Nonempty C] [Fintype Candidate]
    {N : ℕ} (tree : Merkle.RandomOracle.Tree Q C Out N) (point : Out → Q)
    (support : Candidate → Finset Q) (rate : ℚ)
    (models : ∀ i, LocalModel child Z Q C (support i) rate)
    (hr0 : 0 ≤ rate) (hr1 : rate ≤ 1)
    (failure : (Q → C) → Prop) (epsilon kappa : ℚ) (hkappa : 0 ≤ kappa)
    (hquery : ∀ q, (∑ i : Candidate, if q ∈ support i then
      transfer (twoError p.error cp.error) rate else 0) ≤ kappa)
    (hfinal : ∀ out, (∑ i : Candidate, if point out ∈ support i then
      transfer (twoError p.error cp.error) rate else 0) ≤ epsilon)
    (hcover : ∀ H, failure H → ∃ i,
      point (tree.run H).1 ∈ support i ∧ 1 ≤ (models i).weight p cp H) :
    Bcs.FiniteProbability.density failure ≤ epsilon + N * kappa := by
  have hb := (twoProof child p cp).error_bounds
  have hn : 0 ≤ transfer (twoError p.error cp.error) rate := by
    change 0 ≤ (twoProof child p cp).error + (1 - (twoProof child p cp).error) * rate
    exact add_nonneg hb.1 (mul_nonneg (sub_nonneg.mpr hb.2.le) hr0)
  exact selected_event_le tree point support (fun i => (models i).weight p cp)
    (fun _ _ => transfer (twoError p.error cp.error) rate) failure epsilon kappa
    (fun i => (models i).weight_nonneg p cp) (fun _ _ => hn) hkappa
    (fun i => (models i).local_bound p cp hr0 hr1)
    (fun _ => hquery) (fun _ => hfinal) hcover

/-- A simple rigidity discharge of the incidence hypotheses. `multiplicity`
counts complete local certificates sharing a hash input, not merely witness
labels with the same verifier behavior. A final input belongs to at most
one certificate. The underlying footprint compiler also supports unequal,
context-dependent budgets instead of this uniform count. -/
theorem twoLevel_fs_transfer_of_fanout
    {Z Q C Candidate Out : Type} [Fintype Z] [Nonempty Z]
    [Fintype Q] [DecidableEq Q] [Fintype C] [Nonempty C] [Fintype Candidate]
    {N : ℕ} (tree : Merkle.RandomOracle.Tree Q C Out N) (point : Out → Q)
    (support : Candidate → Finset Q) (rate : ℚ)
    (models : ∀ i, LocalModel child Z Q C (support i) rate)
    (hr0 : 0 ≤ rate) (hr1 : rate ≤ 1)
    (failure : (Q → C) → Prop) (multiplicity : ℕ)
    (hquery : ∀ q, (univ.filter fun i => q ∈ support i).card ≤ multiplicity)
    (hfinal : ∀ out, (univ.filter fun i => point out ∈ support i).card ≤ 1)
    (hcover : ∀ H, failure H → ∃ i,
      point (tree.run H).1 ∈ support i ∧ 1 ≤ (models i).weight p cp H) :
    Bcs.FiniteProbability.density failure ≤
      transfer (twoError p.error cp.error) rate +
        N * (multiplicity * transfer (twoError p.error cp.error) rate) := by
  let rho := transfer (twoError p.error cp.error) rate
  have hb := (twoProof child p cp).error_bounds
  have hn : 0 ≤ rho :=
    add_nonneg hb.1 (mul_nonneg (sub_nonneg.mpr hb.2.le) hr0)
  apply twoLevel_fs_transfer child p cp tree point support rate models hr0 hr1 failure
    rho (multiplicity * rho) (mul_nonneg (Nat.cast_nonneg _) hn)
  · intro q
    calc
      (∑ i, if q ∈ support i then rho else 0) =
          ((univ.filter fun i => q ∈ support i).card : ℚ) * rho := by
            rw [← sum_filter]
            simp
      _ ≤ multiplicity * rho := mul_le_mul_of_nonneg_right (by exact_mod_cast hquery q) hn
  · intro out
    calc
      (∑ i, if point out ∈ support i then rho else 0) =
          ((univ.filter fun i => point out ∈ support i).card : ℚ) * rho := by
            rw [← sum_filter]
            simp
      _ ≤ 1 * rho := mul_le_mul_of_nonneg_right (by exact_mod_cast hfinal out) hn
      _ = rho := one_mul _
  · exact hcover

end RecursivePolygero.FiatShamir
