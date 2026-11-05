import LfzkV2.Native.HashReplay
import LfzkV2.Packed.Replay
import LfzkV2.GradedFS

/-!
# Native frontend, packing, and Polygero on one staged oracle

Frontend tests are reconstructed from the native affine streams. Packing has
its own challenge after the complete `U` response and before `A`. Polygero's
challenge/query pair pays its existing graded terminal potential. All three
parts use the same committed candidate list and the same adaptive oracle.
-/

namespace LfzkV2.Packed.FiatShamir

open SumcheckV2 RecursivePolygero NonrecursiveFS Finset ChallengeBlocks
  Bcs.TotalOracle Merkle.RandomOracle
open scoped Classical

variable {F C Key Parent Pad Slot Out : Type}
variable [Field F] [Fintype F] [DecidableEq F] [Fintype C]
variable {out input bound N : ℕ}

variable (circuit : Native.Circuit F out input) (I : Instance F)
variable (plan : Native.Replay.PadPlan (Pad := Pad) (Slot := Slot) circuit)
variable (sampling : LfzkV2.Replay.Sampling F C circuit.shape) (dflt : C)
variable (packed : Bool) (keyOf : Parent → Key)
variable (payloadOf : Parent → Native.Replay.Payload circuit)
variable (inputValue : I.layer.Oracle → Fin bound → Cube input → F)
variable (padValue : I.layer.Oracle → Fin bound → Pad → F)

noncomputable def pointBad (W : I.layer.Oracle)
    (point : LfzkV2.Replay.Point Key F circuit.shape)
    (pref : Fin ((LfzkV2.Replay.points circuit.shape).slot point) → C) (c : C) : Prop :=
  ∃ candidate : Fin bound,
    Data.Bad (Native.Replay.pointData sampling.decode dflt circuit plan point pref
      (inputValue W candidate) (padValue W candidate))
      ((LfzkV2.Replay.querySampler (Other := Unit) circuit.shape sampling (.inl point)).decode c)

theorem pointBad_sum_le (W : I.layer.Oracle)
    (point : LfzkV2.Replay.Point Key F circuit.shape)
    (pref : Fin ((LfzkV2.Replay.points circuit.shape).slot point) → C) :
    (∑ c : C, indicator (pointBad circuit I plan sampling dflt inputValue padValue W point pref c)) ≤
      sampling.unitFiber * (bound * (LfzkV2.Replay.pointKind circuit.shape point).budget) := by
  rw [show (∑ c : C, indicator (pointBad circuit I plan sampling dflt inputValue padValue W point pref c)) =
      ((univ.filter (pointBad circuit I plan sampling dflt inputValue padValue W point pref)).card : ℚ)
      by simp only [indicator, sum_boole]]
  have hcard : (univ.filter (pointBad circuit I plan sampling dflt inputValue padValue W point pref)).card ≤
      sampling.unitFiber * (bound * (LfzkV2.Replay.pointKind circuit.shape point).budget) := by
    have heq : (univ.filter (pointBad circuit I plan sampling dflt inputValue padValue W point pref)) =
        univ.biUnion (fun candidate : Fin bound => univ.filter fun c : C =>
          Data.Bad (Native.Replay.pointData sampling.decode dflt circuit plan point pref
            (inputValue W candidate) (padValue W candidate))
            ((LfzkV2.Replay.querySampler (Other := Unit) circuit.shape sampling (.inl point)).decode c)) := by
      ext c
      simp only [mem_filter, mem_univ, true_and, mem_biUnion, pointBad]
    rw [heq]
    calc
      _ ≤ ∑ candidate : Fin bound, (univ.filter fun c : C =>
          Data.Bad (Native.Replay.pointData sampling.decode dflt circuit plan point pref
            (inputValue W candidate) (padValue W candidate))
            ((LfzkV2.Replay.querySampler (Other := Unit) circuit.shape sampling (.inl point)).decode c)).card :=
        card_biUnion_le
      _ ≤ ∑ _ : Fin bound, sampling.unitFiber * (LfzkV2.Replay.pointKind circuit.shape point).budget :=
        sum_le_sum (fun candidate _ =>
          (LfzkV2.Replay.querySampler (Other := Unit) circuit.shape sampling (.inl point)).raw_bad_card
            sampling.unitFiber sampling.balanced _ (Native.Replay.pointData_valid _ _ _ _ _ _ _ _))
      _ = _ := by simp; ring
  exact_mod_cast hcard

noncomputable def frontendView (H : Replay.Domain Key circuit.shape I Parent → C) (p : Parent) :
    Native.Replay.Reconstruction circuit Pad Slot :=
  Native.Replay.reconstructionFromAnswers sampling.decode circuit plan (payloadOf p)
    (fun j => H (.inl (LfzkV2.Replay.hashInput circuit.shape (keyOf p) (payloadOf p) j)))

noncomputable def frontendAccepts (W : I.layer.Oracle)
    (H : Replay.Domain Key circuit.shape I Parent → C) (p : Parent) (candidate : Fin bound) : Prop :=
  let v := frontendView circuit I plan sampling keyOf payloadOf H p
  Native.ClearAccepts (padValue W candidate) 0
    (circuit.proof v.messages (monomialWeights v.point))
    (dot (circuit.inputWeights v.messages (monomialWeights v.point)) (inputValue W candidate))

theorem pointBad_of_frontend_accepts (W : I.layer.Oracle)
    (H : Replay.Domain Key circuit.shape I Parent → C) (p : Parent) (candidate : Fin bound)
    (hfalse : ¬ circuit.Satisfies (inputValue W candidate))
    (haccept : frontendAccepts circuit I plan sampling keyOf payloadOf inputValue padValue W H p candidate) :
    ∃ i : Fin (LfzkV2.Replay.slots circuit.shape),
      pointBad circuit I plan sampling dflt inputValue padValue W
        (LfzkV2.Replay.pointAt circuit.shape (keyOf p) (payloadOf p) i)
        ((Replay.points circuit.shape I packed keyOf payloadOf).chal H
          (.inl (LfzkV2.Replay.pointAt circuit.shape (keyOf p) (payloadOf p) i)))
        (H (.inl (LfzkV2.Replay.pointAt circuit.shape (keyOf p) (payloadOf p) i))) := by
  obtain ⟨role,hrole⟩ := Native.Replay.semantic_bad_of_accepts sampling.decode circuit plan (payloadOf p)
    (fun j => H (.inl (LfzkV2.Replay.hashInput circuit.shape (keyOf p) (payloadOf p) j)))
    (inputValue W candidate) (padValue W candidate) hfalse haccept
  obtain ⟨i,rfl⟩ := (LfzkV2.Replay.roleEquiv circuit.shape).symm.surjective role
  refine ⟨i,candidate,?_⟩
  change Data.Bad (Native.Replay.pointData sampling.decode dflt circuit plan
    (LfzkV2.Replay.pointAt circuit.shape (keyOf p) (payloadOf p) i)
    ((LfzkV2.Replay.points circuit.shape).chal (fun point => H (.inl point))
      (LfzkV2.Replay.pointAt circuit.shape (keyOf p) (payloadOf p) i))
    (inputValue W candidate) (padValue W candidate))
      ((sampling.blocks i).decode
        (H (.inl (LfzkV2.Replay.pointAt circuit.shape (keyOf p) (payloadOf p) i))))
  rw [Native.Replay.pointData_eq, sampling.agrees i]
  simp only [Equiv.apply_symm_apply, LfzkV2.Replay.hashInput_at] at hrole
  convert! hrole using 1

variable (statement : Parent × F → (ℕ → C) → I.layer.Statement)
variable (packingBad : I.layer.Oracle → Parent → (Fin (LfzkV2.Replay.slots circuit.shape) → C) → C → Prop)
variable (packingBudget : ℚ)
variable {cutoff : ℕ} {decodeCoin : C → I.layer.Coin} {decodeQuery : C → I.layer.Query}
variable (P : TerminalPotential I cutoff decodeCoin decodeQuery)

noncomputable def statementAt (H : Replay.Domain Key circuit.shape I Parent → C) (p : Parent × F) :
    I.layer.Statement := statement p (Replay.statementAnswers circuit.shape I keyOf payloadOf H p.1)

noncomputable def charge (W : I.layer.Oracle) (x : Replay.Domain Key circuit.shape I Parent)
    (pref : Fin ((Replay.points circuit.shape I packed keyOf payloadOf).slot x) → C) (c : C) : ℚ :=
  match x with
  | .inl point => indicator (pointBad circuit I plan sampling dflt inputValue padValue W point pref c)
  | .inr (.inl p) => if packed then indicator (packingBad W p pref c) else 0
  | .inr (.inr (.inl p)) =>
      let σ := Replay.viewAt statement dflt p pref
      if GradedFS.NoSat I cutoff σ W then P.weight σ W (decodeCoin c) else 0
  | .inr (.inr (.inr (p,response))) =>
      let σ := Replay.viewAt statement dflt p pref
      let coin := decodeCoin (pref ⟨LfzkV2.Replay.slots circuit.shape + Replay.packingSlots packed,
        by change _ < _ + 1; omega⟩)
      if GradedFS.NoSat I cutoff σ W ∧ I.layer.verify σ W coin response (decodeQuery c) then
        1-P.weight σ W coin else 0

noncomputable def budget (x : Replay.Domain Key circuit.shape I Parent) : ℚ :=
  match x with
  | .inl point => sampling.unitFiber * (bound * (LfzkV2.Replay.pointKind circuit.shape point).budget)
  | .inr (.inl _) => if packed then packingBudget else 0
  | .inr (.inr (.inl _)) => P.challengeBudget
  | .inr (.inr (.inr _)) => P.queryBudget

theorem budget_nonneg (hp : 0 ≤ packingBudget) (x : Replay.Domain Key circuit.shape I Parent) :
    0 ≤ budget (bound := bound) circuit I sampling packed packingBudget P x := by
  rcases x with point | p | p | pair
  · dsimp only [budget]; positivity
  · dsimp only [budget]; split_ifs <;> positivity
  · exact P.challengeBudget_nonneg
  · exact P.queryBudget_nonneg

theorem charge_nonneg (W : I.layer.Oracle) (x : Replay.Domain Key circuit.shape I Parent)
    (pref : Fin ((Replay.points circuit.shape I packed keyOf payloadOf).slot x) → C) (c : C) :
    0 ≤ charge circuit I plan sampling dflt packed keyOf payloadOf inputValue padValue
      statement packingBad P W x pref c := by
  rcases x with point | p | p | pair
  · exact indicator_nonneg _
  · dsimp only [charge]; split_ifs; exact indicator_nonneg _; exact le_rfl
  · dsimp only [charge]; split_ifs; exact P.nonneg _ _ _; exact le_rfl
  · dsimp only [charge]; split_ifs; exact sub_nonneg.mpr (P.le_one _ _ _); exact le_rfl

theorem charge_sum_le
    (hpacking : ∀ W p pref, (∑ c : C, indicator (packingBad W p pref c)) ≤ packingBudget)
    (W : I.layer.Oracle) (x : Replay.Domain Key circuit.shape I Parent)
    (pref : Fin ((Replay.points circuit.shape I packed keyOf payloadOf).slot x) → C) :
    (∑ c : C, charge circuit I plan sampling dflt packed keyOf payloadOf inputValue padValue
      statement packingBad P W x pref c) ≤
      budget (bound := bound) circuit I sampling packed packingBudget P x := by
  rcases x with point | p | p | ⟨p,response⟩
  · exact pointBad_sum_le circuit I plan sampling dflt inputValue padValue W point pref
  · cases packed <;> simp only [charge, budget, Bool.false_eq_true, if_false, if_true, sum_const_zero]
    · exact le_rfl
    · exact hpacking W p pref
  · let σ := Replay.viewAt statement dflt p pref
    change (∑ c : C, if GradedFS.NoSat I cutoff σ W then P.weight σ W (decodeCoin c) else 0) ≤ P.challengeBudget
    by_cases hn : GradedFS.NoSat I cutoff σ W
    · simpa only [if_pos hn] using P.challenge_le σ W
    · simpa only [if_neg hn, sum_const_zero] using P.challengeBudget_nonneg
  · let σ := Replay.viewAt statement dflt p pref
    let coin := decodeCoin (pref ⟨LfzkV2.Replay.slots circuit.shape + Replay.packingSlots packed,
      by change _ < _ + 1; omega⟩)
    change (∑ c : C, if GradedFS.NoSat I cutoff σ W ∧ I.layer.verify σ W coin response (decodeQuery c)
      then 1-P.weight σ W coin else 0) ≤ P.queryBudget
    by_cases hn : GradedFS.NoSat I cutoff σ W
    · simpa only [hn, true_and] using P.query_le σ W hn coin response
    · simpa only [hn, false_and, if_false, sum_const_zero] using P.queryBudget_nonneg

noncomputable def maxBudget : ℚ :=
  max ((sampling.unitFiber : ℚ) * (bound * max out 2))
    (max (if packed then packingBudget else 0) (max P.challengeBudget P.queryBudget))

theorem maxBudget_nonneg : 0 ≤ maxBudget (bound := bound) circuit I sampling packed packingBudget P := by
  unfold maxBudget
  apply le_trans _ (le_max_left _ _)
  positivity

theorem budget_le_max (x : Replay.Domain Key circuit.shape I Parent) :
    budget (bound := bound) circuit I sampling packed packingBudget P x ≤
      maxBudget (bound := bound) circuit I sampling packed packingBudget P := by
  unfold budget maxBudget
  rcases x with ⟨key,opt⟩ | p | p | pair
  · cases opt with
    | none =>
      change (sampling.unitFiber : ℚ) * (bound * 0) ≤ _
      simpa only [maxBudget, mul_zero] using
        maxBudget_nonneg (bound := bound) circuit I sampling packed packingBudget P
    | some p =>
      apply le_trans _ (le_max_left _ _)
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          ((Nat.cast_le (α := ℚ)).mpr (LfzkV2.Replay.roleKind_budget_le circuit.shape
            ((LfzkV2.Replay.roleEquiv circuit.shape).symm p.1))) (Nat.cast_nonneg _))
        (Nat.cast_nonneg _)
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  · exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))

noncomputable def slotBudget
    (i : Fin (LfzkV2.Replay.slots circuit.shape + Replay.packingSlots packed + 2)) : ℚ :=
  if h : i.val < LfzkV2.Replay.slots circuit.shape then
    sampling.unitFiber * (bound * (LfzkV2.Replay.roleKind circuit.shape
      ((LfzkV2.Replay.roleEquiv circuit.shape).symm ⟨i.val,h⟩)).budget)
  else if packed && i.val == LfzkV2.Replay.slots circuit.shape then packingBudget
  else if i.val = LfzkV2.Replay.slots circuit.shape + Replay.packingSlots packed then
    P.challengeBudget else P.queryBudget

theorem budget_hashInput (s : Replay.Selected I Parent)
    (i : Fin (LfzkV2.Replay.slots circuit.shape + Replay.packingSlots packed + 2)) :
    budget (bound := bound) circuit I sampling packed packingBudget P
      (Replay.hashInput circuit.shape I packed keyOf payloadOf s i.val) =
      slotBudget (bound := bound) circuit I sampling packed packingBudget P i := by
  unfold Replay.hashInput slotBudget
  split_ifs with hfront hpack hback
  · rw [LfzkV2.Replay.hashInput_at circuit.shape _ _ ⟨i.val,hfront⟩]
    rfl
  · cases packed <;> simp_all [budget, Replay.packing]
  · rfl
  · rfl

variable (hstatement : ∀ p first second,
  (∀ j, j < LfzkV2.Replay.slots circuit.shape + Replay.packingSlots packed → first j = second j) →
  statement p first = statement p second)

include hstatement in
theorem backend_charge_eq (W : I.layer.Oracle)
    (H : Replay.Domain Key circuit.shape I Parent → C) (p : Parent × F)
    (hn : GradedFS.NoSat I cutoff (statementAt circuit I keyOf payloadOf statement H p) W) :
    charge circuit I plan sampling dflt packed keyOf payloadOf inputValue padValue statement packingBad P W
      (Replay.backend circuit.shape I p)
      ((Replay.points circuit.shape I packed keyOf payloadOf).chal H (Replay.backend circuit.shape I p))
      (H (Replay.backend circuit.shape I p)) =
      P.weight (statementAt circuit I keyOf payloadOf statement H p) W
        (decodeCoin (H (Replay.backend circuit.shape I p))) := by
  let v := Replay.viewAt statement dflt p
    ((Replay.points circuit.shape I packed keyOf payloadOf).chal H (Replay.backend circuit.shape I p))
  change (if GradedFS.NoSat I cutoff v W then
    P.weight v W (decodeCoin (H (Replay.backend circuit.shape I p))) else 0) = _
  have hv : v = statementAt circuit I keyOf payloadOf statement H p :=
    Replay.backend_view_eq circuit.shape I packed keyOf payloadOf statement dflt hstatement H p
  rw [hv, if_pos hn]

include hstatement in
theorem opening_charge_eq (W : I.layer.Oracle)
    (H : Replay.Domain Key circuit.shape I Parent → C) (p : Parent × F) (response : I.layer.Payload)
    (hn : GradedFS.NoSat I cutoff (statementAt circuit I keyOf payloadOf statement H p) W)
    (ha : I.layer.verify (statementAt circuit I keyOf payloadOf statement H p) W
      (decodeCoin (H (Replay.backend circuit.shape I p))) response
      (decodeQuery (H (Replay.opening circuit.shape I p response)))) :
    charge circuit I plan sampling dflt packed keyOf payloadOf inputValue padValue statement packingBad P W
      (Replay.opening circuit.shape I p response)
      ((Replay.points circuit.shape I packed keyOf payloadOf).chal H (Replay.opening circuit.shape I p response))
      (H (Replay.opening circuit.shape I p response)) =
      1-P.weight (statementAt circuit I keyOf payloadOf statement H p) W
        (decodeCoin (H (Replay.backend circuit.shape I p))) := by
  let v := Replay.viewAt statement dflt p
    ((Replay.points circuit.shape I packed keyOf payloadOf).chal H (Replay.opening circuit.shape I p response))
  let coin := decodeCoin ((Replay.points circuit.shape I packed keyOf payloadOf).chal H
    (Replay.opening circuit.shape I p response)
      ⟨LfzkV2.Replay.slots circuit.shape + Replay.packingSlots packed, by change _ < _ + 1; omega⟩)
  change (if GradedFS.NoSat I cutoff v W ∧ I.layer.verify v W coin response
    (decodeQuery (H (Replay.opening circuit.shape I p response))) then 1-P.weight v W coin else 0) = _
  have hv : v = statementAt circuit I keyOf payloadOf statement H p :=
    Replay.opening_view_eq circuit.shape I packed keyOf payloadOf statement dflt hstatement H p response
  have hc : coin = decodeCoin (H (Replay.backend circuit.shape I p)) :=
    congrArg decodeCoin (Replay.opening_coin circuit.shape I packed keyOf payloadOf H p response)
  rw [hv, hc, if_pos ⟨hn,ha⟩]

noncomputable def packingEvent (W : I.layer.Oracle)
    (H : Replay.Domain Key circuit.shape I Parent → C) (p : Parent) : Prop :=
  packed = true ∧ packingBad W p
    ((Replay.points circuit.shape I packed keyOf payloadOf).chal H (Replay.packing circuit.shape I p))
    (H (Replay.packing circuit.shape I p))

include hstatement in
theorem path_charge_ge_one (W : I.layer.Oracle)
    (H : Replay.Domain Key circuit.shape I Parent → C) (s : Replay.Selected I Parent)
    (hcard : (Counting.committedCandidates I W cutoff).card ≤ bound)
    (hfalse : ∀ candidate : Fin bound,
      Counting.committedCandidate I W cutoff bound candidate ∈ Counting.committedCandidates I W cutoff →
      ¬ circuit.Satisfies (inputValue W candidate))
    (htransfer : ∀ candidate : Fin bound,
      I.layer.satisfies (statementAt circuit I keyOf payloadOf statement H s.1)
        ((Counting.tupleCounts I).witness (Counting.committedCandidate I W cutoff bound candidate)) →
      frontendAccepts circuit I plan sampling keyOf payloadOf inputValue padValue W H s.1.1 candidate ∨
        packingEvent circuit I packed keyOf payloadOf packingBad W H s.1.1)
    (haccept : I.layer.verify (statementAt circuit I keyOf payloadOf statement H s.1) W
      (decodeCoin (H (Replay.backend circuit.shape I s.1))) s.2
      (decodeQuery (H (Replay.opening circuit.shape I s.1 s.2)))) :
    1 ≤ ∑ i : Fin (LfzkV2.Replay.slots circuit.shape + Replay.packingSlots packed + 2),
      charge circuit I plan sampling dflt packed keyOf payloadOf inputValue padValue statement packingBad P W
        (Replay.hashInput circuit.shape I packed keyOf payloadOf s i.val)
        ((Replay.points circuit.shape I packed keyOf payloadOf).chal H
          (Replay.hashInput circuit.shape I packed keyOf payloadOf s i.val))
        (H (Replay.hashInput circuit.shape I packed keyOf payloadOf s i.val)) := by
  apply Bcs.PotentialChain.one_or_two_slots_pay _
    (fun i => charge_nonneg circuit I plan sampling dflt packed keyOf payloadOf inputValue padValue
      statement packingBad P W _ _ _)
  by_cases hb : ∃ i : Fin (LfzkV2.Replay.slots circuit.shape),
      pointBad circuit I plan sampling dflt inputValue padValue W
        (LfzkV2.Replay.pointAt circuit.shape (keyOf s.1.1) (payloadOf s.1.1) i)
        ((Replay.points circuit.shape I packed keyOf payloadOf).chal H
          (.inl (LfzkV2.Replay.pointAt circuit.shape (keyOf s.1.1) (payloadOf s.1.1) i)))
        (H (.inl (LfzkV2.Replay.pointAt circuit.shape (keyOf s.1.1) (payloadOf s.1.1) i)))
  · obtain ⟨i,hi⟩ := hb
    left
    refine ⟨⟨i.val,by omega⟩,?_⟩
    rw [Replay.hashInput, if_pos i.isLt, LfzkV2.Replay.hashInput_at circuit.shape _ _ i]
    change 1 ≤ indicator (pointBad circuit I plan sampling dflt inputValue padValue W _ _ _)
    simp only [indicator, if_pos hi, le_refl]
  · by_cases hp : packingEvent circuit I packed keyOf payloadOf packingBad W H s.1.1
    · left
      obtain ⟨hpacked,hbad⟩ := hp
      subst packed
      refine ⟨⟨LfzkV2.Replay.slots circuit.shape, by change _ < _ + 1 + 2; omega⟩,?_⟩
      rw [Replay.packing_at]
      change 1 ≤ indicator (packingBad W s.1.1 _ _)
      simp only [indicator, if_pos hbad, le_refl]
    · have hn : GradedFS.NoSat I cutoff (statementAt circuit I keyOf payloadOf statement H s.1) W := by
        intro g hg hsat
        obtain ⟨candidate,hcandidate⟩ := Counting.exists_committedCandidate I W cutoff bound hcard g hg
        rw [← hcandidate] at hsat
        rcases htransfer candidate hsat with hfront | hpacking
        · exact hb (pointBad_of_frontend_accepts circuit I plan sampling dflt packed keyOf payloadOf
            inputValue padValue W H s.1.1 candidate
            (hfalse candidate (by rw [hcandidate]; exact hg)) hfront)
        · exact hp hpacking
      right
      refine ⟨⟨LfzkV2.Replay.slots circuit.shape + Replay.packingSlots packed,by omega⟩,
        ⟨LfzkV2.Replay.slots circuit.shape + Replay.packingSlots packed + 1,by omega⟩,?_,?_⟩
      · intro heq
        have h := congrArg Fin.val heq
        change LfzkV2.Replay.slots circuit.shape + Replay.packingSlots packed =
          LfzkV2.Replay.slots circuit.shape + Replay.packingSlots packed + 1 at h
        omega
      · dsimp only [Fin.val_mk]
        rw [Replay.backend_at, Replay.opening_at,
          backend_charge_eq circuit I plan sampling dflt packed keyOf payloadOf inputValue padValue
            statement packingBad P hstatement W H s.1 hn,
          opening_charge_eq circuit I plan sampling dflt packed keyOf payloadOf inputValue padValue
            statement packingBad P hstatement W H s.1 s.2 hn haccept]
        linarith

noncomputable def grinding (tree : Tree (Replay.Domain Key circuit.shape I Parent) C Out N)
    (selected : Out → Replay.Selected I Parent)
    (context : (Replay.Domain Key circuit.shape I Parent → C) → Key → I.layer.Oracle)
    (context_off : ∀ H H' x, AgreeOff x H H' →
      context H' (Replay.key circuit.shape I keyOf x) = context H (Replay.key circuit.shape I keyOf x)) :
    CtxGrinding C (Replay.Domain Key circuit.shape I Parent) Out Key I.layer.Oracle N
      (LfzkV2.Replay.slots circuit.shape + Replay.packingSlots packed + 2) where
  adversary := tree
  hashInput result := Replay.hashInput circuit.shape I packed keyOf payloadOf (selected result)
  pts := Replay.points circuit.shape I packed keyOf payloadOf
  key := Replay.key circuit.shape I keyOf
  ctxAt := context
  ctxAt_off := context_off
  Bad _ _ _ _ := False
  beta _ := 0
  bad_bound := by intros; simp

include dflt hstatement in
/-- The staged verifier bound. The compiler bridge is algebraic: a satisfying
backend candidate supplies either the true source equation and native frontend
acceptance, or the prefix-local packing equation. Its probability is proved
separately by the packing count, not assumed by this theorem. -/
theorem event_soundness_le [Fintype Key] [Fintype Parent]
    (hp : 0 ≤ packingBudget)
    (hpacking : ∀ W p pref, (∑ c : C, indicator (packingBad W p pref c)) ≤ packingBudget)
    (tree : Tree (Replay.Domain Key circuit.shape I Parent) C Out N)
    (selected : Out → Replay.Selected I Parent)
    (context : (Replay.Domain Key circuit.shape I Parent → C) → Key → I.layer.Oracle)
    (context_off : ∀ H H' x, AgreeOff x H H' →
      context H' (Replay.key circuit.shape I keyOf x) = context H (Replay.key circuit.shape I keyOf x))
    (hcard : ∀ W, (Counting.committedCandidates I W cutoff).card ≤ bound)
    (event : (Replay.Domain Key circuit.shape I Parent → C) → Prop) [DecidablePred event]
    (hfalse : ∀ H, event H → ∀ candidate : Fin bound,
      Counting.committedCandidate I (context H (keyOf (selected (tree.run H).1).1.1)) cutoff bound candidate ∈
        Counting.committedCandidates I (context H (keyOf (selected (tree.run H).1).1.1)) cutoff →
      ¬ circuit.Satisfies (inputValue (context H (keyOf (selected (tree.run H).1).1.1)) candidate))
    (htransfer : ∀ H, event H → ∀ candidate,
      let p := (selected (tree.run H).1).1
      I.layer.satisfies (statementAt circuit I keyOf payloadOf statement H p)
        ((Counting.tupleCounts I).witness
          (Counting.committedCandidate I (context H (keyOf p.1)) cutoff bound candidate)) →
      frontendAccepts circuit I plan sampling keyOf payloadOf inputValue padValue
          (context H (keyOf p.1)) H p.1 candidate ∨
        packingEvent circuit I packed keyOf payloadOf packingBad (context H (keyOf p.1)) H p.1)
    (haccept : ∀ H, event H →
      let s := selected (tree.run H).1
      I.layer.verify (statementAt circuit I keyOf payloadOf statement H s.1)
        (context H (keyOf s.1.1)) (decodeCoin (H (Replay.backend circuit.shape I s.1))) s.2
        (decodeQuery (H (Replay.opening circuit.shape I s.1 s.2)))) :
    ((univ.filter event).card : ℚ) /
        (Fintype.card C : ℚ) ^ Fintype.card (Replay.Domain Key circuit.shape I Parent) ≤
      (N * maxBudget (bound := bound) circuit I sampling packed packingBudget P +
        ∑ i : Fin (LfzkV2.Replay.slots circuit.shape + Replay.packingSlots packed + 2),
          slotBudget (bound := bound) circuit I sampling packed packingBudget P i) / Fintype.card C := by
  letI : Nonempty C := ⟨dflt⟩
  let G := grinding circuit I packed keyOf payloadOf tree selected context context_off
  refine G.potential_ratio_le_rat
    (charge circuit I plan sampling dflt packed keyOf payloadOf inputValue padValue statement packingBad P)
    (charge_nonneg circuit I plan sampling dflt packed keyOf payloadOf inputValue padValue statement packingBad P)
    (budget (bound := bound) circuit I sampling packed packingBudget P)
    (budget_nonneg (bound := bound) circuit I sampling packed packingBudget P hp)
    (charge_sum_le circuit I plan sampling dflt packed keyOf payloadOf inputValue padValue statement
      packingBad packingBudget P hpacking)
    (maxBudget (bound := bound) circuit I sampling packed packingBudget P)
    (maxBudget_nonneg (bound := bound) circuit I sampling packed packingBudget P)
    (budget_le_max (bound := bound) circuit I sampling packed packingBudget P)
    (slotBudget (bound := bound) circuit I sampling packed packingBudget P)
    (fun result i => (budget_hashInput (bound := bound) circuit I sampling packed keyOf payloadOf
      packingBudget P (selected result) i).le) event ?_
  intro H hevent
  let s := selected (tree.run H).1
  let W := context H (keyOf s.1.1)
  have hpath := path_charge_ge_one circuit I plan sampling dflt packed keyOf payloadOf inputValue padValue
    statement packingBad P hstatement W H s (hcard W) (hfalse H hevent) (htransfer H hevent) (haccept H hevent)
  let f := fun x : Replay.Domain Key circuit.shape I Parent =>
    charge circuit I plan sampling dflt packed keyOf payloadOf inputValue padValue statement packingBad P
      (context H (G.key x)) x (G.pts.chal H x) (H x)
  apply le_trans _ (G.verifier_charge_le_total
    (fun result => Replay.hashInput_injective circuit.shape I packed keyOf payloadOf (selected result)) f
    (fun x => charge_nonneg circuit I plan sampling dflt packed keyOf payloadOf inputValue padValue
      statement packingBad P (context H (G.key x)) x (G.pts.chal H x) (H x)) H)
  refine hpath.trans_eq ?_
  apply sum_congr rfl
  intro i _
  dsimp only [f]
  have hk : G.key (G.point H i.val) = keyOf s.1.1 :=
    Replay.hashInput_key circuit.shape I packed keyOf payloadOf s i.val
  rw [hk]
  rfl

/-- Exact verifier cost: one packing charge on a nontrivial extension and no
packing cost or oracle slot on the direct path. -/
theorem slotBudget_sum :
    (∑ i : Fin (LfzkV2.Replay.slots circuit.shape + Replay.packingSlots packed + 2),
      slotBudget (bound := bound) circuit I sampling packed packingBudget P i) =
      sampling.unitFiber * bound * (out + circuit.sharpLayerBudget) +
        (if packed then packingBudget else 0) + P.challengeBudget + P.queryBudget := by
  have hs : (∑ i : Fin (LfzkV2.Replay.slots circuit.shape),
      ((LfzkV2.Replay.roleKind circuit.shape ((LfzkV2.Replay.roleEquiv circuit.shape).symm i)).budget : ℚ)) =
      ((out + circuit.sharpLayerBudget : ℕ) : ℚ) := by
    have h := LfzkV2.Replay.budget_sum circuit.shape
    rw [Native.Circuit.shape_sharpLayerBudget] at h
    exact_mod_cast h
  have hfront :
      (∑ i : Fin (LfzkV2.Replay.slots circuit.shape),
        slotBudget (bound := bound) circuit I sampling packed packingBudget P
          ⟨i.val, by have := i.isLt; omega⟩) =
        sampling.unitFiber * bound * (out + circuit.sharpLayerBudget) := by
    simp only [slotBudget, dif_pos (Fin.isLt _)]
    rw [← Finset.mul_sum, ← Finset.mul_sum, hs]
    push_cast
    ring
  cases packed with
  | false =>
    change (∑ i : Fin (LfzkV2.Replay.slots circuit.shape + 2),
      slotBudget (bound := bound) circuit I sampling false packingBudget P i) = _
    rw [Fin.sum_univ_add]
    change (∑ i : Fin (LfzkV2.Replay.slots circuit.shape),
      slotBudget (bound := bound) circuit I sampling false packingBudget P (i.castAdd 2)) = _ at hfront
    rw [hfront, Fin.sum_univ_two]
    simp [slotBudget, Replay.packingSlots]
    ring
  | true =>
    change (∑ i : Fin (LfzkV2.Replay.slots circuit.shape + 3),
      slotBudget (bound := bound) circuit I sampling true packingBudget P i) = _
    rw [Fin.sum_univ_add]
    change (∑ i : Fin (LfzkV2.Replay.slots circuit.shape),
      slotBudget (bound := bound) circuit I sampling true packingBudget P (i.castAdd 3)) = _ at hfront
    rw [hfront, Fin.sum_univ_succ, Fin.sum_univ_two]
    simp [slotBudget, Replay.packingSlots]
    ring

end LfzkV2.Packed.FiatShamir
