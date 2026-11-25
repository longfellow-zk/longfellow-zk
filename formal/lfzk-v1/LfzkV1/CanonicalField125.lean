import LfzkV1.RbrZkLongfellow

/-!
# Field-message repairs for a selected lift

A round may deviate at the third interpolation node while keeping both
other values correct. The repair predicate compares the whole polynomial
and also covers the case where the incoming claim was already wrong.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LfzkV1.CanonicalField125

open Finset SumcheckV1 RbrLongfellow LfzkV1.RbrZkLongfellow
open scoped Classical

variable {F : Type} [Field F] [Fintype F] [SumcheckV1Interp F] {M : ℕ}

/-- The two fields of a unique canonical round message at its scheduled pad
indices. The missing interpolation value is determined by the claim. -/
def roundFields (P : Polynomial F) (pad : Pad M F) (pp0 pp2 : Fin M) : F × F :=
  (P.eval 0 - pad pp0, P.eval (Interp.pts (F := F) (d := 2) 2) - pad pp2)

omit [Fintype F] in
theorem roundFields_eq_of_toPoly_eq (P : Polynomial F) (pad : Pad M F)
    (rm : ZkRoundMsg M F) (claim : F)
    (h : ((roundData rm 0).unpad pad claim).toPoly = P) :
    (rm.tr0, rm.tr2) = roundFields P pad rm.pp0 rm.pp2 := by
  have h0 := congrArg (Polynomial.eval (0 : F)) h
  have h2 := congrArg (Polynomial.eval (Interp.pts (F := F) (d := 2) 2)) h
  rw [RoundPoly.eval_toPoly, RoundPoly.eval_lagrange_zero] at h0
  rw [RoundPoly.eval_toPoly, RoundPoly.eval_lagrange_pts] at h2
  change rm.tr0 + pad rm.pp0 = P.eval 0 at h0
  change rm.tr2 + pad rm.pp2 = P.eval (Interp.pts (F := F) (d := 2) 2) at h2
  exact Prod.ext (eq_sub_of_add_eq h0) (eq_sub_of_add_eq h2)

theorem fieldRepair_card_le (P : Polynomial F) (pad : Pad M F)
    (rm : ZkRoundMsg M F) (claim : F) (hdegree : P.natDegree ≤ 2)
    (hbad : claim ≠ P.eval 0 + P.eval 1 ∨
      (rm.tr0, rm.tr2) ≠ roundFields P pad rm.pp0 rm.pp2) :
    (univ.filter fun r : F => (roundData rm r).step pad claim = P.eval r).card ≤ 2 := by
  let p := (roundData rm 0).unpad pad claim
  have hne : p.toPoly ≠ P := by
    intro heq
    rcases hbad with hclaim | hmessage
    · apply hclaim
      have h0 := congrArg (Polynomial.eval (0 : F)) heq
      have h1 := congrArg (Polynomial.eval (1 : F)) heq
      rw [RoundPoly.eval_toPoly, RoundPoly.eval_lagrange_zero] at h0
      rw [RoundPoly.eval_toPoly, RoundPoly.eval_lagrange_one] at h1
      rw [← h0, ← h1, RoundData.unpad_sum]
    · exact hmessage (roundFields_eq_of_toPoly_eq P pad rm claim heq)
  have hdiff : p.toPoly - P ≠ 0 := sub_ne_zero.mpr hne
  have hsubset : (univ.filter fun r : F => (roundData rm r).step pad claim = P.eval r) ⊆
      (p.toPoly - P).roots.toFinset := by
    intro r hr
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hdiff]
    change (p.toPoly - P).eval r = 0
    rw [Polynomial.eval_sub, RoundPoly.eval_toPoly, sub_eq_zero]
    exact (mem_filter.mp hr).2
  exact (card_le_card hsubset).trans ((Multiset.toFinset_card_le _).trans
    ((Polynomial.card_roots' _).trans
      ((Polynomial.natDegree_sub_le _ _).trans (max_le p.toPoly_natDegree hdegree))))

variable {C X Q Msg Gpt Lift : Type} [Fintype C] {ninp logw logc : ℕ}

/-- The repair count on the actual running-state update. -/
theorem zkRound_repair_card_le
    (V : ZkCode C F X Q Msg Gpt M ninp logw logc) (H : ZkHonest F Lift logw logc)
    (pad : Pad M F) (lift : Lift) (zs : ZkRunning M logw logc F) (rm : ZkRoundMsg M F)
    (k : ℕ) (hbal : ∀ y : F, (univ.filter fun c : C => V.decodeF c = y).card ≤ k)
    (hbad : evaluates_to zs.e pad ≠ H.sum lift zs.layer zs.st zs.beta zs.alpha zs.bound ∨
      (rm.tr0, rm.tr2) ≠ roundFields (H.poly lift zs.layer zs.st zs.beta zs.alpha zs.bound)
        pad rm.pp0 rm.pp2) :
    (univ.filter fun c : C =>
      evaluates_to (builder_next zs.e (roundData rm (V.decodeF c))) pad =
        H.sum lift zs.layer zs.st zs.beta zs.alpha (zs.bound ++ [V.decodeF c])).card ≤ k * 2 := by
  let P := H.poly lift zs.layer zs.st zs.beta zs.alpha zs.bound
  have hbad' : evaluates_to zs.e pad ≠ P.eval 0 + P.eval 1 ∨
      (rm.tr0, rm.tr2) ≠ roundFields P pad rm.pp0 rm.pp2 := by
    simpa only [P, H.sum_eq] using hbad
  have hfield := fieldRepair_card_le P pad rm (evaluates_to zs.e pad)
    (H.deg_le lift zs.layer zs.st zs.beta zs.alpha zs.bound) hbad'
  have hcount := Bcs.card_decode_le V.decodeF k hbal
    (fun r => (roundData rm r).step pad (evaluates_to zs.e pad) = P.eval r) 2 hfield
  simpa only [builder_next_eval, P, H.next_eq] using hcount

variable {V : ZkCode C F X Q Msg Gpt M ninp logw logc}
variable {H : ZkHonest F Lift logw logc}
variable {asg : Lift → LigeroAssignment ninp M F} {nl : ℕ} {widths : ℕ → ℕ}

omit [SumcheckV1Interp F] in
/-- The pair sent at a layer close is fixed before the next grouped draw.
Any disagreement at one value of beta gives a nonzero bilinear repair test. -/
theorem zkCombine_repair_card_le (B : ZkBoundary V H asg nl widths)
    (lift : Lift) (zs : ZkRunning M logw logc F) (cm : ZkCloseMsg M F)
    (k : ℕ) (hbal : ∀ y : F × F, (univ.filter fun c : C => V.decodePair c = y).card ≤ k)
    (hbad : ∃ b : F, B.W lift (zs.layer + 1) (V.stNext zs.bound cm.wc0 cm.wc1) b ≠
      (cm.wc0 + (asg lift).2 cm.dwL, cm.wc1 + (asg lift).2 cm.dwR)) :
    (univ.filter fun c : C =>
      evaluates_to (builder_first (V.decodePair c).2 cm.wc0 cm.wc1 cm.dwL cm.dwR) (asg lift).2 =
        H.sum lift (zs.layer + 1) (V.stNext zs.bound cm.wc0 cm.wc1)
          (V.decodePair c).1 (V.decodePair c).2 []).card ≤ k * (2 * Fintype.card F) := by
  let W := B.W lift (zs.layer + 1) (V.stNext zs.bound cm.wc0 cm.wc1)
  let a := cm.wc0 + (asg lift).2 cm.dwL
  let b := cm.wc1 + (asg lift).2 cm.dwR
  obtain ⟨β, hβ⟩ := hbad
  have hdiff : (W β).1 ≠ a ∨ (W β).2 ≠ b := by
    by_contra! h
    exact hβ (Prod.ext h.1 h.2)
  have hfield := pair_escape_card W a b β (B.W_affine lift (zs.layer + 1) _) hdiff
  have hcount := Bcs.card_decode_le V.decodePair k hbal
    (fun y => a + y.2 * b = (W y.1).1 + y.2 * (W y.1).2) _ hfield
  simpa only [builder_first_eval, B.rel, W, a, b] using hcount

omit [SumcheckV1Interp F] in
/-- If the final transmitted pair disagrees with the selected assignment,
at most one input-fold scalar can make the compiled system hold. -/
theorem zkInput_repair_card_le (B : ZkBoundary V H asg nl widths)
    (lift : Lift) (zs : ZkRunning M logw logc F) (cm : ZkCloseMsg M F)
    (hlen : zs.bound.length = widths zs.layer) (hlast : zs.layer + 1 = nl)
    (k : ℕ) (hbal : ∀ y : F, (univ.filter fun c : C => V.decodeF c = y).card ≤ k)
    (hbad : B.W lift (zs.layer + 1) (V.stNext zs.bound cm.wc0 cm.wc1) 0 ≠
      (cm.wc0 + (asg lift).2 cm.dwL, cm.wc1 + (asg lift).2 cm.dwR)) :
    (univ.filter fun c : C =>
      (inputSystem V zs cm (V.decodeF c)).Sat (asg lift).1 (asg lift).2).card ≤ k * 1 := by
  let W := B.W lift (zs.layer + 1) (V.stNext zs.bound cm.wc0 cm.wc1) 0
  let a := cm.wc0 + (asg lift).2 cm.dwL
  let b := cm.wc1 + (asg lift).2 cm.dwR
  refine (card_le_card (t := univ.filter fun c : C => InputBindingBad W.1 W.2 a b (V.decodeF c))
    ?_).trans (LfzkV1.RbrBudgets.inputBind V.decodeF k hbal W.1 W.2 a b)
  intro c hc
  have hs := (mem_filter.mp hc).2
  rw [inputSystem, buildSystemMulti_Sat] at hs
  have hin := B.hin lift zs.layer zs.bound cm.wc0 cm.wc1 (V.decodeF c) hlen hlast
  have hrow := hs.2
  simp only [ligero_input_row] at hrow
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_⟩
  constructor
  · by_contra! h
    exact hbad (Prod.ext h.1 h.2)
  · dsimp only [W, a, b]
    linear_combination hin.symm + hrow

omit [Fintype C] [SumcheckV1Interp F] in
/-- If the close row holds and the transmitted endpoints are canonical,
the incoming claim at the end of that layer is also right. -/
theorem claim_eq_of_canonical_close (B : ZkBoundary V H asg nl widths)
    (lift : Lift) (zs : ZkRunning M logw logc F) (cm : ZkCloseMsg M F)
    (hbound : zs.bound.length = widths zs.layer) (hlayer : zs.layer < nl)
    (hrow : ligero_layer_checks zs.e (asg lift).2
      (V.eqqOf zs.layer zs.st zs.beta zs.alpha zs.bound) cm.wc0 cm.wc1 cm.dwL cm.dwR cm.dwLR)
    (hpair : B.W lift (zs.layer + 1) (V.stNext zs.bound cm.wc0 cm.wc1) 0 =
      (cm.wc0 + (asg lift).2 cm.dwL, cm.wc1 + (asg lift).2 cm.dwR)) :
    evaluates_to zs.e (asg lift).2 = H.sum lift zs.layer zs.st zs.beta zs.alpha zs.bound := by
  rw [B.final lift zs.layer zs.st zs.beta zs.alpha zs.bound cm.wc0 cm.wc1 hbound hlayer, hpair]
  exact layer_checks_imply_sumcheck _ _ _ _ _ _ _ _ hrow

/-- A right terminal claim either has a repair along the way or every
earlier claim and every transmitted field message was canonical. The first
claim here is the state immediately after initialization. -/
theorem canonical_or_repair (right canonical repair : ℕ → Prop) (rounds : ℕ)
    (hfinal : right rounds)
    (hstep : ∀ j < rounds, right (j + 1) → (right j ∧ canonical j) ∨ repair j) :
    (right 0 ∧ ∀ j < rounds, canonical j) ∨ ∃ j < rounds, repair j := by
  induction rounds with
  | zero => exact Or.inl ⟨hfinal, fun _ hj => (Nat.not_lt_zero _ hj).elim⟩
  | succ n ih =>
    rcases hstep n (Nat.lt_succ_self n) hfinal with ⟨hn, hmsg⟩ | hr
    · rcases ih hn (fun j hj => hstep j (Nat.lt_succ_of_lt hj)) with ⟨h0, hall⟩ | ⟨j, hj, hr⟩
      · exact Or.inl ⟨h0, fun j hj => (Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj)).elim
          (hall j) (fun h => h ▸ hmsg)⟩
      · exact Or.inr ⟨j, Nat.lt_succ_of_lt hj, hr⟩
    · exact Or.inr ⟨n, Nat.lt_succ_self n, hr⟩

end LfzkV1.CanonicalField125
