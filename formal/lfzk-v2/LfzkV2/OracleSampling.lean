import LfzkV2.FiatShamir
import Mathlib.Tactic.FieldSimp

/-!
# A shared oracle answer space for frontend and backend challenges

The adversary sees full hash answers, which may encode a field element, a
Polygero batching coin, and an opening query. Counting frontend roots after a
balanced projection retains the field-size denominator. The adversary is not
restricted to seeing the projected field element.
-/

namespace LfzkV2.FiatShamir

open SumcheckV2 Classical Finset Bcs.TotalOracle Merkle.RandomOracle
open scoped Classical

variable {F C Q Out Key Context Candidate : Type}
variable [Field F] [Fintype F] [DecidableEq F] [Fintype C]
variable [Fintype Candidate] [DecidableEq Q] {N L : ℕ}

structure OracleSetup (F C : Type) [Field F] [Fintype F] [DecidableEq F] [Fintype C]
    (Q Out Key Context Candidate : Type) [DecidableEq Q] (N L : ℕ) where
  adversary : Tree Q C Out N
  hashInput : Out → ℕ → Q
  points : PrefixPoints Q
  key : Q → Key
  context : (Q → C) → Key → Context
  context_off : ∀ (H H' : Q → C) (x : Q), AgreeOff x H H' →
    context H' (key x) = context H (key x)
  decode : C → F
  fiber : ℕ
  fiber_bound : ∀ z, (univ.filter fun c => decode c = z).card ≤ fiber
  balanced : fiber * Fintype.card F = Fintype.card C
  test : Context → (x : Q) → (Fin (points.slot x) → F) → Candidate → ChallengeTest F
  valid : ∀ ctx x pref candidate, (test ctx x pref candidate).Valid
  budget : Q → ℕ
  test_budget : ∀ ctx x pref candidate, (test ctx x pref candidate).budget ≤ budget x

namespace OracleSetup

variable (S : OracleSetup F C Q Out Key Context Candidate N L)

theorem field_bad_bound (ctx : Context) (x : Q) (pref : Fin (S.points.slot x) → F) :
    (univ.filter fun z => ∃ candidate, (S.test ctx x pref candidate).Bad z).card ≤
      Fintype.card Candidate * S.budget x := by
  have heq : (univ.filter fun z => ∃ candidate, (S.test ctx x pref candidate).Bad z) =
      univ.biUnion (fun candidate => univ.filter (S.test ctx x pref candidate).Bad) := by
    ext z
    simp
  rw [heq]
  calc
    _ ≤ ∑ candidate, (univ.filter (S.test ctx x pref candidate).Bad).card := card_biUnion_le
    _ ≤ ∑ _ : Candidate, S.budget x := sum_le_sum fun candidate _ =>
      ((S.test ctx x pref candidate).card_bad_le (S.valid ctx x pref candidate)).trans
        (S.test_budget ctx x pref candidate)
    _ = _ := by simp

noncomputable def grinding : CtxGrinding C Q Out Key Context N L where
  adversary := S.adversary
  hashInput := S.hashInput
  pts := S.points
  key := S.key
  ctxAt := S.context
  ctxAt_off := S.context_off
  Bad ctx x pref c := ∃ candidate,
    (S.test ctx x (S.decode ∘ pref) candidate).Bad (S.decode c)
  beta x := S.fiber * (Fintype.card Candidate * S.budget x)
  bad_bound ctx x pref := by
    convert! Bcs.card_decode_le S.decode S.fiber S.fiber_bound
      (fun z => ∃ candidate, (S.test ctx x (S.decode ∘ pref) candidate).Bad z)
      (Fintype.card Candidate * S.budget x) ?_ using 1
    convert! S.field_bad_bound ctx x (S.decode ∘ pref) using 1
    congr 1
    ext z
    simp only [mem_filter]

def Covers (H : Q → C) (candidate : Candidate) (tests : Tests F) : Prop :=
  ∀ test ∈ tests, ∃ i : Fin L,
    let x := S.hashInput (S.adversary.run H).1 i.val
    test.1 = S.test (S.context H (S.key x)) x (S.decode ∘ S.points.chal H x) candidate ∧
      test.2 = S.decode (H x)

theorem bad_of_tests (H : Q → C) (candidate : Candidate) (tests : Tests F)
    (hcover : S.Covers H candidate tests) (hbad : tests.Bad) : S.grinding.RoundBad H := by
  obtain ⟨test, hmem, htest⟩ := hbad
  obtain ⟨i, hdata, hcoin⟩ := hcover test hmem
  refine ⟨i, candidate, ?_⟩
  change (S.test (S.context H (S.key (S.hashInput (S.adversary.run H).1 i.val)))
    (S.hashInput (S.adversary.run H).1 i.val)
    (S.decode ∘ S.points.chal H (S.hashInput (S.adversary.run H).1 i.val)) candidate).Bad
      (S.decode (H (S.hashInput (S.adversary.run H).1 i.val)))
  rwa [← hdata, ← hcoin]

/-- One adaptive query budget, with no loss for projecting full hash answers
onto frontend field challenges. -/
theorem soundness_le [Fintype Q] [Nonempty C] (maxBudget : ℕ) (hmax : ∀ x, S.budget x ≤ maxBudget)
    (slotBudget : Fin L → ℕ)
    (hslot : ∀ out i, S.budget (S.hashInput out i.val) ≤ slotBudget i)
    (event : (Q → C) → Prop)
    (htests : ∀ H, event H → ∃ candidate tests, S.Covers H candidate tests ∧ tests.Bad) :
    ((univ.filter event).card : ℚ) / (Fintype.card C : ℚ) ^ Fintype.card Q ≤
      (Fintype.card Candidate : ℚ) * (N * maxBudget + ∑ i, slotBudget i) / Fintype.card F := by
  have h := S.grinding.ratio_le (S.fiber * (Fintype.card Candidate * maxBudget))
    (fun x => Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (hmax x)))
    (fun i => S.fiber * (Fintype.card Candidate * slotBudget i))
    (fun out i => Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (hslot out i)))
    event (fun H hE => by
      obtain ⟨candidate, tests, hcover, hbad⟩ := htests H hE
      exact S.bad_of_tests H candidate tests hcover hbad)
  have hf : (0 : ℚ) < S.fiber := by
    have hc := Fintype.card_pos (α := C)
    have hb := S.balanced
    exact_mod_cast (show 0 < S.fiber by nlinarith)
  have hcard : (Fintype.card C : ℚ) = S.fiber * (Fintype.card F : ℚ) := by
    exact_mod_cast S.balanced.symm
  refine h.trans_eq ?_
  rw [hcard, ← Finset.mul_sum, ← Finset.mul_sum]
  push_cast
  field_simp [hf.ne']

def restrictCandidates {Candidate' : Type} (f : Candidate' → Candidate) :
    OracleSetup F C Q Out Key Context Candidate' N L where
  adversary := S.adversary
  hashInput := S.hashInput
  points := S.points
  key := S.key
  context := S.context
  context_off := S.context_off
  decode := S.decode
  fiber := S.fiber
  fiber_bound := S.fiber_bound
  balanced := S.balanced
  test ctx x pref candidate := S.test ctx x pref (f candidate)
  valid ctx x pref candidate := S.valid ctx x pref (f candidate)
  budget := S.budget
  test_budget ctx x pref candidate := S.test_budget ctx x pref (f candidate)

omit [Fintype Candidate] in
theorem fixed_candidate_soundness_le [Fintype Q] [Nonempty C]
    (S : OracleSetup F C Q Out Key Context Candidate N L) (candidate : Candidate)
    (maxBudget : ℕ) (hmax : ∀ x, S.budget x ≤ maxBudget)
    (slotBudget : Fin L → ℕ)
    (hslot : ∀ out i, S.budget (S.hashInput out i.val) ≤ slotBudget i)
    (event : (Q → C) → Prop)
    (htests : ∀ H, event H → ∃ tests, S.Covers H candidate tests ∧ tests.Bad) :
    ((univ.filter event).card : ℚ) / (Fintype.card C : ℚ) ^ Fintype.card Q ≤
      (N * maxBudget + ∑ i, slotBudget i) / Fintype.card F := by
  have h := (S.restrictCandidates (fun _ : Unit => candidate)).soundness_le
    maxBudget hmax slotBudget hslot event (by
      intro H hH
      obtain ⟨tests, hcover, hbad⟩ := htests H hH
      exact ⟨(), tests, hcover, hbad⟩)
  simpa using h

end OracleSetup
end LfzkV2.FiatShamir
