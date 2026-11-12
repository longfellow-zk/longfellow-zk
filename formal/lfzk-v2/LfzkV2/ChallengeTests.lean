import LfzkV2.Challenges

/-! Shared scalar challenge tests, independent of circuit execution models. -/
namespace LfzkV2
open SumcheckV2 Classical
variable {F : Type} [Field F]

inductive ChallengeTest (F : Type) [Field F] where
  | linear (offset slope : F)
  | output {n : ℕ} (table : Cube (n + 1) → F)
  | round (data : RoundData F)
  | combine (data : CombineData F)

namespace ChallengeTest

def Valid : ChallengeTest F → Prop
  | .round data => data.truth.natDegree ≤ 2
  | _ => True

def budget : ChallengeTest F → ℕ
  | .round _ => 2
  | _ => 1

def Bad : ChallengeTest F → F → Prop
  | .linear offset slope, z => BadLinear offset slope z
  | .output table, z => BadFold table z
  | .round data, z => BadRoundEvent data.truth data.message data.claim z
  | .combine data, z => BadCombineEvent data.trueA data.trueB data.claimA data.claimB z

theorem card_bad_le [Fintype F] [DecidableEq F] (test : ChallengeTest F) (hvalid : test.Valid) :
    (Finset.univ.filter test.Bad).card ≤ test.budget := by
  cases test with
  | linear offset slope => exact bad_linear_card offset slope
  | output table => exact bad_fold_card table
  | round data => exact bad_round_roots data.truth data.message data.claim hvalid
  | combine data => exact bad_combine_roots data.trueA data.trueB data.claimA data.claimB

theorem budget_le_two (test : ChallengeTest F) : test.budget ≤ 2 := by
  cases test <;> simp [budget]

end ChallengeTest

abbrev Tests (F : Type) [Field F] := List (ChallengeTest F × F)

def Tests.Bad (tests : Tests F) : Prop := ∃ test ∈ tests, test.1.Bad test.2
def Tests.Valid (tests : Tests F) : Prop := ∀ test ∈ tests, test.1.Valid

@[simp] theorem Tests.bad_append (left right : Tests F) :
    (left ++ right).Bad ↔ left.Bad ∨ right.Bad := by
  constructor
  · rintro ⟨test, hmem, hbad⟩
    rcases List.mem_append.mp hmem with hl | hr
    · exact Or.inl ⟨test, hl, hbad⟩
    · exact Or.inr ⟨test, hr, hbad⟩
  · rintro (⟨test, hmem, hbad⟩ | ⟨test, hmem, hbad⟩)
    · exact ⟨test, List.mem_append_left _ hmem, hbad⟩
    · exact ⟨test, List.mem_append_right _ hmem, hbad⟩

@[simp] theorem Tests.valid_append (left right : Tests F) :
    (left ++ right).Valid ↔ left.Valid ∧ right.Valid := List.forall_mem_append

@[simp] theorem Tests.bad_cons (test : ChallengeTest F × F) (tests : Tests F) :
    Tests.Bad (test :: tests) ↔ test.1.Bad test.2 ∨ tests.Bad := by
  constructor
  · rintro ⟨other, hmem, hbad⟩
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact Or.inl hbad
    · exact Or.inr ⟨other, hmem, hbad⟩
  · rintro (hbad | ⟨other, hmem, hbad⟩)
    · exact ⟨test, List.mem_cons_self, hbad⟩
    · exact ⟨other, List.mem_cons_of_mem _ hmem, hbad⟩

def outputTests : {n : ℕ} → (Cube n → F) → (Fin n → F) → Tests F
  | 0, _, _ => []
  | _ + 1, table, point => (.output table, point 0) ::
      outputTests (fold table (point 0)) (fun j => point j.succ)

theorem outputTests_bad {n : ℕ} (table : Cube n → F) (point : Fin n → F) :
    (outputTests table point).Bad ↔ OutputBad table point := by
  induction n with
  | zero => simp [outputTests, Tests.Bad, OutputBad]
  | succ n ih =>
      simp only [outputTests, Tests.bad_cons, ChallengeTest.Bad, OutputBad]
      exact or_congr_right (ih _ _)

theorem outputTests_valid {n : ℕ} (table : Cube n → F) (point : Fin n → F) :
    (outputTests table point).Valid := by
  induction n with
  | zero => simp [outputTests, Tests.Valid]
  | succ n ih =>
      simp only [outputTests, Tests.Valid, List.forall_mem_cons, ChallengeTest.Valid, true_and]
      exact ih _ _

def roundTests (claim : F) : List (Polynomial F) → List (RoundPoly F) → List F → Tests F
  | P :: Ps, m :: ms, z :: zs => (.round ⟨P, m, claim⟩, z) ::
      roundTests (check_round claim m z) Ps ms zs
  | _, _, _ => []

theorem roundTests_bad (claim : F) (Ps : List (Polynomial F)) (ms : List (RoundPoly F))
    (zs : List F) :
    (roundTests claim Ps ms zs).Bad ↔ multi_round_bad_event claim Ps ms zs := by
  induction ms generalizing claim Ps zs with
  | nil => cases Ps <;> cases zs <;> simp [roundTests, Tests.Bad, multi_round_bad_event]
  | cons m ms ih =>
      cases Ps with
      | nil => simp [roundTests, Tests.Bad, multi_round_bad_event]
      | cons P Ps =>
          cases zs with
          | nil => simp [roundTests, Tests.Bad, multi_round_bad_event]
          | cons z zs =>
              simp only [roundTests, Tests.bad_cons, ChallengeTest.Bad,
                multi_round_bad_event]
              exact or_congr_right (ih _ _ _)

theorem roundTests_valid (claim : F) (Ps : List (Polynomial F)) (ms : List (RoundPoly F))
    (zs : List F) (hdeg : ∀ P ∈ Ps, P.natDegree ≤ 2) :
    (roundTests claim Ps ms zs).Valid := by
  induction ms generalizing claim Ps zs with
  | nil => cases Ps <;> cases zs <;> simp [roundTests, Tests.Valid]
  | cons m ms ih =>
      cases Ps with
      | nil => simp [roundTests, Tests.Valid]
      | cons P Ps =>
          cases zs with
          | nil => simp [roundTests, Tests.Valid]
          | cons z zs =>
              change (∀ test ∈ (.round ⟨P, m, claim⟩, z) ::
                roundTests (check_round claim m z) Ps ms zs, test.1.Valid)
              rw [List.forall_mem_cons]
              exact ⟨hdeg P List.mem_cons_self,
                ih _ _ _ (fun Q hQ => hdeg Q (List.mem_cons_of_mem _ hQ))⟩

def Tests.budget (tests : Tests F) : ℕ := (tests.map fun test => test.1.budget).sum

@[simp] theorem Tests.budget_append (left right : Tests F) :
    (left ++ right).budget = left.budget + right.budget := by
  simp [budget]

theorem outputTests_budget {n : ℕ} (table : Cube n → F) (point : Fin n → F) :
    (outputTests table point).budget = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change 1 + (outputTests (fold table (point 0)) (fun i => point i.succ)).budget = n + 1
      rw [ih, Nat.add_comm]

theorem roundTests_budget_le (claim : F) (Ps : List (Polynomial F))
    (messages : List (RoundPoly F)) (challenges : List F) :
    (roundTests claim Ps messages challenges).budget ≤ 2 * Ps.length := by
  induction Ps generalizing claim messages challenges with
  | nil => simp [roundTests, Tests.budget]
  | cons P Ps ih =>
      cases messages with
      | nil => simp [roundTests, Tests.budget]
      | cons m ms =>
          cases challenges with
          | nil => simp [roundTests, Tests.budget]
          | cons z zs =>
              change 2 + (roundTests (check_round claim m z) Ps ms zs).budget ≤
                2 * (Ps.length + 1)
              have := ih (check_round claim m z) ms zs
              omega

theorem truePolys_length {n : ℕ} (q w : Cube n → F) (point : Fin n → F) :
    (truePolys q w point).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [truePolys, List.length_cons, ih]

end LfzkV2
