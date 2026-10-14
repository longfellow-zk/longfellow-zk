import Bcs.FirstOccurrenceTrace
import Merkle.LazyTape
import Sumcheck.Grinding
import LigeroFamily.Protocol.Finite
import Mathlib.Algebra.Order.Field.Rat

/-! Typed defining queries and their first-occurrence answers on a lazy tape. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bcs.TypedFiatShamir

variable {AlphaKey SubsetKey α : Type*}

inductive Query (AlphaKey SubsetKey : Type*) where
  | alpha (key : AlphaKey)
  | subset (key : SubsetKey)
deriving DecidableEq

abbrev Answer (Alpha Subset : Type*) := Alpha × Subset

def alphaAnswer {Alpha Subset : Type*} (answer : Answer Alpha Subset) : Alpha :=
  answer.1

def subsetAnswer {Alpha Subset : Type*} (answer : Answer Alpha Subset) : Subset :=
  answer.2


theorem alpha_projection_card
    {Alpha Subset : Type*} [Fintype Alpha] [Fintype Subset]
    (event : Alpha → Prop) [DecidablePred event] :
    (Finset.univ.filter (fun answer : Answer Alpha Subset ↦
      event (alphaAnswer answer))).card =
      Fintype.card Subset * (Finset.univ.filter event).card := by
  rw [Bcs.card_filter_prod_fst]
  calc
    ∑ x : Alpha, (Finset.univ.filter fun _answer : Subset ↦ event x).card =
        ∑ x : Alpha, if event x then Fintype.card Subset else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : event x <;> simp [hx]
    _ = Fintype.card Subset *
          ∑ x : Alpha, if event x then 1 else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      split <;> simp_all
    _ = _ := by simp


theorem subset_projection_card
    {Alpha Subset : Type*} [Fintype Alpha] [Fintype Subset]
    (event : Subset → Prop) [DecidablePred event] :
    (Finset.univ.filter (fun answer : Answer Alpha Subset ↦
      event (subsetAnswer answer))).card =
      Fintype.card Alpha * (Finset.univ.filter event).card := by
  rw [Bcs.card_filter_prod_snd]
  calc
    ∑ x : Subset, (Finset.univ.filter fun _answer : Alpha ↦ event x).card =
        ∑ x : Subset, if event x then Fintype.card Alpha else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : event x <;> simp [hx]
    _ = Fintype.card Alpha *
          ∑ x : Subset, if event x then 1 else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      split <;> simp_all
    _ = _ := by simp




abbrev TwoSlotRemainder (T : ℕ) (i j : Fin T) (D : Type*) :=
  { k : Fin T // k ≠ i ∧ k ≠ j } → D


abbrev TwoSlotData (Alpha Subset : Type*) (T : ℕ)
    (subsetSlot alphaSlot : Fin T) :=
  Answer Alpha Subset ×
    TwoSlotRemainder T subsetSlot alphaSlot (Answer Alpha Subset)

def twoSlotData {Alpha Subset : Type*} {T : ℕ}
    (subsetSlot alphaSlot : Fin T) (tape : Fin T → Answer Alpha Subset) :
    TwoSlotData Alpha Subset T subsetSlot alphaSlot :=
  ((alphaAnswer (tape subsetSlot), subsetAnswer (tape alphaSlot)),
    fun k => tape k.1)


theorem card_twoSlotRemainder_index {T : ℕ} (i j : Fin T) (hne : i ≠ j) :
    Fintype.card { k : Fin T // k ≠ i ∧ k ≠ j } = T - 2 := by
  classical
  rw [Fintype.card_subtype]
  change (Finset.univ.filter fun k : Fin T => k ≠ i ∧ k ≠ j).card = T - 2
  rw [show Finset.univ.filter (fun k : Fin T => k ≠ i ∧ k ≠ j) =
      Finset.univ \ {i, j} by ext k; simp]
  rw [Finset.card_sdiff]
  simp [hne]


theorem two_projection_tape_card_le
    {Alpha Subset : Type*} [Fintype Alpha] [Fintype Subset]
    [DecidableEq Alpha] [DecidableEq Subset]
    {T : ℕ} (i j : Fin T) (hne : i ≠ j)
    (success : Subset → Alpha → Prop) [DecidableRel success] (pairBudget : ℕ)
    (hpairs : (Finset.univ.filter fun pair : Subset × Alpha =>
      success pair.1 pair.2).card ≤ pairBudget) :
    (Finset.univ.filter fun tape : Fin T → Answer Alpha Subset =>
      success (subsetAnswer (tape i)) (alphaAnswer (tape j))).card ≤
        pairBudget * Fintype.card (Answer Alpha Subset) ^ (T - 1) := by
  classical
  let Remainder := TwoSlotRemainder T i j (Answer Alpha Subset)
  let Data := Answer Alpha Subset × Remainder
  let pairOf : (Fin T → Answer Alpha Subset) → Subset × Alpha := fun tape =>
    (subsetAnswer (tape i), alphaAnswer (tape j))
  let dataOf : (Fin T → Answer Alpha Subset) → Data := fun tape =>
    ((alphaAnswer (tape i), subsetAnswer (tape j)), fun k => tape k.1)
  have hsplit : Function.Injective (fun tape => (pairOf tape, dataOf tape)) := by
    intro first second heq
    funext k
    by_cases hki : k = i
    · subst k
      apply Prod.ext
      · exact congrArg (fun value => value.2.1.1) heq
      · exact congrArg (fun value => value.1.1) heq
    · by_cases hkj : k = j
      · subst k
        apply Prod.ext
        · exact congrArg (fun value => value.1.2) heq
        · exact congrArg (fun value => value.2.1.2) heq
      · exact congrFun (congrArg (fun value => value.2.2) heq) ⟨k, hki, hkj⟩
  have hT : 2 ≤ T := by
    have hi := i.isLt
    have hj := j.isLt
    have hv : i.val ≠ j.val := fun h => hne (Fin.ext h)
    omega
  have hdata : Fintype.card Data =
      Fintype.card (Answer Alpha Subset) ^ (T - 1) := by
    dsimp [Data, Remainder, TwoSlotRemainder]
    rw [Fintype.card_prod, Fintype.card_fun,
      card_twoSlotRemainder_index i j hne]
    rw [show T - 1 = (T - 2) + 1 by omega, pow_succ]
    ring
  let pairs : Finset (Subset × Alpha) := Finset.univ.filter fun pair =>
    success pair.1 pair.2
  calc
    (Finset.univ.filter fun tape : Fin T → Answer Alpha Subset =>
        success (subsetAnswer (tape i)) (alphaAnswer (tape j))).card
        ≤ (pairs ×ˢ (Finset.univ : Finset Data)).card := by
          apply Finset.card_le_card_of_injOn (fun tape => (pairOf tape, dataOf tape))
          · intro tape htape
            exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, (Finset.mem_filter.mp htape).2⟩,
                Finset.mem_univ _⟩
          · intro first hfirst second hsecond heq
            exact hsplit heq
    _ = pairs.card * Fintype.card Data := by simp
    _ ≤ pairBudget * Fintype.card Data :=
      Nat.mul_le_mul_right _ (by simpa [pairs] using hpairs)
    _ = pairBudget * Fintype.card (Answer Alpha Subset) ^ (T - 1) := by
      rw [hdata]


theorem two_projection_dependent_tape_card_le
    {Alpha Subset : Type*} [Fintype Alpha] [Fintype Subset]
    [DecidableEq Alpha] [DecidableEq Subset]
    {T : ℕ} (subsetSlot alphaSlot : Fin T) (hne : subsetSlot ≠ alphaSlot)
    (success : TwoSlotData Alpha Subset T subsetSlot alphaSlot →
      Subset → Alpha → Prop) [∀ data, DecidableRel (success data)]
    (pairBudget : ℕ)
    (hpairs : ∀ data,
      (Finset.univ.filter fun pair : Subset × Alpha =>
        success data pair.1 pair.2).card ≤ pairBudget) :
    (Finset.univ.filter fun tape : Fin T → Answer Alpha Subset =>
      success (twoSlotData subsetSlot alphaSlot tape)
        (subsetAnswer (tape subsetSlot))
        (alphaAnswer (tape alphaSlot))).card ≤
      pairBudget * Fintype.card (Answer Alpha Subset) ^ (T - 1) := by
  classical
  let Data := TwoSlotData Alpha Subset T subsetSlot alphaSlot
  let pairOf : (Fin T → Answer Alpha Subset) → Subset × Alpha := fun tape =>
    (subsetAnswer (tape subsetSlot), alphaAnswer (tape alphaSlot))
  let dataOf : (Fin T → Answer Alpha Subset) → Data :=
    twoSlotData subsetSlot alphaSlot
  have hsplit : Function.Injective (fun tape => (dataOf tape, pairOf tape)) := by
    intro first second heq
    funext k
    by_cases hks : k = subsetSlot
    · subst k
      apply Prod.ext
      · exact congrArg (fun value => value.1.1.1) heq
      · exact congrArg (fun value => value.2.1) heq
    · by_cases hka : k = alphaSlot
      · subst k
        apply Prod.ext
        · exact congrArg (fun value => value.2.2) heq
        · exact congrArg (fun value => value.1.1.2) heq
      · exact congrFun (congrArg (fun value => value.1.2) heq) ⟨k, hks, hka⟩
  let good : Finset (Data × (Subset × Alpha)) := Finset.univ.filter fun value =>
    success value.1 value.2.1 value.2.2
  have hgood : good.card ≤ Fintype.card Data * pairBudget := by
    rw [show good.card = ∑ data : Data,
        (Finset.univ.filter fun pair : Subset × Alpha =>
          success data pair.1 pair.2).card by
      dsimp [good]
      rw [Bcs.card_filter_prod_fst]]
    calc
      ∑ data : Data, (Finset.univ.filter fun pair : Subset × Alpha =>
          success data pair.1 pair.2).card
        ≤ ∑ _data : Data, pairBudget :=
          Finset.sum_le_sum (fun data _ => hpairs data)
      _ = Fintype.card Data * pairBudget := by simp
  have hT : 2 ≤ T := by
    have hs := subsetSlot.isLt
    have ha := alphaSlot.isLt
    have hv : subsetSlot.val ≠ alphaSlot.val := fun h => hne (Fin.ext h)
    omega
  have hdata : Fintype.card Data =
      Fintype.card (Answer Alpha Subset) ^ (T - 1) := by
    dsimp [Data, TwoSlotData, TwoSlotRemainder]
    rw [Fintype.card_prod, Fintype.card_fun,
      card_twoSlotRemainder_index subsetSlot alphaSlot hne]
    rw [show T - 1 = (T - 2) + 1 by omega, pow_succ]
    ring
  calc
    (Finset.univ.filter fun tape : Fin T → Answer Alpha Subset =>
        success (twoSlotData subsetSlot alphaSlot tape)
          (subsetAnswer (tape subsetSlot))
          (alphaAnswer (tape alphaSlot))).card
      ≤ good.card := by
        apply Finset.card_le_card_of_injOn (fun tape => (dataOf tape, pairOf tape))
        · intro tape htape
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            (Finset.mem_filter.mp htape).2⟩
        · intro first hfirst second hsecond heq
          exact hsplit heq
    _ ≤ Fintype.card Data * pairBudget := hgood
    _ = pairBudget * Fintype.card (Answer Alpha Subset) ^ (T - 1) := by
      rw [hdata]
      ring


theorem two_projection_dependent_tape_ratio_le
    {Alpha Subset : Type*} [Fintype Alpha] [Fintype Subset]
    [DecidableEq Alpha] [DecidableEq Subset]
    [Nonempty Alpha] [Nonempty Subset]
    {T : ℕ} (subsetSlot alphaSlot : Fin T) (hne : subsetSlot ≠ alphaSlot)
    (success : TwoSlotData Alpha Subset T subsetSlot alphaSlot →
      Subset → Alpha → Prop) [∀ data, DecidableRel (success data)]
    (epsilon : ℚ)
    (hpairs : ∀ data,
      ((Finset.univ.filter fun pair : Subset × Alpha =>
        success data pair.1 pair.2).card : ℚ) /
          (Fintype.card Subset * Fintype.card Alpha) ≤ epsilon) :
    ((Finset.univ.filter fun tape : Fin T → Answer Alpha Subset =>
      success (twoSlotData subsetSlot alphaSlot tape)
        (subsetAnswer (tape subsetSlot))
        (alphaAnswer (tape alphaSlot))).card : ℚ) /
      (Fintype.card (Answer Alpha Subset) : ℚ) ^ T ≤ epsilon := by
  classical
  let Data := TwoSlotData Alpha Subset T subsetSlot alphaSlot
  let pairOf : (Fin T → Answer Alpha Subset) → Subset × Alpha := fun tape =>
    (subsetAnswer (tape subsetSlot), alphaAnswer (tape alphaSlot))
  let dataOf : (Fin T → Answer Alpha Subset) → Data :=
    twoSlotData subsetSlot alphaSlot
  have hsplit : Function.Injective (fun tape => (dataOf tape, pairOf tape)) := by
    intro first second heq
    funext k
    by_cases hks : k = subsetSlot
    · subst k
      apply Prod.ext
      · exact congrArg (fun value => value.1.1.1) heq
      · exact congrArg (fun value => value.2.1) heq
    · by_cases hka : k = alphaSlot
      · subst k
        apply Prod.ext
        · exact congrArg (fun value => value.2.2) heq
        · exact congrArg (fun value => value.1.1.2) heq
      · exact congrFun (congrArg (fun value => value.1.2) heq) ⟨k, hks, hka⟩
  let event : Finset (Fin T → Answer Alpha Subset) := Finset.univ.filter fun tape =>
    success (twoSlotData subsetSlot alphaSlot tape)
      (subsetAnswer (tape subsetSlot)) (alphaAnswer (tape alphaSlot))
  let good : Finset (Data × (Subset × Alpha)) := Finset.univ.filter fun value =>
    success value.1 value.2.1 value.2.2
  have hevent : event.card ≤ good.card := by
    apply Finset.card_le_card_of_injOn (fun tape => (dataOf tape, pairOf tape))
    · intro tape htape
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp htape).2⟩
    · intro first hfirst second hsecond heq
      exact hsplit heq
  have hpairDen : (0 : ℚ) <
      Fintype.card Subset * Fintype.card Alpha := by
    have hSubset : 0 < Fintype.card Subset := Fintype.card_pos
    have hAlpha : 0 < Fintype.card Alpha := Fintype.card_pos
    exact_mod_cast Nat.mul_pos hSubset hAlpha
  have hanswerCard : (Fintype.card (Answer Alpha Subset) : ℚ) =
      Fintype.card Subset * Fintype.card Alpha := by
    simp [Answer, mul_comm]
  have hpair (data : Data) :
      ((Finset.univ.filter fun pair : Subset × Alpha =>
        success data pair.1 pair.2).card : ℚ) ≤
          epsilon * Fintype.card (Answer Alpha Subset) := by
    have h := (div_le_iff₀ hpairDen).mp (hpairs data)
    rw [hanswerCard]
    exact h
  have hgoodEq : good.card = ∑ data : Data,
      (Finset.univ.filter fun pair : Subset × Alpha =>
        success data pair.1 pair.2).card := by
    dsimp [good]
    rw [Bcs.card_filter_prod_fst]
  have hgood : (good.card : ℚ) ≤
      Fintype.card Data *
        (epsilon * Fintype.card (Answer Alpha Subset)) := by
    rw [hgoodEq]
    push_cast
    calc
      ∑ data : Data, ((Finset.univ.filter fun pair : Subset × Alpha =>
          success data pair.1 pair.2).card : ℚ)
        ≤ ∑ _data : Data,
            epsilon * Fintype.card (Answer Alpha Subset) :=
          Finset.sum_le_sum (fun data _ => hpair data)
      _ = Fintype.card Data *
          (epsilon * Fintype.card (Answer Alpha Subset)) := by simp
  have hT : 2 ≤ T := by
    have hs := subsetSlot.isLt
    have ha := alphaSlot.isLt
    have hv : subsetSlot.val ≠ alphaSlot.val := fun h => hne (Fin.ext h)
    omega
  have hdata : (Fintype.card Data : ℚ) =
      (Fintype.card (Answer Alpha Subset) : ℚ) ^ (T - 1) := by
    have hnat : Fintype.card Data =
        Fintype.card (Answer Alpha Subset) ^ (T - 1) := by
      dsimp [Data, TwoSlotData, TwoSlotRemainder]
      rw [Fintype.card_prod, Fintype.card_fun,
        card_twoSlotRemainder_index subsetSlot alphaSlot hne]
      rw [show T - 1 = (T - 2) + 1 by omega, pow_succ]
      ring
    exact_mod_cast hnat
  have hN : (0 : ℚ) < Fintype.card (Answer Alpha Subset) := by
    exact_mod_cast Fintype.card_pos
  have hpow : (Fintype.card (Answer Alpha Subset) : ℚ) ^ T =
      (Fintype.card (Answer Alpha Subset) : ℚ) ^ (T - 1) *
        Fintype.card (Answer Alpha Subset) := by
    calc
      (Fintype.card (Answer Alpha Subset) : ℚ) ^ T =
          (Fintype.card (Answer Alpha Subset) : ℚ) ^ ((T - 1) + 1) := by
            congr 1
            omega
      _ = _ := pow_succ _ _
  rw [div_le_iff₀ (pow_pos hN T)]
  calc
    ((Finset.univ.filter fun tape : Fin T → Answer Alpha Subset =>
        success (twoSlotData subsetSlot alphaSlot tape)
          (subsetAnswer (tape subsetSlot))
          (alphaAnswer (tape alphaSlot))).card : ℚ)
      ≤ (good.card : ℚ) := by exact_mod_cast hevent
    _ ≤ Fintype.card Data *
        (epsilon * Fintype.card (Answer Alpha Subset)) := hgood
    _ = epsilon * (Fintype.card (Answer Alpha Subset) : ℚ) ^ T := by
      rw [hdata, hpow]
      ring





def definingAlphaAnswer
    {Alpha Subset Query : Type*} [BEq Query] [LawfulBEq Query]
    {T : ℕ}
    (trace : Bcs.FirstOccurrenceTrace
      (Fin T → Answer Alpha Subset) Query T)
    (tape : Fin T → Answer Alpha Subset) : Alpha :=
  alphaAnswer (tape (trace.alphaSlot tape))

def definingSubsetAnswer
    {Alpha Subset Query : Type*} [BEq Query] [LawfulBEq Query]
    {T : ℕ}
    (trace : Bcs.FirstOccurrenceTrace
      (Fin T → Answer Alpha Subset) Query T)
    (tape : Fin T → Answer Alpha Subset) : Subset :=
  subsetAnswer (tape (trace.subsetSlot tape))

def appendIfMissing [DecidableEq α] (trace : List α) (query : α) : List α :=
  if query ∈ trace then trace else trace ++ [query]

theorem mem_appendIfMissing [DecidableEq α] (trace : List α) (query : α) :
    query ∈ appendIfMissing trace query := by
  by_cases h : query ∈ trace <;> simp [appendIfMissing, h]

theorem mem_appendIfMissing_of_mem [DecidableEq α]
    {trace : List α} {query item : α} (hitem : item ∈ trace) :
    item ∈ appendIfMissing trace query := by
  by_cases hquery : query ∈ trace <;>
    simp [appendIfMissing, hquery, hitem]

theorem length_appendIfMissing_le [DecidableEq α]
    (trace : List α) (query : α) :
    (appendIfMissing trace query).length ≤ trace.length + 1 := by
  by_cases h : query ∈ trace <;> simp [appendIfMissing, h]

theorem idxOf_appendIfMissing_of_mem [DecidableEq α]
    (trace : List α) (query item : α) (hitem : item ∈ trace) :
    (appendIfMissing trace query).idxOf item = trace.idxOf item := by
  unfold appendIfMissing
  split
  · rfl
  · exact List.idxOf_append_of_mem hitem

theorem take_appendIfMissing_congr [DecidableEq α]
    (left right : List α) (query : α) (k : ℕ)
    (h : left.take k = right.take k) :
    (appendIfMissing left query).take k =
      (appendIfMissing right query).take k := by
  by_cases hleft : k ≤ left.length
  · have hright : k ≤ right.length := by
      have hlen := congrArg List.length h
      simpa [List.length_take, Nat.min_eq_left hleft] using hlen.symm
    unfold appendIfMissing
    split <;> split
    all_goals simpa [List.take_append_of_le_length hleft,
      List.take_append_of_le_length hright] using h
  · have hleftLen : left.length < k := Nat.lt_of_not_ge hleft
    have hlen := congrArg List.length h
    have hrightLen : right.length < k := by
      by_contra hnot
      have hk : k ≤ right.length := Nat.le_of_not_gt hnot
      simp [List.length_take, Nat.min_eq_right (Nat.le_of_lt hleftLen),
        Nat.min_eq_left hk] at hlen
      omega
    have heq : left = right := by
      simpa [(List.take_eq_self_iff left).2 (Nat.le_of_lt hleftLen),
        (List.take_eq_self_iff right).2 (Nat.le_of_lt hrightLen)] using h
    subst right
    rfl

theorem idxOf_eq_of_take_congr
    {Q : Type*} [BEq Q] [LawfulBEq Q]
    (left right : List Q) (query : Q) (j : ℕ)
    (hmem : query ∈ left) (hidx : left.idxOf query = j)
    (htake : left.take (j + 1) = right.take (j + 1)) :
    right.idxOf query = j := by
  have hmemTake : query ∈ left.take (j + 1) :=
    (List.mem_take_iff_idxOf_lt hmem).2 (by omega)
  have hmemTake' : query ∈ right.take (j + 1) := htake ▸ hmemTake
  have hmem' : query ∈ right := List.mem_of_mem_take hmemTake'
  have hupper : right.idxOf query < j + 1 :=
    (List.mem_take_iff_idxOf_lt hmem').1 hmemTake'
  have htakej : left.take j = right.take j := by
    have hprefix := congrArg (List.take j) htake
    simpa [List.take_take] using hprefix
  have hnot : query ∉ left.take j := by
    intro hquery
    have hlt := (List.mem_take_iff_idxOf_lt hmem).1 hquery
    omega
  have hnot' : query ∉ right.take j := by simpa [htakej.symm] using hnot
  have hlower : ¬ right.idxOf query < j := by
    intro hlt
    exact hnot' ((List.mem_take_iff_idxOf_lt hmem').2 hlt)
  omega

def augmentedTrace [DecidableEq AlphaKey] [DecidableEq SubsetKey]
    (trace : List (Query AlphaKey SubsetKey))
    (alphaKey : AlphaKey) (subsetKey : SubsetKey) :
    List (Query AlphaKey SubsetKey) :=
  appendIfMissing
    (appendIfMissing trace (.alpha alphaKey)) (.subset subsetKey)

theorem alpha_mem_augmentedTrace [DecidableEq AlphaKey] [DecidableEq SubsetKey]
    (trace : List (Query AlphaKey SubsetKey))
    (alphaKey : AlphaKey) (subsetKey : SubsetKey) :
    Query.alpha alphaKey ∈ augmentedTrace trace alphaKey subsetKey := by
  unfold augmentedTrace
  have hmem := mem_appendIfMissing trace (Query.alpha alphaKey)
  exact mem_appendIfMissing_of_mem hmem

theorem subset_mem_augmentedTrace [DecidableEq AlphaKey] [DecidableEq SubsetKey]
    (trace : List (Query AlphaKey SubsetKey))
    (alphaKey : AlphaKey) (subsetKey : SubsetKey) :
    Query.subset subsetKey ∈ augmentedTrace trace alphaKey subsetKey := by
  exact mem_appendIfMissing _ _

theorem augmentedTrace_length_le [DecidableEq AlphaKey] [DecidableEq SubsetKey]
    (trace : List (Query AlphaKey SubsetKey))
    (alphaKey : AlphaKey) (subsetKey : SubsetKey) :
    (augmentedTrace trace alphaKey subsetKey).length ≤ trace.length + 2 := by
  unfold augmentedTrace
  exact (length_appendIfMissing_le _ _).trans (by
    have h := length_appendIfMissing_le trace (Query.alpha alphaKey)
    omega)

def firstOccurrenceTrace
    {Ω AlphaKey SubsetKey : Type*} [Fintype Ω]
    [DecidableEq AlphaKey] [DecidableEq SubsetKey]
    (queryBudget : ℕ)
    (trace : Ω → List (Query AlphaKey SubsetKey))
    (alphaKey : Ω → AlphaKey) (subsetKey : Ω → SubsetKey)
    (trace_length : ∀ ω, (trace ω).length ≤ queryBudget) :
    Bcs.FirstOccurrenceTrace Ω (Query AlphaKey SubsetKey) (queryBudget + 2) where
  trace ω := augmentedTrace (trace ω) (alphaKey ω) (subsetKey ω)
  alphaQuery ω := .alpha (alphaKey ω)
  subsetQuery ω := .subset (subsetKey ω)
  alpha_mem ω := alpha_mem_augmentedTrace _ _ _
  subset_mem ω := subset_mem_augmentedTrace _ _ _
  separated _ := by simp
  trace_length ω :=
    (augmentedTrace_length_le _ _ _).trans (by
      have h := trace_length ω
      omega)

def lazyFirstOccurrenceTrace
    {AlphaKey SubsetKey Alpha Subset Output : Type*}
    [DecidableEq AlphaKey] [DecidableEq SubsetKey]
    [Fintype Alpha] [Fintype Subset]
    (queryBudget : ℕ)
    (adversary : Merkle.RandomOracle.Tree
      (Query AlphaKey SubsetKey) (Answer Alpha Subset) Output queryBudget)
    (dflt : Answer Alpha Subset)
    (alphaKey : Output → AlphaKey) (subsetKey : Output → SubsetKey) :
    Bcs.FirstOccurrenceTrace
      (Fin (queryBudget + 2) → Answer Alpha Subset)
      (Query AlphaKey SubsetKey) (queryBudget + 2) :=
  firstOccurrenceTrace queryBudget
    (fun tape => (Merkle.RandomOracle.lazyRun tape dflt adversary []).2.1)
    (fun tape => alphaKey (Merkle.RandomOracle.lazyRun tape dflt adversary []).1)
    (fun tape => subsetKey (Merkle.RandomOracle.lazyRun tape dflt adversary []).1)
    (fun tape => by
      simpa using
        (Merkle.RandomOracle.lazyRun_seen_length_le tape dflt adversary []))

def canonicalAlphaTargetFromPrefix
    {AlphaKey Response D : Type*}
    (fallback : AlphaKey)
    (pref : List (Query AlphaKey (AlphaKey × Response))) (_fixed : D) :
    Query AlphaKey (AlphaKey × Response) :=
  match pref.getLast? with
  | some (.subset value) => .alpha value.1
  | _ => .alpha fallback

def canonicalSubsetKeyFromPrefix
    {AlphaKey Response : Type*}
    (fallback : AlphaKey × Response)
    (pref : List (Query AlphaKey (AlphaKey × Response))) :
    AlphaKey × Response :=
  match pref.getLast? with
  | some (.subset value) => value
  | _ => fallback

noncomputable def canonicalCaseAFloorSubsetKey
    {AlphaKey Alpha Subset Response Output : Type*} {N : ℕ}
    [DecidableEq AlphaKey] [DecidableEq Response]
    (adversary : Merkle.RandomOracle.Tree
      (Query AlphaKey (AlphaKey × Response)) (Answer Alpha Subset) Output N)
    (dflt : Answer Alpha Subset) (alphaKey : AlphaKey)
    (responseOf : Output → Response) (i : Fin (N + 2))
    (pref : Sumcheck.Prefix (Answer Alpha Subset) i.val) :
    AlphaKey × Response :=
  let padded := Merkle.RandomOracle.pad (T := N + 2) dflt pref
  match Merkle.RandomOracle.slotQuery (T := N + 2) dflt adversary pref with
  | some (.subset value) => value
  | _ =>
      (alphaKey,
        responseOf (Merkle.RandomOracle.lazyRun padded dflt adversary []).1)

theorem canonicalCaseAFloorSubsetKey_eq
    {AlphaKey Alpha Subset Response Output : Type*} {N : ℕ}
    [DecidableEq AlphaKey] [DecidableEq Response]
    [Fintype Alpha] [Fintype Subset]
    (adversary : Merkle.RandomOracle.Tree
      (Query AlphaKey (AlphaKey × Response)) (Answer Alpha Subset) Output N)
    (dflt : Answer Alpha Subset) (alphaKey : AlphaKey)
    (responseOf : Output → Response)
    (listed win bindBreak :
      (Fin (N + 2) → Answer Alpha Subset) → Prop)
    (i : Fin (N + 2)) (tape : Fin (N + 2) → Answer Alpha Subset)
    (hcase : (lazyFirstOccurrenceTrace N adversary dflt
      (fun _output ↦ alphaKey)
      (fun output ↦ (alphaKey, responseOf output))).caseA
        listed win bindBreak i tape)
    (hunlisted : ¬listed tape) :
    canonicalCaseAFloorSubsetKey adversary dflt alphaKey responseOf i
        (Sumcheck.extract_prefix tape i) =
      (alphaKey,
        responseOf (Merkle.RandomOracle.lazyRun tape dflt adversary []).1) := by
  classical
  let run := Merkle.RandomOracle.lazyRun tape dflt adversary []
  let seen := run.2.1
  let target : Query AlphaKey (AlphaKey × Response) :=
    .subset (alphaKey, responseOf run.1)
  let first := appendIfMissing seen (.alpha alphaKey)
  let augmented := appendIfMissing first target
  have hslot :=
    (lazyFirstOccurrenceTrace N adversary dflt
      (fun _output ↦ alphaKey)
      (fun output ↦ (alphaKey, responseOf output))).subsetSlot_eq_of_caseA_floor
        listed win bindBreak i tape hcase hunlisted
  have hidx : augmented.idxOf target = i.val := by
    exact Fin.ext_iff.mp hslot
  by_cases hi : i.val < seen.length
  · have htargetSeen : target ∈ seen := by
      by_contra hnot
      have hnotFirst : target ∉ first := by
        unfold first appendIfMissing
        split
        · exact hnot
        · simp [hnot, target]
      have htargetIndex : augmented.idxOf target = first.length := by
        rw [show augmented = first ++ [target] by
          simp [augmented, appendIfMissing, hnotFirst]]
        rw [List.idxOf_append_of_notMem hnotFirst]
        simp
      have hseenFirst : seen.length ≤ first.length := by
        unfold first appendIfMissing
        split <;> simp
      rw [hidx] at htargetIndex
      omega
    have htargetFirst : target ∈ first :=
      mem_appendIfMissing_of_mem htargetSeen
    have hidxSeen : seen.idxOf target = i.val := by
      rw [idxOf_appendIfMissing_of_mem first target target htargetFirst,
        idxOf_appendIfMissing_of_mem seen (.alpha alphaKey) target
          htargetSeen] at hidx
      exact hidx
    have hget : seen[i.val]? = some target := by
      rw [List.getElem?_eq_getElem hi]
      congr 1
      have htargetIndexLt : seen.idxOf target < seen.length :=
        List.idxOf_lt_length_of_mem htargetSeen
      simpa only [hidxSeen] using List.getElem_idxOf htargetIndexLt
    have hslotQuery := Merkle.RandomOracle.slotQuery_eq
      (T := N + 2) dflt adversary (j := i.val) (by omega) tape
    have hslotQuery' :
        Merkle.RandomOracle.slotQuery (T := N + 2) dflt adversary
            (Sumcheck.extract_prefix tape i) = some target := by
      convert hslotQuery.trans hget using 1
      congr 1
    simp only [canonicalCaseAFloorSubsetKey, hslotQuery', target, run]
  · have hseenLe : seen.length ≤ i.val := Nat.le_of_not_gt hi
    let padded := Merkle.RandomOracle.pad (T := N + 2) dflt
      (Sumcheck.extract_prefix tape i)
    have hagree : ∀ j : Fin (N + 2), j.val < seen.length →
        tape j = padded j := by
      intro j hj
      symm
      exact Merkle.RandomOracle.pad_agree dflt
        (Sumcheck.extract_prefix tape i) j (hj.trans_le hseenLe)
    have hrun : Merkle.RandomOracle.lazyRun tape dflt adversary [] =
        Merkle.RandomOracle.lazyRun padded dflt adversary [] := by
      apply Merkle.RandomOracle.lazyRun_eq_of_agree_below_seen_length
      simpa only [run, seen] using hagree
    have hnone : seen[i.val]? = none :=
      List.getElem?_eq_none hseenLe
    have hslotQuery := Merkle.RandomOracle.slotQuery_eq
      (T := N + 2) dflt adversary (j := i.val) (by omega) tape
    have hslotQuery' :
        Merkle.RandomOracle.slotQuery (T := N + 2) dflt adversary
            (Sumcheck.extract_prefix tape i) = none := by
      convert hslotQuery.trans hnone using 1
      congr 1
    simp only [canonicalCaseAFloorSubsetKey, hslotQuery']
    rw [← hrun]

theorem canonicalCaseB_prefix_subsetKey
    {AlphaKey Alpha Subset Response Output : Type*} {N : ℕ}
    [DecidableEq AlphaKey] [DecidableEq Response]
    [Fintype Alpha] [Fintype Subset]
    (adversary : Merkle.RandomOracle.Tree
      (Query AlphaKey (AlphaKey × Response)) (Answer Alpha Subset) Output N)
    (dflt : Answer Alpha Subset)
    (keyOf : Output → AlphaKey) (responseOf : Output → Response)
    (fallback : AlphaKey × Response)
    (win bindBreak : (Fin (N + 2) → Answer Alpha Subset) → Prop)
    (i : Fin (N + 2)) (tape : Fin (N + 2) → Answer Alpha Subset)
    (hcase : (lazyFirstOccurrenceTrace N adversary dflt keyOf
      (fun output ↦ (keyOf output, responseOf output))).caseB
        win bindBreak i tape) :
    let output := (Merkle.RandomOracle.lazyRun tape dflt adversary []).1
    let seen := (Merkle.RandomOracle.lazyRun tape dflt adversary []).2.1
    canonicalSubsetKeyFromPrefix fallback (seen.take (i.val + 1)) =
      (keyOf output, responseOf output) := by
  dsimp only
  let output := (Merkle.RandomOracle.lazyRun tape dflt adversary []).1
  let seen := (Merkle.RandomOracle.lazyRun tape dflt adversary []).2.1
  let alphaQuery : Query AlphaKey (AlphaKey × Response) :=
    .alpha (keyOf output)
  let subsetQuery : Query AlphaKey (AlphaKey × Response) :=
    .subset (keyOf output, responseOf output)
  let first := appendIfMissing seen alphaQuery
  have hsubsetSeen : subsetQuery ∈ seen := by
    by_contra hmissing
    have hmissingFirst : subsetQuery ∉ first := by
      unfold first appendIfMissing
      split
      · exact hmissing
      · simp [hmissing, subsetQuery, alphaQuery]
    have halphaFirst : alphaQuery ∈ first := mem_appendIfMissing _ _
    have halphaLt : first.idxOf alphaQuery < first.length :=
      List.idxOf_lt_length_of_mem halphaFirst
    have horder := hcase.2.2.2
    change (appendIfMissing first subsetQuery).idxOf subsetQuery <
      (appendIfMissing first subsetQuery).idxOf alphaQuery at horder
    have htrace : appendIfMissing first subsetQuery = first ++ [subsetQuery] := by
      simp [appendIfMissing, hmissingFirst]
    rw [htrace, List.idxOf_append_of_notMem hmissingFirst,
      List.idxOf_append_of_mem halphaFirst] at horder
    simp at horder
    omega
  have hidxSeen : seen.idxOf subsetQuery = i.val := by
    have hslot := hcase.2.2.1
    change (appendIfMissing first subsetQuery).idxOf subsetQuery = i.val at hslot
    have hsubsetFirst : subsetQuery ∈ first :=
      mem_appendIfMissing_of_mem hsubsetSeen
    have hfinal : appendIfMissing first subsetQuery = first := by
      simp [appendIfMissing, hsubsetFirst]
    have hfirst : first.idxOf subsetQuery = seen.idxOf subsetQuery := by
      unfold first appendIfMissing
      split
      · rfl
      · exact List.idxOf_append_of_mem hsubsetSeen
    rw [hfinal, hfirst] at hslot
    exact hslot
  have hilt : i.val < seen.length := by
    rw [← hidxSeen]
    exact List.idxOf_lt_length_of_mem hsubsetSeen
  have hget : seen[i.val] = subsetQuery := by
    have hidxlt : seen.idxOf subsetQuery < seen.length :=
      List.idxOf_lt_length_of_mem hsubsetSeen
    simpa only [hidxSeen] using List.getElem_idxOf hidxlt
  rw [List.take_succ_eq_append_getElem hilt, hget]
  simp [canonicalSubsetKeyFromPrefix, subsetQuery]
  exact ⟨rfl, rfl⟩

def canonicalResponseAtSlot
    {AlphaKey Alpha Subset Response Output : Type*} {N : ℕ}
    [DecidableEq AlphaKey] [DecidableEq Response]
    (adversary : Merkle.RandomOracle.Tree
      (Query AlphaKey (AlphaKey × Response)) (Answer Alpha Subset) Output N)
    (dflt : Answer Alpha Subset) (fallback : AlphaKey × Response)
    (i : Fin (N + 2)) (tape : Fin (N + 2) → Answer Alpha Subset) : Response :=
  (canonicalSubsetKeyFromPrefix fallback
    ((Merkle.RandomOracle.lazyRun tape dflt adversary []).2.1.take
      (i.val + 1))).2

theorem canonicalResponseAtSlot_eq_of_caseB
    {AlphaKey Alpha Subset Response Output : Type*} {N : ℕ}
    [DecidableEq AlphaKey] [DecidableEq Response]
    [Fintype Alpha] [Fintype Subset]
    (adversary : Merkle.RandomOracle.Tree
      (Query AlphaKey (AlphaKey × Response)) (Answer Alpha Subset) Output N)
    (dflt : Answer Alpha Subset)
    (keyOf : Output → AlphaKey) (responseOf : Output → Response)
    (fallback : AlphaKey × Response)
    (win bindBreak : (Fin (N + 2) → Answer Alpha Subset) → Prop)
    (i : Fin (N + 2)) (tape : Fin (N + 2) → Answer Alpha Subset)
    (hcase : (lazyFirstOccurrenceTrace N adversary dflt keyOf
      (fun output ↦ (keyOf output, responseOf output))).caseB
        win bindBreak i tape) :
    canonicalResponseAtSlot adversary dflt fallback i tape =
      responseOf (Merkle.RandomOracle.lazyRun tape dflt adversary []).1 := by
  have h := canonicalCaseB_prefix_subsetKey adversary dflt keyOf responseOf
    fallback win bindBreak i tape hcase
  simpa only [canonicalResponseAtSlot] using congrArg Prod.snd h

theorem canonicalResponseAtSlot_congr
    {AlphaKey Alpha Subset Response Output : Type*} {N : ℕ}
    [DecidableEq AlphaKey] [DecidableEq Response]
    (adversary : Merkle.RandomOracle.Tree
      (Query AlphaKey (AlphaKey × Response)) (Answer Alpha Subset) Output N)
    (dflt : Answer Alpha Subset) (fallback : AlphaKey × Response)
    (i : Fin (N + 2))
    (left right : Fin (N + 2) → Answer Alpha Subset)
    (hagree : ∀ j, j.val < i.val → left j = right j) :
    canonicalResponseAtSlot adversary dflt fallback i left =
      canonicalResponseAtSlot adversary dflt fallback i right := by
  have hseen := Merkle.RandomOracle.lazyRun_seen_take_congr
    left right dflt i.val hagree adversary []
  exact congrArg
    (fun pref ↦ (canonicalSubsetKeyFromPrefix fallback pref).2) hseen

end Bcs.TypedFiatShamir
