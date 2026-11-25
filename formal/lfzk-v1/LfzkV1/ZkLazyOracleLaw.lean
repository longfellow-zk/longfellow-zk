import LfzkV1.ZkTwoTape
import Bcs.PotentialOracle
import Bcs.StatisticalDistance

/-! A uniformly sampled lazy oracle tape and a uniform total oracle table
give the same finite observer law whenever the tape covers the query budget. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LfzkV1.ZkLazyOracleLaw

open Bcs Bcs.TotalOracle Finset Merkle.RandomOracle
open scoped Classical

variable {Q D A : Type}

private def Fresh (seen : Q → Prop) : {f : ℕ} → Tree Q D A f → Prop
  | _, .done _ => True
  | _, .query q next => ¬ seen q ∧ ∀ d, Fresh (fun p => p = q ∨ seen p) (next d)

private theorem fresh_weaken {seen : Q → Prop} {f : ℕ} (t : Tree Q D A f) (h : Fresh seen t) :
    Fresh seen t.weaken := by
  induction t generalizing seen with
  | done => trivial
  | query q next ih => exact ⟨h.1, fun d => ih d (h.2 d)⟩

private theorem fresh_not_queried {seen : Q → Prop} {f : ℕ} (t : Tree Q D A f)
    (h : Fresh seen t) (H : Q → D) (q : Q) (hq : seen q) : q ∉ queried t H := by
  induction t generalizing seen with
  | done => simp
  | query p next ih =>
    intro hp
    rcases List.mem_cons.mp hp with he | ht
    · cases he
      exact h.1 hq
    · exact ih (H p) (h.2 _) (Or.inr hq) ht

private noncomputable def mean [Fintype D] (val : A → ℚ) : {f : ℕ} → Tree Q D A f → ℚ
  | _, .done a => val a
  | _, .query _ next => (∑ d, mean val (next d)) / Fintype.card D

private theorem mean_weaken [Fintype D] (val : A → ℚ) {f : ℕ} (t : Tree Q D A f) :
    mean val t.weaken = mean val t := by
  induction t with
  | done => rfl
  | query _ _ ih => simp only [Tree.weaken, mean, ih]

private theorem uniform_mean [Fintype Q] [DecidableEq Q] [Fintype D] [Nonempty D]
    (val : A → ℚ) {f : ℕ} (t : Tree Q D A f) {seen : Q → Prop} (hf : Fresh seen t) :
    (∑ H : Q → D, val (t.run H).1) / (Fintype.card D : ℚ)^Fintype.card Q = mean val t := by
  have hDpos : 0 < (Fintype.card D : ℚ) := by exact_mod_cast Fintype.card_pos
  have hD := ne_of_gt hDpos
  have hp : (Fintype.card D : ℚ)^Fintype.card Q ≠ 0 := pow_ne_zero _ hD
  induction t generalizing seen with
  | done => simp [mean, Nat.cast_pow, hp]
  | query q next ih =>
    let weight (H : Q → D) (d : D) := val ((next d).run H).1
    have hoff (H H' : Q → D) (he : AgreeOff q H H') (d : D) : weight H d = weight H' d := by
      have hmiss := fresh_not_queried (next d) (hf.2 d) H q (Or.inl rfl)
      exact congrArg (fun o => val o.1) (run_eq_of_not_mem (next d) q he hmiss).symm
    have each (d : D) : (∑ H : Q → D, weight H d) =
        mean val (next d) * (Fintype.card D : ℚ)^Fintype.card Q :=
      (div_eq_iff hp).mp (ih d (hf.2 d))
    change (∑ H : Q → D, weight H (H q)) / (Fintype.card D : ℚ)^Fintype.card Q =
      (∑ d : D, mean val (next d)) / Fintype.card D
    apply (div_eq_div_iff hp hD).mpr
    calc
      _ = ∑ H : Q → D, ∑ d : D, weight H d := sum_coord_mul_rat q weight hoff
      _ = ∑ d : D, ∑ H : Q → D, weight H d := sum_comm
      _ = _ := by simp_rw [each]; rw [sum_mul]

variable [DecidableEq Q]

/-- Remove repeat queries by answering them from the known partial table. -/
private def memo : {f : ℕ} → Tree Q D A f → (Q → Option D) → Tree Q D A f
  | _, .done a, _ => .done a
  | _, .query q next, cache =>
    match cache q with
    | some d => (memo (next d) cache).weaken
    | none => .query q fun d => memo (next d) (Function.update cache q (some d))

/-- Run the same memoization, naming each new query by its tape slot. -/
private def slots (T : ℕ) : {f : ℕ} → Tree Q D A f → (Q → Option D) →
    (k : ℕ) → k + f ≤ T → Tree (Fin T) D A f
  | _, .done a, _, _, _ => .done a
  | f + 1, .query q next, cache, k, h =>
    match cache q with
    | some d => (slots T (next d) cache k (by omega)).weaken
    | none => .query ⟨k, by omega⟩ fun d =>
      slots T (next d) (Function.update cache q (some d)) (k + 1) (by omega)

private theorem update_known (cache : Q → Option D) (q : Q) (d : D) :
    (fun p => Function.update cache q (some d) p ≠ none) = fun p => p = q ∨ cache p ≠ none := by
  funext p
  by_cases h : p = q
  · subst p
    simp
  · simp [h]

private theorem memo_fresh {f : ℕ} (t : Tree Q D A f) (cache : Q → Option D) :
    Fresh (fun q => cache q ≠ none) (memo t cache) := by
  induction t generalizing cache with
  | done => trivial
  | query q next ih =>
    cases hc : cache q with
    | some d =>
      simp only [memo, hc]
      exact fresh_weaken _ (ih d cache)
    | none =>
      simp only [memo, hc, Fresh]
      refine ⟨fun h => h rfl, fun d => ?_⟩
      rw [← update_known cache q d]
      exact ih d _

private theorem slots_fresh {f T : ℕ} (t : Tree Q D A f) (cache : Q → Option D) (k : ℕ)
    (h : k + f ≤ T) : Fresh (fun p => p.val < k) (slots T t cache k h) := by
  induction t generalizing cache k with
  | done => trivial
  | query q next ih =>
    cases hc : cache q with
    | some d =>
      simp only [slots, hc]
      exact fresh_weaken _ (ih d cache k _)
    | none =>
      simp only [slots, hc, Fresh]
      refine ⟨lt_irrefl _, fun d => ?_⟩
      have he : (fun p : Fin T => p.val < k + 1) = fun p => p = ⟨k, by omega⟩ ∨ p.val < k := by
        funext p
        apply propext
        rw [Fin.ext_iff]
        change p.val < k + 1 ↔ p.val = k ∨ p.val < k
        omega
      rw [← he]
      exact ih d _ _ _

private theorem same_mean [Fintype D] {f T : ℕ} (val : A → ℚ) (t : Tree Q D A f)
    (cache : Q → Option D) (k : ℕ) (h : k + f ≤ T) :
    mean val (memo t cache) = mean val (slots T t cache k h) := by
  induction t generalizing cache k with
  | done => rfl
  | query q next ih =>
    cases hc : cache q with
    | some d => simpa only [memo, slots, hc, mean_weaken] using ih d cache k (by omega)
    | none =>
      simp only [memo, slots, hc, mean]
      congr 1
      exact sum_congr rfl fun d _ => ih d _ _ (by omega)

private theorem memo_run {f : ℕ} (t : Tree Q D A f) (H : Q → D) (cache : Q → Option D)
    (hknown : ∀ q d, cache q = some d → H q = d) : ((memo t cache).run H).1 = (t.run H).1 := by
  induction t generalizing cache with
  | done => rfl
  | query q next ih =>
    cases hc : cache q with
    | some d =>
      simp only [memo, hc, Tree.run_weaken, Tree.run_query]
      rw [hknown q d hc]
      exact ih d cache hknown
    | none =>
      simp only [memo, hc, Tree.run_query]
      apply ih (H q) _ _
      intro p d he
      by_cases hp : p = q
      · subst p
        rw [Function.update_self, Option.some.injEq] at he
        exact he
      · exact hknown p d (by simpa only [Function.update_of_ne hp] using he)

private def seenCache {T : ℕ} (tape : Fin T → D) (dflt : D) (seen : List Q) : Q → Option D :=
  fun q => if q ∈ seen then some (tapeAt tape dflt (seen.idxOf q)) else none

private theorem seenCache_append {T : ℕ} (tape : Fin T → D) (dflt : D) (seen : List Q) (q : Q)
    (hq : q ∉ seen) :
    seenCache tape dflt (seen ++ [q]) =
      Function.update (seenCache tape dflt seen) q (some (tapeAt tape dflt seen.length)) := by
  funext p
  by_cases he : p = q
  · subst p
    simp [seenCache, List.idxOf_append_of_notMem hq]
  · by_cases hm : p ∈ seen
    · simp [seenCache, Function.update_of_ne he, hm, List.idxOf_append_of_mem hm]
    · simp [seenCache, hm, he]

private theorem slots_run {f T : ℕ} (t : Tree Q D A f) (tape : Fin T → D) (dflt : D)
    (seen : List Q) (h : seen.length + f ≤ T) :
    ((slots T t (seenCache tape dflt seen) seen.length h).run tape).1 =
      (lazyRun tape dflt t seen).1 := by
  induction t generalizing seen with
  | done => rfl
  | query q next ih =>
    by_cases hq : q ∈ seen
    · simp only [slots, seenCache, if_pos hq, Tree.run_weaken, lazyRun_query]
      exact ih _ seen (by omega)
    · have hlt : seen.length < T := by omega
      have hidx : (seen ++ [q]).idxOf q = seen.length := by simp [List.idxOf_append_of_notMem hq]
      have hslot : tapeAt tape dflt seen.length = tape ⟨seen.length, hlt⟩ := by simp [tapeAt, hlt]
      simp only [slots, show seenCache tape dflt seen q = none by simp [seenCache, hq],
        Tree.run_query, lazyRun_query, if_neg hq, hidx]
      rw [← hslot, ← seenCache_append tape dflt seen q hq]
      simpa only [List.length_append, List.length_singleton] using
        ih (tapeAt tape dflt seen.length) (seen ++ [q]) (by
          simp only [List.length_append, List.length_singleton]
          omega)

/-- The tape and total table experiments have equal probability for every
observer predicate, including predicates of the full trace recorded in its output. -/
theorem lazyRun_statClose [Fintype Q] [Fintype D] [Nonempty D] {f T : ℕ}
    (dflt : D) (t : Tree Q D A f) (h : f ≤ T) :
    StatClose 0 (fun tape : Fin T → D => (lazyRun tape dflt t []).1)
      (fun H : Q → D => (t.run H).1) := by
  classical
  intro P
  let value (a : A) : ℚ := if P a then 1 else 0
  have heager := uniform_mean value (memo t (fun _ => none)) (memo_fresh t (fun _ => none))
  have hlazy := uniform_mean value (slots T t (fun _ => none) 0 (by simpa using h))
    (slots_fresh t (fun _ => none) 0 (by simpa using h))
  have hm := same_mean value t (fun _ => none) 0 (by simpa using h)
  have he : (fun H : Q → D => ((memo t (fun _ => none)).run H).1) =
      fun H => (t.run H).1 := by
    funext H
    exact memo_run t H (fun _ => none) (by simp)
  have hl : (fun tape : Fin T → D => ((slots T t (fun _ => none) 0 (by simpa using h)).run tape).1) =
      fun tape => (lazyRun tape dflt t []).1 := by
    funext tape
    exact slots_run t tape dflt [] (by simpa using h)
  have heq (H : Q → D) := congrFun he H
  have hlq (tape : Fin T → D) := congrFun hl tape
  simp only [heq] at heager
  simp only [hlq] at hlazy
  have hf := hlazy.trans (hm.symm.trans heager.symm)
  simp only [value, Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, mul_one, mul_zero, add_zero,
    Fintype.card_fin] at hf
  simp only [probOf, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  rw [hf, sub_self, abs_zero]


section TwoTables

open LfzkV1.ZkTwoTape

variable {Q₁ Q₂ : Type} [DecidableEq Q₁] [DecidableEq Q₂]
variable {T₁ T₂ : ℕ}

private def rename {P Q' D' O : Type} (name : P → Q') : {f : ℕ} →
    Tree P D' O f → Tree Q' D' O f
  | _, .done a => .done a
  | _, .query q next => .query (name q) fun d => rename name (next d)

private theorem renamed_run {P Q' D' O : Type} (name : P → Q') {f : ℕ}
    (t : Tree P D' O f) (H : Q' → D') : ((rename name t).run H).1 = (t.run (H ∘ name)).1 := by
  induction t with
  | done => rfl
  | query q next ih => exact ih (H (name q))

abbrev tagLeft {f : ℕ} (t : Tree Q₁ D A f) : Tree (Q₁ ⊕ Q₂) D A f :=
  rename Sum.inl t

abbrev tagRight {f : ℕ} (t : Tree Q₂ D A f) : Tree (Q₁ ⊕ Q₂) D A f :=
  rename Sum.inr t

omit [DecidableEq Q₁] [DecidableEq Q₂] in
@[simp] theorem run_tagLeft {f : ℕ} (t : Tree Q₁ D A f) (G₁ : Q₁ → D) (G₂ : Q₂ → D) :
    ((tagLeft t).run (Sum.elim G₁ G₂)).1 = (t.run G₁).1 := renamed_run _ t _

omit [DecidableEq Q₁] [DecidableEq Q₂] in
@[simp] theorem run_tagRight {f : ℕ} (t : Tree Q₂ D A f) (G₁ : Q₁ → D) (G₂ : Q₂ → D) :
    ((tagRight t).run (Sum.elim G₁ G₂)).1 = (t.run G₂).1 := renamed_run _ t _

private theorem lazyRun2_weaken (τ₁ : Fin T₁ → D) (τ₂ : Fin T₂ → D) (dflt : D)
    {f : ℕ} (t : Tree (Q₁ ⊕ Q₂) D A f) (s₁ : List Q₁) (s₂ : List Q₂) :
    lazyRun2 τ₁ τ₂ dflt t.weaken s₁ s₂ = lazyRun2 τ₁ τ₂ dflt t s₁ s₂ := by
  induction t generalizing s₁ s₂ with
  | done => rfl
  | query q next ih =>
    cases q <;> simp only [Tree.weaken, lazyRun2, ih]

private theorem lazyRun2_weakenAdd (τ₁ : Fin T₁ → D) (τ₂ : Fin T₂ → D) (dflt : D)
    {f : ℕ} (t : Tree (Q₁ ⊕ Q₂) D A f) (l : ℕ) (s₁ : List Q₁) (s₂ : List Q₂) :
    lazyRun2 τ₁ τ₂ dflt (t.weakenAdd l) s₁ s₂ = lazyRun2 τ₁ τ₂ dflt t s₁ s₂ := by
  induction l with
  | zero => rfl
  | succ l ih => rw [Tree.weakenAdd, lazyRun2_weaken, ih]

/-- Running a left-only tree advances exactly the left tape before continuing. -/
theorem lazyRun2_tagLeft_bind {Out : Type} (τ₁ : Fin T₁ → D) (τ₂ : Fin T₂ → D) (dflt : D)
    {f g : ℕ} (t : Tree Q₁ D A f) (k : A → Tree (Q₁ ⊕ Q₂) D Out g)
    (s₁ : List Q₁) (s₂ : List Q₂) :
    lazyRun2 τ₁ τ₂ dflt ((tagLeft t).bind k) s₁ s₂ =
      let out := lazyRun τ₁ dflt t s₁
      lazyRun2 τ₁ τ₂ dflt (k out.1) out.2.1 s₂ := by
  induction t generalizing s₁ with
  | done => exact lazyRun2_weakenAdd _ _ _ _ _ _ _
  | query q next ih => simp only [tagLeft, rename, Tree.bind, lazyRun2, lazyRun_query, ih]

/-- Running a right-only tree advances exactly the right tape before continuing. -/
theorem lazyRun2_tagRight_bind {Out : Type} (τ₁ : Fin T₁ → D) (τ₂ : Fin T₂ → D) (dflt : D)
    {f g : ℕ} (t : Tree Q₂ D A f) (k : A → Tree (Q₁ ⊕ Q₂) D Out g)
    (s₁ : List Q₁) (s₂ : List Q₂) :
    lazyRun2 τ₁ τ₂ dflt ((tagRight t).bind k) s₁ s₂ =
      let out := lazyRun τ₂ dflt t s₂
      lazyRun2 τ₁ τ₂ dflt (k out.1) s₁ out.2.1 := by
  induction t generalizing s₂ with
  | done => exact lazyRun2_weakenAdd _ _ _ _ _ _ _
  | query q next ih => simp only [tagRight, rename, Tree.bind, lazyRun2, lazyRun_query, ih]

private def answerLeft (H : Q₁ → D) : {f : ℕ} → Tree (Q₁ ⊕ Q₂) D A f → Tree Q₂ D A f
  | _, .done a => .done a
  | _, .query (.inl q) next => (answerLeft H (next (H q))).weaken
  | _, .query (.inr q) next => .query q fun d => answerLeft H (next d)

omit [DecidableEq Q₁] [DecidableEq Q₂] in
private theorem run_answerLeft (H : Q₁ → D) (G : Q₂ → D) {f : ℕ}
    (t : Tree (Q₁ ⊕ Q₂) D A f) :
    ((answerLeft H t).run G).1 = (t.run (Sum.elim H G)).1 := by
  induction t with
  | done => rfl
  | query q next ih =>
    cases q with
    | inl q => simpa only [answerLeft, Tree.run_weaken, Tree.run_query, Sum.elim_inl] using ih (H q)
    | inr q => exact ih (G q)

omit [DecidableEq Q₁] in
private theorem run_proj₁ (τ : Fin T₂ → D) (dflt : D) (H : Q₁ → D)
    {f : ℕ} (t : Tree (Q₁ ⊕ Q₂) D A f) (s : List Q₂) :
    ((proj₁ τ dflt t s).run H).1 = (lazyRun τ dflt (answerLeft H t) s).1 := by
  induction t generalizing s with
  | done => rfl
  | query q next ih =>
    cases q with
    | inl q =>
      simp only [proj₁, Tree.run_query, answerLeft, lazyRun_weaken]
      exact ih (H q) s
    | inr q =>
      simp only [proj₁, Tree.run_weaken, answerLeft, lazyRun_query]
      exact ih _ _

/-- Both lazy tapes give the same law as independent total tables, including
when the observer interleaves its queries adaptively. Each tape may be sized
for the whole composed tree since extra unused positions do not change the law. -/
theorem lazyRun2_statClose [Fintype Q₁] [Fintype Q₂] [Fintype D] [Nonempty D]
    (dflt : D) {f : ℕ} (t : Tree (Q₁ ⊕ Q₂) D A f) (h₁ : f ≤ T₁) (h₂ : f ≤ T₂) :
    StatClose 0
      (fun p : (Fin T₁ → D) × (Fin T₂ → D) => lazyRun2 p.1 p.2 dflt t [] [])
      (fun p : (Q₁ → D) × (Q₂ → D) => (t.run (Sum.elim p.1 p.2)).1) := by
  let real (p : (Fin T₁ → D) × (Fin T₂ → D)) := lazyRun2 p.1 p.2 dflt t [] []
  let mid (p : (Q₁ → D) × (Fin T₂ → D)) := ((proj₁ p.2 dflt t []).run p.1).1
  have left : StatClose 0 real mid := by
    let e₁ := Equiv.prodComm (Fin T₂ → D) (Fin T₁ → D)
    let e₂ := Equiv.prodComm (Fin T₂ → D) (Q₁ → D)
    intro P
    rw [← probOf_equiv e₁ real P, ← probOf_equiv e₂ mid P]
    refine statClose_mix le_rfl (fun τ₂ τ₁ => real (τ₁, τ₂)) (fun τ₂ H => mid (H, τ₂)) ?_ P
    intro τ
    have h := lazyRun_statClose dflt (proj₁ τ dflt t []) h₁
    have he : (fun tape : Fin T₁ → D => (lazyRun tape dflt (proj₁ τ dflt t []) []).1) =
        fun tape => lazyRun2 tape τ dflt t [] [] :=
      funext fun tape => lazyRun_proj₁ tape τ dflt t [] []
    rw [he] at h
    exact h
  have right : StatClose 0 mid (fun p : (Q₁ → D) × (Q₂ → D) => (t.run (Sum.elim p.1 p.2)).1) := by
    apply statClose_mix le_rfl (fun H τ => mid (H, τ)) (fun H G => (t.run (Sum.elim H G)).1)
    intro H
    have h := lazyRun_statClose dflt (answerLeft H t) h₂
    simpa only [mid, run_proj₁, run_answerLeft] using h
  simpa only [zero_add] using left.trans right

end TwoTables

end LfzkV1.ZkLazyOracleLaw
