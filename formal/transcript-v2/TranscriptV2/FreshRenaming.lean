import TranscriptV2.FreshOracle

/-! An online decoder may choose the name of a fresh query from its
already answered prefix. Memoizing raw answers prevents that choice from
changing a repeated query's answer. An erasure back to the raw input proves
freshness, and uniform averaging then ignores the chosen fresh names. -/
noncomputable section
namespace TranscriptV2.FreshOracle
open Finset Merkle.RandomOracle
open scoped Classical

variable {P L A Out S : Type} [DecidableEq P]

def rename (label : S → P → L) (advance : S → P → A → S) : {fuel : ℕ} →
    Tree P A Out fuel → Finset P → (P → A) → S → Tree L A Out fuel
  | _, .done output, _, _, _ => .done output
  | _, .query point next, known, cache, state =>
      if point ∈ known then (rename label advance (next (cache point)) known cache state).weaken
      else .query (label state point) fun answer =>
        rename label advance (next answer) (insert point known)
          (Function.update cache point answer) (advance state point answer)

def memoize {fuel : ℕ} (program : Tree P A Out fuel) (known : Finset P) (cache : P → A) :
    Tree P A Out fuel := rename (fun _ : Unit => id) (fun _ _ _ => ()) program known cache ()

/-- Each recorded name is chosen using precisely the preceding answers.
This exposes the online invariant without a claim about successful outputs. -/
def NamedTrace (label : S → P → L) (advance : S → P → A → S) (erase : L → P) :
    S → List (L × A) → Prop
  | _, [] => True
  | state, (point,answer)::rest =>
      label state (erase point) = point ∧ NamedTrace label advance erase
        (advance state (erase point) answer) rest

omit [DecidableEq P] in
theorem NamedTrace.append {label : S → P → L} {advance : S → P → A → S}
    {erase : L → P} {state : S} {first rest : List (L × A)}
    (named : NamedTrace label advance erase state (first ++ rest)) :
    NamedTrace label advance erase state first ∧
      NamedTrace label advance erase
        (first.foldl (fun past qa => advance past (erase qa.1) qa.2) state) rest := by
  induction first generalizing state with
  | nil => exact ⟨trivial,named⟩
  | cons qa first ih =>
      obtain ⟨head,tail⟩ := named
      obtain ⟨initial,suffix⟩ := ih tail
      exact ⟨⟨head,initial⟩,suffix⟩

omit [DecidableEq P] in
theorem NamedTrace.name_after {label : S → P → L} {advance : S → P → A → S}
    {erase : L → P} {state : S} {first rest : List (L × A)} {point : L} {answer : A}
    (named : NamedTrace label advance erase state (first ++ (point,answer)::rest)) :
    label (first.foldl (fun past qa => advance past (erase qa.1) qa.2) state) (erase point) = point :=
  named.append.2.1

theorem rename_trace (label : S → P → L) (advance : S → P → A → S)
    (erase : L → P) (erases : ∀ state point, erase (label state point) = point)
    {fuel : ℕ} (program : Tree P A Out fuel) (known : Finset P) (cache : P → A)
    (state : S) (H : L → A) :
    NamedTrace label advance erase state ((rename label advance program known cache state).run H).2 := by
  induction program generalizing known cache state with
  | done output => trivial
  | query point next ih =>
      by_cases old : point ∈ known
      · simpa only [rename,if_pos old,Tree.run_weaken] using ih (cache point) known cache state
      · simp only [rename,if_neg old,Tree.run_query,NamedTrace,erases]
        exact ⟨trivial,ih (H (label state point)) _ _ _⟩

theorem FreshFrom.mono {fuel : ℕ} {tree : Tree L A Out fuel}
    {first second : L → Prop} (fresh : FreshFrom second tree)
    (subset : ∀ p, first p → second p) : FreshFrom first tree := by
  induction tree generalizing first second with
  | done output => trivial
  | query point next ih =>
      refine ⟨fun member => fresh.1 (subset point member),?_⟩
      intro answer
      apply ih answer (fresh.2 answer)
      intro p member
      exact member.elim Or.inl (fun old => Or.inr (subset p old))

theorem FreshFrom.weaken {fuel : ℕ} {tree : Tree L A Out fuel}
    {known : L → Prop} (fresh : FreshFrom known tree) : FreshFrom known tree.weaken := by
  induction tree generalizing known with
  | done output => trivial
  | query point next ih => exact ⟨fresh.1,fun answer => ih answer (fresh.2 answer)⟩

omit [DecidableEq P] in
theorem FreshFrom.map {Result : Type} {fuel : ℕ} {tree : Tree L A Out fuel}
    {known : L → Prop} (fresh : FreshFrom known tree) (f : Out → Result) :
    FreshFrom known (tree.map f) := by
  induction tree generalizing known with
  | done output => trivial
  | query point next ih => exact ⟨fresh.1,fun answer => ih answer (fresh.2 answer)⟩

omit [DecidableEq P] in
theorem FreshFrom.of_map {Result : Type} {fuel : ℕ} {tree : Tree L A Out fuel}
    {known : L → Prop} (f : Out → Result) (fresh : FreshFrom known (tree.map f)) :
    FreshFrom known tree := by
  induction tree generalizing known with
  | done output => trivial
  | query point next ih => exact ⟨fresh.1,fun answer => ih answer (fresh.2 answer)⟩

omit [DecidableEq P] in
/-- A source that already memoizes its answers needs only a naming state.
Keep that state at the cut so a verifier continuation can resume it exactly. -/
def relabel (label : S → P → L) (advance : S → P → A → S) : {fuel : ℕ} →
    Tree P A Out fuel → S → Tree L A (Out × S) fuel
  | _, .done output, state => .done (output,state)
  | _, .query point next, state => .query (label state point) fun answer =>
      relabel label advance (next answer) (advance state point answer)

omit [DecidableEq P] in
theorem relabel_map {Result : Type} (label : S → P → L) (advance : S → P → A → S)
    {fuel : ℕ} (program : Tree P A Out fuel) (f : Out → Result) (state : S) :
    relabel label advance (program.map f) state =
      (relabel label advance program state).map (Prod.map f id) := by
  induction program generalizing state with
  | done output => rfl
  | query point next ih => exact congrArg (Tree.query (label state point)) (funext fun a => ih a _)

omit [DecidableEq P] in
theorem relabel_fresh (label : S → P → L) (advance : S → P → A → S)
    (erase : L → P) (erases : ∀ state point, erase (label state point) = point)
    {fuel : ℕ} (program : Tree P A Out fuel) (known : P → Prop) (state : S)
    (fresh : FreshFrom known program) :
    FreshFrom (fun point => known (erase point)) (relabel label advance program state) := by
  induction program generalizing known state with
  | done output => trivial
  | query point next ih =>
      refine ⟨by simpa only [erases] using fresh.1,?_⟩
      intro answer
      apply (ih answer _ _ (fresh.2 answer)).mono
      intro p member
      rcases member with same | member
      · subst p
        exact Or.inl (erases state point)
      · exact Or.inr member

omit [DecidableEq P] in
theorem relabel_trace (label : S → P → L) (advance : S → P → A → S)
    (erase : L → P) (erases : ∀ state point, erase (label state point) = point)
    {fuel : ℕ} (program : Tree P A Out fuel) (state : S) (H : L → A) :
    NamedTrace label advance erase state ((relabel label advance program state).run H).2 := by
  induction program generalizing state with
  | done output => trivial
  | query point next ih =>
      simp only [relabel,Tree.run_query,NamedTrace,erases]
      exact ⟨trivial,ih (H (label state point)) _⟩

omit [DecidableEq P] in
theorem relabel_mean [Fintype A] (value : Out → ℚ)
    (label : S → P → L) (advance : S → P → A → S)
    {fuel : ℕ} (program : Tree P A Out fuel) (state : S) :
    mean (fun result => value result.1) (relabel label advance program state) = mean value program := by
  induction program generalizing state with
  | done output => rfl
  | query point next ih =>
      simp only [relabel,mean]
      congr 1
      exact sum_congr rfl (fun answer _ => ih answer _)

theorem relabel_uniform [Fintype P] [Fintype L] [DecidableEq L] [Fintype A] [Nonempty A]
    (value : Out → ℚ) (label : S → P → L) (advance : S → P → A → S)
    (erase : L → P) (erases : ∀ state point, erase (label state point) = point)
    {fuel : ℕ} (program : Tree P A Out fuel) (state : S)
    (fresh : FreshFrom (fun _ => False) program) :
    (∑ H : L → A, value (((relabel label advance program state).run H).1.1)) /
        (Fintype.card A : ℚ)^Fintype.card L =
      (∑ H : P → A, value ((program.run H).1)) /
        (Fintype.card A : ℚ)^Fintype.card P := by
  rw [uniform_mean (fun result : Out × S => value result.1) _
    (relabel_fresh label advance erase erases program _ state fresh),
    relabel_mean,uniform_mean value program fresh]

omit [DecidableEq P] in
theorem relabel_weaken (label : S → P → L) (advance : S → P → A → S)
    {fuel : ℕ} (program : Tree P A Out fuel) (state : S) (H : L → A) :
    (relabel label advance program.weaken state).run H =
      (relabel label advance program state).run H := by
  induction program generalizing state with
  | done output => rfl
  | query point next ih => simp only [Tree.weaken,relabel,Tree.run_query,ih]

omit [DecidableEq P] in
theorem relabel_weakenAdd (label : S → P → L) (advance : S → P → A → S)
    {fuel : ℕ} (program : Tree P A Out fuel) (extra : ℕ) (state : S) (H : L → A) :
    (relabel label advance (program.weakenAdd extra) state).run H =
      (relabel label advance program state).run H := by
  induction extra with
  | zero => rfl
  | succ extra ih => rw [Tree.weakenAdd,relabel_weaken,ih]

omit [DecidableEq P] in
/-- Query naming resumes from its actual state at the submission cut.
Previously unresolved names are not retroactively changed by the replay. -/
theorem relabel_bind {Result : Type} (label : S → P → L) (advance : S → P → A → S)
    {fuel extra : ℕ} (program : Tree P A Out fuel) (replay : Out → Tree P A Result extra)
    (state : S) (H : L → A) :
    (relabel label advance (program.bind replay) state).run H =
      ((relabel label advance program state).bind fun cut =>
        relabel label advance (replay cut.1) cut.2).run H := by
  rw [Tree.run_bind]
  induction program generalizing state with
  | done output => simp only [Tree.bind,relabel_weakenAdd,relabel,Tree.run_done,List.nil_append]
  | query point next ih => simp only [Tree.bind,relabel,Tree.run_query,ih,List.cons_append]

/-- Erasing an actual renamed run yields a run of the source program with
one consistent oracle. Fresh source queries let the current answer be patched
without changing the already reconstructed continuation. -/
theorem relabel_run_exists [Nonempty A]
    (label : S → P → L) (advance : S → P → A → S)
    (erase : L → P) (erases : ∀ state point, erase (label state point) = point)
    {fuel : ℕ} (program : Tree P A Out fuel) (state : S) (H : L → A)
    (known : P → Prop) (fresh : FreshFrom known program) :
    ∃ G : P → A, program.run G =
      (((relabel label advance program state).run H).1.1,
        ((relabel label advance program state).run H).2.map (fun qa => (erase qa.1,qa.2))) := by
  induction program generalizing known state with
  | done output => exact ⟨fun _ => Classical.choice ‹Nonempty A›,rfl⟩
  | query point next ih =>
      let answer := H (label state point)
      obtain ⟨G,run⟩ := ih answer (advance state point answer) _ (fresh.2 answer)
      let updated := Function.update G point answer
      have absent := (fresh.2 answer).not_queried G point (Or.inl rfl)
      have unchanged := Bcs.TotalOracle.run_eq_of_not_mem (next answer) point
        (Bcs.TotalOracle.agreeOff_update point G answer) absent
      refine ⟨updated,?_⟩
      simp only [Tree.run_query,updated,Function.update_self,relabel,List.map_cons,erases]
      change (((next answer).run (Function.update G point answer)).1,
          (point,answer)::((next answer).run (Function.update G point answer)).2) = _
      rw [unchanged,run]

theorem rename_fresh (label : S → P → L) (advance : S → P → A → S)
    (erase : L → P) (erases : ∀ state point, erase (label state point) = point)
    {fuel : ℕ} (program : Tree P A Out fuel) (known : Finset P) (cache : P → A) (state : S) :
    FreshFrom (fun point => erase point ∈ known) (rename label advance program known cache state) := by
  induction program generalizing known cache state with
  | done output => trivial
  | query point next ih =>
      by_cases old : point ∈ known
      · simpa only [rename,if_pos old] using (ih (cache point) known cache state).weaken
      · simp only [rename,if_neg old,FreshFrom]
        refine ⟨by simpa only [erases] using old,?_⟩
        intro answer
        apply (ih answer (insert point known) (Function.update cache point answer)
          (advance state point answer)).mono
        intro p member
        rcases member with same | member
        · subst p
          simp only [erases,mem_insert_self]
        · exact mem_insert_of_mem member

theorem rename_mean [Fintype A] (value : Out → ℚ)
    (label : S → P → L) (advance : S → P → A → S)
    {fuel : ℕ} (program : Tree P A Out fuel) (known : Finset P) (cache : P → A) (state : S) :
    mean value (rename label advance program known cache state) =
      mean value (memoize program known cache) := by
  induction program generalizing known cache state with
  | done output => rfl
  | query point next ih =>
      by_cases old : point ∈ known
      · simp only [rename,memoize,if_pos old,mean_weaken]
        exact ih (cache point) known cache state
      · simp only [rename,memoize,if_neg old,mean]
        congr 1
        apply sum_congr rfl
        intro answer _
        exact ih answer _ _ _

/-- Repeated raw calls are removed only after their original answers have
been cached. This is an equality of outputs for every fixed oracle. -/
theorem memoize_output {fuel : ℕ} (program : Tree P A Out fuel)
    (known : Finset P) (cache H : P → A)
    (agree : ∀ point ∈ known, cache point = H point) :
    ((memoize program known cache).run H).1 = (program.run H).1 := by
  induction program generalizing known cache with
  | done output => rfl
  | query point next ih =>
      by_cases old : point ∈ known
      · simp only [memoize,rename,if_pos old,Tree.run_weaken,Tree.run_query,agree point old]
        exact ih (H point) known cache agree
      · simp only [memoize,rename,if_neg old,Tree.run_query]
        apply ih (H point)
        intro p member
        rcases mem_insert.mp member with rfl | member
        · simp
        · by_cases same : p = point
          · subst p; simp
          · simpa only [Function.update_of_ne same] using agree p member

/-- With finite domains, an online fresh renaming preserves the entire
output distribution. The state and labels may depend on all earlier answers;
only the erasure law is required. Infinite byte domains are handled by the
existing finite-window restriction. -/
theorem rename_uniform [Fintype P] [Fintype L] [DecidableEq L]
    [Fintype A] [Nonempty A] (value : Out → ℚ)
    (label : S → P → L) (advance : S → P → A → S)
    (erase : L → P) (erases : ∀ state point, erase (label state point) = point)
    {fuel : ℕ} (program : Tree P A Out fuel) (cache : P → A) (state : S) :
    (∑ H : L → A, value ((rename label advance program ∅ cache state).run H).1) /
        (Fintype.card A : ℚ)^Fintype.card L =
      (∑ H : P → A, value (program.run H).1) /
        (Fintype.card A : ℚ)^Fintype.card P := by
  rw [uniform_mean value _ (rename_fresh label advance erase erases program ∅ cache state),
    rename_mean]
  have fresh := rename_fresh (fun _ : Unit => id) (fun _ _ _ => ()) id
    (fun _ _ => rfl) program ∅ cache ()
  change FreshFrom (fun point => point ∈ (∅ : Finset P)) (memoize program ∅ cache) at fresh
  rw [← uniform_mean value _ fresh]
  congr 1
  apply sum_congr rfl
  intro H _
  rw [memoize_output program ∅ cache H (by simp)]

end TranscriptV2.FreshOracle
