import LfzkV2.Current.ZeroKnowledge.MerkleBound

/-! A commitment programs its own fresh inputs, leaving a pre-existing
oracle table intact everywhere else.  Unlike an empty-cache lazy execution,
this representation retains every earlier oracle answer.  The freshness
splice supplies disjointness from the prior trace; hiding then compares two
such prepared tables over the same unchanged background oracle.

The background may be any total function. It is not exposed to the observer,
which accesses it only through its bounded query tree. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.MerkleCache
open Merkle Merkle.MH Merkle.RandomOracle Finset
open scoped Classical

section FirstHit
variable {Secret Query Answer Value : Type}
variable [DecidableEq Secret] [DecidableEq Query]

/-- Pairwise agreement away from two injective secret markers suffices for
the first-hit count.  Previously cached answers can be arbitrary: the proof
only uses that they are the same for the remaining candidate secrets. -/
theorem caught_card_le {fuel : ℕ} (tree : Tree Query Answer Value fuel)
    (oracle : Secret → Query → Answer) (first second : Secret → Query)
    (first_injective : Function.Injective first) (second_injective : Function.Injective second)
    (candidates : Finset Secret)
    (compatible : ∀ a ∈ candidates, ∀ b ∈ candidates, ∀ q,
      q ≠ first a → q ≠ second a → q ≠ first b → q ≠ second b → oracle a q = oracle b q)
    (caught : ∀ a ∈ candidates, first a ∈ (tree.run (oracle a)).2.map Prod.fst ∨
      second a ∈ (tree.run (oracle a)).2.map Prod.fst) :
    candidates.card ≤ 2*fuel := by
  induction tree generalizing candidates with
  | done value =>
      have empty : candidates = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro a ha
        simpa only [Tree.run_done,List.map_nil,List.not_mem_nil,or_self] using caught a ha
      simp only [empty,card_empty,Nat.zero_le]
  | @query fuel q next ih =>
      let hits := candidates.filter fun a => q = first a ∨ q = second a
      let remaining := candidates \ hits
      have hits_le : hits.card ≤ 2 := by
        have one (marker : Secret → Query) (injective : Function.Injective marker) :
            (candidates.filter fun a => q = marker a).card ≤ 1 := by
          apply card_le_one.mpr
          intro a ha b hb
          exact injective ((mem_filter.mp ha).2.symm.trans (mem_filter.mp hb).2)
        have union : hits = (candidates.filter fun a => q = first a) ∪
            (candidates.filter fun a => q = second a) := by
          ext a
          simp only [hits,mem_filter,mem_union]
          tauto
        rw [union]
        exact (card_union_le _ _).trans (by
          have hfirst := one first first_injective
          have hsecond := one second second_injective
          omega)
      have remainder_le : remaining.card ≤ 2*fuel := by
        by_cases empty : remaining = ∅
        · simp only [empty,card_empty,Nat.zero_le]
        · obtain ⟨reference,href⟩ := nonempty_iff_ne_empty.mpr empty
          have subset : remaining ⊆ candidates := sdiff_subset
          have avoids (a : Secret) (ha : a ∈ remaining) : q ≠ first a ∧ q ≠ second a := by
            obtain ⟨hcan,hnot⟩ := mem_sdiff.mp ha
            simp only [hits,mem_filter,not_and,not_or] at hnot
            exact hnot hcan
          have answers (a : Secret) (ha : a ∈ remaining) : oracle a q = oracle reference q :=
            compatible a (subset ha) reference (subset href) q
              (avoids a ha).1 (avoids a ha).2 (avoids reference href).1 (avoids reference href).2
          apply ih (oracle reference q) remaining
          · intro a ha b hb r h1 h2 h3 h4
            exact compatible a (subset ha) b (subset hb) r h1 h2 h3 h4
          · intro a ha
            have h := caught a (subset ha)
            simp only [Tree.run_query,List.map_cons,List.mem_cons] at h
            rcases h with h | h
            · rcases h with h | h
              · exact ((avoids a ha).1 h.symm).elim
              · left
                simpa only [answers a ha] using h
            · rcases h with h | h
              · exact ((avoids a ha).2 h.symm).elim
              · right
                simpa only [answers a ha] using h
      have count : candidates.card ≤ hits.card+remaining.card := by
        have : candidates = hits ∪ remaining := by
          ext a
          simp only [remaining,mem_union,mem_sdiff]
          have : hits ⊆ candidates := filter_subset _ _
          tauto
        rw [this]
        exact card_union_le _ _
      omega
end FirstHit

section Prepared
variable {Salt Message Digest Enc Observed : Type}
variable [Inhabited Digest] [DecidableEq Enc]
variable (C : Codec Salt Message Digest Enc) (n : ℕ)
variable (nonce : Fin n → Salt) (message : Fin n → Message)
variable {T : ℕ} (labels : Fin T → Digest) (background : Enc → Digest)

/-- Replace only the commitment's inputs. Every other answer, including
every retained prior cache entry, stays the background oracle's answer. -/
def prepared : Enc → Digest := fun query =>
  if query ∈ commitSeen C n nonce message labels then
    commitOracle C n nonce message labels query else background query

theorem prepared_outside (query : Enc)
    (outside : query ∉ commitSeen C n nonce message labels) :
    prepared C n nonce message labels background query = background query := by
  rw [prepared,if_neg outside]

/-- A previous adaptive execution is preserved together with its complete
trace, provided the freshness splice kept the committed inputs out of it. -/
theorem prior_preserved {fuel : ℕ} (before : Tree Enc Digest Observed fuel)
    (fresh : ∀ qa ∈ (before.run background).2,
      qa.1 ∉ commitSeen C n nonce message labels) :
    before.run (prepared C n nonce message labels background) = before.run background := by
  apply Tree.run_congr_on_trace
  intro qa hqa
  rw [prepared_outside C n nonce message labels background qa.1 (fresh qa hqa)]
  exact (Tree.trace_sound before background qa hqa).symm

/-- The commitment itself sees exactly the labels it saw in its canonical
lazy construction. Earlier cache entries are not deleted to obtain this. -/
theorem commit_run :
    (commitPass C n nonce message (2*n-1) fun _ => default).run
        (prepared C n nonce message labels background) =
      (commitPass C n nonce message (2*n-1) fun _ => default).run
        (commitOracle C n nonce message labels) := by
  apply Tree.run_congr_on_trace
  intro qa hqa
  have runEq := RandomOracle.lazyRun_eq_run labels default
    (commitPass C n nonce message (2*n-1) fun _ => default) []
    (commitOracle C n nonce message labels) (fun _ => rfl)
  have hlazy : qa ∈ (RandomOracle.lazyRun labels default
      (commitPass C n nonce message (2*n-1) fun _ => default) []).2.2 := by
    simpa only [runEq] using hqa
  have memSeen : qa.1 ∈ commitSeen C n nonce message labels := by
    have slot := RandomOracle.lazyRun_trace_slot labels default
      (commitPass C n nonce message (2*n-1) fun _ => default) [] qa hlazy
    exact slot.1
  rw [prepared,if_pos memSeen]
  exact (Tree.trace_sound _ _ qa hqa).symm

/-- The actual commitment traversal supplies the root and frontier; they
are not chosen independently of the prepared table. -/
def openingView (I : Finset (Fin n)) : OpeningView n I Salt Digest :=
  let values := ((commitPass C n nonce message (2*n-1) fun _ => default).run
    (prepared C n nonce message labels background)).1
  ⟨values 1,{ nonce := fun i => nonce i.val
              frontierValue := fun vertex => values vertex.val }⟩

theorem openingView_eq (positive : 0 < n) (I : Finset (Fin n))
    (injective : commitInputsInjective C n nonce message
      (commitOracle C n nonce message labels))
    (fits : 2*n-2 < T) (fitsAll : 2*n-1 ≤ T) :
    openingView C n nonce message labels background I = openingViewOf n I nonce labels fits := by
  have runEq := RandomOracle.lazyRun_eq_run labels default
    (commitPass C n nonce message (2*n-1) fun _ => default) []
    (commitOracle C n nonce message labels) (fun _ => rfl)
  have values := congrArg Prod.fst ((commit_run C n nonce message labels background).trans runEq)
  unfold openingView
  rw [values]
  exact openingHidingRun_view C n positive I nonce message labels injective fits fitsAll

theorem prepared_compatible
    (nonce' : Fin n → Salt) (message' : Fin n → Message) (query : Enc)
    (compatible : BaseCompat (commitSeen C n nonce message labels)
      (commitSeen C n nonce' message' labels) query) :
    prepared C n nonce message labels background query =
      prepared C n nonce' message' labels background query := by
  obtain ⟨membership,slot⟩ := compatible
  unfold prepared
  by_cases present : query ∈ commitSeen C n nonce message labels
  · rw [if_pos present,if_pos (membership.mp present)]
    unfold commitOracle
    change tapeAt labels default ((commitSeen C n nonce message labels).idxOf query) =
      tapeAt labels default ((commitSeen C n nonce' message' labels).idxOf query)
    rw [slot]
  · rw [if_neg present,if_neg (fun h => present (membership.mpr h))]

end Prepared

section LeafCatch
variable {Salt Message Digest Enc Observed : Type}
variable [Inhabited Digest] [DecidableEq Enc] [DecidableEq Salt]
variable (C : Codec Salt Message Digest Enc) (n : ℕ) (positive : 0 < n)
variable {T : ℕ} (labels : Fin T → Digest) (background : Enc → Digest)

include positive in
/-- Changing one hidden nonce changes the prepared oracle only at its leaf
input.  Consequently the old cache does not cost a second nonce-guessing
factor; it is already part of the shared background. -/
theorem leafCatch_card_le (first second : Fin n → Message) (fits : 2*n-2 < T)
    (i : Fin n) (nonceOf : Salt → Fin n → Salt)
    (off : ∀ a b : Salt, ∀ j : Fin n, j ≠ i → nonceOf a j = nonceOf b j)
    (at_index : ∀ a : Salt, nonceOf a i = a)
    (first_injective : Function.Injective fun a : Salt => C.leafEnc (a,first i))
    (second_injective : Function.Injective fun a : Salt => C.leafEnc (a,second i))
    (candidates : Finset Salt)
    (good : ∀ a ∈ candidates, commitInputsInjective C n (nonceOf a) first
      (commitOracle C n (nonceOf a) first labels))
    {queries : ℕ} (observer : Tree Enc Digest Observed queries)
    (caught : ∀ a ∈ candidates,
      C.leafEnc (a,first i) ∈ (observer.run
        (prepared C n (nonceOf a) first labels background)).2.map Prod.fst ∨
      C.leafEnc (a,second i) ∈ (observer.run
        (prepared C n (nonceOf a) first labels background)).2.map Prod.fst) :
    candidates.card ≤ 2*queries := by
  apply caught_card_le observer
    (fun a => prepared C n (nonceOf a) first labels background)
    (fun a => C.leafEnc (a,first i)) (fun a => C.leafEnc (a,second i))
    first_injective second_injective candidates _ caught
  intro a ha b hb query h1 _ h3 _
  apply prepared_compatible
  apply commitSeen_baseCompat C n positive (nonceOf a) (nonceOf b) first first labels
    (good a ha) (good b hb) fits {i}
    (fun j hj => ⟨off a b j (by simpa using hj),rfl⟩)
  intro j hj
  rw [mem_singleton] at hj
  subst j
  simpa only [at_index] using And.intro h1 h3

variable [Fintype Salt] [Fintype Digest] [DecidableEq Digest]

include positive in
theorem leafCatch_prod_card_le
    (first second : (Fin T → Digest) → Fin n → Message) (fits : 2*n-2 < T)
    (i : Fin n) {queries : ℕ}
    (tree : ({j : Fin n // j ≠ i} → Salt) → (Fin T → Digest) → Tree Enc Digest Observed queries)
    (first_injective : ∀ tape, Function.Injective fun a : Salt => C.leafEnc (a,first tape i))
    (second_injective : ∀ tape, Function.Injective fun a : Salt => C.leafEnc (a,second tape i))
    (bad : Finset (HidingSample n T Salt Digest))
    (good : ∀ sample ∈ bad, commitInputsInjective C n sample.1 (first sample.2)
      (commitOracle C n sample.1 (first sample.2) sample.2))
    (caught : ∀ sample ∈ bad,
      C.leafEnc (sample.1 i,first sample.2 i) ∈
        ((tree (fun j => sample.1 j.val) sample.2).run
          (prepared C n sample.1 (first sample.2) sample.2 background)).2.map Prod.fst ∨
      C.leafEnc (sample.1 i,second sample.2 i) ∈
        ((tree (fun j => sample.1 j.val) sample.2).run
          (prepared C n sample.1 (first sample.2) sample.2 background)).2.map Prod.fst) :
    bad.card ≤ (Fintype.card Salt)^(n-1) * (Fintype.card Digest)^T * (2*queries) := by
  rw [card_eq_sum_card_fiberwise
    (f := fun sample : HidingSample n T Salt Digest =>
      ((fun j : {j : Fin n // j ≠ i} => sample.1 j.val),sample.2))
    (t := (univ : Finset (({j : Fin n // j ≠ i} → Salt) × (Fin T → Digest))))
    (fun _ _ => mem_univ _)]
  calc
    ∑ p : ({j : Fin n // j ≠ i} → Salt) × (Fin T → Digest),
        (bad.filter fun sample => ((fun j : {j : Fin n // j ≠ i} => sample.1 j.val),sample.2) = p).card
      ≤ ∑ _p : ({j : Fin n // j ≠ i} → Salt) × (Fin T → Digest), 2*queries := by
        apply sum_le_sum
        intro p _
        let nonceOf : Salt → Fin n → Salt := fun a j => if h : j = i then a else p.1 ⟨j,h⟩
        have fiber : ∀ sample ∈ bad.filter
            (fun sample : HidingSample n T Salt Digest =>
              ((fun j : {j : Fin n // j ≠ i} => sample.1 j.val),sample.2) = p),
            sample.1 = nonceOf (sample.1 i) ∧ sample.2 = p.2 := by
          intro sample hs
          have hp := (mem_filter.mp hs).2
          refine ⟨?_,congrArg Prod.snd hp⟩
          funext j
          by_cases same : j = i
          · subst j
            simp only [nonceOf,dif_pos rfl]
          · simp only [nonceOf,dif_neg same]
            exact congrFun (congrArg Prod.fst hp) ⟨j,same⟩
        apply le_trans (le_of_eq (card_image_of_injOn (f := fun sample => sample.1 i) ?_).symm)
        · apply leafCatch_card_le C n positive p.2 background (first p.2) (second p.2) fits i nonceOf
            (fun a b j hj => by simp only [nonceOf,dif_neg hj])
            (fun a => by simp only [nonceOf,dif_pos rfl])
            (first_injective p.2) (second_injective p.2) (observer := tree p.1 p.2)
          · intro a ha
            obtain ⟨sample,hs,equal⟩ := mem_image.mp ha
            obtain ⟨hs1,hs2⟩ := fiber sample hs
            rw [← equal,← hs1,← hs2]
            exact good sample (mem_filter.mp hs).1
          · intro a ha
            obtain ⟨sample,hs,equal⟩ := mem_image.mp ha
            obtain ⟨hs1,hs2⟩ := fiber sample hs
            have hp1 := congrArg Prod.fst (mem_filter.mp hs).2
            rw [← equal,← hs1,← hs2,← hp1]
            exact caught sample (mem_filter.mp hs).1
        · intro a ha b hb equal
          change a.1 i = b.1 i at equal
          obtain ⟨ha1,ha2⟩ := fiber a ha
          obtain ⟨hb1,hb2⟩ := fiber b hb
          exact Prod.ext (by rw [ha1,hb1,equal]) (by rw [ha2,hb2])
    _ = (Fintype.card Salt)^(n-1) * (Fintype.card Digest)^T * (2*queries) := by
      rw [sum_const,card_univ,smul_eq_mul,Fintype.card_prod,Fintype.card_fun,Fintype.card_fun]
      congr 2
      · congr 1
        rw [Fintype.card_subtype_compl]
        simp
      · simp

end LeafCatch
end LfzkV2.Current.ZeroKnowledge.MerkleCache
