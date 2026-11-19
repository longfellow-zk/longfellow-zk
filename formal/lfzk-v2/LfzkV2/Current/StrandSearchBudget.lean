import LfzkV2.Current.StrandReplay

/-! Grouping counter reads into streams preserves the original distinct-query
budget. Each sampled coordinate has a source in the original raw search. -/
namespace LfzkV2.Current.StrandReplay
open Finset Merkle.RandomOracle TranscriptV2 TranscriptV2.Strand TranscriptV2.StrandCoupling
open scoped Classical

private theorem fresh_nodup {Query Answer Output : Type} {fuel : ℕ}
    (tree : Tree Query Answer Output fuel) {known : Query → Prop}
    (fresh : FreshOracle.FreshFrom known tree) (H : Query → Answer) :
    ((tree.run H).2.map Prod.fst).Nodup := by
  induction tree generalizing known with
  | done output => exact .nil
  | query point next ih =>
      apply List.nodup_cons.mpr
      exact ⟨(fresh.2 (H point)).not_queried H point (Or.inl rfl),ih (H point) (fresh.2 (H point))⟩

private def coordinate {P K I : Type} : Point P K I → SamplePoint P K
  | .inl raw => .inl raw
  | .inr (key,_) => .inr key

private theorem sampled_sublist {P K D I Out : Type} [DecidableEq P] [DecidableEq K]
    (streamKey : P → D → K) {fuel : ℕ} (program : Tree (Point P K I) D Out fuel)
    (state : Cache P K D I) (H : SamplePoint P K → Sample D I) :
    (((eagerState streamKey (recordTrace program) state).run H).2.map Prod.fst).Sublist
      (((eagerState streamKey (recordTrace program) state).run H).1.1.2.map
        fun qa => coordinate qa.1) := by
  induction program generalizing state with
  | done output => exact .refl _
  | query point next ih =>
      cases point with
      | inl raw =>
          cases found : state.nodes raw with
          | some digest =>
              simpa only [recordTrace,eagerState,found,eagerState_map,Tree.run_weaken,
                Tree.run_map,Prod.map,List.map_cons,coordinate] using (ih digest state).cons (.inl raw)
          | none =>
              cases reserved : state.streams (streamKey raw (H (.inl raw)).1) <;>
                simp only [recordTrace,eagerState,found,Tree.run_query,eagerState_map,Tree.run_map,
                  Prod.map,List.map_cons,coordinate,reserved] <;>
                exact (ih (H (.inl raw)).1 _).cons_cons (.inl raw)
      | inr address =>
          rcases address with ⟨key,counter⟩
          cases found : state.streams key with
          | some row =>
              simpa only [recordTrace,eagerState,found,eagerState_map,Tree.run_weaken,
                Tree.run_map,Prod.map,List.map_cons,coordinate] using (ih (row counter) state).cons (.inr key)
          | none =>
              simp only [recordTrace,eagerState,found,Tree.run_query,eagerState_map,Tree.run_map,
                Prod.map,List.map_cons,coordinate]
              exact (ih ((H (.inr key)).2 counter) _).cons_cons (.inr key)

/-- Each grouped draw accounts for a distinct projected input of the same
raw execution. Reserving a row at a node does not add another draw. -/
theorem search_card_le {P T Out : Type} [DecidableEq P] [DecidableEq T]
    (schema : History.Codec T) (bytes : P → Framing.Bytes) {fuel : ℕ}
    (program : Tree (Point P PrfKey Word) Digest Out fuel)
    (H : StrandSearch.Name P T → Sample Digest Word) (G : Point P PrfKey Word → Digest)
    (agreement : ((search schema bytes program).run H).1.1.2.Matches G) :
    (seen (search schema bytes program) H).card ≤ (seen program G).card := by
  let tree := search schema bytes program
  obtain ⟨sample,run⟩ := StrandSearch.searchState_samples schema bytes (recordTrace program) Cache.empty [] H
  change (eagerState (StrandSearch.key bytes) (recordTrace program) Cache.empty).run sample =
    (((tree.run H).1.1), (tree.run H).2.map fun qa => (StrandSearch.erase qa.1,qa.2)) at run
  have source := (StrandSearch.searchState_source schema bytes (recordTrace program) Cache.empty [] H G agreement).1
  rw [run_recordTrace] at source
  have trace : (program.run G).2 = (tree.run H).1.1.1.2 := congrArg Prod.snd source
  have subset := sampled_sublist (StrandSearch.key bytes) program Cache.empty sample
  rw [run,← trace] at subset
  have distinct := fresh_nodup (eagerState (StrandSearch.key bytes) (recordTrace program) Cache.empty)
    (eagerState_fresh (StrandSearch.key bytes) (recordTrace program) Cache.empty) sample
  rw [run] at distinct
  calc
    (seen tree H).card ≤ (((tree.run H).2.map
        fun qa => (StrandSearch.erase qa.1,qa.2)).map Prod.fst).toFinset.card := by
      rw [List.toFinset_card_of_nodup distinct,List.length_map,List.length_map]
      simpa only [seen,Bcs.TotalOracle.queried,List.length_map] using
        (List.toFinset_card_le (l := (tree.run H).2.map Prod.fst))
    _ ≤ ((program.run G).2.map fun qa => coordinate qa.1).toFinset.card :=
      card_le_card (fun _ member => List.mem_toFinset.mpr (subset.subset (List.mem_toFinset.mp member)))
    _ ≤ (seen program G).card := by
      have image : ((program.run G).2.map fun qa => coordinate qa.1).toFinset =
          (seen program G).image coordinate := by
        ext point
        simp only [seen,Bcs.TotalOracle.queried,mem_image,List.mem_toFinset,List.mem_map]
        constructor
        · rintro ⟨qa,member,same⟩
          exact ⟨qa.1,⟨qa,member,rfl⟩,same⟩
        · rintro ⟨raw,⟨qa,member,same⟩,equal⟩
          exact ⟨qa,member,(congrArg coordinate same).trans equal⟩
      rw [image]
      exact card_image_le

end LfzkV2.Current.StrandReplay
