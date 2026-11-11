import TranscriptV2.Composition
import TranscriptV2.DigestProjection

/-! Injective query renaming preserves the composition contract, including
the full observed extraction cut. Unused target coordinates are independent
padding, not extra queries or oracle assumptions. This lets runtime adapters
expose typed protocol addresses while retaining every auxiliary query. -/
noncomputable section
namespace TranscriptV2.Composition
open Finset Bcs.TotalOracle Bcs.FiniteProbability Merkle.RandomOracle
open scoped Classical

section Restriction
variable {P Q A : Type} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
variable [Fintype A] [Nonempty A]
variable (encode : P → Q) (injective : Function.Injective encode)

private def splitOracle : (Q → A) ≃ (P → A) × ({q // q ∉ Set.range encode} → A) :=
  (Equiv.piEquivPiSubtypeProd (fun q => q ∈ Set.range encode) (fun _ => A)).trans
    (Equiv.prodCongr
      (Equiv.arrowCongr (Equiv.ofInjective encode injective).symm (Equiv.refl A))
      (Equiv.refl _))

include injective in
/-- Uniform restriction to an injective image has exactly the smaller
oracle law. Events may inspect the entire restricted table, not just one
answer or one chosen execution. -/
theorem density_pullback (event : (P → A) → Prop) :
    density (fun H : Q → A => event (H ∘ encode)) = density event := by
  let split := splitOracle (A := A) encode injective
  have changed := density_equiv split (fun pair => event pair.1)
  have projected : density (fun pair : (P → A) × ({q // q ∉ Set.range encode} → A) => event pair.1) =
      density event := by
    have swapped := density_equiv
      (Equiv.prodComm (P → A) ({q // q ∉ Set.range encode} → A))
      (fun pair => event pair.2)
    exact swapped.trans (density_product_snd event)
  exact changed.trans projected

end Restriction

section Queries
variable {P Q A Out : Type} [DecidableEq P] [DecidableEq Q]
variable (encode : P → Q) (injective : Function.Injective encode)

include injective in
theorem firstOfTwo_mapQueries {fuel : ℕ} (tree : Tree P A Out fuel) (H : Q → A) (p q : P) :
    firstOfTwo (mapQueries encode tree) H (encode p) (encode q) =
      firstOfTwo tree (H ∘ encode) p q := by
  induction tree with
  | done out => rfl
  | query point next ih =>
      simp only [mapQueries,firstOfTwo,injective.eq_iff,Function.comp_apply,ih]

include injective in
theorem before_mapQueries {fuel : ℕ} (tree : Tree P A Out fuel) (H : Q → A) (point : P) :
    before (mapQueries encode tree) H (encode point) =
      (before tree (H ∘ encode) point).map encode := by
  induction tree with
  | done _ => rfl
  | query current next ih =>
      by_cases same : current = point
      · simp [before,mapQueries,same]
      · simpa only [before,mapQueries,injective.eq_iff,same,if_false,List.map_cons,Function.comp_apply]
          using congrArg (List.cons (encode current)) (ih (H (encode current)))

include injective in
theorem targets_mapQueries {D : Type} [DecidableEq D] {fuel : ℕ} (claims : Q → Finset D) (tree : Tree P A Out fuel)
    (H : Q → A) (point : P) :
    DigestCharging.targets claims (mapQueries encode tree) H (encode point) =
      DigestCharging.targets (claims ∘ encode) tree (H ∘ encode) point := by
  ext digest
  simp only [DigestCharging.targets,before_mapQueries encode injective,Finset.mem_biUnion,Finset.mem_insert,
    List.mem_toFinset,List.mem_map,Function.comp_apply]
  aesop

end Queries

namespace SoundnessRealization
variable {P Q D C Out RawCoin View : Type}
variable [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
variable [Fintype D] [Nonempty D] [Fintype C] [Nonempty C] [Fintype RawCoin]
variable {fuel rounds : ℕ}
variable {tree : Tree P (D × C) Out fuel} {raw : RawCoin → View}
variable {observe : Out → (P → D × C) → View} {accepted : View → Prop}
variable {path : Out → (P → D × C) → ℕ → P}

/-- Transport a checked realization without changing its accepting
predicate, extractor observation, exception or speculative charge. Only
addresses change; additional target coordinates are never queried. -/
def rename (realization : SoundnessRealization (rounds := rounds) tree raw observe accepted path)
    (encode : P → Q) (injective : Function.Injective encode) :
    SoundnessRealization (rounds := rounds) (mapQueries encode tree) raw
      (fun out H => observe out (H ∘ encode)) accepted
      (fun out H i => encode (path out (H ∘ encode) i)) where
  observation_law event := by
    rw [realization.observation_law]
    simp only [run_mapQueries]
    exact (density_pullback encode injective (fun H => event (observe (tree.run H).1 H))).symm
  exception H := realization.exception (H ∘ encode)
  speculation H := realization.speculation (H ∘ encode)
  speculation_nonneg H := realization.speculation_nonneg (H ∘ encode)
  accepted_path H accepted good := by
    simp only [run_mapQueries] at accepted ⊢
    rcases realization.accepted_path (H ∘ encode) accepted good with ordered | paid
    · left
      constructor
      · intro i bound
        rw [seen_mapQueries]
        exact mem_image.mpr ⟨path (tree.run (H ∘ encode)).1 (H ∘ encode) i,ordered.queried i bound,rfl⟩
      · intro i bound
        rw [firstOfTwo_mapQueries encode injective]
        exact ordered.ordered i bound
    · exact Or.inr paid

end SoundnessRealization
end TranscriptV2.Composition

namespace TranscriptV2.DigestProjection
open Finset Bcs.TotalOracle Merkle.RandomOracle
open scoped Classical

/-- Digest charges depend only on the ordered query names and their digest
answers. Padding or reindexing challenge coordinates preserves this data. -/
theorem charge_congr {P D C C' Out Out' : Type} [DecidableEq P] [DecidableEq D]
    {fuel extra : ℕ} (claims : P → Finset D)
    (first : Tree P (D × C) Out fuel) (second : Tree P (D × C') Out' extra)
    (H : P → D × C) (H' : P → D × C')
    (queries : queried first H = queried second H')
    (digests : ∀ p, (H p).1 = (H' p).1) :
    charge claims first H = charge claims second H' := by
  have seenEq : seen first H = seen second H' := congrArg List.toFinset queries
  have beforeEq p : before first H p = before second H' p := by
    rw [before_eq_takeWhile,before_eq_takeWhile,queries]
  unfold charge
  rw [seenEq]
  apply Finset.sum_congr rfl
  intro point _
  have same : bad claims first point H (H point) ↔ bad claims second point H' (H' point) := by
    simp only [bad,DigestCharging.targets,seenEq,beforeEq,digests]
  by_cases hit : bad claims first point H (H point)
  · rw [if_pos hit,if_pos (same.mp hit)]
  · rw [if_neg hit,if_neg (fun h => hit (same.mpr h))]

/-- Injective address renaming preserves each planted-target charge. -/
theorem charge_mapQueries {P Q D C Out : Type} [DecidableEq P] [DecidableEq Q] [DecidableEq D]
    {fuel : ℕ} (encode : P → Q) (injective : Function.Injective encode)
    (claims : Q → Finset D) (tree : Tree P (D × C) Out fuel) (H : Q → D × C) :
    charge claims (mapQueries encode tree) H = charge (claims ∘ encode) tree (H ∘ encode) := by
  unfold charge
  rw [TranscriptV2.seen_mapQueries]
  rw [Finset.sum_image (fun _ _ _ _ same => injective same)]
  apply Finset.sum_congr rfl
  intro point member
  have present : encode point ∈ seen (mapQueries encode tree) H := by
    rw [TranscriptV2.seen_mapQueries]
    exact Finset.mem_image.mpr ⟨point,member,rfl⟩
  simp only [bad,present,member,true_and,Composition.targets_mapQueries encode injective,Function.comp_apply]

/-- Restricting the receiving role commutes with injective address renaming. -/
theorem receivingCharge_mapQueries {P Q D C Out : Type} [DecidableEq P] [DecidableEq Q] [DecidableEq D]
    {fuel : ℕ} (encode : P → Q) (injective : Function.Injective encode)
    (receives : Q → Prop) (claims : Q → Finset D) (tree : Tree P (D × C) Out fuel) (H : Q → D × C) :
    receivingCharge receives claims (mapQueries encode tree) H =
      receivingCharge (receives ∘ encode) (claims ∘ encode) tree (H ∘ encode) := by
  unfold receivingCharge
  rw [TranscriptV2.seen_mapQueries,Finset.sum_image (fun _ _ _ _ same => injective same)]
  apply Finset.sum_congr rfl
  intro point member
  have present : encode point ∈ seen (mapQueries encode tree) H := by
    rw [TranscriptV2.seen_mapQueries]
    exact Finset.mem_image.mpr ⟨point,member,rfl⟩
  simp only [bad,present,member,true_and,Composition.targets_mapQueries encode injective,Function.comp_apply]

end TranscriptV2.DigestProjection
