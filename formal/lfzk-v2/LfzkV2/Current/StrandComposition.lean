import LfzkV2.Current.StrandSampling
import TranscriptV2.CompositionTransport

/-! Transport a transcript realization to uniform protocol coordinates.
Analysis-only coordinates do not change any executed answer. A pointwise
bijection then separates joint challenges from retained residual randomness.
Conditioning on the latter preserves the whole verifier/extractor view; the
final averaging identity returns to the original raw experiment. -/
noncomputable section
namespace LfzkV2.Current.StrandComposition
open Finset Merkle.RandomOracle TranscriptV2 TranscriptV2.Composition
open Bcs.TotalOracle Bcs.FiniteProbability
open scoped Classical

section Padding
variable {P D C Extra Out : Type} [DecidableEq P]

/-- Independent proof-analysis coordinates are ignored by the original
program. In particular they cannot affect its messages or accepting result. -/
def pad : {fuel : ℕ} → Tree P (D × C) Out fuel → Tree P (D × (C × Extra)) Out fuel
  | _, .done out => .done out
  | _, .query point next => .query point fun answer => pad (next (answer.1,answer.2.1))

def drop (H : P → D × (C × Extra)) (point : P) : D × C := ((H point).1,(H point).2.1)

omit [DecidableEq P] in
theorem pad_run {fuel : ℕ} (tree : Tree P (D × C) Out fuel) (H : P → D × (C × Extra)) :
    ((pad tree).run H).1 = (tree.run (drop H)).1 ∧
      ((pad tree).run H).2.map Prod.fst = (tree.run (drop H)).2.map Prod.fst := by
  induction tree with
  | done out => exact ⟨rfl,rfl⟩
  | query point next ih =>
      have later := ih ((H point).1,(H point).2.1)
      exact ⟨later.1,congrArg (List.cons point) later.2⟩

theorem pad_seen {fuel : ℕ} (tree : Tree P (D × C) Out fuel) (H : P → D × (C × Extra)) :
    seen (pad tree) H = seen tree (drop H) :=
  congrArg List.toFinset (pad_run tree H).2

theorem pad_order {fuel : ℕ} (tree : Tree P (D × C) Out fuel) (H : P → D × (C × Extra))
    (first second : P) :
    firstOfTwo (pad tree) H first second = firstOfTwo tree (drop H) first second := by
  induction tree with
  | done out => rfl
  | query point next ih => simp only [pad,firstOfTwo,drop,ih]

variable [Fintype P] [Fintype D] [Fintype C] [Fintype Extra] [Nonempty Extra]

private theorem density_first {A B : Type} [Fintype A] [Fintype B] [Nonempty B]
    (event : A → Prop) : density (fun pair : A × B => event pair.1) = density event :=
  (density_equiv (Equiv.prodComm A B) (fun pair => event pair.2)).trans (density_product_snd event)

/-- Adding unused coordinates is an exact probability identity, including
events depending on the complete original oracle table. -/
theorem pad_law (event : (P → D × C) → Prop) :
    density (fun H : P → D × (C × Extra) => event (drop H)) = density event := by
  let split := StrandSampling.oracleEquiv (Link := D) (fun _ : P => Equiv.refl (C × Extra))
  exact (density_equiv split (fun pair => event pair.1)).trans (density_first event)

variable {RawCoin View : Type} [Fintype RawCoin] {fuel rounds : ℕ}
variable {tree : Tree P (D × C) Out fuel} {raw : RawCoin → View}
variable {observe : Out → (P → D × C) → View} {accepted : View → Prop}
variable {path : Out → (P → D × C) → ℕ → P}

/-- The original observation law and accepted-path proof remain valid
after adding independent analysis coordinates to each answer. -/
def padded (realization : SoundnessRealization (rounds := rounds) tree raw observe accepted path) :
    SoundnessRealization (rounds := rounds) (pad (Extra := Extra) tree) raw
      (fun out H => observe out (drop H)) accepted (fun out H => path out (drop H)) where
  observation_law event := by
    rw [realization.observation_law]
    have same := pad_law (Extra := Extra) (fun H => event (observe (tree.run H).1 H))
    apply same.symm.trans
    apply density_congr
    intro H
    rw [(pad_run tree H).1]
  exception H := realization.exception (drop H)
  speculation H := realization.speculation (drop H)
  speculation_nonneg H := realization.speculation_nonneg (drop H)
  accepted_path H valid good := by
    rw [(pad_run tree H).1] at valid ⊢
    rcases realization.accepted_path (drop H) valid good with queried | paid
    · left
      constructor
      · intro i bound
        rw [pad_seen]
        exact queried.queried i bound
      · intro i bound
        rw [pad_order]
        exact queried.ordered i bound
    · exact Or.inr paid

end Padding

section Coordinates
variable {P D Raw Challenge Residual Out RawCoin View : Type}
variable [Fintype P] [DecidableEq P] [Fintype D] [Fintype Raw]
variable [Fintype Challenge] [Fintype Residual] [Nonempty Residual] [Nonempty D] [Nonempty Challenge]
variable [Fintype RawCoin] {fuel rounds : ℕ}
variable {tree : Tree P (D × Raw) Out fuel} {raw : RawCoin → View}
variable {observe : Out → (P → D × Raw) → View} {accepted : View → Prop}
variable {path : Out → (P → D × Raw) → ℕ → P}
variable (split : P → Raw ≃ Challenge × Residual)

/-- The retained view at fixed residual randomness. This is the original
observation evaluated at the inverse coordinate map, not a weakened verifier. -/
def conditionedView (residual : P → Residual) (H : P → D × Challenge) : View :=
  let restored := (StrandSampling.oracleEquiv split).symm (H,residual)
  observe (tree.run restored).1 restored

/-- Each residual slice uses an ordinary adaptive tree over uniform
challenges. The same raw path, exceptions and speculative charge apply. -/
def atResidual (realization : SoundnessRealization (rounds := rounds) tree raw observe accepted path)
    (residual : P → Residual) :
    SoundnessRealization (rounds := rounds) (StrandSampling.reindex split residual tree)
      (conditionedView (tree := tree) (observe := observe) split residual)
      (fun out H => observe out ((StrandSampling.oracleEquiv split).symm (H,residual))) accepted
      (fun out H => path out ((StrandSampling.oracleEquiv split).symm (H,residual))) where
  observation_law event := by
    apply density_congr
    intro H
    rw [(StrandSampling.reindex_run split residual tree H).1]
    rfl
  exception H := realization.exception ((StrandSampling.oracleEquiv split).symm (H,residual))
  speculation H := realization.speculation ((StrandSampling.oracleEquiv split).symm (H,residual))
  speculation_nonneg H := realization.speculation_nonneg _
  accepted_path H valid good := by
    rw [(StrandSampling.reindex_run split residual tree H).1] at valid ⊢
    rcases realization.accepted_path _ valid good with queried | paid
    · left
      constructor
      · intro i bound
        rw [StrandSampling.reindex_seen]
        exact queried.queried i bound
      · intro i bound
        rw [StrandSampling.reindex_firstOfTwo]
        exact queried.ordered i bound
    · exact Or.inr paid

/-- Average the conditional experiments to recover the exact raw law.
This applies to the full accepted-extraction-failure event as well as any
other observation; no uniformity of the cut alone is substituted for it. -/
theorem observation_average
    (realization : SoundnessRealization (rounds := rounds) tree raw observe accepted path)
    (event : View → Prop) :
    density (fun coin => event (raw coin)) =
      (∑ residual : P → Residual, density (fun H : P → D × Challenge =>
        event (conditionedView (tree := tree) (observe := observe) split residual H))) /
          Fintype.card (P → Residual) := by
  rw [realization.observation_law]
  have changed : density (fun H => event (observe (tree.run H).1 H)) =
      density (fun pair : (P → D × Challenge) × (P → Residual) =>
        event (conditionedView (tree := tree) (observe := observe) split pair.2 pair.1)) :=
    (density_equiv (StrandSampling.oracleEquiv split).symm
      (fun H => event (observe (tree.run H).1 H))).symm
  have swapped := density_equiv
    (Equiv.prodComm (P → D × Challenge) (P → Residual))
    (fun pair => event (conditionedView (tree := tree) (observe := observe) split pair.1 pair.2))
  have average := density_product_average
    (fun (residual : P → Residual) (H : P → D × Challenge) =>
      event (conditionedView (tree := tree) (observe := observe) split residual H))
  exact changed.trans (swapped.trans average)

end Coordinates
section EventTransport
variable {P Q D Raw Extra Challenge Residual : Type}
variable [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
variable [Fintype D] [Nonempty D] [Fintype Raw] [Nonempty Raw]
variable [Fintype Extra] [Nonempty Extra] [Fintype Challenge] [Nonempty Challenge]
variable [Fintype Residual] [Nonempty Residual]
variable (encode : P → Q) (injective : Function.Injective encode)
variable (split : Q → (Raw × Extra) ≃ Challenge × Residual)

include injective in
/-- Averaging all retained sampler coordinates recovers the ORIGINAL
oracle event exactly. This applies to exceptions inspecting the whole table,
not only events observable at a protocol boundary. It requires no uniform
exception bound on individual residual slices. -/
theorem event_average (event : (P → D × Raw) → Prop) :
    density event =
      (∑ residual : Q → Residual, density (fun H : Q → D × Challenge =>
        event (drop ((StrandSampling.oracleEquiv split).symm (H,residual) ∘ encode)))) /
          Fintype.card (Q → Residual) := by
  let pull := fun G : Q → D × (Raw × Extra) => event (drop (G ∘ encode))
  have tagged : density pull = density event :=
    (Composition.density_pullback encode injective (fun G : P → D × (Raw × Extra) => event (drop G))).trans
      (pad_law (Extra := Extra) event)
  have changed := (density_equiv (StrandSampling.oracleEquiv split).symm pull).symm
  have swapped := density_equiv
    (Equiv.prodComm (Q → D × Challenge) (Q → Residual))
    (fun pair : (Q → Residual) × (Q → D × Challenge) =>
      event (drop ((StrandSampling.oracleEquiv split).symm (pair.2,pair.1) ∘ encode)))
  have average := density_product_average
    (fun (residual : Q → Residual) (H : Q → D × Challenge) =>
      event (drop ((StrandSampling.oracleEquiv split).symm (H,residual) ∘ encode)))
  exact tagged.symm.trans (changed.trans (swapped.trans average))

end EventTransport

section ChargeTransport
variable {P Q D Raw Extra Challenge Residual Out : Type}
variable [DecidableEq P] [DecidableEq Q] [DecidableEq D]
variable (encode : P → Q) (injective : Function.Injective encode)
variable (split : Q → (Raw × Extra) ≃ Challenge × Residual)
variable (residual : Q → Residual)
variable {fuel : ℕ} (tree : Tree P (D × Raw) Out fuel)
local notation "changed" => StrandSampling.reindex split residual (mapQueries encode (pad (Extra := Extra) tree))
local notation "restored" => Equiv.symm (StrandSampling.oracleEquiv (Link := D) split)

omit [DecidableEq D] in
/-- Coordinate changes preserve exactly the original search's query image.
In particular they cannot turn reserved PRF rows into additional queries. -/
theorem coordinates_seen (H : Q → D × Challenge) :
    seen changed H = (seen tree (drop (restored (H,residual) ∘ encode))).image encode := by
  rw [StrandSampling.reindex_seen,TranscriptV2.seen_mapQueries,pad_seen]

include injective in
/-- The speculative charge is unchanged by padding, address renaming and
sampler reindexing. This is an execution identity, without probability or
sampler-success hypotheses. -/
theorem coordinates_charge (claims : Q → Finset D) (H : Q → D × Challenge) :
    DigestProjection.charge claims changed H =
      DigestProjection.charge (claims ∘ encode) tree (drop (restored (H,residual) ∘ encode)) := by
  have indexed := DigestProjection.charge_congr claims changed
    (mapQueries encode (pad (Extra := Extra) tree)) H (restored (H,residual))
    (StrandSampling.reindex_run split residual _ H).2 (fun _ => rfl)
  rw [indexed,DigestProjection.charge_mapQueries encode injective]
  exact DigestProjection.charge_congr (claims ∘ encode) (pad (Extra := Extra) tree) tree
    (restored (H,residual) ∘ encode) (drop (restored (H,residual) ∘ encode))
    (pad_run tree _).2 (fun _ => rfl)

end ChargeTransport
end LfzkV2.Current.StrandComposition
