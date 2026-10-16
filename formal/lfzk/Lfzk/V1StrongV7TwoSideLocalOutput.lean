import Lfzk.V1StrongV7TwoSideLocal

/-! Output-level V1 failure at the actual two-side deployed hash inputs. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Lfzk.V1StrongV7TwoSideLocalOutput

open Finset LigeroFamily Lfzk.V1StrongV7Numeric
open Bcs.TotalOracle Merkle.RandomOracle
open scoped Classical

theorem v7_v1_two_side_local_output_failure_le (i : Fin 4)
    {F : Type} {Equations : Type*} {D Coin X Other Msg₂ Out State : Type}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations]
    [Fintype D] [DecidableEq D]
    [Fintype Coin] [DecidableEq Coin] [Nonempty Coin]
    [Fintype X] [DecidableEq X]
    [Fintype Other] [DecidableEq Other] [Inhabited Other]
    [Fintype Msg₂] [DecidableEq Msg₂] [Inhabited Msg₂]
    {qw nw nq nl nl₂ N : ℕ} {rounds rounds₂ : ℕ → ℕ}
    (hrows : CoreRowsNonempty nw nq)
    (hfield : Fintype.card F = (row i).fieldSize)
    (dom : ReedSolomon.Domain F (row i).openings qw (row i).n)
    (hkrow : (row i).openings + qw = (row i).k)
    (baseNodes : Fin (row i).k ↪
      Position (row i).openings qw (row i).n)
    (responseNodes : Fin (2 * (row i).k - 1) ↪
      Position (row i).openings qw (row i).n)
    (tree : Tree (Lfzk.V1StrongV7TwoSideFinal.Point i D Coin X Other F Msg₂
      nl nl₂ rounds rounds₂) Coin Out N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → Coin) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Lfzk.LigeroTranscriptInputs.Message
      (Other := Other) (F := F)
      (block := (row i).k) (dblock := 2 * (row i).k - 1)
      (r := (row i).openings))
    (msgOf₂ : Out → ℕ → Msg₂)
    (responseOf : Out → Lfzk.V1StrongV7Terminal.Payload i F)
    (wellFormed : Out → Prop)
    (hresponse : ∀ out, wellFormed out →
      msgOf₁ out (Rounds.Role.layerBase rounds nl + 2) =
        Sum.inr (responseOf out))
    (state : Lfzk.V1StrongV7TwoSideFinal.Prefix i D Coin X Other F nl rounds →
      (Lfzk.V1StrongV7TwoSideFinal.Point i D Coin X Other F Msg₂
        nl nl₂ rounds rounds₂ → Coin) → State)
    (hstateOff : ∀ p response (H H' :
        Lfzk.V1StrongV7TwoSideFinal.Point i D Coin X Other F Msg₂
          nl nl₂ rounds rounds₂ → Coin),
      (∀ z, z ≠ Lfzk.LigeroPairGeometryTwoSide.parent
          (Msg₂ := Msg₂) (nl₂ := nl₂) (w₂ := rounds₂) p →
        z ≠ Lfzk.LigeroPairGeometryTwoSide.child
          (Msg₂ := Msg₂) (nl₂ := nl₂) (w₂ := rounds₂) p response →
        H z = H' z) → state p H = state p H')
    (oracle : State →
      Lfzk.V1StrongV7TwoSideFinal.Prefix i D Coin X Other F nl rounds →
      Ligero.V1.Oracle F nw nq (row i).n 1)
    (statement : State →
      Lfzk.V1StrongV7TwoSideFinal.Prefix i D Coin X Other F nl rounds →
      ConstraintSystem F nw nq qw Equations)
    (decodeChallenge : State →
      Lfzk.V1StrongV7TwoSideFinal.Prefix i D Coin X Other F nl rounds →
      Coin → Ligero.V1.Challenge F nw nq 1 Equations)
    (decodeQuery : State →
      Lfzk.V1StrongV7TwoSideFinal.Prefix i D Coin X Other F nl rounds →
      Coin → QuerySet (row i).n (row i).openings)
    (kchal kquery : ℕ)
    (hchal : ∀ s p challenge,
      (univ.filter fun c : Coin => decodeChallenge s p c = challenge).card ≤ kchal)
    (hqueryBalance : ∀ s p query,
      (univ.filter fun c : Coin => decodeQuery s p c = query).card ≤ kquery)
    (hkchal : kchal * Fintype.card
      (Ligero.V1.Challenge F nw nq 1 Equations) ≤ Fintype.card Coin)
    (hkquery : kquery * Fintype.card
      (QuerySet (row i).n (row i).openings) ≤ Fintype.card Coin) :
    let selected := Lfzk.LigeroPairGeometry.selectedFromOutput
      (nl := nl) (w := rounds)
      (Lfzk.NizkDeployedHashTwoField.ctxOf rootOf₁ rootOf₂ avOf pubOf)
      msgOf₁ responseOf
    let failure := fun H : Lfzk.V1StrongV7TwoSideFinal.Point i D Coin X
        Other F Msg₂ nl nl₂ rounds rounds₂ → Coin =>
      let out := (tree.run H).1
      let pr := selected out
      wellFormed out ∧
      Lfzk.V1StrongV7Terminal.accepts i dom hkrow baseNodes responseNodes
        (oracle (state pr.1 H) pr.1)
        (statement (state pr.1 H) pr.1)
        (decodeChallenge (state pr.1 H) pr.1
          (H (Lfzk.NizkDeployedHashTwoField.hash2
          (nl₁ := nl) (nl₂ := nl₂) (w₁ := rounds) (w₂ := rounds₂)
          rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out
          (1 + (Rounds.Role.layerBase rounds nl + 1)))))
        pr.2
        (decodeQuery (state pr.1 H) pr.1
          (H (Lfzk.NizkDeployedHashTwoField.hash2
          (nl₁ := nl) (nl₂ := nl₂) (w₁ := rounds) (w₂ := rounds₂)
          rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out
          (1 + (Rounds.Role.layerBase rounds nl + 2)))))
    ((univ.filter failure).card : ℚ) /
      (Fintype.card Coin : ℚ) ^
        Fintype.card (Lfzk.V1StrongV7TwoSideFinal.Point i D Coin X
          Other F Msg₂ nl nl₂ rounds rounds₂) ≤
      (N + 1 : ℕ) * density i := by
  let selected := Lfzk.LigeroPairGeometry.selectedFromOutput
    (nl := nl) (w := rounds)
    (Lfzk.NizkDeployedHashTwoField.ctxOf rootOf₁ rootOf₂ avOf pubOf)
    msgOf₁ responseOf
  have h := Lfzk.V1StrongV7TwoSideLocal.v7_v1_two_side_local_final_le i
    hrows hfield dom hkrow baseNodes responseNodes tree selected
    state hstateOff oracle statement decodeChallenge decodeQuery kchal kquery
    hchal hqueryBalance hkchal hkquery
  dsimp only at h ⊢
  have hsub :
      (univ.filter (fun H : Lfzk.V1StrongV7TwoSideFinal.Point i D Coin X
          Other F Msg₂ nl nl₂ rounds rounds₂ → Coin =>
        let out := (tree.run H).1
        let pr := selected out
        wellFormed out ∧
        Lfzk.V1StrongV7Terminal.accepts i dom hkrow baseNodes responseNodes
          (oracle (state pr.1 H) pr.1)
          (statement (state pr.1 H) pr.1)
          (decodeChallenge (state pr.1 H) pr.1
            (H (Lfzk.NizkDeployedHashTwoField.hash2
            (nl₁ := nl) (nl₂ := nl₂) (w₁ := rounds) (w₂ := rounds₂)
            rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out
            (1 + (Rounds.Role.layerBase rounds nl + 1)))))
          pr.2
          (decodeQuery (state pr.1 H) pr.1
            (H (Lfzk.NizkDeployedHashTwoField.hash2
            (nl₁ := nl) (nl₂ := nl₂) (w₁ := rounds) (w₂ := rounds₂)
            rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out
            (1 + (Rounds.Role.layerBase rounds nl + 2))))))) ⊆
      (univ.filter (fun H : Lfzk.V1StrongV7TwoSideFinal.Point i D Coin X
          Other F Msg₂ nl nl₂ rounds rounds₂ → Coin =>
        let pr := selected (tree.run H).1
        Lfzk.V1StrongV7Terminal.accepts i dom hkrow baseNodes responseNodes
          (oracle (state pr.1 H) pr.1)
          (statement (state pr.1 H) pr.1)
          (decodeChallenge (state pr.1 H) pr.1
            (H (Lfzk.LigeroPairGeometryTwoSide.parent
            (Msg₂ := Msg₂) (nl₂ := nl₂) (w₂ := rounds₂) pr.1)))
          pr.2
          (decodeQuery (state pr.1 H) pr.1
            (H (Lfzk.LigeroPairGeometryTwoSide.child
            (Msg₂ := Msg₂) (nl₂ := nl₂) (w₂ := rounds₂) pr.1 pr.2))))) := by
    intro H hH
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hH ⊢
    let out := (tree.run H).1
    obtain ⟨hwell, hacc⟩ := hH
    have hp := Lfzk.LigeroPairGeometry.parent_selectedFromOutput
      (nl := nl) (w := rounds)
      (Lfzk.NizkDeployedHashTwoField.ctxOf rootOf₁ rootOf₂ avOf pubOf)
      msgOf₁ responseOf out
    have hc := Lfzk.LigeroPairGeometry.child_selectedFromOutput
      (nl := nl) (w := rounds)
      (Lfzk.NizkDeployedHashTwoField.ctxOf rootOf₁ rootOf₂ avOf pubOf)
      msgOf₁ responseOf out (hresponse out hwell)
    have hkp := Lfzk.NizkDeployedHashTwoField.hash2_side1
      (nl₁ := nl) (nl₂ := nl₂) (w₁ := rounds) (w₂ := rounds₂)
      rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out
      (show Rounds.Role.layerBase rounds nl + 1 <
        Rounds.Role.length nl rounds by simp [Rounds.Role.length])
    have hkq := Lfzk.NizkDeployedHashTwoField.hash2_side1
      (nl₁ := nl) (nl₂ := nl₂) (w₁ := rounds) (w₂ := rounds₂)
      rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out
      (show Rounds.Role.layerBase rounds nl + 2 <
        Rounds.Role.length nl rounds by simp [Rounds.Role.length])
    simp only [selected] at hp hc hacc ⊢
    rw [hkp, hkq, ← hp, ← hc] at hacc
    exact hacc
  have hq : (0 : ℚ) < (Fintype.card Coin : ℚ) ^
      Fintype.card (Lfzk.V1StrongV7TwoSideFinal.Point i D Coin X
        Other F Msg₂ nl nl₂ rounds rounds₂) := by positivity
  exact (div_le_div_of_nonneg_right
    (by exact_mod_cast Finset.card_le_card hsub) hq.le).trans h

end Lfzk.V1StrongV7TwoSideLocalOutput
