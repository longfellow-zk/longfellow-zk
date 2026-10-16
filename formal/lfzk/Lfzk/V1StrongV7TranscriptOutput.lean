import Lfzk.V1StrongV7TranscriptFinal

/-! V1 FS extraction failure at the verifier's message-schedule hash points. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Lfzk.V1StrongV7TranscriptOutput

open Finset LigeroFamily Lfzk.V1StrongV7Numeric
open Bcs.TotalOracle Merkle.RandomOracle
open scoped Classical

/-- The prover outputs a message schedule whose query-round message is its
four-slice response.  The verifier hashes those exact message prefixes. -/
theorem v7_v1_output_extraction_failure_le (i : Fin 4)
    {F : Type} {Equations : Type*} {Ctx Other Coin Out : Type}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations]
    [Fintype Ctx] [DecidableEq Ctx]
    [Fintype Other] [DecidableEq Other] [Inhabited Other]
    [Fintype Coin] [Nonempty Coin]
    {w nw nq nl N : ℕ} {rounds : ℕ → ℕ}
    (hrows : CoreRowsNonempty nw nq)
    (hfield : Fintype.card F = (row i).fieldSize)
    (D : ReedSolomon.Domain F (row i).openings w (row i).n)
    (hkrow : (row i).openings + w = (row i).k)
    (baseNodes : Fin (row i).k ↪
      Position (row i).openings w (row i).n)
    (responseNodes : Fin (2 * (row i).k - 1) ↪
      Position (row i).openings w (row i).n)
    (tree : Tree
      (Lfzk.V1StrongV7TranscriptTerminal.Point i Ctx Other F nl rounds)
      Coin Out N)
    (ctxOf : Out → Ctx)
    (msgOf : Out → ℕ → Lfzk.LigeroTranscriptInputs.Message
      (Other := Other) (F := F)
      (block := (row i).k) (dblock := 2 * (row i).k - 1)
      (r := (row i).openings))
    (responseOf : Out → Lfzk.V1StrongV7Terminal.Payload i F)
    (wellFormed : Out → Prop)
    (hresponse : ∀ out, wellFormed out →
      msgOf out (Rounds.Role.layerBase rounds nl + 2) =
        Sum.inr (responseOf out))
    (oracle : Lfzk.V1StrongV7TranscriptTerminal.Prefix
      i Ctx Other F nl rounds →
      Ligero.V1.Oracle F nw nq (row i).n 1)
    (statement : Lfzk.V1StrongV7TranscriptTerminal.Prefix
      i Ctx Other F nl rounds →
      ConstraintSystem F nw nq w Equations)
    (decodeChallenge : Coin → Ligero.V1.Challenge F nw nq 1 Equations)
    (decodeQuery : Coin → QuerySet (row i).n (row i).openings)
    (kchal kquery : ℕ)
    (hchal : ∀ challenge,
      (univ.filter fun c : Coin => decodeChallenge c = challenge).card ≤ kchal)
    (hqueryBalance : ∀ query,
      (univ.filter fun c : Coin => decodeQuery c = query).card ≤ kquery)
    (hkchal : kchal * Fintype.card
      (Ligero.V1.Challenge F nw nq 1 Equations) ≤ Fintype.card Coin)
    (hkquery : kquery * Fintype.card
      (QuerySet (row i).n (row i).openings) ≤ Fintype.card Coin) :
    let selected := Lfzk.LigeroPairGeometry.selectedFromOutput
      (nl := nl) (w := rounds) ctxOf msgOf responseOf
    let failure := fun H :
        Lfzk.V1StrongV7TranscriptTerminal.Point
          i Ctx Other F nl rounds → Coin =>
      let out := (tree.run H).1
      let pr := selected out
      wellFormed out ∧
      Lfzk.V1StrongV7Terminal.accepts i D hkrow baseNodes responseNodes
        (oracle pr.1) (statement pr.1)
        (decodeChallenge (H (Lfzk.NizkDeployedHash.msgPoint
          (nl := nl) (w := rounds) (ctxOf out) msgOf out
          (Rounds.Role.layerBase rounds nl + 1))))
        pr.2
        (decodeQuery (H (Lfzk.NizkDeployedHash.msgPoint
          (nl := nl) (w := rounds) (ctxOf out) msgOf out
          (Rounds.Role.layerBase rounds nl + 2))))
    ((univ.filter failure).card : ℚ) /
      (Fintype.card Coin : ℚ) ^
        Fintype.card (Lfzk.V1StrongV7TranscriptTerminal.Point
          i Ctx Other F nl rounds) ≤
      (N + 1 : ℕ) * density i := by
  let selected := Lfzk.LigeroPairGeometry.selectedFromOutput
    (nl := nl) (w := rounds) ctxOf msgOf responseOf
  have h := Lfzk.V1StrongV7TranscriptFinal.v7_v1_transcript_final_le i
    hrows hfield D hkrow baseNodes responseNodes tree selected
    oracle statement decodeChallenge decodeQuery kchal kquery
    hchal hqueryBalance hkchal hkquery
  dsimp only at h ⊢
  have hsub :
      (univ.filter (fun H : Lfzk.V1StrongV7TranscriptTerminal.Point
          i Ctx Other F nl rounds → Coin =>
        let out := (tree.run H).1
        let pr := selected out
        wellFormed out ∧
        Lfzk.V1StrongV7Terminal.accepts i D hkrow baseNodes responseNodes
          (oracle pr.1) (statement pr.1)
          (decodeChallenge (H (Lfzk.NizkDeployedHash.msgPoint
            (nl := nl) (w := rounds) (ctxOf out) msgOf out
            (Rounds.Role.layerBase rounds nl + 1)))) pr.2
          (decodeQuery (H (Lfzk.NizkDeployedHash.msgPoint
            (nl := nl) (w := rounds) (ctxOf out) msgOf out
            (Rounds.Role.layerBase rounds nl + 2)))))) ⊆
      (univ.filter (fun H : Lfzk.V1StrongV7TranscriptTerminal.Point
          i Ctx Other F nl rounds → Coin =>
        let pr := selected (tree.run H).1
        Lfzk.V1StrongV7Terminal.accepts i D hkrow baseNodes responseNodes
          (oracle pr.1) (statement pr.1)
          (decodeChallenge (H (Lfzk.LigeroPairGeometry.parent pr.1)))
          pr.2 (decodeQuery (H
            (Lfzk.LigeroPairGeometry.child pr.1 pr.2))))) := by
    intro H hH
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hH ⊢
    let out := (tree.run H).1
    obtain ⟨hwell, hacc⟩ := hH
    have hp := Lfzk.LigeroPairGeometry.parent_selectedFromOutput
      (nl := nl) (w := rounds) ctxOf msgOf responseOf out
    have hc := Lfzk.LigeroPairGeometry.child_selectedFromOutput
      (nl := nl) (w := rounds) ctxOf msgOf responseOf out
      (hresponse out hwell)
    simp only [selected] at hp hc hacc ⊢
    rw [hp, hc]
    exact hacc
  have hq : (0 : ℚ) <
      (Fintype.card Coin : ℚ) ^
        Fintype.card (Lfzk.V1StrongV7TranscriptTerminal.Point
          i Ctx Other F nl rounds) := by positivity
  exact (div_le_div_of_nonneg_right
    (by exact_mod_cast Finset.card_le_card hsub) hq.le).trans h

end Lfzk.V1StrongV7TranscriptOutput
