import Lfzk.V1StrongV7Terminal
import Bcs.AffineCharges
import Lfzk.AffineBlockInstances

/-! Terminal extraction-failure bound for Ligero V1 at each v7 geometry. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Lfzk.AffineLocal

open Finset LigeroFamily Lfzk.V1StrongV7Numeric
open Bcs.TotalOracle Merkle.RandomOracle Bcs.AffineBlock
open scoped Classical

/-- Actual local-domain soundness of the V1 terminal block, uniform over
all adaptive trees on Q, with arbitrary outside-context dependence. -/
theorem ligero_oracle_sound (i : Fin 4)
    {F : Type} {Equations : Type*} {Coin Q Prefix Out State : Type}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations]
    [Fintype Coin] [Nonempty Coin]
    [Fintype Q] [DecidableEq Q] [Fintype Prefix]
    {w nw nq : ℕ}
    (hrows : CoreRowsNonempty nw nq)
    (hfield : Fintype.card F = (row i).fieldSize)
    (D : ReedSolomon.Domain F (row i).openings w (row i).n)
    (hkrow : (row i).openings + w = (row i).k)
    (baseNodes : Fin (row i).k ↪
      Position (row i).openings w (row i).n)
    (responseNodes : Fin (2 * (row i).k - 1) ↪
      Position (row i).openings w (row i).n)
    (domain : Finset Q)
    (selected : Out → Prefix × Lfzk.V1StrongV7Terminal.Payload i F)
    (parent : Prefix → Q)
    (child : Prefix → Lfzk.V1StrongV7Terminal.Payload i F → Q)
    (hparent : Function.Injective parent)
    (hchild : Function.Injective
      (fun pr : Prefix × Lfzk.V1StrongV7Terminal.Payload i F => child pr.1 pr.2))
    (hdisjoint : ∀ p p' payload, parent p ≠ child p' payload)
    (hpDomain : ∀ p, parent p ∈ domain)
    (hcDomain : ∀ p r, child p r ∈ domain)
    (state : Prefix → (Q → Coin) → State)
    (hstateOff : ∀ p payload (H H' : Q → Coin),
      (∀ z, z ≠ parent p → z ≠ child p payload → H z = H' z) →
      state p H = state p H')
    (oracle : State → Prefix → Ligero.V1.Oracle F nw nq (row i).n 1)
    (statement : State → Prefix → ConstraintSystem F nw nq w Equations)
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
    OracleSound domain (fun out H =>
      let pr := selected out
      Lfzk.V1StrongV7Terminal.accepts i D hkrow baseNodes responseNodes
        (oracle (state pr.1 H) pr.1) (statement (state pr.1 H) pr.1) (decodeChallenge (H (parent pr.1)))
        pr.2 (decodeQuery (H (child pr.1 pr.2)))) (Lfzk.AffineBlockInstances.ligeroRate i) := by
  intro N tree
  refine ⟨queryCost_nonneg domain tree, ?_⟩
  simp only [Bcs.FiniteProbability.density, Fintype.card_fun, Nat.cast_pow,
    Lfzk.AffineBlockInstances.ligeroRate, Rate.diagonal]
  let lowAt := fun s p payload a b =>
    Lfzk.V1StrongV7Terminal.low i D hkrow baseNodes responseNodes
      (oracle s p) (statement s p) decodeChallenge decodeQuery payload a b
  let highAt := fun s p payload a b =>
    Lfzk.V1StrongV7Terminal.high i D hkrow baseNodes responseNodes
      (oracle s p) (statement s p) decodeChallenge decodeQuery payload a b
  have hlow (s : State) (p : Prefix) (payload : Lfzk.V1StrongV7Terminal.Payload i F)
      (a : Coin) :
      ∑ b : Coin, (if lowAt s p payload a b then (1 : ℚ) else 0) ≤
        Fintype.card Coin * cover (row i) (cutoff (row i)) := by
    by_cases ha : (Lfzk.V1StrongV7Terminal.good i D hkrow baseNodes responseNodes
        (oracle s p) (statement s p) (decodeChallenge a) payload).card ≤
        cutoff (row i)
    · have h := Lfzk.V1StrongV7LowQuery.decoded_low_query_le i
        D hkrow (oracle s p) (statement s p) (decodeChallenge a)
        (Lfzk.V1StrongV7Terminal.decodePayload i D baseNodes responseNodes payload)
        decodeQuery kquery hqueryBalance hkquery ha
      simp only [lowAt, Lfzk.V1StrongV7Terminal.low, ha, true_and]
      exact h
    · have hcover : 0 ≤ cover (row i) (cutoff (row i)) := by
        unfold cover hypergeometricRatio
        positivity
      simpa only [lowAt, Lfzk.V1StrongV7Terminal.low, ha, false_and,
        ite_false, Finset.sum_const_zero]
        using mul_nonneg (by positivity : (0 : ℚ) ≤ Fintype.card Coin) hcover
  have hhigh (s : State) (p : Prefix) :
      ∑ payload : Lfzk.V1StrongV7Terminal.Payload i F,
        ∑ a : Coin, ∑ b : Coin,
        (if highAt s p payload a b then (1 : ℚ) else 0) ≤
        (Fintype.card Coin : ℚ) ^ 2 * highMass i := by
    exact Lfzk.V1StrongV7HighCount.v7_v1_high_count_le i
      hrows hfield D hkrow baseNodes responseNodes (oracle s p)
      (statement s p) decodeChallenge decodeQuery kchal kquery
      hchal hqueryBalance hkchal hkquery
  have hcover : 0 ≤ cover (row i) (cutoff (row i)) := by
    unfold cover hypergeometricRatio
    positivity
  have h := tree_two_scale_local_context_final_domain_le tree domain selected parent child
    hparent hchild hdisjoint hpDomain hcDomain state hstateOff lowAt highAt
    (cover (row i) (cutoff (row i))) (highMass i)
    hcover (highMass_nonneg i) hlow hhigh
  have heq :
      (univ.filter (fun H : Q → Coin =>
        let pr := selected (tree.run H).1
        Lfzk.V1StrongV7Terminal.accepts i D hkrow baseNodes responseNodes
          (oracle (state pr.1 H) pr.1) (statement (state pr.1 H) pr.1) (decodeChallenge (H (parent pr.1)))
          pr.2 (decodeQuery (H (child pr.1 pr.2))))).card =
      (univ.filter (fun H : Q → Coin =>
        let pr := selected (tree.run H).1
        lowAt (state pr.1 H) pr.1 pr.2 (H (parent pr.1)) (H (child pr.1 pr.2)) ∨
        highAt (state pr.1 H) pr.1 pr.2 (H (parent pr.1)) (H (child pr.1 pr.2)))).card := by
    congr 1
    ext H
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (Lfzk.V1StrongV7Terminal.low_or_high_iff_accepts i
      D hkrow baseNodes responseNodes
      (oracle (state (selected (tree.run H).1).1 H) (selected (tree.run H).1).1)
      (statement (state (selected (tree.run H).1).1 H) (selected (tree.run H).1).1)
      decodeChallenge decodeQuery
      (selected (tree.run H).1).2 (H (parent (selected (tree.run H).1).1))
      (H (child (selected (tree.run H).1).1 (selected (tree.run H).1).2))).symm
  dsimp only at ⊢ h
  rw [heq]
  convert h using 1; simp only [density]; ring

theorem transcript_ligero_oracle_sound (i : Fin 4)
    {F : Type} {Equations : Type*} {Ctx Other Coin Out : Type}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations]
    [Fintype Ctx] [DecidableEq Ctx]
    [Fintype Other] [DecidableEq Other] [Inhabited Other]
    [Fintype Coin] [Nonempty Coin]
    {w nw nq nl : ℕ} {rounds : ℕ → ℕ}
    (hrows : CoreRowsNonempty nw nq)
    (hfield : Fintype.card F = (row i).fieldSize)
    (D : ReedSolomon.Domain F (row i).openings w (row i).n)
    (hkrow : (row i).openings + w = (row i).k)
    (baseNodes : Fin (row i).k ↪
      Position (row i).openings w (row i).n)
    (responseNodes : Fin (2 * (row i).k - 1) ↪
      Position (row i).openings w (row i).n)
    (selected : Out →
      Lfzk.V1StrongV7TranscriptTerminal.Prefix i Ctx Other F nl rounds ×
      Lfzk.V1StrongV7Terminal.Payload i F)
    (oracle : (Lfzk.LigeroPairGeometry.OutsideTerminal
      (Ctx := Ctx) (Other := Other) (F := F)
      (nl := nl) (block := (row i).k)
      (dblock := 2 * (row i).k - 1) (r := (row i).openings)
      (w := rounds) → Coin) → Lfzk.V1StrongV7TranscriptTerminal.Prefix
      i Ctx Other F nl rounds →
      Ligero.V1.Oracle F nw nq (row i).n 1)
    (statement : (Lfzk.LigeroPairGeometry.OutsideTerminal
      (Ctx := Ctx) (Other := Other) (F := F)
      (nl := nl) (block := (row i).k)
      (dblock := 2 * (row i).k - 1) (r := (row i).openings)
      (w := rounds) → Coin) → Lfzk.V1StrongV7TranscriptTerminal.Prefix
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
    let parent := Lfzk.LigeroPairGeometry.parent
      (Ctx := Ctx) (Other := Other) (F := F) (nl := nl)
      (block := (row i).k) (dblock := 2 * (row i).k - 1)
      (r := (row i).openings) (w := rounds)
    let child := Lfzk.LigeroPairGeometry.child
      (Ctx := Ctx) (Other := Other) (F := F) (nl := nl)
      (block := (row i).k) (dblock := 2 * (row i).k - 1)
      (r := (row i).openings) (w := rounds)
    OracleSound
      ((univ.image parent) ∪ (univ.image (fun pr :
        Lfzk.V1StrongV7TranscriptTerminal.Prefix i Ctx Other F nl rounds ×
          Lfzk.V1StrongV7Terminal.Payload i F => child pr.1 pr.2)))
      (fun out H =>
        let pr := selected out
        Lfzk.V1StrongV7Terminal.accepts i D hkrow baseNodes responseNodes
          (oracle (Lfzk.LigeroPairGeometry.outsideTerminal H) pr.1)
          (statement (Lfzk.LigeroPairGeometry.outsideTerminal H) pr.1)
          (decodeChallenge (H (parent pr.1))) pr.2 (decodeQuery (H (child pr.1 pr.2))))
      (Lfzk.AffineBlockInstances.ligeroRate i) := by
  dsimp only
  apply ligero_oracle_sound i hrows hfield D hkrow baseNodes responseNodes _ selected
    Lfzk.LigeroPairGeometry.parent Lfzk.LigeroPairGeometry.child
    Lfzk.LigeroPairGeometry.parent_injective Lfzk.LigeroPairGeometry.child_injective
    Lfzk.LigeroPairGeometry.parent_ne_child
    (fun p => mem_union_left _ (mem_image.mpr ⟨p, mem_univ _, rfl⟩))
    (fun p r => mem_union_right _ (mem_image.mpr ⟨(p,r), mem_univ _, rfl⟩))
    (fun _ => Lfzk.LigeroPairGeometry.outsideTerminal)
    (fun p r H H' h => Lfzk.LigeroPairGeometry.outsideTerminal_off p r H H' h)
    oracle statement decodeChallenge decodeQuery kchal kquery hchal hqueryBalance hkchal hkquery

end Lfzk.AffineLocal
