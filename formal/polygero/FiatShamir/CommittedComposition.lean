import polygero.FiatShamir.Nonrecursive
import polygero.FiatShamir.OutsideList
import polygero.FiatShamir.WitnessSelection

/-! Composition with a frontend bound for a fixed committed witness list.
All stages use the same adaptive oracle. The statement can be satisfiable;
only acceptance without extraction and extraction outside the list are
charged to the backend. -/

namespace RecursivePolygero.NonrecursiveFS

open Counting Finset Bcs.TotalOracle Merkle.RandomOracle
open scoped Classical

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

theorem committed_composition_le
    (I : Instance F) (p : HahnSystemCertificate I)
    (hsmall : p.rankError ≤ 1/(Nat.card F : ℚ))
    {C Pt Out Parent State : Type}
    [Fintype C] [Nonempty C] [Fintype Pt] [DecidableEq Pt] [Fintype Parent]
    {N : ℕ} (tree : Tree Pt C Out N) (selected : Out → Parent × I.layer.Payload)
    (parent : Parent → Pt) (child : Parent → I.layer.Payload → Pt)
    (hparent : Function.Injective parent)
    (hchild : Function.Injective (fun i : Parent × I.layer.Payload => child i.1 i.2))
    (hdisjoint : ∀ j j' payload, parent j ≠ child j' payload)
    (state : Parent → (Pt → C) → State)
    (hstateOff : ∀ j payload H H',
      (∀ z, z ≠ parent j → z ≠ child j payload → H z = H' z) → state j H = state j H')
    (statement : State → Parent → I.layer.Statement)
    (oracle : State → Parent → I.layer.Oracle)
    [DecidableEq I.layer.Coin] [DecidableEq I.layer.Query]
    (decodeCoin : C → I.layer.Coin) (decodeQuery : C → I.layer.Query)
    (kCoin kQuery : ℕ)
    (hcoin : ∀ coin, (univ.filter fun a : C => decodeCoin a = coin).card ≤ kCoin)
    (hquery : ∀ query, (univ.filter fun b : C => decodeQuery b = query).card ≤ kQuery)
    (hkCoin : kCoin*Fintype.card I.layer.Coin ≤ Fintype.card C)
    (hkQuery : kQuery*Fintype.card I.layer.Query ≤ Fintype.card C)
    (cutoff bound : ℕ) (hcutoff : I.r+I.w-1 < cutoff)
    (hpacking : CodingTheory.UniformFamilyBound I.n cutoff (I.r+I.w-1) bound)
    (Good : (Pt → C) → (tupleCounts I).Index → Prop)
    (hvalid : ∀ H g,
      let i := selected (tree.run H).1
      scanRecoverAt I (statement (state i.1 H) i.1) (oracle (state i.1 H) i.1)
        (decodeCoin (H (parent i.1))) i.2 = some g → Good H g)
    (frontendError : ℚ)
    (hfrontend :
      let frontend := fun H : Pt → C =>
        let i := selected (tree.run H).1
        ∃ candidate : Fin bound, Good H
          (committedCandidate I (oracle (state i.1 H) i.1) cutoff bound candidate)
      ((univ.filter frontend).card : ℚ)/(Fintype.card C : ℚ)^Fintype.card Pt ≤ frontendError) :
    let accepts := fun H : Pt → C =>
      let i := selected (tree.run H).1
      I.layer.verify (statement (state i.1 H) i.1) (oracle (state i.1 H) i.1)
        (decodeCoin (H (parent i.1))) i.2 (decodeQuery (H (child i.1 i.2)))
    ((univ.filter accepts).card : ℚ)/(Fintype.card C : ℚ)^Fintype.card Pt ≤
      (N+1 : ℕ)*(p.error + ((cutoff+I.s-1).choose I.t : ℚ)/I.n.choose I.t) + frontendError := by
  intro accepts
  let chosen := fun H : Pt → C => selected (tree.run H).1
  let extract := fun H => scanRecoverAt I (statement (state (chosen H).1 H) (chosen H).1)
    (oracle (state (chosen H).1 H) (chosen H).1) (decodeCoin (H (parent (chosen H).1))) (chosen H).2
  let frontend := fun H : Pt → C => ∃ candidate : Fin bound,
    Good H (committedCandidate I (oracle (state (chosen H).1 H) (chosen H).1) cutoff bound candidate)
  let outside := fun H => accepts H ∧ decodedOutsideList I
    (statement (state (chosen H).1 H) (chosen H).1) (oracle (state (chosen H).1 H) (chosen H).1)
      (decodeCoin (H (parent (chosen H).1))) (chosen H).2 cutoff
  letI : DecidablePred frontend := fun _ => Classical.propDecidable _
  have hfront : ((univ.filter frontend).card : ℚ)/(Fintype.card C : ℚ)^Fintype.card Pt ≤
      frontendError := by
    convert! hfrontend using 1
    congr 3
    ext H
    simp only [frontend, chosen, mem_filter]
  have hbackend : ((univ.filter fun H => accepts H ∧ extract H = none).card : ℚ)/
      (Fintype.card C : ℚ)^Fintype.card Pt ≤ (N+1 : ℕ)*p.error := by
    convert! extraction_failure_le I p hsmall tree selected parent child hparent hchild hdisjoint
      state hstateOff statement oracle decodeCoin decodeQuery kCoin kQuery hcoin hquery hkCoin hkQuery using 1
  have houtside : ((univ.filter outside).card : ℚ)/(Fintype.card C : ℚ)^Fintype.card Pt ≤
      (N+1 : ℕ)*(((cutoff+I.s-1).choose I.t : ℚ)/I.n.choose I.t) := by
    convert! decoded_outside_list_le I tree selected parent child hchild
      (fun j payload => hdisjoint j j payload) state
      (by intro j payload H H' h; exact hstateOff j payload H H' (fun z _ hz => h z hz))
      statement oracle decodeCoin decodeQuery kQuery hquery hkQuery cutoff using 1
  have hsub : univ.filter accepts ⊆
      (univ.filter fun H => accepts H ∧ extract H = none) ∪
        ((univ.filter outside) ∪ univ.filter frontend) := by
    intro H hH
    have ha := (mem_filter.mp hH).2
    cases he : extract H with
    | none => exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, ha, he⟩)
    | some g =>
        apply mem_union_right
        by_cases hg : g ∈ committedCandidates I (oracle (state (chosen H).1 H) (chosen H).1) cutoff
        · obtain ⟨candidate,hcandidate⟩ := exists_committedCandidate I
            (oracle (state (chosen H).1 H) (chosen H).1) cutoff bound
            (committedCandidates_card_le I _ cutoff bound hcutoff hpacking) g hg
          apply mem_union_right
          apply mem_filter.mpr
          refine ⟨mem_univ _,candidate,?_⟩
          rw [hcandidate]
          exact hvalid H g he
        · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,ha,g,he,hg⟩)
  have hc : ((univ.filter accepts).card : ℚ) ≤
      (univ.filter fun H => accepts H ∧ extract H = none).card +
        ((univ.filter outside).card + (univ.filter frontend).card) := by
    exact_mod_cast (card_le_card hsub).trans
      ((card_union_le _ _).trans (Nat.add_le_add_left (card_union_le _ _) _))
  have hd := div_le_div_of_nonneg_right hc
    (show (0 : ℚ) ≤ (Fintype.card C : ℚ)^Fintype.card Pt by positivity)
  rw [add_div, add_div] at hd
  apply (hd.trans (add_le_add hbackend (add_le_add houtside hfront))).trans_eq
  ring

end RecursivePolygero.NonrecursiveFS
