import LfzkV2.Current.FingerprintRows
import LfzkV2.Current.JointResponse

/-! Recovering the two complete backend witnesses recovers the early selected
frontend pair. Several backend lifts may have the same projected cells; the
selection list is their image, so such lifts introduce no extra list factor. -/
noncomputable section
namespace LfzkV2.Current.BackendSelection
open RecursivePolygero NonrecursiveFS Counting SumcheckV2 WitnessSelection
open scoped Classical

variable {k s n t : ℕ} (P R : Joint.Participant k s n t)
variable {SlotB SlotN IB IN : Type}
variable [Fintype IB] [Fintype IN] [DecidableEq IB] [DecidableEq IN]

/-- Outside the already-counted recovery, outside-list and selection events,
the selected pair exists and all frontend rows hold on its recovered lifts.
The premise is successful decoding of the actual appended affine statements,
not a separate assumption that the fingerprints have been authenticated. -/
theorem recovered_selected
    (frontB : List (LinearRow SlotB P.Carrier)) (frontN : List (LinearRow SlotN R.Carrier))
    (primaryB : SlotB → Fin P.backend.nw × Fin P.backend.q)
    (primaryN : SlotN → Fin R.backend.nw × Fin R.backend.q)
    (dataB : IB → SlotB) (dataN : IN → SlotN) (maskB : Fin 2 → SlotB) (maskN : Fin 2 → SlotN)
    (coinsB : Coins P.Carrier IB) (coinsN : Coins R.Carrier IN)
    (targetB : P.Carrier × P.Carrier) (targetN : R.Carrier × R.Carrier)
    (eqB : P.backend.Equations ≃ Fin (frontB ++ FingerprintRows.rows dataB maskB coinsB targetB).length)
    (eqN : R.backend.Equations ≃ Fin (frontN ++ FingerprintRows.rows dataN maskN coinsN targetN).length)
    (W : JointResponse.Oracle P R) (c : JointResponse.Coin P R) (a : JointResponse.Response P R)
    (cutoff : ℕ × ℕ) :
    let σ : JointResponse.Statement P R :=
      (FingerprintRows.statement P.backend frontB primaryB dataB maskB coinsB targetB eqB,
       FingerprintRows.statement R.backend frontN primaryN dataN maskN coinsN targetN eqN)
    let viewB := FingerprintRows.view P.backend primaryB dataB maskB
    let viewN := FingerprintRows.view R.backend primaryN dataN maskN
    let ctx : Selection.Context P.Carrier R.Carrier IB IN := {
      binaryList := (committedCandidates P.backend W.1 cutoff.1).image viewB
      primeList := (committedCandidates R.backend W.2 cutoff.2).image viewN
      binaryCoins := coinsB, primeCoins := coinsN
      binaryResponse := targetB, primeResponse := targetN }
    ¬ JointResponse.failure P R σ W c a →
    ¬ decodedOutsideList P.backend σ.1 W.1 c.1 a.1 cutoff.1 →
    ¬ decodedOutsideList R.backend σ.2 W.2 c.2 a.2 cutoff.2 →
    ¬ ctx.Collision →
    ∃ gB gN, scanRecoverAt P.backend σ.1 W.1 c.1 a.1 = some gB ∧
      scanRecoverAt R.backend σ.2 W.2 c.2 a.2 = some gN ∧
      ctx.extract = some (viewB gB, viewN gN) ∧
      RowsHold frontB (Backend.read ((tupleCounts P.backend).witness gB) ∘ Backend.linearAddress primaryB) ∧
      RowsHold frontN (Backend.read ((tupleCounts R.backend).witness gN) ∘ Backend.linearAddress primaryN) := by
  intro σ viewB viewN ctx hfail houtsideB houtsideN hcollision
  obtain ⟨gB,hB⟩ : ∃ gB, scanRecoverAt P.backend σ.1 W.1 c.1 a.1 = some gB := by
    cases h : scanRecoverAt P.backend σ.1 W.1 c.1 a.1 with
    | none => exact (hfail (Or.inl h)).elim
    | some g => exact ⟨g,rfl⟩
  obtain ⟨gN,hN⟩ : ∃ gN, scanRecoverAt R.backend σ.2 W.2 c.2 a.2 = some gN := by
    cases h : scanRecoverAt R.backend σ.2 W.2 c.2 a.2 with
    | none => exact (hfail (Or.inr h)).elim
    | some g => exact ⟨g,rfl⟩
  have hmemB : gB ∈ committedCandidates P.backend W.1 cutoff.1 := by
    by_contra h
    exact houtsideB ⟨gB,hB,h⟩
  have hmemN : gN ∈ committedCandidates R.backend W.2 cutoff.2 := by
    by_contra h
    exact houtsideN ⟨gN,hN,h⟩
  have hb := FingerprintRows.decoded_view P.backend frontB primaryB dataB maskB coinsB targetB eqB
    W.1 c.1 a.1 gB hB
  have hn := FingerprintRows.decoded_view R.backend frontN primaryN dataN maskN coinsN targetN eqN
    W.2 c.2 a.2 gN hN
  refine ⟨gB,gN,hB,hN,?_,hb.1,hn.1⟩
  apply ctx.extract_of_match (viewB gB,viewN gN) hcollision
  exact ⟨⟨Finset.mem_image.mpr ⟨gB,hmemB,rfl⟩,hb.2⟩,
    ⟨Finset.mem_image.mpr ⟨gN,hmemN,rfl⟩,hn.2⟩⟩

/-- At a complete frontend layout, late authentication either identifies the
early selected cells and proves all their frontend rows, or encounters one
of the backend/list/selection events. The recovered tableaux are not exposed
to the frontend: only their previously selected cell vectors are used. -/
theorem extraction_reduction
    (frontB : List (LinearRow SlotB P.Carrier)) (frontN : List (LinearRow SlotN R.Carrier))
    (primaryB : SlotB → Fin P.backend.nw × Fin P.backend.q)
    (primaryN : SlotN → Fin R.backend.nw × Fin R.backend.q)
    (layoutB : (IB ⊕ Fin 2) ≃ SlotB) (layoutN : (IN ⊕ Fin 2) ≃ SlotN)
    (coinsB : Coins P.Carrier IB) (coinsN : Coins R.Carrier IN)
    (targetB : P.Carrier × P.Carrier) (targetN : R.Carrier × R.Carrier)
    (eqB : P.backend.Equations ≃ Fin
      (frontB ++ FingerprintRows.rows (fun i => layoutB (.inl i))
        (fun j => layoutB (.inr j)) coinsB targetB).length)
    (eqN : R.backend.Equations ≃ Fin
      (frontN ++ FingerprintRows.rows (fun i => layoutN (.inl i))
        (fun j => layoutN (.inr j)) coinsN targetN).length)
    (W : JointResponse.Oracle P R) (c : JointResponse.Coin P R) (a : JointResponse.Response P R)
    (cutoff : ℕ × ℕ) :
    let dataB := fun i => layoutB (.inl i)
    let dataN := fun i => layoutN (.inl i)
    let maskB := fun j => layoutB (.inr j)
    let maskN := fun j => layoutN (.inr j)
    let σ : JointResponse.Statement P R :=
      (FingerprintRows.statement P.backend frontB primaryB dataB maskB coinsB targetB eqB,
       FingerprintRows.statement R.backend frontN primaryN dataN maskN coinsN targetN eqN)
    let ctx : Selection.Context P.Carrier R.Carrier IB IN := {
      binaryList := (committedCandidates P.backend W.1 cutoff.1).image
        (FingerprintRows.view P.backend primaryB dataB maskB)
      primeList := (committedCandidates R.backend W.2 cutoff.2).image
        (FingerprintRows.view R.backend primaryN dataN maskN)
      binaryCoins := coinsB, primeCoins := coinsN
      binaryResponse := targetB, primeResponse := targetN }
    (∃ w, ctx.extract = some w ∧
      RowsHold frontB (FingerprintRows.realize layoutB w.1) ∧
      RowsHold frontN (FingerprintRows.realize layoutN w.2)) ∨
    JointResponse.failure P R σ W c a ∨
    decodedOutsideList P.backend σ.1 W.1 c.1 a.1 cutoff.1 ∨
    decodedOutsideList R.backend σ.2 W.2 c.2 a.2 cutoff.2 ∨ ctx.Collision := by
  intro dataB dataN maskB maskN σ ctx
  classical
  by_cases hf : JointResponse.failure P R σ W c a
  · exact Or.inr (Or.inl hf)
  by_cases hb : decodedOutsideList P.backend σ.1 W.1 c.1 a.1 cutoff.1
  · exact Or.inr (Or.inr (Or.inl hb))
  by_cases hn : decodedOutsideList R.backend σ.2 W.2 c.2 a.2 cutoff.2
  · exact Or.inr (Or.inr (Or.inr (Or.inl hn)))
  by_cases hc : ctx.Collision
  · exact Or.inr (Or.inr (Or.inr (Or.inr hc)))
  obtain ⟨gB,gN,_,_,hs,hrowsB,hrowsN⟩ := recovered_selected P R frontB frontN primaryB primaryN
    dataB dataN maskB maskN coinsB coinsN targetB targetN eqB eqN W c a cutoff hf hb hn hc
  refine Or.inl ⟨_,hs,?_,?_⟩
  · exact (FingerprintRows.rows_realized layoutB frontB _).mpr hrowsB
  · exact (FingerprintRows.rows_realized layoutN frontN _).mpr hrowsN

end LfzkV2.Current.BackendSelection
