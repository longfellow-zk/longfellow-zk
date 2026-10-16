import Lfzk.LigeroPayloadDecode
import LigeroFamily.Soundness.PolicyProfiledMaster

/-!
# Sharper overlap for transmitted V1 response payloads

The formal response code admits degree below `2*k`, and hence the general
response-overlap theorem uses `2*k-1`.  The verifier reconstructs a transmitted
payload from only `2*k-1` interpolation values per linear/quadratic row.
Therefore two distinct transmitted payloads cannot both pass on `2*k-1`
common committed columns.  This result concerns the payload image only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.LigeroPayloadOverlap

open Finset LigeroFamily Lfzk.LigeroTranscriptInputs
open scoped Classical

variable {F : Type} {Equations CheckedMask DirectMask : Type*}
variable [Field F] [Fintype Equations] [Fintype CheckedMask]
variable {r w n nw nq block dblock : ℕ}

/-- Distinct wire payloads have at most `dblock-1` accepting columns in
common, assuming their decoded responses pass the same verifier. -/
theorem complete_payload_overlap
    (D : ReedSolomon.Domain F r w n)
    (baseNodes : Fin block ↪ Position r w n)
    (responseNodes : Fin dblock ↪ Position r w n)
    (hrb : r ≤ block) (hbd : block ≤ dblock)
    (C : MultiplicativeCode F r w n)
    (scheme : MaskScheme F CheckedMask DirectMask r w n)
    (oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1)
    (statement : ConstraintSystem F nw nq w Equations)
    (challenge : SchemeChallenge F CheckedMask nw nq 1 Equations)
    (first second : ResponsePayload F block dblock r)
    (goodFirst goodSecond : Finset (Fin n))
    (hfirst : ∀ j ∈ goodFirst, ∃ query : QuerySet n r,
      SchemeVerifier.Accepts C scheme statement challenge
        (Lfzk.LigeroPayloadDecode.decode D baseNodes responseNodes hrb hbd first)
        query (openSchemeOracle oracle query) ∧ j ∈ query.coordinates)
    (hsecond : ∀ j ∈ goodSecond, ∃ query : QuerySet n r,
      SchemeVerifier.Accepts C scheme statement challenge
        (Lfzk.LigeroPayloadDecode.decode D baseNodes responseNodes hrb hbd second)
        query (openSchemeOracle oracle query) ∧ j ∈ query.coordinates)
    (hne : first ≠ second) :
    (goodFirst ∩ goodSecond).card ≤ dblock - 1 := by
  classical
  by_contra hlarge
  have hbig : dblock ≤ (goodFirst ∩ goodSecond).card := by omega
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hbig
  let a := Lfzk.LigeroPayloadDecode.decode D baseNodes responseNodes hrb hbd first
  let b := Lfzk.LigeroPayloadDecode.decode D baseNodes responseNodes hrb hbd second
  have hpoint (j : Fin n) (hj : j ∈ S) :
      a.proximity 0 (codePosition j) = b.proximity 0 (codePosition j) ∧
      a.linear 0 (codePosition j) = b.linear 0 (codePosition j) ∧
      a.quadratic 0 (codePosition j) = b.quadratic 0 (codePosition j) := by
    have hjfirst : j ∈ goodFirst := (Finset.mem_inter.mp (hSsub hj)).1
    have hjsecond : j ∈ goodSecond := (Finset.mem_inter.mp (hSsub hj)).2
    obtain ⟨qfirst, hacceptFirst, hmemFirst⟩ := hfirst j hjfirst
    obtain ⟨qsecond, hacceptSecond, hmemSecond⟩ := hsecond j hjsecond
    have hpf := (hacceptFirst 0).1.2 ⟨j, hmemFirst⟩
    have hps := (hacceptSecond 0).1.2 ⟨j, hmemSecond⟩
    have hlf := (hacceptFirst 0).2.1.2.2 ⟨j, hmemFirst⟩
    have hls := (hacceptSecond 0).2.1.2.2 ⟨j, hmemSecond⟩
    have hqf := (hacceptFirst 0).2.2.2.2 ⟨j, hmemFirst⟩
    have hqs := (hacceptSecond 0).2.2.2.2 ⟨j, hmemSecond⟩
    dsimp [openSchemeOracle] at hpf hps hlf hls hqf hqs
    exact ⟨hpf.trans hps.symm, hlf.trans hls.symm,
      hqf.trans hqs.symm⟩
  have heq : first = second :=
    Lfzk.LigeroPayloadDecode.decode_eq_of_code_agree D baseNodes
      responseNodes hrb hbd first second S (by omega)
      (fun j hj => (hpoint j hj).1)
      (fun j hj => (hpoint j hj).2.1)
      (fun j hj => (hpoint j hj).2.2)
  exact hne heq

end Lfzk.LigeroPayloadOverlap
