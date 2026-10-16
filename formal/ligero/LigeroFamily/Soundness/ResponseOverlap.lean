import LigeroFamily.Soundness.ResponseMass
import LigeroFamily.Soundness.PolicyProfiledMaster

/-!
# Pairwise overlap of complete Ligero responses

Two different legal response triples cannot both agree with one committed
oracle at `2*k` columns. All three response components are checked at every
accepted opening, and each belongs to the response evaluation code. The
formal response code has dimension `2*k`, hence the safe overlap parameter is
`2*k-1`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LigeroFamily.ResponseMass

open Finset
open scoped Classical

variable {F Equations CheckedMask DirectMask : Type*}
variable [Field F] [Fintype Equations] [Fintype CheckedMask]
variable {r w n nw nq : ℕ}

/-- Agreement columns for two distinct complete responses overlap in at
most `2*k-1` positions. The `accepting` premise may include additional
conditions (such as extraction failure) beyond the verifier test. -/
theorem complete_response_overlap
    (C : MultiplicativeCode F r w n)
    (scheme : MaskScheme F CheckedMask DirectMask r w n)
    (oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1)
    (statement : ConstraintSystem F nw nq w Equations)
    (challenge : SchemeChallenge F CheckedMask nw nq 1 Equations)
    (first second : Response F r w n 1)
    (goodFirst goodSecond : Finset (Fin n))
    (hfirst : ∀ j ∈ goodFirst, ∃ query : QuerySet n r,
      SchemeVerifier.Accepts C scheme statement challenge first query
        (openSchemeOracle oracle query) ∧ j ∈ query.coordinates)
    (hsecond : ∀ j ∈ goodSecond, ∃ query : QuerySet n r,
      SchemeVerifier.Accepts C scheme statement challenge second query
        (openSchemeOracle oracle query) ∧ j ∈ query.coordinates)
    (hk : 0 < C.k)
    (hne : first ≠ second) :
    (goodFirst ∩ goodSecond).card ≤ 2 * C.k - 1 := by
  classical
  by_contra hlarge
  have hbig : 2 * C.k ≤ (goodFirst ∩ goodSecond).card := by omega
  obtain ⟨S, hSsub, hScard⟩ :=
    Finset.exists_subset_card_eq hbig
  have hSnonempty : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨j₀, hj₀⟩ := hSnonempty
  have hj₀first : j₀ ∈ goodFirst := (Finset.mem_inter.mp (hSsub hj₀)).1
  have hj₀second : j₀ ∈ goodSecond := (Finset.mem_inter.mp (hSsub hj₀)).2
  obtain ⟨q₁, hq₁, _⟩ := hfirst j₀ hj₀first
  obtain ⟨q₂, hq₂, _⟩ := hsecond j₀ hj₀second
  have hpoint (j : Fin n) (hj : j ∈ S) (h : Fin 1) :
      first.proximity h (codePosition j) = second.proximity h (codePosition j) ∧
      first.linear h (codePosition j) = second.linear h (codePosition j) ∧
      first.quadratic h (codePosition j) = second.quadratic h (codePosition j) := by
    have hjfirst : j ∈ goodFirst := (Finset.mem_inter.mp (hSsub hj)).1
    have hjsecond : j ∈ goodSecond := (Finset.mem_inter.mp (hSsub hj)).2
    obtain ⟨qfirst, hacceptFirst, hmemFirst⟩ := hfirst j hjfirst
    obtain ⟨qsecond, hacceptSecond, hmemSecond⟩ := hsecond j hjsecond
    have hpf := (hacceptFirst h).1.2 ⟨j, hmemFirst⟩
    have hps := (hacceptSecond h).1.2 ⟨j, hmemSecond⟩
    have hlf := (hacceptFirst h).2.1.2.2 ⟨j, hmemFirst⟩
    have hls := (hacceptSecond h).2.1.2.2 ⟨j, hmemSecond⟩
    have hqf := (hacceptFirst h).2.2.2.2 ⟨j, hmemFirst⟩
    have hqs := (hacceptSecond h).2.2.2.2 ⟨j, hmemSecond⟩
    dsimp [openSchemeOracle] at hpf hps hlf hls hqf hqs
    exact ⟨hpf.trans hps.symm, hlf.trans hls.symm,
      hqf.trans hqs.symm⟩
  have hresponse (h : Fin 1) :
      first.proximity h = second.proximity h ∧
      first.linear h = second.linear h ∧
      first.quadratic h = second.quadratic h := by
    have hpositions : (codePositions (r := r) (w := w) S).card = 2 * C.k := by
      simpa using hScard
    have hagree (rowFirst rowSecond : EvaluationRow F r w n)
        (hrow : ∀ j ∈ S, rowFirst (codePosition j) = rowSecond (codePosition j))
        (hmemFirst : rowFirst ∈ C.response)
        (hmemSecond : rowSecond ∈ C.response) : rowFirst = rowSecond := by
      apply C.response_unique hmemFirst hmemSecond
        (codePositions S) hpositions
      intro pos hpos
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hpos
      exact hrow j hj
    refine ⟨?_, ?_, ?_⟩
    · apply hagree (first.proximity h) (second.proximity h)
      · intro j hj; exact (hpoint j hj h).1
      · exact C.base_le_response (hq₁ h).1.1
      · exact C.base_le_response (hq₂ h).1.1
    · apply hagree (first.linear h) (second.linear h)
      · intro j hj; exact (hpoint j hj h).2.1
      · exact (hq₁ h).2.1.1
      · exact (hq₂ h).2.1.1
    · apply hagree (first.quadratic h) (second.quadratic h)
      · intro j hj; exact (hpoint j hj h).2.2
      · exact (hq₁ h).2.2.1
      · exact (hq₂ h).2.2.1
  apply hne
  apply Response.ext
  · funext h; exact (hresponse h).1
  · funext h; exact (hresponse h).2.1
  · funext h; exact (hresponse h).2.2

end LigeroFamily.ResponseMass
