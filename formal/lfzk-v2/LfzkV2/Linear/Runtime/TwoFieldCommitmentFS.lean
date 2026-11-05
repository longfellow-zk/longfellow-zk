import LfzkV2.Linear.Runtime.TwoFieldFS
import LfzkV2.TwoFieldCommitmentFS

/-!
# Authenticated extraction for the linear-terminal protocol

The model targets Rust snapshot 21cb029: independent affine frontend
streams, binary input packing, the linear-only Polygero backend, and the
retained two-field MAC. Both roots fix the common commitment key before
the MAC challenge. Future changes to the backend are outside this endpoint.

The generic cut-trace and joint Merkle checker are reused unchanged. Only
the semantic sides and their causal transcript are the linear-terminal frontend and its packed/direct adapters here.
-/

namespace LfzkV2.Linear.Runtime.TwoFieldCommitmentFS

open RecursivePolygero Merkle Merkle.MH Bcs.TotalOracle Finset
  Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree TwoFieldReplay
open LfzkV2.TwoFieldCommitmentFS (cutOracle cutOracle_off check check_contains_one check_contains_two)
open scoped Classical

variable {F₁ F₂ Key C Public Out Enc D Salt₁ Salt₂ : Type}
variable [Field F₁] [Fintype F₁] [DecidableEq F₁]
variable [Field F₂] [Fintype F₂] [DecidableEq F₂] [Fintype C]
variable {out₁ input₁ out₂ input₂ tA N : ℕ}
variable {circuit₁ : Native.Circuit F₁ out₁ input₁} {I₁ : Instance F₁}
variable {circuit₂ : Native.Circuit F₂ out₂ input₂} {I₂ : Instance F₂}
variable (S₁ : CompiledSide F₁ C (Context Key C Public) circuit₁ I₁)
variable (S₂ : CompiledSide F₂ C S₁.Selected circuit₂ I₂)

def setup [DecidableEq (Domain S₁ S₂)]
    (body : TwoOracleTree Enc D (Domain S₁ S₂) C Out tA N)
    (proofOf : Out → Proof S₁ S₂) (dflt : C) :
    Bcs.TotalOracleCommit.Setup Enc D (Domain S₁ S₂) C Out Key tA N
      (1+S₁.slots+S₂.slots) where
  body := body
  hashInput out := hashInput S₁ S₂ (proofOf out)
  dflt := dflt
  key := key S₁ S₂
  keyOut out := (TwoFieldReplay.context S₁ S₂ (proofOf out)).1
  hkey out k := hashInput_key S₁ S₂ (proofOf out) k

variable [DecidableEq Enc] [Inhabited D]
variable (codec₁ : Codec Salt₁ (MerkleCompiler.Leaf F₁ I₁.nw I₁.nq) D Enc)
variable (codec₂ : Codec Salt₂ (MerkleCompiler.Leaf F₂ I₂.nw I₂.nq) D Enc)
variable (claimOf₁ : Out → OpeningClaim I₁.n Salt₁ (MerkleCompiler.Leaf F₁ I₁.nw I₁.nq) D)
variable (claimOf₂ : Out → OpeningClaim I₂.n Salt₂ (MerkleCompiler.Leaf F₂ I₂.nw I₂.nq) D)
variable [Fintype Key] [Fintype Public] [Fintype D]
variable [DecidableEq Key] [DecidableEq D] [Inhabited Salt₁] [Inhabited Salt₂]
variable [Inhabited (MerkleCompiler.Leaf F₁ I₁.nw I₁.nq)]
variable [Inhabited (MerkleCompiler.Leaf F₂ I₂.nw I₂.nq)]
variable [Fintype S₁.Data] [Fintype S₂.Data]
variable [DecidableEq (Domain S₁ S₂)]
variable {Fmac : Type} [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {blocks TM : ℕ}
variable (M : MacData C Fmac (Counting.tupleCounts I₁).Index (Counting.tupleCounts I₂).Index blocks)

/-- The annotated authenticated two-field verifier, using the shared two-opening
reduction and the native staged shared-query potential compiler. No backend
soundness or commitment-context invariance is left as a premise. -/
theorem extraction_le
    (ht₁ : 0 < I₁.t) (ht₂ : 0 < I₂.t)
    (body : TwoOracleTree Enc D (Domain S₁ S₂) C Out tA N)
    (proofOf : Out → Proof S₁ S₂)
    (dec₁ : RoleDecoders codec₁) (dec₂ : RoleDecoders codec₂)
    (rootOf₁ rootOf₂ : Key → D)
    (tag : Public → Fin blocks → Fmac)
    (hrowOne : ∀ (ctx : Context Key C Public) W g, S₁.Good ctx W g →
      M.macOne g (M.decode ctx.2.1) = tag ctx.2.2)
    (hrowTwo : ∀ (ctx : S₁.Selected) W g,
      S₂.Good ctx W g → M.macTwo g (M.decode (S₁.context ctx).2.1) = tag (S₁.context ctx).2.2)
    (hspace : 2*I₂.n+2*I₁.n+tA ≤ TM) :
    let K := setup S₁ S₂ body proofOf S₁.dflt
    let ck := check I₁ I₂ codec₁ codec₂ claimOf₁ claimOf₂
    let context := fun (mt : Fin TM → D) (H : Domain S₁ S₂ → C) key =>
      (cutOracle I₁ K dec₁ rootOf₁ mt H key,cutOracle I₂ K dec₂ rootOf₂ mt H key)
    let acceptedAt := fun (mt : Fin TM → D) (H : Domain S₁ S₂ → C) (result : Out) =>
      let proof := proofOf result
      (TwoFieldReplay.context S₁ S₂ proof).2.1 = H (.inl (TwoFieldReplay.context S₁ S₂ proof).1) ∧
      S₁.CompiledAccepts ht₁ (codec₁.withOracle (K.merkleOracle ck mt H))
        (fun x => H (.inr (.inl x))) (selectedOne S₁ S₂ proof)
        (rootOf₁ (TwoFieldReplay.context S₁ S₂ proof).1) (claimOf₁ result) ∧
      S₂.CompiledAccepts ht₂ (codec₂.withOracle (K.merkleOracle ck mt H))
        (fun x => H (.inr (.inr x))) proof
        (rootOf₂ (TwoFieldReplay.context S₁ S₂ proof).1) (claimOf₂ result)
    let badAt := fun (mt : Fin TM → D) (H : Domain S₁ S₂ → C) (result : Out) =>
      let proof := proofOf result
      let W := context mt H (TwoFieldReplay.context S₁ S₂ proof).1
      TwoFieldPotential.extract S₁ S₂ M W proof = none
    let accepts := fun mt H => acceptedAt mt H (K.proof mt H)
    let fails := fun mt H => badAt mt H (K.proof mt H)
    ((univ.filter fun ω : (Fin TM → D) × (Domain S₁ S₂ → C) =>
        accepts ω.1 ω.2 ∧ fails ω.1 ω.2).card : ℚ) /
      ((Fintype.card D : ℚ)^TM * (Fintype.card C : ℚ)^Fintype.card (Domain S₁ S₂)) ≤
      (N * TwoFieldFS.maxBudget S₁ S₂ M +
        ∑ i, TwoFieldFS.slotBudget S₁ S₂ M i)/Fintype.card C +
      2 * (Bcs.AdaptiveCommit.adaptiveNumerator (2*I₂.n+2*I₁.n) tA
        (1+S₁.slots+S₂.slots+N) : ℚ)/Fintype.card D := by
  letI : Nonempty C := ⟨S₁.dflt⟩
  intro K ck context acceptedAt badAt accepts fails
  let idealAt := fun (mt : Fin TM → D) (H : Domain S₁ S₂ → C) (result : Out) =>
    let proof := proofOf result
    let W := context mt H (TwoFieldReplay.context S₁ S₂ proof).1
    (TwoFieldReplay.context S₁ S₂ proof).2.1 = H (.inl (TwoFieldReplay.context S₁ S₂ proof).1) ∧
    S₁.Accepts W.1 (fun x => H (.inr (.inl x))) (selectedOne S₁ S₂ proof) ∧
    S₂.Accepts W.2 (fun x => H (.inr (.inr x))) proof ∧
    badAt mt H result
  let fsError : ℚ := (N * TwoFieldFS.maxBudget S₁ S₂ M +
    ∑ i, TwoFieldFS.slotBudget S₁ S₂ M i)/Fintype.card C
  have hfs mt : ((univ.filter fun H => idealAt mt H (K.proof mt H)).card : ℚ)/
      (Fintype.card C : ℚ)^Fintype.card (Domain S₁ S₂) ≤ fsError := by
    have h := TwoFieldFS.extraction_le S₁ S₂ M
      (K.search mt) proofOf (context mt)
      (by
        intro H H' x hoff
        exact Prod.ext (cutOracle_off I₁ K dec₁ rootOf₁ mt H H' x hoff)
          (cutOracle_off I₂ K dec₂ rootOf₂ mt H H' x hoff)) tag hrowOne hrowTwo
    convert! h using 1
    congr 3
    ext H
    simp only [mem_filter]
    change (H ∈ univ ∧ idealAt mt H (K.proof mt H)) ↔
      (H ∈ univ ∧ idealAt mt H ((K.search mt).run H).1)
    rw [K.proof_eq]
  have hbridge mt H (ha : accepts mt H)
      (he₁ : K.Explains dec₁ rootOf₁ claimOf₁ mt H)
      (he₂ : K.Explains dec₂ rootOf₂ claimOf₂ mt H) (hb : fails mt H) : idealAt mt H (K.proof mt H) := by
    obtain ⟨e₁,hext₁,hagree₁,-⟩ := he₁
    obtain ⟨e₂,hext₂,hagree₂,-⟩ := he₂
    let result := K.proof mt H
    let proof := proofOf result
    refine ⟨ha.1,?_,?_,hb⟩
    · exact S₁.accepts_of_extraction ht₁ dec₁
        (codec₁.withOracle (K.merkleOracle ck mt H)) (fun x => H (.inr (.inl x)))
        (selectedOne S₁ S₂ proof) (rootOf₁ (TwoFieldReplay.context S₁ S₂ proof).1)
        ((K.atOracle H).cutTrace mt Bcs.TotalOracleCommit.Setup.emptyTape (TwoFieldReplay.context S₁ S₂ proof).1)
        (claimOf₁ result) e₁ hext₁ hagree₁ ha.2.1
    · exact S₂.accepts_of_extraction ht₂ dec₂
        (codec₂.withOracle (K.merkleOracle ck mt H)) (fun x => H (.inr (.inr x)))
        proof (rootOf₂ (TwoFieldReplay.context S₁ S₂ proof).1)
        ((K.atOracle H).cutTrace mt Bcs.TotalOracleCommit.Setup.emptyTape (TwoFieldReplay.context S₁ S₂ proof).1)
        (claimOf₂ result) e₂ hext₂ hagree₂ ha.2.2
  have hTM : 1 ≤ TM := by have := I₁.query_le; omega
  have h := K.ratio_le_two_from_potential codec₁ dec₁ ck rootOf₁ claimOf₁
    (check_contains_one I₁ I₂ codec₁ codec₂ claimOf₁ claimOf₂)
    codec₂ dec₂ ck rootOf₂ claimOf₂ (check_contains_two I₁ I₂ codec₁ codec₂ claimOf₁ claimOf₂)
    (by omega) (by omega) hspace hTM accepts fails
    (fun _ _ h => h.2.1.2.2.1) (fun _ _ h => h.2.2.2.2.1) fsError (by
      intro mt
      apply le_trans _ (hfs mt)
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply (Nat.cast_le (α := ℚ)).mpr
      exact card_le_card (by
        intro H hH
        simp only [mem_filter] at hH
        exact mem_filter.mpr ⟨mem_univ _,hbridge mt H hH.2.1 hH.2.2.2.1 hH.2.2.1 hH.2.2.2.2⟩))
  convert! h using 1
  congr 3
  ext ω
  simp only [mem_filter]

end LfzkV2.Linear.Runtime.TwoFieldCommitmentFS
