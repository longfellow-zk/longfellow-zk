import Bcs.TotalOracleCommit
import Merkle.NumberedLeaves

/-! A small Merkle-query budget bounds acceptance itself. Fixing the total
transcript oracle leaves an ordinary bounded Merkle program, so no bound on
transcript queries is needed for the predictable-digest argument. -/

namespace Bcs.AdaptiveCommit.Setup

open Finset Merkle.MH Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree
open scoped Classical

variable {Enc D Pt C Out Key Salt M : Type}
variable [DecidableEq Enc] [Inhabited D] [DecidableEq Pt] [Fintype D] [DecidableEq D]
variable {tA N L TM TC n fc : ℕ}
variable (S : Setup Enc D Pt C Out Key tA N L)

theorem merkle_small_ratio_le
    (codec : Codec Salt M D Enc) (dec : RoleDecoders codec)
    (check : Out → Tree Enc D Unit fc) (rootOf : Key → D)
    (claimOf : Out → OpeningClaim n Salt M D)
    (hcheck : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec n (claimOf out).I (claimOf out).a
          (claimOf out).pf (2*n) fun _ => default).run H).2,
        qa ∈ ((check out).run H).2)
    (hsmall : tA < 8) (hn : 128 ≤ n) (ht : tA ≤ TM) (hF : fc+tA ≤ TM)
    (hTM : 1 ≤ TM) (ct : Fin TC → C) :
    ((univ.filter fun mt : Fin TM → D => S.MerkleAccepts codec check rootOf claimOf mt ct).card : ℚ)/
      (Fintype.card D : ℚ)^TM ≤
      (2*tA*tA+(fc+tA)*(2*tA+1) : ℕ)/(Fintype.card D : ℚ) := by
  let commit := fixRight ct S.dflt S.joint []
  have hpref mt : (lazyRun mt default commit []).2.1 <+: runSlots TM (S.merkleRun check ct) mt :=
    lazyRun_seen_prefix_bind mt default _ _ []
  have hc mt :
      let cl := claimOf (lazyRun mt default commit []).1.1
      ∀ qa ∈ ((checkPass codec n cl.I cl.a cl.pf (2*n) fun _ => default).run
        (runOracle TM (S.merkleRun check ct) mt)).2,
        qa ∈ ((S.merkleRun check ct).run (runOracle TM (S.merkleRun check ct) mt)).2 := by
    dsimp only
    rw [S.joint_output]
    intro qa hqa
    exact S.mem_merkleRun_trace check mt ct qa (hcheck _ _ qa hqa)
  have h := smallBudget_acceptance_ratio_le codec dec commit
    (fun out => rootOf (S.keyOut out.1)) (fun out => claimOf out.1)
    (S.merkleRun check ct) hsmall hn ht hF hpref hc hTM
  have he : (univ.filter fun mt : Fin TM → D => S.MerkleAccepts codec check rootOf claimOf mt ct) =
      univ.filter (smallBudgetAccepts (TM := TM) codec commit
        (fun out => rootOf (S.keyOut out.1)) (fun out => claimOf out.1) (S.merkleRun check ct)) := by
    ext mt
    simp only [mem_filter,smallBudgetAccepts,MerkleAccepts]
    rw [← S.joint_output mt ct]
    rfl
  rw [he]
  exact h

theorem merkle_numbered_ratio_le
    (codec : Codec Salt M D Enc) (dec : RoleDecoders codec)
    (check : Out → Tree Enc D Unit fc) (rootOf : Key → D)
    (claimOf : Out → OpeningClaim n Salt M D)
    (hcheck : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec n (claimOf out).I (claimOf out).a
          (claimOf out).pf (2*n) fun _ => default).run H).2,
        qa ∈ ((check out).run H).2)
    (hF : fc+tA ≤ TM) (hTM : 1 ≤ TM) (ct : Fin TC → C) :
    ((univ.filter fun mt : Fin TM → D =>
        S.MerkleAccepts codec check rootOf claimOf mt ct ∧
        (claimOf (S.proof mt ct)).DistinctLeafInputs codec ∧
        tA < (claimOf (S.proof mt ct)).I.card).card : ℚ)/(Fintype.card D : ℚ)^TM ≤
      ((fc+tA)*(2*tA+1) : ℕ)/(Fintype.card D : ℚ) := by
  let commit := fixRight ct S.dflt S.joint []
  have hpref mt : (lazyRun mt default commit []).2.1 <+: runSlots TM (S.merkleRun check ct) mt :=
    lazyRun_seen_prefix_bind mt default _ _ []
  have hc mt :
      let cl := claimOf (lazyRun mt default commit []).1.1
      ∀ qa ∈ ((checkPass codec n cl.I cl.a cl.pf (2*n) fun _ => default).run
        (runOracle TM (S.merkleRun check ct) mt)).2,
        qa ∈ ((S.merkleRun check ct).run (runOracle TM (S.merkleRun check ct) mt)).2 := by
    dsimp only
    rw [S.joint_output]
    intro qa hqa
    exact S.mem_merkleRun_trace check mt ct qa (hcheck _ _ qa hqa)
  have h := numberedBudget_acceptance_ratio_le codec dec commit
    (fun out => rootOf (S.keyOut out.1)) (fun out => claimOf out.1)
    (S.merkleRun check ct) hF hpref hc hTM
  have he : (univ.filter fun mt : Fin TM → D =>
        S.MerkleAccepts codec check rootOf claimOf mt ct ∧
        (claimOf (S.proof mt ct)).DistinctLeafInputs codec ∧
        tA < (claimOf (S.proof mt ct)).I.card) =
      univ.filter (numberedBudgetAccepts (TM := TM) codec commit
        (fun out => rootOf (S.keyOut out.1)) (fun out => claimOf out.1) (S.merkleRun check ct)) := by
    ext mt
    have ha : S.MerkleAccepts codec check rootOf claimOf mt ct =
        smallBudgetAccepts codec commit (fun out => rootOf (S.keyOut out.1))
          (fun out => claimOf out.1) (S.merkleRun check ct) mt := by
      unfold smallBudgetAccepts MerkleAccepts
      rw [← S.joint_output mt ct]
      rfl
    have he := congrArg Prod.fst (S.joint_output mt ct)
    change (lazyRun mt default commit []).1.1 = S.proof mt ct at he
    simp only [mem_filter,numberedBudgetAccepts,ha,← he]
  rw [he]
  exact h

end Bcs.AdaptiveCommit.Setup

namespace Bcs.TotalOracleCommit.Setup

open Finset Merkle.MH Merkle.RandomOracle
open scoped Classical

variable {Enc D Pt C Out Key Salt M : Type}
variable [DecidableEq Enc] [Inhabited D] [DecidableEq Pt] [Fintype D] [DecidableEq D]
variable [Fintype Pt] [Fintype C] [Nonempty C]
variable {tA N L TM n fc : ℕ}
variable (S : Setup Enc D Pt C Out Key tA N L)

/-- Fewer than eight Merkle queries cannot explain one authentication path
in this geometry, except through a predictable digest hit. This includes
arbitrary adaptive interleaving with the transcript oracle. -/
theorem merkle_small_ratio_le
    (codec : Codec Salt M D Enc) (dec : RoleDecoders codec)
    (check : Out → Tree Enc D Unit fc) (rootOf : Key → D)
    (claimOf : Out → OpeningClaim n Salt M D)
    (hcheck : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec n (claimOf out).I (claimOf out).a
          (claimOf out).pf (2*n) fun _ => default).run H).2,
        qa ∈ ((check out).run H).2)
    (hsmall : tA < 8) (hn : 128 ≤ n) (ht : tA ≤ TM) (hF : fc+tA ≤ TM) (hTM : 1 ≤ TM) :
    ((univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
        S.MerkleAccepts codec check rootOf claimOf ω.1 ω.2).card : ℚ)/
      ((Fintype.card D : ℚ)^TM*(Fintype.card C : ℚ)^Fintype.card Pt) ≤
      (2*tA*tA+(fc+tA)*(2*tA+1) : ℕ)/(Fintype.card D : ℚ) := by
  have h := Bcs.product_ratio_le_of_snd_fiber
    (fun (mt : Fin TM → D) (H : Pt → C) => S.MerkleAccepts codec check rootOf claimOf mt H)
    ((2*tA*tA+(fc+tA)*(2*tA+1) : ℕ)/(Fintype.card D : ℚ)) (fun H => by
      simpa only [MerkleAccepts,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow] using
        (S.atOracle H).merkle_small_ratio_le codec dec check rootOf claimOf
          hcheck hsmall hn ht hF hTM emptyTape)
  simpa only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Nat.cast_mul,Nat.cast_pow] using h

/-- Numbered leaves give a lower bound equal to the number of openings,
including arbitrary adaptive interleaving with the transcript oracle. -/
theorem merkle_numbered_ratio_le
    (codec : Codec Salt M D Enc) (dec : RoleDecoders codec)
    (check : Out → Tree Enc D Unit fc) (rootOf : Key → D)
    (claimOf : Out → OpeningClaim n Salt M D)
    (hcheck : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec n (claimOf out).I (claimOf out).a
          (claimOf out).pf (2*n) fun _ => default).run H).2,
        qa ∈ ((check out).run H).2)
    (hF : fc+tA ≤ TM) (hTM : 1 ≤ TM) :
    ((univ.filter fun ω : (Fin TM → D) × (Pt → C) =>
        S.MerkleAccepts codec check rootOf claimOf ω.1 ω.2 ∧
        (claimOf (S.proof ω.1 ω.2)).DistinctLeafInputs codec ∧
        tA < (claimOf (S.proof ω.1 ω.2)).I.card).card : ℚ)/
      ((Fintype.card D : ℚ)^TM*(Fintype.card C : ℚ)^Fintype.card Pt) ≤
      ((fc+tA)*(2*tA+1) : ℕ)/(Fintype.card D : ℚ) := by
  have h := Bcs.product_ratio_le_of_snd_fiber
    (fun (mt : Fin TM → D) (H : Pt → C) =>
      S.MerkleAccepts codec check rootOf claimOf mt H ∧
      (claimOf (S.proof mt H)).DistinctLeafInputs codec ∧ tA < (claimOf (S.proof mt H)).I.card)
    (((fc+tA)*(2*tA+1) : ℕ)/(Fintype.card D : ℚ)) (fun H => by
      simpa only [MerkleAccepts,proof,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow] using
        (S.atOracle H).merkle_numbered_ratio_le codec dec check rootOf claimOf
          hcheck hF hTM emptyTape)
  simpa only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Nat.cast_mul,Nat.cast_pow] using h

end Bcs.TotalOracleCommit.Setup
