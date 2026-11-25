import Bcs.TotalOracleCommit
import LfzkV1.TwoFieldV1Rows
import LigeroFamily.Protocol.Finite
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Perm

/-!
# Analytical annotation of a raw v1 proof

A raw proof carries neither the decoded MAC share nor the ordered Ligero
queries. These three verifier lookups run after the adversary has selected
its proof. They preserve the adversary's left-oracle queries and preserve
its original right-oracle trace as a prefix. The right-oracle suffix is
available for separate role accounting.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LfzkV1.RawProofAnnotation125

open Bcs.TotalOracle Bcs.TotalOracleCommit Merkle.RandomOracle Tree TwoOracleTree
open Finset LigeroFamily LfzkV1.TwoFieldV1Rows

/-- The two opening addresses can read the key answer and raw proof. The
signature opening address does not read the hash opening answer. -/
structure Annotator (Raw Point Coin Aux : Type) where
  key : Raw → Point
  hashOpening : Raw → Coin → Point
  signatureOpening : Raw → Coin → Point
  decorate : Raw → Coin → Coin → Coin → Aux

namespace Annotator

variable {Raw Point Coin Aux Enc Digest : Type}
variable (a : Annotator Raw Point Coin Aux)
variable {N tA TM TR : ℕ}

/-- The verifier's three lookups in protocol order. -/
def program (raw : Raw) : Tree Point Coin (Raw × Aux) 3 :=
  .query (a.key raw) fun keyCoin =>
    .query (a.hashOpening raw keyCoin) fun hashCoin =>
      .query (a.signatureOpening raw keyCoin) fun sigCoin =>
        .done (raw, a.decorate raw keyCoin hashCoin sigCoin)

/-- The exact post-processing of a fixed raw output at a total oracle. -/
def result (H : Point → Coin) (raw : Raw) : Raw × Aux :=
  let k := H (a.key raw)
  (raw, a.decorate raw k (H (a.hashOpening raw k)) (H (a.signatureOpening raw k)))

/-- The extra ordered trace, including repeated addresses if present. -/
def trace (H : Point → Coin) (raw : Raw) : List (Point × Coin) :=
  let k := H (a.key raw)
  let h := a.hashOpening raw k
  let s := a.signatureOpening raw k
  [(a.key raw, k), (h, H h), (s, H s)]

@[simp] theorem program_run (H : Point → Coin) (raw : Raw) :
    (a.program raw).run H = (a.result H raw, a.trace H raw) := rfl

/-- The analytical right continuation adds no left fuel. -/
def append (body : TwoOracleTree Enc Digest Point Coin Raw tA N) :
    TwoOracleTree Enc Digest Point Coin (Raw × Aux) tA (3 + N) :=
  body.bindRight a.program

/-- For a fixed left tape, the original right execution is preserved before
the three annotation lookups. -/
theorem run_append [DecidableEq Enc] (body : TwoOracleTree Enc Digest Point Coin Raw tA N)
    (mt : Fin TM → Digest) (defaultMerkle : Digest) (seen : List Enc) (H : Point → Coin) :
    let run := (fixLeft mt defaultMerkle body seen).run H
    (fixLeft mt defaultMerkle (a.append body) seen).run H =
      (a.result H run.1, run.2 ++ a.trace H run.1) := by
  simp only [append, fixLeft_bindRight, Tree.run_bind, program_run]

/-- The distinct observed addresses of any role after annotation lie in the
union of that role's original addresses and its three analytical lookups. -/
theorem observed_role_append_le [DecidableEq Enc] [DecidableEq Point]
    (body : TwoOracleTree Enc Digest Point Coin Raw tA N)
    (mt : Fin TM → Digest) (defaultMerkle : Digest) (seen : List Enc) (H : Point → Coin)
    (isRole : Point → Prop) [DecidablePred isRole] :
    let raw := fixLeft mt defaultMerkle body seen
    let extended := fixLeft mt defaultMerkle (a.append body) seen
    ((queried extended H).toFinset.filter isRole).card ≤
      ((queried raw H).toFinset.filter isRole).card +
        (((a.trace H (raw.run H).1).map Prod.fst).toFinset.filter isRole).card := by
  dsimp only
  rw [queried, a.run_append, List.map_append, List.toFinset_append, Finset.filter_union]
  exact card_union_le _ _

section LeftTrace

variable [DecidableEq Point]
variable (rt : Fin TR → Coin) (defaultCoin : Coin) (H : Point → Coin)

private theorem left_liftRightAt {B : Type} {fuel : ℕ}
    (program : Tree Point Coin B fuel) (seen : List Point) :
    fixRight rt defaultCoin
      (answerRight H (liftRightAt (QL := Enc) (DL := Digest) tA program)) seen =
      .done (program.run H).1 := by
  induction program generalizing seen with
  | done _ => rfl
  | query q next ih =>
    simp only [liftRightAt, answerRight, fixRight, Tree.run_query]
    exact ih (H q) _

private theorem left_weakenRight {B : Type} {fuel : ℕ}
    (body : TwoOracleTree Enc Digest Point Coin B tA fuel) (seen : List Point) :
    fixRight rt defaultCoin (answerRight H (weakenRight body)) seen =
      fixRight rt defaultCoin (answerRight H body) seen := by
  induction body generalizing seen with
  | done _ => rfl
  | queryLeft q next ih =>
    simp only [weakenRight, answerRight, fixRight]
    exact congrArg (Tree.query q) (funext fun y => ih y seen)
  | queryRight q next ih =>
    simp only [weakenRight, answerRight, fixRight]
    exact ih (H q) _

private theorem left_weakenRightAdd {B : Type} {fuel : ℕ}
    (k : ℕ) (body : TwoOracleTree Enc Digest Point Coin B tA fuel) (seen : List Point) :
    fixRight rt defaultCoin (answerRight H (weakenRightAdd k body)) seen =
      fixRight rt defaultCoin (answerRight H body) seen := by
  induction k with
  | zero => rfl
  | succ k ih => rw [weakenRightAdd, left_weakenRight, ih]

/-- After fixing the right oracle, the annotated prover is a post-process
of the original left program. The complete left trace is unchanged. -/
theorem left_program_append (body : TwoOracleTree Enc Digest Point Coin Raw tA N)
    (seen : List Point) :
    fixRight rt defaultCoin (answerRight H (a.append body)) seen =
      (fixRight rt defaultCoin (answerRight H body) seen).map (a.result H) := by
  unfold append
  induction body generalizing seen with
  | done raw =>
    simp only [bindRight, left_weakenRightAdd, left_liftRightAt, program_run,
      answerRight, fixRight, Merkle.RandomOracle.Tree.map]
  | queryLeft q next ih =>
    simp only [bindRight, answerRight, fixRight, Merkle.RandomOracle.Tree.map]
    exact congrArg (Tree.query q) (funext fun y => ih y seen)
  | queryRight q next ih =>
    simp only [bindRight, answerRight, fixRight]
    exact ih (H q) _

/-- The annotation preserves both the left slot list and the trace of
individual left calls, including repeats. -/
theorem left_run_append [DecidableEq Enc]
    (body : TwoOracleTree Enc Digest Point Coin Raw tA N) (seenRight : List Point)
    (mt : Fin TM → Digest) (defaultMerkle : Digest) (seenLeft : List Enc) :
    let run := lazyRun mt defaultMerkle
      (fixRight rt defaultCoin (answerRight H body) seenRight) seenLeft
    lazyRun mt defaultMerkle
      (fixRight rt defaultCoin (answerRight H (a.append body)) seenRight) seenLeft =
      (a.result H run.1, run.2) := by
  rw [a.left_program_append, lazyRun_map]

end LeftTrace

end Annotator

section OrderedQuery

/-- A uniform unordered set and a uniform permutation describe one ordered
sample without replacement. -/
abbrev OrderedQuery (n r : ℕ) := QuerySet n r × Equiv.Perm (Fin r)

namespace OrderedQuery

variable {n r : ℕ}

/-- Recover the original sampler order from the selected set and its order. -/
def indices (q : OrderedQuery n r) : Fin r ↪ Fin n :=
  q.2.toEmbedding.trans (q.1.coordinates.orderEmbOfFin q.1.card_coordinates).toEmbedding

theorem map_indices (q : OrderedQuery n r) : univ.map q.indices = q.1.coordinates := by
  unfold indices
  rw [← Finset.map_map, Finset.map_univ_equiv, Finset.map_orderEmbOfFin_univ]

/-- The pair of a set and an order is equivalent to a sequence of distinct
sampled indices. -/
noncomputable def equivEmbedding : OrderedQuery n r ≃ (Fin r ↪ Fin n) :=
  Equiv.ofBijective indices (by
    constructor
    · rintro ⟨qa, pa⟩ ⟨qb, pb⟩ h
      have hq : qa = qb := by
        apply Subtype.ext
        change qa.coordinates = qb.coordinates
        exact (map_indices (qa, pa)).symm.trans
          ((congrArg (fun e => univ.map e) h).trans (map_indices (qb, pb)))
      subst qb
      refine Prod.ext rfl ?_
      apply Equiv.ext
      intro i
      have hi := congrArg (fun f : Fin r ↪ Fin n => f i) h
      exact (qa.coordinates.orderEmbOfFin qa.card_coordinates).injective hi
    · intro e
      let q : QuerySet n r := ⟨univ.map e, mem_powersetCard.mpr ⟨subset_univ _, by simp⟩⟩
      let iso := q.coordinates.orderIsoOfFin q.card_coordinates
      let toSet (i : Fin r) : q.coordinates := ⟨e i, mem_map.mpr ⟨i, mem_univ _, rfl⟩⟩
      have hn : Function.Injective toSet := fun _ _ h => e.injective (congrArg Subtype.val h)
      let perm : Equiv.Perm (Fin r) :=
        Equiv.ofBijective (iso.symm ∘ toSet) (Finite.injective_iff_bijective.mp (iso.symm.injective.comp hn))
      refine ⟨(q, perm), ?_⟩
      apply Function.Embedding.ext
      intro i
      exact congrArg Subtype.val (iso.apply_symm_apply (toSet i)))

/-- Each unordered set has exactly `r!` orders. -/
theorem set_fiber_card (q : QuerySet n r) :
    (univ.filter fun x : OrderedQuery n r => x.1 = q).card = r.factorial := by
  have hq : (univ.filter fun x : QuerySet n r => x = q) = {q} := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
  rw [card_filter_comp_fst (fun x : QuerySet n r => x), hq, card_singleton,
    Fintype.card_perm, one_mul, Fintype.card_fin]

/-- The analysis can read only the set while retaining the sampler order
for reindexing raw verifier openings. -/
def setDecoder : ExactDecoder (OrderedQuery n r) (QuerySet n r) :=
  (ExactDecoder.self (QuerySet n r)).fst (Equiv.Perm (Fin r))

end OrderedQuery

end OrderedQuery

end LfzkV1.RawProofAnnotation125
