import TranscriptV2.Queries
import LfzkV2.Current.OracleWindow

/-! Query-domain facts compose with oracle programs. They concern the
program's inputs, including counterfactual branches, independently of any
particular oracle answers. -/
namespace LfzkV2.Current.OracleDomain
open Merkle.RandomOracle

variable {P A Out Next Q : Type}

/-- Every query on every branch lies in the specified byte domain. -/
def UsesOnly (domain : P → Prop) : {fuel : ℕ} → Tree P A Out fuel → Prop
  | _, .done _ => True
  | _, .query p next => domain p ∧ ∀ answer, UsesOnly domain (next answer)

namespace UsesOnly
variable {domain : P → Prop}

theorem weaken {fuel : ℕ} {tree : Tree P A Out fuel} (h : UsesOnly domain tree) :
    UsesOnly domain tree.weaken := by
  induction tree with
  | done _ => trivial
  | query p next ih => exact ⟨h.1,fun answer => ih answer (h.2 answer)⟩

theorem weakenAdd {fuel : ℕ} {tree : Tree P A Out fuel} (h : UsesOnly domain tree) (extra : ℕ) :
    UsesOnly domain (tree.weakenAdd extra) := by
  induction extra with
  | zero => exact h
  | succ extra ih => exact ih.weaken

theorem map {fuel : ℕ} {tree : Tree P A Out fuel} (h : UsesOnly domain tree) (f : Out → Next) :
    UsesOnly domain (tree.map f) := by
  induction tree with
  | done _ => trivial
  | query p next ih => exact ⟨h.1,fun answer => ih answer (h.2 answer)⟩

theorem bind {fuel nextFuel : ℕ} {tree : Tree P A Out fuel} (h : UsesOnly domain tree)
    (next : Out → Tree P A Next nextFuel) (later : ∀ out, UsesOnly domain (next out)) :
    UsesOnly domain (tree.bind next) := by
  induction tree with
  | done out => exact (later out).weakenAdd _
  | query p continuation ih => exact ⟨h.1,fun answer => ih answer (h.2 answer)⟩

theorem trace {fuel : ℕ} {tree : Tree P A Out fuel} (h : UsesOnly domain tree)
    (H : P → A) (qa : P × A) (member : qa ∈ (tree.run H).2) : domain qa.1 := by
  induction tree with
  | done _ => cases member
  | query p next ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact h.1
      · exact ih (H p) (h.2 (H p)) member

theorem run_eq {fuel : ℕ} {tree : Tree P A Out fuel} (h : UsesOnly domain tree)
    (H H' : P → A) (agree : ∀ p, domain p → H' p = H p) : tree.run H' = tree.run H :=
  Tree.run_congr_on_trace tree H H' (fun qa member =>
    (agree qa.1 (h.trace H qa member)).trans (Tree.trace_sound tree H qa member).symm)

theorem mapQueries_all {fuel : ℕ} (tree : Tree Q A Out fuel) (encode : Q → P)
    (allowed : ∀ p, domain (encode p)) : UsesOnly domain (TranscriptV2.mapQueries encode tree) := by
  induction tree with
  | done _ => trivial
  | query p next ih => exact ⟨allowed p,ih⟩

theorem mapQueries {fuel : ℕ} {source : Q → Prop} {tree : Tree Q A Out fuel}
    (h : UsesOnly source tree) (encode : Q → P) (allowed : ∀ p, source p → domain (encode p)) :
    UsesOnly domain (TranscriptV2.mapQueries encode tree) := by
  induction tree with
  | done _ => trivial
  | query p next ih => exact ⟨allowed p h.1,fun answer => ih answer (h.2 answer)⟩

theorem expandQueries {D : Type} {cost fuel : ℕ} (tree : Tree Q D Out fuel)
    (read : Q → Tree P A D cost) (allowed : ∀ p, UsesOnly domain (read p)) :
    UsesOnly domain (TranscriptV2.expandQueries read tree) := by
  induction tree with
  | done _ => trivial
  | query p next ih => exact (allowed p).bind _ ih

theorem of_queries [Fintype A] [DecidableEq P] {fuel : ℕ} (tree : Tree P A Out fuel)
    (allowed : ∀ p ∈ OracleWindow.queries tree, domain p) : UsesOnly domain tree := by
  induction tree with
  | done _ => trivial
  | query p next ih =>
      refine ⟨allowed p (Finset.mem_insert_self _ _),fun answer => ih answer ?_⟩
      intro q member
      exact allowed q (Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨answer,Finset.mem_univ _,member⟩))

end UsesOnly

end LfzkV2.Current.OracleDomain
