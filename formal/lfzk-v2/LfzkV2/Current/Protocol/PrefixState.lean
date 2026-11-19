import TranscriptV2.Queries
import LfzkV2.Current.Prefix

/-! Direct state extraction: stop the recorded prefix at the first context
occurrence, and read the strict ancestor tape. Neither operation replays the
adversary under an oracle completion. -/
noncomputable section
namespace LfzkV2.Current.Protocol.PrefixState
open Merkle.RandomOracle TranscriptV2 LfzkV2.Current
open scoped Classical

section Cut
variable {P A Key Out : Type} [DecidableEq Key]

def cut (label : P → Key) (key : Key) (past : List (P × A)) : List (P × A) :=
  past.takeWhile (fun qa => decide (label qa.1 ≠ key))

theorem cut_append_query (label : P → Key) (past rest : List (P × A)) (p : P) (a : A) :
    cut label (label p) (past ++ (p,a)::rest) = cut label (label p) past := by
  induction past with
  | nil => simp [cut]
  | cons qa past ih =>
      by_cases same : label qa.1 = label p
      · simp [cut, same]
      · simpa [cut, same] using congrArg (List.cons qa) ih

/-- The original first-context cut is already determined by the actual
strict prefix, even if the current query is a malformed speculative query. -/
theorem cut_eq_original (label : P → Key) {fuel : ℕ} (tree : Tree P A Out fuel) (H : P → A)
    (past rest : List (P × A)) (p : P) (a : A)
    (executed : (tree.run H).2 = past ++ (p,a)::rest) :
    cut label (label p) past = beforeLabel label (label p) tree H := by
  rw [beforeLabel_eq_takeWhile, executed]
  exact (cut_append_query label past rest p a).symm

end Cut

section Tape
variable {roles : List Role} {Context Block Link Body C : Type}
local notation "Point" => Input roles Context Block Link Body

/-- This small representative fills only the point's named strict ancestor
coordinates. It does not replay the adversary or store a complete prefix.
It is a temporary adapter to existing oracle-argument local lemmas. -/
def tapeOracle (fallback : Link × C) (point : Point) (tape : Fin point.rank → C) : Point → Link × C :=
  fun q => if h : q.rank < point.rank then
    if q = point.priorPoints ⟨q.rank,h⟩ then (fallback.1,tape ⟨q.rank,h⟩) else fallback
  else fallback

theorem tapeOracle_prior (fallback : Link × C) (point : Point) (tape : Fin point.rank → C) :
    point.priorAnswers (tapeOracle fallback point tape) = tape := by
  funext i
  have rank := point.priorPoints_rank i
  simp only [Input.priorAnswers, tapeOracle]
  have within : (point.priorPoints i).rank < point.rank := rank ▸ i.isLt
  rw [dif_pos within]
  have index : (⟨(point.priorPoints i).rank,within⟩ : Fin point.rank) = i := Fin.ext rank
  rw [index, if_pos rfl]

def lookup {P A : Type} [DecidableEq P] (fallback : A) (past : List (P × A)) (p : P) : A :=
  match past.find? (fun qa => qa.1 = p) with
  | none => fallback
  | some qa => qa.2

theorem lookup_agrees {P A : Type} [DecidableEq P] (fallback : A)
    (past : List (P × A)) (H : P → A)
    (sound : ∀ qa ∈ past, qa.2 = H qa.1) (p : P) (present : p ∈ past.map Prod.fst) :
    lookup fallback past p = H p := by
  induction past with
  | nil => simp at present
  | cons qa past ih =>
      by_cases same : qa.1 = p
      · simp only [lookup, List.find?_cons, same, decide_true]
        exact (sound qa List.mem_cons_self).trans (congrArg H same)
      · simp only [lookup, List.find?_cons, same, decide_false]
        apply ih (fun entry member => sound entry (List.mem_cons_of_mem _ member))
        simpa only [List.map_cons, List.mem_cons, Ne.symm same, false_or] using present

end Tape
end LfzkV2.Current.Protocol.PrefixState
