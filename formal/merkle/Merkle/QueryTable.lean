import Merkle.Extraction
import Merkle.RandomOracle

/-! Deterministic lookup in an existing oracle query table. No oracle
evaluation or assumption about the order of the recorded queries is needed. -/
namespace Merkle.QueryTable

/-- Membership names an original query, independently of its answer. -/
def Known {P D : Type*} (trace : List (P × D)) (raw : P) : Prop :=
  ∃ digest, (raw,digest) ∈ trace

def Sound {P D : Type*} (trace : List (P × D)) (H : P → D) : Prop :=
  ∀ entry ∈ trace, H entry.1 = entry.2

theorem known_run_iff {P D Out : Type*} [DecidableEq P] {fuel : ℕ}
    (program : RandomOracle.Tree P D Out fuel) (H : P → D) (raw : P) :
    Known (program.run H).2 raw ↔ raw ∈ ((program.run H).2.map Prod.fst).toFinset := by
  constructor
  · rintro ⟨digest,member⟩
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨(raw,digest),member,rfl⟩)
  · intro member
    obtain ⟨⟨point,digest⟩,present,same⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
    cases same
    exact ⟨digest,present⟩

theorem equal_of_known {P D : Type*} (trace : List (P × D)) (H : P → D)
    (sound : Sound trace H) (free : MH.CollisionFree trace) (a b : P)
    (knownA : Known trace a) (knownB : Known trace b) (equal : H a = H b) : a = b := by
  obtain ⟨da,ha⟩ := knownA
  obtain ⟨db,hb⟩ := knownB
  exact free (a,da) ha (b,db) hb ((sound _ ha).symm.trans (equal.trans (sound _ hb)))

variable {P D : Type*} [DecidableEq D]

def preimage (trace : List (P × D)) (digest : D) : Option P :=
  (trace.find? fun entry => decide (entry.2 = digest)).map Prod.fst

theorem preimage_mem (trace : List (P × D)) (digest : D) (raw : P)
    (found : preimage trace digest = some raw) : (raw,digest) ∈ trace := by
  obtain ⟨entry,selected,same⟩ := Option.map_eq_some_iff.mp found
  have answer := of_decide_eq_true
    (List.find?_some (p := fun entry : P × D => decide (entry.2 = digest)) selected)
  have member := List.mem_of_find?_eq_some selected
  have equal : entry = (raw,digest) := Prod.ext same answer
  rwa [equal] at member

/-- Original-table collision freedom makes the first matching input unique.
It imposes no constraint on oracle answers outside the table. -/
theorem preimage_of_mem (trace : List (P × D)) (unique : MH.CollisionFree trace)
    (raw : P) (digest : D) (member : (raw,digest) ∈ trace) :
    preimage trace digest = some raw := by
  cases found : trace.find? (fun entry => decide (entry.2 = digest)) with
  | none =>
      have absent := List.find?_eq_none.mp found (raw,digest) member
      exact False.elim (absent (by simp))
  | some entry =>
      have same := MH.find?_answer_unique trace unique digest entry found (raw,digest) member rfl
      change Option.map Prod.fst _ = _
      rw [found,Option.map_some]
      exact congrArg some same.symm

section Answer
variable [DecidableEq P]

/-- Forward lookup needs no collision assumption: repeated queries have
the same answer in every actual oracle trace. -/
def answer (trace : List (P × D)) (raw : P) : Option D :=
  (trace.find? fun entry => decide (entry.1 = raw)).map Prod.snd

omit [DecidableEq D] in
theorem answer_of_mem (trace : List (P × D)) (H : P → D)
    (sound : ∀ entry ∈ trace, H entry.1 = entry.2) (raw : P)
    (known : ∃ digest, (raw,digest) ∈ trace) : answer trace raw = some (H raw) := by
  obtain ⟨digest,member⟩ := known
  cases found : trace.find? (fun entry => decide (entry.1 = raw)) with
  | none =>
      have absent := List.find?_eq_none.mp found (raw,digest) member
      exact False.elim (absent (by simp))
  | some entry =>
      have present := List.mem_of_find?_eq_some found
      have same : entry.1 = raw := of_decide_eq_true
        (List.find?_some (p := fun entry : P × D => decide (entry.1 = raw)) found)
      change Option.map Prod.snd _ = _
      rw [found,Option.map_some]
      exact congrArg some ((sound entry present).symm.trans (congrArg H same))

end Answer
end Merkle.QueryTable
