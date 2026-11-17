import LfzkV2.Current.StrandCutObservation
import Merkle.QueryTable
import TranscriptV2.StrandVerifier

/-! The adversary's row trace in the wide-oracle model. A node query there
returns the node's digest together with its whole row of PRF words, so the
adversary's own trace lists, for each node it queried, the input bytes, the
digest and the row. Over raw SHA the experiment computes each row from the
oracle at the PRF inputs of that node (`ofLog`). The SHA answers the trace
determines (`oracle`) agree with the oracle on every queried node and on
every PRF input keyed by a queried node; no other input is read. -/
noncomputable section
namespace LfzkV2.Current.StrandRowTrace
open Merkle.RandomOracle TranscriptV2 TranscriptV2.Strand

/-- One wide-oracle query: input bytes, digest and row of PRF words. -/
abbrev Entry := Framing.Bytes × Digest × (Word → Digest)

/-- The row of PRF words keyed by a node query, read from a SHA oracle. -/
def row (SHA : Framing.Bytes → Digest) (raw : Framing.Bytes) (digest : Digest) : Word → Digest :=
  fun counter => SHA (Input.prf (nodeKey raw digest).1 (nodeKey raw digest).2 counter).encode

/-- The row trace of a raw query log: each entry with its row. -/
def ofLog (SHA : Framing.Bytes → Digest) (log : List (Framing.Bytes × Digest)) : List Entry :=
  log.map fun qa => (qa.1,qa.2,row SHA qa.1 qa.2)

/-- The SHA answers a row trace determines: a PRF input is answered from
the row of any entry with its key, any other input from its first entry,
and an input the trace does not determine by zero. -/
def oracle (trace : List Entry) (raw : Framing.Bytes) : Digest :=
  match decodePrf raw with
  | some (key,counter) =>
      match trace.find? (fun entry => decide (nodeKey entry.1 entry.2.1 = key)) with
      | some entry => entry.2.2 counter
      | none => 0
  | none =>
      match trace.find? (fun entry => decide (entry.1 = raw)) with
      | some entry => entry.2.1
      | none => 0

/-- The raw query log of a row trace. -/
theorem log_ofLog (SHA : Framing.Bytes → Digest) (log : List (Framing.Bytes × Digest)) :
    (ofLog SHA log).map (fun entry => (entry.1,entry.2.1)) = log := by
  simp only [ofLog,List.map_map]
  exact List.map_id' _ |>.trans rfl

variable (SHA : Framing.Bytes → Digest) (log : List (Framing.Bytes × Digest))

/-- A queried non-PRF input is answered by the oracle. -/
theorem oracle_node (sound : ∀ qa ∈ log, qa.2 = SHA qa.1) (raw : Framing.Bytes)
    (notPrf : decodePrf raw = none) (known : Merkle.QueryTable.Known log raw) :
    oracle (ofLog SHA log) raw = SHA raw := by
  obtain ⟨digest,member⟩ := known
  unfold oracle
  rw [notPrf]
  dsimp only
  cases found : (ofLog SHA log).find? (fun entry => decide (entry.1 = raw)) with
  | none =>
      have absent := List.find?_eq_none.mp found (raw,digest,row SHA raw digest)
        (List.mem_map.mpr ⟨(raw,digest),member,rfl⟩)
      simp only [decide_true,not_true_eq_false] at absent
  | some entry =>
      have present := List.mem_of_find?_eq_some found
      have same : entry.1 = raw := by simpa only [decide_eq_true_eq] using List.find?_some found
      obtain ⟨qa,listed,rfl⟩ := List.mem_map.mp present
      dsimp only at same ⊢
      rw [sound qa listed,same]

/-- A PRF input keyed by a queried input is answered by the oracle: every
row with that key is the oracle's row at that key. -/
theorem oracle_prf (key : PrfKey) (counter : Word)
    (listed : ∃ qa ∈ log, nodeKey qa.1 qa.2 = key) :
    oracle (ofLog SHA log) (Input.prf key.1 key.2 counter).encode =
      SHA (Input.prf key.1 key.2 counter).encode := by
  obtain ⟨qa,member,keyed⟩ := listed
  unfold oracle
  rw [decodePrf_encode key counter]
  dsimp only
  cases found : (ofLog SHA log).find? (fun entry => decide (nodeKey entry.1 entry.2.1 = key)) with
  | none =>
      have absent := List.find?_eq_none.mp found (qa.1,qa.2,row SHA qa.1 qa.2)
        (List.mem_map.mpr ⟨qa,member,rfl⟩)
      simp only [keyed,decide_true,not_true_eq_false] at absent
  | some entry =>
      have same : nodeKey entry.1 entry.2.1 = key := by
        simpa only [decide_eq_true_eq] using List.find?_some found
      obtain ⟨other,_,rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some found)
      dsimp only at same ⊢
      simp only [row,same]

/-- At a strand point whose node was queried, the strand verifier reads the
same digest and challenge from the row trace as from the oracle. -/
theorem strand_oracle {Pt C : Type} {blocks : ℕ} (history : Pt → History)
    (sample : Pt → Tree Word Digest (Option C) blocks) (fallback : C)
    (sound : ∀ qa ∈ log, qa.2 = SHA qa.1) (point : Pt)
    (known : Merkle.QueryTable.Known log (history point).input.encode) :
    StrandVerifier.oracle history sample fallback (oracle (ofLog SHA log)) point =
      StrandVerifier.oracle history sample fallback SHA point := by
  have node : oracle (ofLog SHA log) (history point).input.encode = SHA (history point).input.encode :=
    oracle_node SHA log sound _ (history point).nodePoint.property known
  have keyed : ∃ qa ∈ log, nodeKey qa.1 qa.2 = ((history point).id,SHA (history point).input.encode) := by
    obtain ⟨digest,member⟩ := known
    refine ⟨_,member,?_⟩
    rw [← sound _ member]
    exact (history point).nodeKey _
  apply Prod.ext
  · rw [StrandVerifier.oracle_node,StrandVerifier.oracle_node,node]
  · rw [StrandVerifier.oracle_challenge,StrandVerifier.oracle_challenge,node]
    have rowEq : (fun counter => oracle (ofLog SHA log)
        (Input.prf (history point).id (SHA (history point).input.encode) counter).encode) =
        fun counter => SHA (Input.prf (history point).id (SHA (history point).input.encode) counter).encode :=
      funext fun counter => oracle_prf SHA log ((history point).id,SHA (history point).input.encode) counter keyed
    rw [rowEq]

end LfzkV2.Current.StrandRowTrace
