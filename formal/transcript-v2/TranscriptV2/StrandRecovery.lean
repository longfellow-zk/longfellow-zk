import TranscriptV2.StrandLinear
import Merkle.QueryTable

/-! Recover one target per strand position from the original query table.
This walk reads no oracle. If a submitted chain contains a missing query,
the first missing input encountered backwards must hit its position's target.
Only collisions inside the original table are excluded. -/
namespace TranscriptV2.StrandRecovery
open Strand Framing Merkle.QueryTable

abbrev Trace := List (Bytes × Digest)

/-- Each position selects at most one digest. A malformed or missing
preimage stops the walk, retaining the target at which it stopped. -/
def target (trace : Trace) : ℕ → Digest → ℕ → Option Digest
  | 0, digest, wanted => if wanted = 0 then some digest else none
  | depth+1, digest, wanted =>
      if wanted = depth+1 then some digest
      else match (preimage trace digest).bind Input.decode with
        | some (.node id [parent] _) =>
            if id.val = depth+1 then target trace depth parent wanted else none
        | _ => none

@[simp] theorem target_self (trace : Trace) (depth : ℕ) (digest : Digest) :
    target trace depth digest depth = some digest := by
  cases depth <;> simp only [target,ite_true]

/-- Every accepted missing node has a fixed target obtained by walking the
original table backwards. No uniqueness assumption is made about replay
answers, and the target is indexed by position rather than a set of labels. -/
theorem missing_node (trace : Trace) (unique : Merkle.MH.CollisionFree trace)
    (messages : ℕ → Bytes) (H : Oracle) (depth : ℕ) (fits : depth < 2^64)
    (missing : ∃ i ≤ depth,
      ((StrandLinear.replay messages H i).input.encode,
        H (StrandLinear.replay messages H i).input.encode) ∉ trace) :
    ∃ i ≤ depth,
      ((StrandLinear.replay messages H i).input.encode,
        H (StrandLinear.replay messages H i).input.encode) ∉ trace ∧
      target trace depth (H (StrandLinear.replay messages H depth).input.encode) i =
        some (H (StrandLinear.replay messages H i).input.encode) := by
  induction depth with
  | zero =>
      obtain ⟨i,bound,absent⟩ := missing
      have same : i = 0 := by omega
      subst i
      exact ⟨0,le_rfl,absent,target_self trace 0 _⟩
  | succ depth ih =>
      by_cases present :
          ((StrandLinear.replay messages H (depth+1)).input.encode,
            H (StrandLinear.replay messages H (depth+1)).input.encode) ∈ trace
      · have earlier : ∃ i ≤ depth,
            ((StrandLinear.replay messages H i).input.encode,
              H (StrandLinear.replay messages H i).input.encode) ∉ trace := by
          obtain ⟨i,bound,absent⟩ := missing
          refine ⟨i,?_,absent⟩
          by_contra later
          have same : i = depth+1 := by omega
          exact absent (same ▸ present)
        obtain ⟨i,bound,absent,hit⟩ := ih (by omega) earlier
        have found := preimage_of_mem trace unique _ _ present
        have id : (StrandLinear.replay messages H (depth+1)).id.val = depth+1 := by
          rw [History.id_val _ (by simpa only [StrandLinear.replay_depth] using fits),
            StrandLinear.replay_depth]
        refine ⟨i,by omega,absent,?_⟩
        rw [target,if_neg (by omega),found,Option.bind_some,
          Input.decode_encode _ (History.valid _)]
        change (if (StrandLinear.replay messages H (depth+1)).id.val = depth+1 then
          target trace depth (H (StrandLinear.replay messages H depth).input.encode) i
          else none) = _
        rw [if_pos id]
        exact hit
      · exact ⟨depth+1,le_rfl,present,target_self trace (depth+1) _⟩

/-- A queried final seal chooses the start of the backwards walk. Its id
must match the terminal position, and only PRF counter zero is a seal. -/
def sealTarget (trace : Trace) (depth : ℕ) (finalSeal : Digest) (wanted : ℕ) : Option Digest :=
  match (preimage trace finalSeal).bind Input.decode with
  | some (.prf id digest counter) =>
      if id.val = depth ∧ counter = 0 then target trace depth digest wanted else none
  | _ => none

theorem sealTarget_of_mem (trace : Trace) (unique : Merkle.MH.CollisionFree trace)
    (messages : ℕ → Bytes) (H : Oracle) (depth : ℕ) (fits : depth < 2^64)
    (finalSeal : Digest)
    (present : ((Input.prf (StrandLinear.replay messages H depth).id
      (H (StrandLinear.replay messages H depth).input.encode) 0).encode,finalSeal) ∈ trace)
    (wanted : ℕ) :
    sealTarget trace depth finalSeal wanted =
      target trace depth (H (StrandLinear.replay messages H depth).input.encode) wanted := by
  have found := preimage_of_mem trace unique _ _ present
  have id : (StrandLinear.replay messages H depth).id.val = depth := by
    rw [History.id_val _ (by simpa only [StrandLinear.replay_depth] using fits),
      StrandLinear.replay_depth]
  simp only [sealTarget,found,Option.bind_some,Input.decode_encode (.prf _ _ _) trivial,id,
    and_self,ite_true]

end TranscriptV2.StrandRecovery
