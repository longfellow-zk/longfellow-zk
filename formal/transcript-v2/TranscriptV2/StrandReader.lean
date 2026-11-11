import TranscriptV2.Strand

/-! The round's buffered PRF reader. Reads use one stream and retain unused
block bytes. A zero-length read makes no query, including at counter exhaustion.
The explicit oracle program includes each counter-block query actually issued;
the fuel is only a conservative bound of one query per requested byte. -/
namespace TranscriptV2.Strand
open Framing Merkle.RandomOracle

structure Reader where
  prf : Prf
  buffer : Bytes
  bound : buffer.length < 32

def Reader.ofPrf (prf : Prf) : Reader := ⟨prf,[],by decide⟩

def Reader.afterBlock (prf : Prf) (block : Digest) : Reader :=
  ⟨prf,List.ofFn (fun i : Fin 31 => block i.succ),by simp only [List.length_ofFn]; decide⟩

def Reader.readByte (state : Reader) : Tree Bytes Digest (Option (Byte × Reader)) 1 :=
  match h : state.buffer with
  | byte::tail => .done (some (byte,⟨state.prf,tail,by
      have hb := state.bound
      rw [h,List.length_cons] at hb
      omega⟩))
  | [] => state.prf.nextBlock.map fun result => result.map fun value =>
      (value.1 0,Reader.afterBlock value.2 value.1)

def Reader.read : (count : ℕ) → Reader → Tree Bytes Digest (Option (Bytes × Reader)) count
  | 0, state => .done (some ([],state))
  | count+1, state => state.readByte.bind fun result => match result with
      | none => .done none
      | some (byte,next) => (Reader.read count next).map fun result =>
          result.map fun value => (byte::value.1,value.2)

@[simp] theorem Reader.read_zero (state : Reader) (H : Oracle) :
    (Reader.read 0 state).run H = (some ([],state),[]) := rfl

theorem Reader.read_buffered (state : Reader) (byte : Byte) (tail : Bytes)
    (h : state.buffer = byte::tail) (H : Oracle) :
    state.readByte.run H =
      (some (byte,⟨state.prf,tail,by
        have hb := state.bound
        rw [h,List.length_cons] at hb
        omega⟩),[]) := by
  rcases state with ⟨prf,buffer,bound⟩
  change buffer = byte::tail at h
  subst buffer
  rfl

theorem Reader.read_empty (state : Reader) (h : state.buffer = [])
    (next : Word) (hc : nextCounter state.prf.counter = some next) (H : Oracle) :
    state.readByte.run H =
      (some ((H state.prf.input.encode) 0,
        Reader.afterBlock ⟨state.prf.id,state.prf.parent,next⟩ (H state.prf.input.encode)),
        [(state.prf.input.encode,H state.prf.input.encode)]) := by
  rcases state with ⟨prf,buffer,bound⟩
  change buffer = [] at h
  subst buffer
  simp only [Reader.readByte,Tree.run_map,Prf.nextBlock_run prf next hc,Option.map_some]

theorem Reader.read_exhausted (state : Reader) (h : state.buffer = [])
    (hc : nextCounter state.prf.counter = none) (H : Oracle) :
    state.readByte.run H = (none,[]) := by
  rcases state with ⟨prf,buffer,bound⟩
  change buffer = [] at h
  subst buffer
  simp only [Reader.readByte,Tree.run_map,Prf.exhausted prf hc,Option.map_none]

private theorem Reader.readByte_key_and_queries (state : Reader) (H : Oracle) :
    (∀ byte next, (state.readByte.run H).1 = some (byte,next) → next.prf.key = state.prf.key) ∧
    (∀ raw answer, (raw,answer) ∈ (state.readByte.run H).2 →
      ∃ counter, raw = (Input.prf state.prf.key.1 state.prf.key.2 counter).encode) := by
  cases buffer : state.buffer with
  | cons byte tail =>
      rw [Reader.read_buffered state byte tail buffer H]
      constructor
      · intro value next equal
        cases Option.some.inj equal
        rfl
      · intro raw answer member
        cases member
  | nil =>
      cases counter : nextCounter state.prf.counter with
      | none =>
          rw [Reader.read_exhausted state buffer counter H]
          exact ⟨(fun _ _ equal => nomatch equal),(fun _ _ member => nomatch member)⟩
      | some next =>
          rw [Reader.read_empty state buffer next counter H]
          constructor
          · intro value reader equal
            cases Option.some.inj equal
            rfl
          · intro raw answer member
            obtain equal := List.mem_singleton.mp member
            exact ⟨state.prf.counter,(congrArg Prod.fst equal)⟩

/-- Every raw SHA call made while reading a round stays in that round's
PRF stream. This remains true on rejection or counter exhaustion, and for
segmented reads starting with a buffered tail. -/
theorem Reader.read_key_and_queries (count : ℕ) (state : Reader) (H : Oracle) :
    (∀ bytes next, ((Reader.read count state).run H).1 = some (bytes,next) →
      next.prf.key = state.prf.key) ∧
    (∀ raw answer, (raw,answer) ∈ ((Reader.read count state).run H).2 →
      ∃ counter, raw = (Input.prf state.prf.key.1 state.prf.key.2 counter).encode) := by
  induction count generalizing state with
  | zero =>
      constructor
      · intro bytes next equal
        cases Option.some.inj equal
        rfl
      · intro raw answer member
        cases member
  | succ count ih =>
      have step := Reader.readByte_key_and_queries state H
      simp only [Reader.read,Tree.run_bind]
      rcases result : state.readByte.run H with ⟨value,trace⟩
      rw [result] at step
      cases value with
      | none =>
          simp only [Tree.run_done,List.append_nil]
          exact ⟨(fun _ _ equal => nomatch equal),step.2⟩
      | some pair =>
          rcases pair with ⟨byte,next⟩
          have parent := step.1 byte next rfl
          have tail := ih next
          simp only [Tree.run_map]
          constructor
          · intro bytes last equal
            obtain ⟨⟨suffix,reader⟩,found,same⟩ := Option.map_eq_some_iff.mp equal
            cases same
            exact (tail.1 suffix reader found).trans parent
          · intro raw answer member
            rcases List.mem_append.mp member with first | later
            · exact step.2 raw answer first
            · obtain ⟨counter,same⟩ := tail.2 raw answer later
              exact ⟨counter,by simpa only [parent] using same⟩

/-- Segmentation changes neither the returned bytes nor the query trace.
Failure preserves the queries made before the same exhausted counter. -/
theorem Reader.read_add (n m : ℕ) (state : Reader) (H : Oracle) :
    (Reader.read (n+m) state).run H =
      let first := (Reader.read n state).run H
      match first.1 with
      | none => (none,first.2)
      | some (headBytes,next) =>
          let second := (Reader.read m next).run H
          (second.1.map (fun value => (headBytes ++ value.1,value.2)),first.2 ++ second.2) := by
  induction n generalizing state with
  | zero =>
      rw [Nat.zero_add]
      simp only [Reader.read,Tree.run_done]
      rcases (Reader.read m state).run H with ⟨result,trace⟩
      cases result with
      | none => rfl
      | some value => rcases value with ⟨bytes,last⟩; rfl
  | succ n ih =>
      rw [show n+1+m = (n+m)+1 by omega]
      simp only [Reader.read,Tree.run_bind]
      rcases hstep : state.readByte.run H with ⟨value,trace⟩
      cases value with
      | none => simp only [Tree.run_done,List.append_nil]
      | some pair =>
          rcases pair with ⟨byte,next⟩
          simp only [Tree.run_map]
          rw [ih next]
          rcases hfirst : (Reader.read n next).run H with ⟨result,firstTrace⟩
          cases result with
          | none => simp only [Option.map_none]
          | some pair =>
              rcases pair with ⟨headBytes,last⟩
              simp only [Option.map_map,Option.map_some,Function.comp_def,
                List.cons_append,List.append_assoc]

end TranscriptV2.Strand
