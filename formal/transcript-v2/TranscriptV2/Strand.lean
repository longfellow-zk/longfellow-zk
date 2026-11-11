import TranscriptV2.StrandEncoding
import Merkle.TreeCompose

/-! Linear strand transitions as explicit SHA-256 oracle programs. Continuing
starts one node with its parent's id plus one. Overflow fails before querying;
the optional result models Rust's checked-counter failure. Every actual SHA
query occurs in the program's trace. -/
namespace TranscriptV2.Strand
open Framing Merkle.RandomOracle

abbrev Oracle := Bytes → Digest

/-- The Rust counter check happens before issuing a query. -/
def nextCounter (counter : Word) : Option Word :=
  if h : counter.val+1 < 2^64 then some ⟨counter.val+1,h⟩ else none

inductive Absorbing where
  | root (message : Bytes)
  | node (id : Word) (parent : Digest) (message : Bytes)

def Absorbing.id : Absorbing → Word
  | .root _ => 0
  | .node id .. => id

def Absorbing.input : Absorbing → Input
  | .root message => .root message
  | .node id parent message => .node id [parent] message

@[simp] theorem Absorbing.input_id (state : Absorbing) : state.input.id = state.id := by
  cases state <;> rfl

theorem Absorbing.valid (state : Absorbing) : state.input.Valid := by
  cases state with
  | root _ => trivial
  | node id parent message => exact ⟨List.cons_ne_nil _ _,by change 1 < 2^32; decide⟩

def Absorbing.write (state : Absorbing) (message : Bytes) : Absorbing :=
  match state with
  | .root before => .root (before ++ message)
  | .node id parent before => .node id parent (before ++ message)

@[simp] theorem Absorbing.write_id (state : Absorbing) (message : Bytes) :
    (state.write message).id = state.id := by cases state <;> rfl

@[simp] theorem Absorbing.write_append (state : Absorbing) (a b : Bytes) :
    (state.write a).write b = state.write (a ++ b) := by
  cases state <;> simp only [Absorbing.write,List.append_assoc]

theorem Absorbing.write_input (state : Absorbing) (message : Bytes) :
    (state.write message).input.encode = state.input.encode ++ message := by
  cases state <;> simp only [Absorbing.write,Absorbing.input,Input.encode,List.append_assoc]

structure Prf where
  id : Word
  parent : Digest
  counter : Word

def Prf.key (state : Prf) : Word × Digest := (state.id,state.parent)

def endStrand (state : Absorbing) : Tree Bytes Digest Prf 1 :=
  .query state.input.encode fun digest => .done ⟨state.id,digest,0⟩

@[simp] theorem endStrand_run (state : Absorbing) (H : Oracle) :
    (endStrand state).run H =
      (⟨state.id,H state.input.encode,0⟩,[(state.input.encode,H state.input.encode)]) := rfl

def continuation (id : Word) (parent : Digest) : Absorbing := .node id parent []

def continueStrand (state : Absorbing) : Tree Bytes Digest (Option (Prf × Absorbing)) 1 :=
  match nextCounter state.id with
  | none => .done none
  | some id => (endStrand state).map fun prf => some (prf,continuation id prf.parent)

@[simp] theorem continueStrand_run (state : Absorbing) (id : Word)
    (next : nextCounter state.id = some id) (H : Oracle) :
    (continueStrand state).run H =
      (some (⟨state.id,H state.input.encode,0⟩,continuation id (H state.input.encode)),
        [(state.input.encode,H state.input.encode)]) := by
  simp only [continueStrand,next,Tree.run_map,endStrand_run]

theorem continueStrand_exhausted (state : Absorbing)
    (exhausted : nextCounter state.id = none) (H : Oracle) :
    (continueStrand state).run H = (none,[]) := by
  simp only [continueStrand,exhausted,Tree.run_done]

def Prf.input (state : Prf) : Input := .prf state.id state.parent state.counter

def Prf.nextBlock (state : Prf) : Tree Bytes Digest (Option (Digest × Prf)) 1 :=
  match nextCounter state.counter with
  | none => .done none
  | some next => .query state.input.encode fun digest => .done (some (digest,⟨state.id,state.parent,next⟩))

theorem Prf.nextBlock_run (state : Prf) (next : Word) (h : nextCounter state.counter = some next)
    (H : Oracle) : (state.nextBlock.run H) =
      (some (H state.input.encode,⟨state.id,state.parent,next⟩),[(state.input.encode,H state.input.encode)]) := by
  simp only [Prf.nextBlock,h,Tree.run_query,Tree.run_done]

theorem Prf.exhausted (state : Prf) (h : nextCounter state.counter = none) (H : Oracle) :
    state.nextBlock.run H = (none,[]) := by simp only [Prf.nextBlock,h,Tree.run_done]

end TranscriptV2.Strand
