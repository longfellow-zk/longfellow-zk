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

end TranscriptV2.Strand
