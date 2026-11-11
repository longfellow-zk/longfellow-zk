import TranscriptV2.Strands

/-! Small regressions for the SHA-256 strand syntax and its actual query
schedule. Cryptographic assertions use an arbitrary oracle, never a native
SHA implementation hidden behind a proof shortcut. -/
namespace TranscriptV2.Tests.Strand
open Framing TranscriptV2.Strand Merkle.RandomOracle

example : (Input.root []).encode = [1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] := rfl

example (id : Word) (parent : Digest) (counter : Word) :
    (Input.prf id parent counter).encode.length = 52 := Input.prf_length id parent counter

example (id : Word) (parent : Digest) (message : Bytes) :
    (Input.node id [parent] message).encode.length = 48+message.length := by
  simpa only [List.length_cons,List.length_nil] using Input.node_length id [parent] message

example (state : Absorbing) (first second : Bytes) :
    ((state.write first).write second).input.encode = state.input.encode ++ (first ++ second) := by
  rw [Absorbing.write_append,Absorbing.write_input]

example (id : Word) (parent : Digest) :
    (continuation id parent).input = .node id [parent] [] := rfl

example (state : Absorbing) (next : Word) (within : nextCounter state.id = some next) (H : Oracle) :
    ((continueStrand state).run H).1.map (fun pair => pair.1.counter) = some 0 := by
  rw [continueStrand_run state next within H]
  rfl

-- Position separation survives equal digests and equal payloads.
example (first second : Word) (parent : Digest) (message : Bytes) (different : first ≠ second) :
    (Input.node first [parent] message).encode ≠ (Input.node second [parent] message).encode :=
  Input.encode_ne_of_id_ne (Absorbing.valid (.node first parent message))
    (Absorbing.valid (.node second parent message)) different

example (first second : Word) (parent : Digest) (counter : Word) (different : first ≠ second) :
    (Input.prf first parent counter).encode ≠ (Input.prf second parent counter).encode :=
  Input.encode_ne_of_id_ne trivial trivial different

example (id : Word) (parent : Digest) (H : Oracle) :
    (Prf.nextBlock ⟨id,parent,0⟩).run H =
      (some (H (Input.prf id parent 0).encode,⟨id,parent,1⟩),
        [((Input.prf id parent 0).encode,H (Input.prf id parent 0).encode)]) :=
  Prf.nextBlock_run ⟨id,parent,0⟩ 1 (by change nextCounter (0 : Word) = some 1; decide) H

example (id : Word) (parent : Digest) (H : Oracle) :
    (Prf.nextBlock ⟨id,parent,⟨2^64-1,by decide⟩⟩).run H = (none,[]) :=
  Prf.exhausted _ (by change nextCounter ⟨2^64-1,by decide⟩ = none; decide) H

example (parent : Digest) (H : Oracle) :
    (continueStrand (.node ⟨2^64-1,by decide⟩ parent [])).run H = (none,[]) :=
  continueStrand_exhausted _ (by change nextCounter ⟨2^64-1,by decide⟩ = none; decide) H

example (reader : Reader) (H : Oracle) :
    (Reader.read 0 reader).run H = (some ([],reader),[]) := Reader.read_zero reader H

-- Large and segmented reads obey the same theorem as reads within one block.
example (reader : Reader) (H : Oracle) :
    (Reader.read 4096 reader).run H =
      let first := (Reader.read 17 reader).run H
      match first.1 with
      | none => (none,first.2)
      | some (headBytes,next) =>
          let second := (Reader.read 4079 next).run H
          (second.1.map (fun value => (headBytes ++ value.1,value.2)),first.2 ++ second.2) :=
  Reader.read_add 17 4079 reader H

example (state : Absorbing) (label : Byte) (next : Word)
    (within : nextCounter state.id = some next) (H : Oracle) :
    ((StrandTranscript.beginSqueeze state label).run H).1.map (fun reading => reading.reader.prf.counter) = some 0 := by
  rw [StrandTranscript.beginSqueeze_run state label next within H]
  rfl

example (state : Absorbing) (body : Bytes) (H : Oracle) :
    ((StrandTranscript.finalSeal state body).run H).2.length = 2 := by
  rw [StrandTranscript.finalSeal_run]
  rfl

example (state : Absorbing) {first second : Bytes} (h : first ≠ second) :
    StrandTranscript.finalNodeInput state first ≠ StrandTranscript.finalNodeInput state second :=
  fun heq => h (StrandTranscript.finalNodeInput_injective state heq)

example (state : Absorbing) (body : Bytes) (wrong : Digest) (H : Oracle)
    (h : H (StrandTranscript.finalSealInput state body H) ≠ wrong) :
    ¬StrandTranscript.verifyFinalSeal id state ⟨body,wrong⟩ H := by
  rwa [StrandTranscript.verifyFinalSeal_iff]

example (state : Absorbing) (body : Bytes) (H : Oracle) :
    StrandTranscript.checkEncodedSeal state
      (StrandTranscript.encodeComplete id ((StrandTranscript.complete id state body).run H).1) H := by
  rw [StrandTranscript.checkEncodedSeal_iff]
  exact StrandTranscript.verifyFinalSeal_complete id state body H

-- Splitting the one SHA function introduces no extra oracle or consistency premise.
example (H : Bytes → Digest) : assembleOracle (splitOracle H) = H := assemble_split H

example {Out : Type} {fuel : ℕ} (tree : Tree Bytes Digest Out fuel) (H : Bytes → Digest) :
    ((bundle tree).run (groupedOracle (splitOracle H))).1 = (tree.run H).1 :=
  bundle_run_sha tree H

example (message : Bytes) : unfoldInput [] (.root message) = some (.root message) := rfl

example (id : Word) (parent : Digest) (message : Bytes) : unfoldInput [] (.node id [parent] message) = none := rfl

example (table : List Entry) (raw : Bytes) (history : History)
    (h : unfoldNode table raw = some history) : raw = history.input.encode :=
  unfoldNode_erases table raw history h

end TranscriptV2.Tests.Strand
