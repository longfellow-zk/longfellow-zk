import LfzkV2.Current.ZeroKnowledge.StrandGhostMerkleObserver
import LfzkV2.Current.ZeroKnowledge.StrandCompletion
import LfzkV2.Current.StrandMerkleDomains
import LfzkV2.Current.ZeroKnowledge.StrandReadWindow

/-! Leaf-only programming leaves every numbered strand node and PRF block
unchanged. In particular the normal final seal is computed directly under
the same oracle; no transcript challenge or PRF row is programmed. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.StrandGhostMerkle.Domains
open TranscriptV2
open scoped Classical

variable {k s n t : ℕ} {fields : Fields} {Advice : Type}
variable (P R : Joint.Participant k s n t)
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (binary : fields .binary ≃ P.Carrier) (prime : fields .prime ≃ R.Carrier)
variable (context : Digest) (columnsFit : n ≤ 2^64)

local notation "codec" => MerkleWireCodec.codec P R repr binary prime context columnsFit
local notation "dec" => MerkleWireCodec.decoders P R repr binary prime context columnsFit

theorem input_ne_leaf (input : Strand.Input) (value : MerkleWireCodec.Salt n × (Joint.Pair.family P R).Leaf) :
    input.encode ≠ (codec).leafEnc value :=
  Current.StrandMerkleDomains.input_ne_leaf P R repr binary prime context columnsFit input value

def inputOther (input : Strand.Input) : Observer.Other codec dec :=
  ⟨input.encode,by
    cases found : (dec).leafDec input.encode with
    | none => rfl
    | some value =>
        exact False.elim ((input_ne_leaf P R repr binary prime context columnsFit input value)
          ((dec).leaf_sound _ _ found).symm)⟩

/-- Extend the public non-leaf view with an unused dummy value on leaf
addresses. The prover and final seal read only strand addresses. -/
def extendOther (read : Observer.Other codec dec → Digest) : Strand.Oracle :=
  fun raw => if absent : (dec).leafDec raw = none then read ⟨raw,absent⟩ else 0

theorem extendOther_agree (SHA : Strand.Oracle) (input : Strand.Input) :
    extendOther P R repr binary prime context columnsFit (fun raw => SHA raw.val) input.encode = SHA input.encode := by
  exact dif_pos (inputOther P R repr binary prime context columnsFit input).2

section Congruence
variable {Point Answer : Type} {blocks : ℕ}
variable (history : Point → Strand.History)
variable (sample : Point → Merkle.RandomOracle.Tree Strand.Word Strand.Digest (Option Answer) blocks)
variable (fallback : Answer)

/-- Equality on syntactically encoded strand queries suffices. No full
oracle equality, hash collision assumption, or chronological freshness is
needed to preserve every ordinary logical challenge. -/
theorem oracle_congr (H G : Strand.Oracle)
    (agree : ∀ input : Strand.Input, H input.encode = G input.encode) :
    StrandVerifier.oracle history sample fallback H = StrandVerifier.oracle history sample fallback G := by
  funext point
  unfold StrandVerifier.oracle
  apply congrArg Prod.fst
  apply Merkle.RandomOracle.Tree.run_congr_on_trace
  intro entry member
  rcases StrandVerifier.readRound_queries history sample fallback G point entry.1 entry.2 member with node | stream
  · rw [node,agree]
    exact (congrArg G node).symm.trans
      (Merkle.RandomOracle.Tree.trace_sound _ _ entry member).symm
  · obtain ⟨counter,equal⟩ := stream
    rw [equal,agree]
    exact (congrArg G equal).symm.trans
      (Merkle.RandomOracle.Tree.trace_sound _ _ entry member).symm

end Congruence

section Finish
variable {g : Geometry} {fs : Fields} {A Auth Key Answer : Type} {capacity blocks : ℕ}
variable (bodyCodec : PrefixCodec (Body g fs A Auth))
variable (encoding : ProofBodyReplay.BodyEncoding (g := g) (fields := fs) (Advice := A)
  (Authentication := Auth) (Context := Key)
  (Block := QueryRuntime.Block capacity (ProtocolWrites.Fresh g fs A)) (C := Answer))
variable (sample : Replay.Point g fs A Auth Key
  (QueryRuntime.Block capacity (ProtocolWrites.Fresh g fs A)) →
    Merkle.RandomOracle.Tree Strand.Word Strand.Digest (Option Answer) blocks)
variable (fallback : Answer) (initial : Digest)

theorem finish_congr_reads (body : Body g fs A Auth) (H G : Strand.Oracle)
    (agree : StrandReadWindow.Agree
      (Point := Replay.Point g fs A Auth Key (QueryRuntime.Block capacity (ProtocolWrites.Fresh g fs A)))
      (StrandRuntime.history bodyCodec) H G) :
    StrandCompletion.finish bodyCodec encoding sample fallback initial body H =
      StrandCompletion.finish bodyCodec encoding sample fallback initial body G := by
  have logical := StrandReadWindow.Agree.oracle _ sample fallback agree
  simp only [StrandCompletion.finish,logical]
  rw [agree.node,agree.prf]

theorem finish_congr (body : Body g fs A Auth) (H G : Strand.Oracle)
    (agree : ∀ input : Strand.Input, H input.encode = G input.encode) :
    StrandCompletion.finish bodyCodec encoding sample fallback initial body H =
      StrandCompletion.finish bodyCodec encoding sample fallback initial body G := by
  exact finish_congr_reads bodyCodec encoding sample fallback initial body H G
    (StrandReadWindow.Agree.of_inputs _ H G agree)

end Finish
end LfzkV2.Current.ZeroKnowledge.StrandGhostMerkle.Domains
