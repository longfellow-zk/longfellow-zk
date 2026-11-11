import LfzkV2.Current.OracleWindow
import TranscriptV2.StrandVerifier

/-! Finite raw support for a fixed typed protocol. Histories may contain
arbitrary public messages, but the typed point space is finite. All indexed
PRF coordinates are finite as well. Equality on these addresses preserves
the physical readers, including sampler failures and final-seal reads. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.StrandReadWindow
open TranscriptV2 TranscriptV2.Framing TranscriptV2.Strand Merkle.RandomOracle
open scoped Classical

variable {Point Answer : Type} {blocks : ℕ}
variable (history : Point → Strand.History)

structure Agree (first second : Strand.Oracle) : Prop where
  node : ∀ point, first (history point).input.encode = second (history point).input.encode
  prf : ∀ id parent counter,
    first (Strand.Input.prf id parent counter).encode = second (Strand.Input.prf id parent counter).encode

theorem Agree.of_inputs (first second : Strand.Oracle)
    (same : ∀ input : Strand.Input, first input.encode = second input.encode) :
    Agree history first second :=
  ⟨fun point => same (history point).input,fun id parent counter => same (.prf id parent counter)⟩

theorem Agree.stream {first second : Strand.Oracle} (same : Agree history first second) (point : Point) :
    (fun counter => first (Strand.Input.prf (history point).id (first (history point).input.encode) counter).encode) =
      (fun counter => second (Strand.Input.prf (history point).id (second (history point).input.encode) counter).encode) := by
  funext counter
  rw [same.node point,same.prf]

variable (sample : Point → Tree Strand.Word Strand.Digest (Option Answer) blocks) (fallback : Answer)

theorem Agree.oracle {first second : Strand.Oracle} (same : Agree history first second) :
    StrandVerifier.oracle history sample fallback first = StrandVerifier.oracle history sample fallback second := by
  funext point
  simp only [StrandVerifier.oracle,StrandVerifier.readRound,Tree.run_query,Tree.run_map,StrandVerifier.stream_run]
  rw [same.stream,same.node]

theorem Agree.sampled {first second : Strand.Oracle} (same : Agree history first second) (point : Point) :
    StrandVerifier.sampled history sample first point ↔ StrandVerifier.sampled history sample second point := by
  simp only [StrandVerifier.sampled,same.stream]

variable [Fintype Point]

def window : Finset Bytes :=
  (Finset.univ.image fun point => (history point).input.encode) ∪
    (Finset.univ.image fun input : Strand.Word × Strand.Digest × Strand.Word =>
      (Strand.Input.prf input.1 input.2.1 input.2.2).encode)

theorem node_mem (point : Point) : (history point).input.encode ∈ window history :=
  Finset.mem_union_left _ (Finset.mem_image.mpr ⟨point,Finset.mem_univ _,rfl⟩)

theorem prf_mem (id : Strand.Word) (parent : Strand.Digest) (counter : Strand.Word) :
    (Strand.Input.prf id parent counter).encode ∈ window history := by
  unfold window
  apply Finset.mem_union_right
  simp only [Finset.mem_image,Finset.mem_univ,true_and]
  exact ⟨(id,parent,counter),rfl⟩

theorem agree_of_window (first second : Strand.Oracle)
    (same : ∀ raw ∈ window history, first raw = second raw) : Agree history first second :=
  ⟨fun point => same _ (node_mem history point),fun id parent counter => same _ (prf_mem history id parent counter)⟩

theorem reader_queries (SHA : Strand.Oracle) (point : Point) (entry : Bytes × Digest)
    (member : entry ∈ ((StrandVerifier.readRound history sample fallback point).run SHA).2) :
    entry.1 ∈ window history := by
  rcases StrandVerifier.readRound_queries history sample fallback SHA point entry.1 entry.2 member with node | stream
  · rw [node]
    exact node_mem history point
  · obtain ⟨counter,equal⟩ := stream
    rw [equal]
    exact prf_mem history _ _ counter

end LfzkV2.Current.ZeroKnowledge.StrandReadWindow
