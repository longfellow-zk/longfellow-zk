import TranscriptV2.StrandSealCharging
import TranscriptV2.StrandUnfolding
import TranscriptV2.Recompute

/-! Raw SHA replay of a logical verifier. Each round first hashes its node,
then runs its whole sampler against that node's counter stream. The sampler
may reject; this module records that result rather than assuming that a
finite SHA stream is an exactly uniform field element. Finalization binds
the final node and uses PRF counter zero as the received seal's check. -/
namespace TranscriptV2.StrandVerifier
open Framing Strand Merkle.RandomOracle

variable {P C Out : Type} {rounds blocks : ℕ}

/-- A sampler can request counter blocks only from its own round. The
query tree retains all such requests, including rejected draws. -/
def stream {Value : Type} (id : Word) (parent : Digest) :
    {fuel : ℕ} → Tree Word Digest Value fuel → Tree Bytes Digest Value fuel :=
  mapQueries (fun counter => (Input.prf id parent counter).encode)

theorem stream_run {Value : Type} (id : Word) (parent : Digest) (program : Tree Word Digest Value blocks)
    (G : Strand.Oracle) :
    (stream id parent program).run G =
      let result := program.run (fun counter => G (Input.prf id parent counter).encode)
      (result.1,result.2.map fun qa => ((Input.prf id parent qa.1).encode,qa.2)) := by
  exact run_mapQueries _ program G

variable (history : P → History) (sample : P → Tree Word Digest (Option C) blocks) (fallback : C)

/-- A failed sampler returns a dummy value solely to finish mathematical
replay. Acceptance separately requires `sampled` at every ordinary round. -/
def readRound (point : P) : Tree Bytes Digest (Digest × C) (blocks+1) :=
  .query (history point).input.encode fun digest =>
    (stream (history point).id digest (sample point)).map fun value => (digest,value.getD fallback)

def oracle (G : Strand.Oracle) (point : P) : Digest × C :=
  ((readRound history sample fallback point).run G).1

def sampled (G : Strand.Oracle) (point : P) : Prop :=
  ((sample point).run (fun counter => G (Input.prf (history point).id (G (history point).input.encode) counter).encode)).1.isSome

theorem oracle_node (G : Strand.Oracle) (point : P) :
    (oracle history sample fallback G point).1 = G (history point).input.encode := by
  simp only [oracle,readRound,Tree.run_query,Tree.run_map]

theorem oracle_challenge (G : Strand.Oracle) (point : P) :
    (oracle history sample fallback G point).2 =
      ((sample point).run (fun counter => G (Input.prf (history point).id
        (G (history point).input.encode) counter).encode)).1.getD fallback := by
  simp only [oracle,readRound,Tree.run_query,Tree.run_map,stream_run]

theorem readRound_queries (G : Strand.Oracle) (point : P) (raw : Bytes) (answer : Digest)
    (member : (raw,answer) ∈ ((readRound history sample fallback point).run G).2) :
    raw = (history point).input.encode ∨
      ∃ counter, raw = (Input.prf (history point).id (G (history point).input.encode) counter).encode := by
  simp only [readRound,Tree.run_query,Tree.run_map,stream_run] at member
  rcases List.mem_cons.mp member with first | later
  · exact Or.inl (congrArg Prod.fst first)
  · obtain ⟨⟨counter,value⟩,_,equal⟩ := List.mem_map.mp later
    exact Or.inr ⟨counter,(congrArg Prod.fst equal).symm⟩

variable (model : Chain P Digest C Out rounds)

/-- Reuse the existing verifier's state transitions, replacing each
logical boundary by its node hash and actual counter-block queries. -/
def replay (out : Out) : Tree Bytes Digest (Out × model.State) ((blocks+1)*rounds) :=
  expandQueries (readRound history sample fallback) (model.recompute out)

theorem replay_result (out : Out) (G : Strand.Oracle) :
    ((replay history sample fallback model out).run G).1 =
      (out,model.replay out (oracle history sample fallback G) rounds) := by
  rw [replay,expandQueries_run]
  exact model.recompute_result out (oracle history sample fallback G)

/-- Every PRF call in replay belongs to an ordinary round that the logical
verifier actually reaches. In particular no sampler can query a future
round's stream merely by passing an arbitrary digest to this model. -/
theorem replay_queries (out : Out) (G : Strand.Oracle) (raw : Bytes) (answer : Digest)
    (member : (raw,answer) ∈ ((replay history sample fallback model out).run G).2) :
    ∃ i : Fin rounds, raw = (history (model.point out (oracle history sample fallback G) i.val)).input.encode ∨
      ∃ counter, raw = (Input.prf (history (model.point out (oracle history sample fallback G) i.val)).id (G (history (model.point out (oracle history sample fallback G) i.val)).input.encode) counter).encode := by
  rw [replay,expandQueries_run] at member
  obtain ⟨qa,queried,member⟩ := List.mem_flatMap.mp member
  rw [model.recompute_trace] at queried
  obtain ⟨i,equal⟩ := List.mem_ofFn.mp queried
  subst qa
  exact ⟨i,readRound_queries history sample fallback G _ raw answer member⟩

theorem replay_node_visible (out : Out) (G : Strand.Oracle) (i : Fin rounds) :
    ((history (model.point out (oracle history sample fallback G) i.val)).input.encode,
      G (history (model.point out (oracle history sample fallback G) i.val)).input.encode) ∈
        ((replay history sample fallback model out).run G).2 := by
  rw [replay,expandQueries_run]
  apply List.mem_flatMap.mpr
  refine ⟨(model.point out (oracle history sample fallback G) i.val,
    oracle history sample fallback G (model.point out (oracle history sample fallback G) i.val)),?_,?_⟩
  · rw [model.recompute_trace]
    exact List.mem_ofFn.mpr ⟨i,rfl⟩
  · exact List.mem_cons_self

/-- The verifier reconstructs the final state itself. The final-node read
is retained before checking the received seal; it does not add a round. -/
def beforeSeal (out : Out) : Tree Bytes Digest (Out × model.State) (1+(blocks+1)*rounds) :=
  (replay history sample fallback model out).bind fun result =>
    .query (history (model.input result.2)).input.encode fun _ => .done result

theorem beforeSeal_result (out : Out) (G : Strand.Oracle) :
    ((beforeSeal history sample fallback model out).run G).1 =
      (out,model.replay out (oracle history sample fallback G) rounds) := by
  rw [beforeSeal,Tree.run_bind,Tree.run_query,Tree.run_done,replay_result]

theorem beforeSeal_queries (out : Out) (G : Strand.Oracle) (raw : Bytes) (answer : Digest)
    (member : (raw,answer) ∈ ((beforeSeal history sample fallback model out).run G).2) :
    raw = (history (model.finalSealPoint out (oracle history sample fallback G))).input.encode ∨
      ∃ i : Fin rounds, raw = (history (model.point out (oracle history sample fallback G) i.val)).input.encode ∨
        ∃ counter, raw = (Input.prf (history (model.point out (oracle history sample fallback G) i.val)).id (G (history (model.point out (oracle history sample fallback G) i.val)).input.encode) counter).encode := by
  rw [beforeSeal,Tree.run_bind,Tree.run_query,Tree.run_done] at member
  rcases List.mem_append.mp member with earlier | last
  · exact Or.inr (replay_queries history sample fallback model out G raw answer earlier)
  · have equal := congrArg Prod.fst (List.mem_singleton.mp last)
    rw [replay_result] at equal
    exact Or.inl equal

/-- Every node used by the history proof is among the verifier's actual
raw calls, including the final node. Collision scope can therefore be the
queried set rather than all possible SHA inputs. -/
theorem beforeSeal_nodes_visible (out : Out) (G : Strand.Oracle) (i : Fin (rounds+1)) :
    (history (model.point out (oracle history sample fallback G) i.val)).input.encode ∈
      seen (beforeSeal history sample fallback model out) G := by
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  refine ⟨(_,G (history (model.point out (oracle history sample fallback G) i.val)).input.encode),?_,rfl⟩
  rw [beforeSeal,Tree.run_bind,Tree.run_query,Tree.run_done]
  by_cases earlier : i.val < rounds
  · exact List.mem_append_left _ (replay_node_visible history sample fallback model out G ⟨i.val,earlier⟩)
  · have last : i.val = rounds := by have := i.isLt; omega
    rw [last,replay_result]
    exact List.mem_append_right _ List.mem_cons_self

/-- Only boundary nodes enter the shared node/Merkle collision allowance.
Sampler blocks, including rejected draws, are in the disjoint PRF domain.
The bound therefore does not depend on the sampler's raw query cutoff. -/
theorem beforeSeal_nonPrf_card (out : Out) (G : Strand.Oracle) :
    ((seen (beforeSeal history sample fallback model out) G).filter
      (fun raw => decodePrf raw = none)).card ≤ rounds+1 := by
  classical
  let node := fun i : Fin (rounds+1) =>
    (history (model.point out (oracle history sample fallback G) i.val)).input.encode
  have subset : (seen (beforeSeal history sample fallback model out) G).filter
      (fun raw => decodePrf raw = none) ⊆ Finset.univ.image node := by
    intro raw member
    obtain ⟨queried,nonPrf⟩ := Finset.mem_filter.mp member
    obtain ⟨⟨point,answer⟩,member,equal⟩ := List.mem_map.mp (List.mem_toFinset.mp queried)
    change point = raw at equal
    subst point
    rcases beforeSeal_queries history sample fallback model out G raw answer member with final | earlier
    · exact Finset.mem_image.mpr ⟨Fin.last rounds,Finset.mem_univ _,final.symm⟩
    · obtain ⟨i,current | ⟨counter,prf⟩⟩ := earlier
      · exact Finset.mem_image.mpr ⟨i.castSucc,Finset.mem_univ _,current.symm⟩
      · rw [prf,decodePrf_input] at nonPrf
        contradiction
  exact (Finset.card_le_card subset).trans
    ((Finset.card_image_le).trans_eq (by simp only [Finset.card_univ,Fintype.card_fin]))

def sealModel : StrandSealCharging.Model Bytes Digest (Out × model.State) where
  node result := (history (model.input result.2)).input.encode
  prf result digest := (Input.prf (history (model.input result.2)).id digest 0).encode
  provided result := model.finalSeal result.1
  domains result digest := (history (model.input result.2)).input_ne_prf _ digest 0

/-- The prefix computation cannot pay for its own final-seal query.
Distinct strand ids suffice even when the reached node digests collide. -/
theorem seal_fresh (out : Out) (G : Strand.Oracle)
    (distinct : ∀ i : Fin rounds,
      (history (model.point out (oracle history sample fallback G) i.val)).id ≠
        (history (model.finalSealPoint out (oracle history sample fallback G))).id) :
    (sealModel history model).point ((beforeSeal history sample fallback model out).run G).1 G ∉
      seen (beforeSeal history sample fallback model out) G := by
  rw [beforeSeal_result]
  intro member
  obtain ⟨⟨raw,answer⟩,queried,equal⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
  change raw = (sealModel history model).point (out,model.replay out (oracle history sample fallback G) rounds) G at equal
  subst raw
  rcases beforeSeal_queries history sample fallback model out G _ answer queried with final | earlier
  · exact (history (model.finalSealPoint out (oracle history sample fallback G))).input_ne_prf _ _ _ final.symm
  · obtain ⟨i,node | ⟨counter,prf⟩⟩ := earlier
    · exact (history (model.point out (oracle history sample fallback G) i.val)).input_ne_prf _ _ _ node.symm
    · have same := Input.prf.inj (Input.encode_injective (a := .prf _ _ _) (b := .prf _ _ _) trivial trivial prf)
      exact distinct i same.1.symm

/-- Arithmetic checking can use the original logical replay. The seal is
checked against the actual SHA PRF answer, not against the final node hash. -/
def sealValid (out : Out) (G : Strand.Oracle) : Prop :=
  let final := ((beforeSeal history sample fallback model out).run G).1
  G ((sealModel history model).point final G) = model.finalSeal out

theorem sealValid_iff (out : Out) (G : Strand.Oracle) :
    sealValid history sample fallback model out G ↔
      G (Input.prf (history (model.finalSealPoint out (oracle history sample fallback G))).id (G (history (model.finalSealPoint out (oracle history sample fallback G))).input.encode) 0).encode =
        model.finalSeal out := by
  rw [sealValid,beforeSeal_result]
  rfl

end TranscriptV2.StrandVerifier
