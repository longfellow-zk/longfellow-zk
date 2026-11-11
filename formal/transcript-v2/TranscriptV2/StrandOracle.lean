import TranscriptV2.StrandEncoding
import TranscriptV2.Queries

/-! The SHA oracle splits into PRF blocks and all other inputs by an exact
bijection. Bundling a parent's counter blocks reveals extra information to a
search, but does not change any of the raw SHA answers it actually uses.
These are deterministic transport results; the distributional coupling to
the complete protocol is a separate obligation. -/
namespace TranscriptV2.Strand
open Framing Merkle.RandomOracle

abbrev PrfKey := Word × Digest
abbrev PrfPoint := PrfKey × Word

def decodePrf (raw : Bytes) : Option PrfPoint :=
  match Input.decode raw with
  | some (.prf id parent counter) => some ((id,parent),counter)
  | _ => none

@[simp] theorem decodePrf_encode (parent : PrfKey) (counter : Word) :
    decodePrf (Input.prf parent.1 parent.2 counter).encode = some (parent,counter) := by
  simp only [decodePrf,Input.decode_encode (.prf parent.1 parent.2 counter) trivial]

@[simp] theorem decodePrf_input (id : Word) (parent : Digest) (counter : Word) :
    decodePrf (Input.prf id parent counter).encode = some ((id,parent),counter) :=
  decodePrf_encode (id,parent) counter

theorem decodePrf_sound (raw : Bytes) (point : PrfPoint)
    (h : decodePrf raw = some point) : raw = (Input.prf point.1.1 point.1.2 point.2).encode := by
  unfold decodePrf at h
  split at h
  next id parent counter hd =>
    cases Option.some.inj h
    exact (Input.decode_sound raw (.prf id parent counter) hd).2
  next hnone => contradiction

abbrev OtherPoint := {raw : Bytes // decodePrf raw = none}
abbrev PrfOracle := PrfKey → Word → Digest
abbrev OtherOracle := OtherPoint → Digest

/-- The row reserved by a node query includes its public position. Malformed
non-PRF inputs are assigned position zero only for the sampling coupling;
that choice never changes the underlying raw oracle answers. -/
def nodeKey (raw : Bytes) (digest : Digest) : PrfKey :=
  (((Input.decode raw).map Input.id).getD 0,digest)

@[simp] theorem nodeKey_encode (input : Input) (valid : input.Valid) (digest : Digest) :
    nodeKey input.encode digest = (input.id,digest) := by
  simp only [nodeKey,Input.decode_encode input valid,Option.map_some,Option.getD_some]

/-- Partition actual SHA inputs. The complement retains every non-PRF
input, including malformed nodes and other protocol domains. This is a
bijection of addresses, so it adds no oracle or independence assumption. -/
def rawPoint (raw : Bytes) : Sum OtherPoint PrfPoint :=
  match h : decodePrf raw with
  | some point => .inr point
  | none => .inl ⟨raw,h⟩

def rawBytes : Sum OtherPoint PrfPoint → Bytes
  | .inl point => point.val
  | .inr (parent,counter) => (Input.prf parent.1 parent.2 counter).encode

@[simp] theorem rawBytes_point (raw : Bytes) : rawBytes (rawPoint raw) = raw := by
  unfold rawPoint
  split
  next point found => exact (decodePrf_sound raw point found).symm
  next => rfl

@[simp] theorem rawPoint_bytes (point : Sum OtherPoint PrfPoint) : rawPoint (rawBytes point) = point := by
  cases point with
  | inl point =>
      unfold rawBytes rawPoint
      split
      next address found =>
        have impossible := found.symm.trans point.property
        contradiction
      next => rfl
  | inr point =>
      unfold rawBytes rawPoint
      split
      next address found =>
        exact congrArg Sum.inr (Option.some.inj (found.symm.trans (decodePrf_encode point.1 point.2)))
      next found =>
        have impossible := found.symm.trans (decodePrf_encode point.1 point.2)
        contradiction

def rawPointEquiv : Bytes ≃ Sum OtherPoint PrfPoint where
  toFun := rawPoint
  invFun := rawBytes
  left_inv := rawBytes_point
  right_inv := rawPoint_bytes

/-- Splitting the byte-address space preserves every raw answer and the
ordered trace, including queries unrelated to transcript nodes. -/
theorem run_rawPoint {Out : Type} {fuel : ℕ} (program : Tree Bytes Digest Out fuel)
    (SHA : Bytes → Digest) :
    (mapQueries rawPoint program).run (SHA ∘ rawBytes) =
      ((program.run SHA).1,(program.run SHA).2.map fun qa => (rawPoint qa.1,qa.2)) := by
  have same : (SHA ∘ rawBytes) ∘ rawPoint = SHA := by
    funext raw
    simp only [Function.comp_apply,rawBytes_point]
  simp only [run_mapQueries,same]

theorem seen_rawPoint [DecidableEq OtherPoint] {Out : Type} {fuel : ℕ} (program : Tree Bytes Digest Out fuel)
    (SHA : Bytes → Digest) (raw : Bytes) :
    rawPoint raw ∈ seen (mapQueries rawPoint program) (SHA ∘ rawBytes) ↔ raw ∈ seen program SHA := by
  simp only [seen,Bcs.TotalOracle.queried,run_rawPoint,List.mem_toFinset,List.mem_map]
  constructor
  · rintro ⟨_,⟨qa,member,rfl⟩,equal⟩
    exact ⟨qa,member,rawPointEquiv.injective equal⟩
  · rintro ⟨qa,member,equal⟩
    exact ⟨(rawPoint qa.1,qa.2),⟨qa,member,rfl⟩,congrArg rawPoint equal⟩

/-- No SHA answer is discarded: the complement contains arbitrary raw
inputs, including every strand node. Other protocol SHA domains remain
subject to their own explicit domain-separation checks. -/
def splitOracle (H : Bytes → Digest) : PrfOracle × OtherOracle :=
  (fun parent counter => H (Input.prf parent.1 parent.2 counter).encode,fun raw => H raw.val)

def assembleOracle (oracles : PrfOracle × OtherOracle) (raw : Bytes) : Digest :=
  match h : decodePrf raw with
  | some (parent,counter) => oracles.1 parent counter
  | none => oracles.2 ⟨raw,h⟩

@[simp] theorem assemble_prf (oracles : PrfOracle × OtherOracle)
    (parent : PrfKey) (counter : Word) :
    assembleOracle oracles (Input.prf parent.1 parent.2 counter).encode = oracles.1 parent counter := by
  unfold assembleOracle
  split
  next p c h =>
    have heq := Option.some.inj (h.symm.trans (decodePrf_encode parent counter))
    cases heq
    rfl
  next h =>
    have heq := h.symm.trans (decodePrf_encode parent counter)
    contradiction

@[simp] theorem assemble_other (oracles : PrfOracle × OtherOracle) (raw : OtherPoint) :
    assembleOracle oracles raw.val = oracles.2 raw := by
  unfold assembleOracle
  split
  next p c h =>
    have heq := h.symm.trans raw.property
    contradiction
  next h => rfl

@[simp] theorem assemble_split (H : Bytes → Digest) : assembleOracle (splitOracle H) = H := by
  funext raw
  unfold assembleOracle
  split
  next parent counter h =>
    change H (Input.prf parent.1 parent.2 counter).encode = H raw
    rw [← decodePrf_sound raw (parent,counter) h]
  next h => rfl

@[simp] theorem split_assemble (oracles : PrfOracle × OtherOracle) :
    splitOracle (assembleOracle oracles) = oracles := by
  simp only [splitOracle,assemble_prf,assemble_other]

def oracleEquiv : (Bytes → Digest) ≃ (PrfOracle × OtherOracle) where
  toFun := splitOracle
  invFun := assembleOracle
  left_inv := assemble_split
  right_inv := split_assemble

/-- One grouped query returns all counter blocks for that parent. Its
second coordinate is only used at complement inputs. This answer space makes
ordinary query trees sufficient without a dependent-answer tree type. The
unused coordinates below are fixed, not claimed to be uniform coins. -/
abbrev GroupAnswer := (Word → Digest) × Digest
abbrev GroupPoint := Sum PrfKey OtherPoint

def groupedOracle (oracles : PrfOracle × OtherOracle) : GroupPoint → GroupAnswer
  | .inl parent => (oracles.1 parent,fun _ => 0)
  | .inr raw => (fun _ _ => 0,oracles.2 raw)

def groupPoint (raw : Bytes) : GroupPoint :=
  match h : decodePrf raw with
  | some (parent,_) => .inl parent
  | none => .inr ⟨raw,h⟩

@[simp] theorem groupPoint_prf (parent : PrfKey) (counter : Word) :
    groupPoint (Input.prf parent.1 parent.2 counter).encode = .inl parent := by
  unfold groupPoint
  split
  next p c h =>
    have heq := Option.some.inj (h.symm.trans (decodePrf_encode parent counter))
    cases heq
    rfl
  next h =>
    have heq := h.symm.trans (decodePrf_encode parent counter)
    contradiction

@[simp] theorem groupPoint_other (raw : OtherPoint) : groupPoint raw.val = .inr raw := by
  unfold groupPoint
  split
  next p c h =>
    have heq := h.symm.trans raw.property
    contradiction
  next h => rfl

def projectAnswer (raw : Bytes) (answer : GroupAnswer) : Digest :=
  match decodePrf raw with
  | some (_,counter) => answer.1 counter
  | none => answer.2

@[simp] theorem project_grouped (oracles : PrfOracle × OtherOracle) (raw : Bytes) :
    projectAnswer raw (groupedOracle oracles (groupPoint raw)) = assembleOracle oracles raw := by
  cases h : decodePrf raw with
  | some pair =>
      rcases pair with ⟨parent,counter⟩
      rw [decodePrf_sound raw (parent,counter) h,groupPoint_prf,assemble_prf]
      simp only [projectAnswer,decodePrf_encode,groupedOracle]
  | none =>
      let point : OtherPoint := ⟨raw,h⟩
      change projectAnswer point.val (groupedOracle oracles (groupPoint point.val)) =
        assembleOracle oracles point.val
      rw [groupPoint_other,assemble_other]
      simp only [projectAnswer,point,h,groupedOracle]

/-- Compile an arbitrary raw-query program, not just an honest prover.
The grouped search may see complete PRF streams; it returns the same result
when it uses only the particular coordinates requested by the original. -/
def bundle {Out : Type} : {fuel : ℕ} → Tree Bytes Digest Out fuel →
    Tree GroupPoint GroupAnswer Out fuel
  | _, .done out => .done out
  | _, .query raw next => .query (groupPoint raw) fun answer =>
      bundle (next (projectAnswer raw answer))

def ungroupOracle (H : GroupPoint → GroupAnswer) (raw : Bytes) : Digest :=
  projectAnswer raw (H (groupPoint raw))

theorem bundle_run_project {Out : Type} {fuel : ℕ} (tree : Tree Bytes Digest Out fuel)
    (H : GroupPoint → GroupAnswer) :
    ((bundle tree).run H).1 = (tree.run (ungroupOracle H)).1 ∧
    ((bundle tree).run H).2.map Prod.fst =
      (tree.run (ungroupOracle H)).2.map (fun qa => groupPoint qa.1) := by
  induction tree with
  | done _ => exact ⟨rfl,rfl⟩
  | query raw next ih =>
      simp only [bundle,Tree.run_query,ungroupOracle,List.map_cons]
      exact ⟨(ih _).1,congrArg (List.cons (groupPoint raw)) (ih _).2⟩

/-- Grouping does not increase the distinct-query budget, even if the search
asks counter blocks out of order or repeats a block. -/
theorem bundle_seen_card_le {Out : Type} {fuel : ℕ} (tree : Tree Bytes Digest Out fuel)
    (H : GroupPoint → GroupAnswer) :
    (seen (bundle tree) H).card ≤ (seen tree (ungroupOracle H)).card := by
  classical
  have heq : seen (bundle tree) H = (seen tree (ungroupOracle H)).image groupPoint := by
    unfold seen Bcs.TotalOracle.queried
    rw [(bundle_run_project tree H).2]
    ext point
    simp
  rw [heq]
  exact Finset.card_image_le

theorem bundle_run {Out : Type} {fuel : ℕ} (tree : Tree Bytes Digest Out fuel)
    (oracles : PrfOracle × OtherOracle) :
    ((bundle tree).run (groupedOracle oracles)).1 = (tree.run (assembleOracle oracles)).1 ∧
    ((bundle tree).run (groupedOracle oracles)).2.map Prod.fst =
      (tree.run (assembleOracle oracles)).2.map (fun qa => groupPoint qa.1) := by
  have h : ungroupOracle (groupedOracle oracles) = assembleOracle oracles :=
    funext (project_grouped oracles)
  simpa only [h] using bundle_run_project tree (groupedOracle oracles)

theorem bundle_run_sha {Out : Type} {fuel : ℕ} (tree : Tree Bytes Digest Out fuel)
    (H : Bytes → Digest) :
    ((bundle tree).run (groupedOracle (splitOracle H))).1 = (tree.run H).1 := by
  simpa only [assemble_split] using (bundle_run tree (splitOracle H)).1

/-! The following finite marginal includes every possible PRF counter input
and any fixed finite set of complement inputs. Its SHA coordinates have an
injective raw encoding. Thus the product law here comes from a bijection of
uniform tables, not an assumption that an extra oracle is independent. -/
noncomputable section
open Finset
open scoped Classical

abbrev WindowPoint (other : Finset OtherPoint) :=
  Sum PrfPoint {raw : OtherPoint // raw ∈ other}

def windowEncode {other : Finset OtherPoint} : WindowPoint other → Bytes
  | .inl (parent,counter) => (Input.prf parent.1 parent.2 counter).encode
  | .inr raw => raw.val.val

theorem windowEncode_injective (other : Finset OtherPoint) :
    Function.Injective (windowEncode (other := other)) := by
  intro first second h
  cases first with
  | inl a =>
      cases second with
      | inl b =>
          have heq := Input.encode_injective (a := .prf a.1.1 a.1.2 a.2)
            (b := .prf b.1.1 b.1.2 b.2) trivial trivial h
          have hh := Input.prf.inj heq
          exact congrArg Sum.inl (Prod.ext (Prod.ext hh.1 hh.2.1) hh.2.2)
      | inr b =>
          have hd := congrArg decodePrf h
          simp only [windowEncode,decodePrf_encode,b.val.property] at hd
          contradiction
  | inr a =>
      cases second with
      | inl b =>
          have hd := congrArg decodePrf h
          simp only [windowEncode,decodePrf_encode,a.val.property] at hd
          contradiction
      | inr b =>
          exact congrArg Sum.inr (Subtype.ext (Subtype.ext h))

def windowEquiv (other : Finset OtherPoint) :
    (WindowPoint other → Digest) ≃
      PrfOracle × ({raw : OtherPoint // raw ∈ other} → Digest) where
  toFun H := (fun parent counter => H (.inl (parent,counter)),fun raw => H (.inr raw))
  invFun pair raw := match raw with
    | .inl (parent,counter) => pair.1 parent counter
    | .inr raw => pair.2 raw
  left_inv H := by funext raw; cases raw with
    | inl pair => rcases pair with ⟨parent,counter⟩; rfl
    | inr raw => rfl
  right_inv pair := rfl

/-- Uniform raw SHA tables on this marginal are exactly uniform independent
PRF-parent streams and complement tables. No decoding or sampler premise
is used; projecting those streams to field challenges is separate. -/
theorem window_ratio_eq (other : Finset OtherPoint)
    (event : PrfOracle × ({raw : OtherPoint // raw ∈ other} → Digest) → Prop) :
    ((univ.filter fun H => event (windowEquiv other H)).card : ℚ) /
        Fintype.card (WindowPoint other → Digest) =
      ((univ.filter event).card : ℚ) /
        Fintype.card (PrfOracle × ({raw : OtherPoint // raw ∈ other} → Digest)) := by
  have hc : (univ.filter fun H => event (windowEquiv other H)).card =
      (univ.filter event).card := Finset.card_equiv (windowEquiv other) (fun _ => by simp)
  rw [hc,Fintype.card_congr (windowEquiv other)]

end

end TranscriptV2.Strand
