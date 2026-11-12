import LfzkV2.Current.ProofBodyReplay

/-! The simulator programs one complete answer at the opening boundary.
Rank separation proves that this operation preserves every earlier input and
answer.  The answer includes its feedback link and every sampler coordinate;
there is no operation for programming only the selected columns.

These are replay and encoding facts, not an indistinguishability claim.
The probability that an outside observer queried this input earlier must be
bounded separately.  Finalization computes the seal on the actual body. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.OracleProgramming

open scoped Classical

section Chain
variable {P Link C Out : Type} {R : ℕ}
variable (chain : TranscriptV2.Chain P Link C Out R)

/-- Replacing the whole oracle answer is essential: links and sampled
challenges belong to the same oracle evaluation. -/
def program (output : Out) (H : P → Link × C) (cut : Fin R) (answer : Link × C) :
    P → Link × C :=
  Function.update H (chain.point output H cut.val) answer

theorem point_ne_before (output : Out) (H : P → Link × C)
    (cut : Fin R) (index : ℕ) (before : index < cut.val) :
    chain.point output H index ≠ chain.point output H cut.val := by
  intro equal
  have hi := chain.point_rank output H (show index ≤ R by omega)
  have hc := chain.point_rank output H (Nat.le_of_lt cut.isLt)
  rw [equal] at hi
  omega

/-- The programmed point is itself unchanged: computing a query input uses
only strict earlier answers. -/
theorem replay_prefix (output : Out) (H : P → Link × C)
    (cut : Fin R) (answer : Link × C) (index : ℕ) (before : index ≤ cut.val) :
    chain.replay output (program chain output H cut answer) index =
      chain.replay output H index := by
  symm
  apply chain.replay_congr_prefix
  intro earlier hearlier
  have hne := point_ne_before chain output H cut earlier (by omega)
  simp only [program, Function.update_of_ne hne]

theorem point_prefix (output : Out) (H : P → Link × C)
    (cut : Fin R) (answer : Link × C) (index : ℕ) (before : index ≤ cut.val) :
    chain.point output (program chain output H cut answer) index =
      chain.point output H index :=
  congrArg chain.input (replay_prefix chain output H cut answer index before)

theorem answer_before (output : Out) (H : P → Link × C)
    (cut : Fin R) (answer : Link × C) (index : ℕ) (before : index < cut.val) :
    program chain output H cut answer
        (chain.point output (program chain output H cut answer) index) =
      H (chain.point output H index) := by
  rw [point_prefix chain output H cut answer index (by omega)]
  exact Function.update_of_ne (point_ne_before chain output H cut index before) _ _

theorem answer_at (output : Out) (H : P → Link × C)
    (cut : Fin R) (answer : Link × C) :
    program chain output H cut answer
      (chain.point output (program chain output H cut answer) cut.val) = answer := by
  rw [point_prefix chain output H cut answer cut.val (le_refl _)]
  exact Function.update_self _ _ _

theorem answer_elsewhere (output : Out) (H : P → Link × C)
    (cut : Fin R) (answer : Link × C) (point : P)
    (different : point ≠ chain.point output H cut.val) :
    program chain output H cut answer point = H point :=
  Function.update_of_ne different _ _

/-- All earlier query results, including repetitions, remain literal oracle
answers rather than a simulator cache with different replay semantics. -/
theorem prior_execution {A : Type} {fuel : ℕ} (output : Out) (H : P → Link × C)
    (cut : Fin R) (answer : Link × C)
    (observer : Merkle.RandomOracle.Tree P (Link × C) A fuel)
    (fresh : ∀ query ∈ (observer.run H).2,
      query.1 ≠ chain.point output H cut.val) :
    observer.run (program chain output H cut answer) = observer.run H := by
  apply Merkle.RandomOracle.Tree.run_congr_on_trace
  intro query member
  rw [answer_elsewhere chain output H cut answer query.1 (fresh query member)]
  exact (Merkle.RandomOracle.Tree.trace_sound observer H query member).symm

end Chain

section Current
variable {g : Geometry} {fields : Fields} {Advice Authentication Context Block C : Type}

/-- Encoding from the public body has no access to the future final seal.
This is a constructor, not a supplied independence or privacy certificate. -/
structure BodyEncoding where
  context : Body g fields Advice Authentication → Context
  block : Body g fields Advice Authentication →
    (i : Fin g.roles.length) → (Fin i.val → C) → Block

def BodyEncoding.encoding (e : BodyEncoding (g := g) (fields := fields)
    (Advice := Advice) (Authentication := Authentication) (Context := Context)
    (Block := Block) (C := C)) : Replay.Encoding g fields Advice Authentication Context Block C where
  context proof := e.context proof.body
  block proof := e.block proof.body

variable (e : BodyEncoding (g := g) (fields := fields) (Advice := Advice)
  (Authentication := Authentication) (Context := Context) (Block := Block) (C := C))

theorem replay_same_body (initial : Digest)
    (first second : Proof g fields Advice Authentication)
    (same : first.body = second.body)
    (H : Replay.Point g fields Advice Authentication Context Block → Digest × C) (index : ℕ) :
    (e.encoding.chain initial).replay first H index =
      (e.encoding.chain initial).replay second H index := by
  rcases first with ⟨body,firstSeal⟩
  rcases second with ⟨otherBody,secondSeal⟩
  cases same
  induction index with
  | zero => rfl
  | succ index ih =>
      by_cases inside : index < g.roles.length
      · simp only [TranscriptV2.Chain.replay, dif_pos inside]
        rw [ih]
        generalize (e.encoding.chain initial).replay ⟨body,secondSeal⟩ H index = state
        rcases state with ⟨point,answers⟩
        cases point <;> rfl
      · simpa only [TranscriptV2.Chain.replay, dif_neg inside] using ih

def finalize (initial : Digest) (body : Body g fields Advice Authentication)
    (H : Replay.Point g fields Advice Authentication Context Block → Digest × C) :
    Proof g fields Advice Authentication :=
  let pending : Proof g fields Advice Authentication := ⟨body,fun _ => 0⟩
  ⟨body,(H ((e.encoding.chain initial).finalSealPoint pending H)).1⟩

@[simp] theorem finalize_body (initial : Digest) (body : Body g fields Advice Authentication)
    (H : Replay.Point g fields Advice Authentication Context Block → Digest × C) :
    (finalize e initial body H).body = body := rfl

/-- Finalization performs an ordinary oracle evaluation after all terminal
authentication is in the body. It does not program or guess the final seal. -/
theorem finalize_correct (initial : Digest) (body : Body g fields Advice Authentication)
    (H : Replay.Point g fields Advice Authentication Context Block → Digest × C) :
    (H ((e.encoding.chain initial).finalSealPoint (finalize e initial body H) H)).1 =
      (finalize e initial body H).finalSeal := by
  have h := replay_same_body e initial (finalize e initial body H)
    (⟨body,fun _ => 0⟩ : Proof g fields Advice Authentication) rfl H g.roles.length
  change (H ((e.encoding.chain initial).input _)).1 = _
  rw [h]
  rfl

/-- The simulator has already constructed the complete body, including the
opening authentication selected by the sampled answer. It programs that one
whole answer, then computes the final seal with an ordinary oracle read. -/
def programAndFinalize (initial : Digest) (body : Body g fields Advice Authentication)
    (H : Replay.Point g fields Advice Authentication Context Block → Digest × C)
    (cut : Fin g.roles.length) (answer : Digest × C) :
    Proof g fields Advice Authentication ×
      (Replay.Point g fields Advice Authentication Context Block → Digest × C) :=
  let pending : Proof g fields Advice Authentication := ⟨body,fun _ => 0⟩
  let oracle := program (e.encoding.chain initial) pending H cut answer
  (finalize e initial body oracle,oracle)

theorem programAndFinalize_answer (initial : Digest) (body : Body g fields Advice Authentication)
    (H : Replay.Point g fields Advice Authentication Context Block → Digest × C)
    (cut : Fin g.roles.length) (answer : Digest × C) :
    let result := programAndFinalize e initial body H cut answer
    result.2 ((e.encoding.chain initial).point result.1 result.2 cut.val) = answer := by
  let pending : Proof g fields Advice Authentication := ⟨body,fun _ => 0⟩
  let oracle := program (e.encoding.chain initial) pending H cut answer
  have same := replay_same_body e initial (finalize e initial body oracle) pending rfl oracle cut.val
  change oracle ((e.encoding.chain initial).input
    ((e.encoding.chain initial).replay (finalize e initial body oracle) oracle cut.val)) = answer
  rw [same]
  exact answer_at (e.encoding.chain initial) pending H cut answer

theorem programAndFinalize_answer_before (initial : Digest) (body : Body g fields Advice Authentication)
    (H : Replay.Point g fields Advice Authentication Context Block → Digest × C)
    (cut : Fin g.roles.length) (answer : Digest × C) (index : ℕ) (before : index < cut.val) :
    let result := programAndFinalize e initial body H cut answer
    result.2 ((e.encoding.chain initial).point result.1 result.2 index) =
      H ((e.encoding.chain initial).point (⟨body,fun _ => 0⟩ : Proof g fields Advice Authentication) H index) := by
  let pending : Proof g fields Advice Authentication := ⟨body,fun _ => 0⟩
  let oracle := program (e.encoding.chain initial) pending H cut answer
  have same := replay_same_body e initial (finalize e initial body oracle) pending rfl oracle index
  change oracle ((e.encoding.chain initial).input
    ((e.encoding.chain initial).replay (finalize e initial body oracle) oracle index)) = _
  rw [same]
  exact answer_before (e.encoding.chain initial) pending H cut answer index before

theorem programAndFinalize_seal (initial : Digest) (body : Body g fields Advice Authentication)
    (H : Replay.Point g fields Advice Authentication Context Block → Digest × C)
    (cut : Fin g.roles.length) (answer : Digest × C) :
    let result := programAndFinalize e initial body H cut answer
    (result.2 ((e.encoding.chain initial).finalSealPoint result.1 result.2)).1 =
      result.1.finalSeal :=
  finalize_correct e initial body _

theorem programAndFinalize_body (initial : Digest) (body : Body g fields Advice Authentication)
    (H : Replay.Point g fields Advice Authentication Context Block → Digest × C)
    (cut : Fin g.roles.length) (answer : Digest × C) :
    (programAndFinalize e initial body H cut answer).1.body = body := rfl

/-- Updating the final seal cannot change the input that was programmed or
any earlier query input. No caller may select a different final-message buffer. -/
theorem programAndFinalize_prefix (initial : Digest) (body : Body g fields Advice Authentication)
    (H : Replay.Point g fields Advice Authentication Context Block → Digest × C)
    (cut : Fin g.roles.length) (answer : Digest × C) (index : ℕ) (before : index ≤ cut.val) :
    let result := programAndFinalize e initial body H cut answer
    (e.encoding.chain initial).point result.1 result.2 index =
      (e.encoding.chain initial).point (⟨body,fun _ => 0⟩ : Proof g fields Advice Authentication) H index := by
  let pending : Proof g fields Advice Authentication := ⟨body,fun _ => 0⟩
  let oracle := program (e.encoding.chain initial) pending H cut answer
  have same := replay_same_body e initial (finalize e initial body oracle) pending rfl oracle index
  change (e.encoding.chain initial).input
    ((e.encoding.chain initial).replay (finalize e initial body oracle) oracle index) =
    (e.encoding.chain initial).point pending H index
  rw [same]
  exact point_prefix (e.encoding.chain initial) pending H cut answer index before

end Current
end LfzkV2.Current.ZeroKnowledge.OracleProgramming
