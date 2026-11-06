import LfzkV2.Current.BackendQueries
import LfzkV2.Current.ReplayPrefix

/-! Identify the backend's two adjacent inputs on the actual current replay.
The batching input supplies the whole parent prefix. The next input adds its
actual link and the canonical complete response pair. Only the opening block
codec is a correspondence premise; adjacent-point identities are derived. -/
noncomputable section
namespace LfzkV2.Current.BackendPath
open Replay

variable {g : Geometry} {F : Fields} {Advice Authentication Context Block C : Type}
variable (e : Encoding g F Advice Authentication Context Block C)
variable (initialLink : Digest) (proof : Output g F Advice Authentication)
variable (H : Point g F Advice Authentication Context Block → Digest × C)
variable (i : Fin g.roles.length)

private theorem priorPoints_congr {roles : List Role} {Key Block Link Body : Type}
    {first second : Input roles Key Block Link Body} (heq : first = second)
    (j : Fin first.rank) :
    first.priorPoints j = second.priorPoints ⟨j.val, by rw [← heq]; exact j.isLt⟩ := by
  subst second
  rfl

/-- Every ordinary replay boundary has its prescribed counter and is
therefore exactly one parent prefix of that counter. -/
theorem exists_parent :
    ∃ parent : BackendQueries.Parent g.roles Context Block Digest i,
      parent.point = (e.chain initialLink).point proof H i.val := by
  have hr := (e.chain initialLink).point_rank proof H (Nat.le_of_lt i.isLt)
  change Input.rank _ = i.val at hr
  cases hpoint : (e.chain initialLink).point proof H i.val with
  | round j history block =>
      rw [hpoint] at hr
      have he : j = i := Fin.ext hr
      subst j
      exact ⟨⟨history,block⟩,rfl⟩
  | finalSeal history body =>
      rw [hpoint] at hr
      have hi := i.isLt
      change g.roles.length = i.val at hr
      omega

/-- The actual batching prefix, with no stored challenge answers in its
preimage. Earlier answers are recovered from the oracle at its ancestors. -/
def parent : BackendQueries.Parent g.roles Context Block Digest i :=
  Classical.choose (exists_parent e initialLink proof H i)

theorem parent_point :
    (parent e initialLink proof H i).point = (e.chain initialLink).point proof H i.val :=
  Classical.choose_spec (exists_parent e initialLink proof H i)



theorem parent_context :
    ((parent e initialLink proof H i).point
      (Body := Body g F Advice Authentication)).context = e.context proof := by
  rw [parent_point]
  exact e.point_context initialLink proof H i.val

/-- Decoding a source boundary from the batching prefix retrieves that
boundary's actual replay preimage, including all its bound source messages. -/
theorem parent_atRank (n : ℕ) (hn : n ≤ i.val) :
    (parent e initialLink proof H i).point.atRank n =
      some ((e.chain initialLink).point proof H n) := by
  rw [parent_point]
  exact e.point_atRank initialLink proof H i.val n (Nat.le_of_lt i.isLt) hn

theorem successor_parent :
    Input.parent ((e.chain initialLink).point proof H (i.val+1)) =
      some (parent e initialLink proof H i).point := by
  rw [parent_point]
  exact (e.chain initialLink).point_parent proof H i.isLt

theorem successor_link :
    Input.claimed initialLink ((e.chain initialLink).point proof H (i.val+1)) =
      (H (parent e initialLink proof H i).point).1 := by
  rw [parent_point]
  exact (e.chain initialLink).point_link proof H i.isLt

/-- A block codec law identifies what was written at the opening boundary.
Replay itself supplies its parent history and actual link; neither is an
additional caller-provided path assumption. -/
theorem opening_eq {Response : Type} (next : i.val+1 < g.roles.length)
    (encode : Response → Block) (responses : Output g F Advice Authentication → Response)
    (hcodec : ∀ past, e.block proof ⟨i.val+1,next⟩ past = encode (responses proof)) :
    (e.chain initialLink).point proof H (i.val+1) =
      (parent e initialLink proof H i).child next encode
        ((H (parent e initialLink proof H i).point).1,responses proof) := by
  have hp := parent_point e initialLink proof H i
  change (e.chain initialLink).input ((e.chain initialLink).replay proof H (i.val+1)) = _
  rw [TranscriptV2.Chain.replay, dif_pos i.isLt]
  change (e.advance proof ((e.chain initialLink).replay proof H i.val)
    (H ((e.chain initialLink).replay proof H i.val).point)).point = _
  generalize hs : (e.chain initialLink).replay proof H i.val = state
  change (parent e initialLink proof H i).point =
    ((e.chain initialLink).replay proof H i.val).point at hp
  rw [hs] at hp
  rcases state with ⟨point,answers⟩
  rcases hparent : parent e initialLink proof H i with ⟨history,block⟩
  rw [hparent] at hp
  change Input.round i history block = point at hp
  subst point
  change (e.stateAt proof (i.val+1) _
    (history,block,(H (.round i history block)).1)
    (Fin.snoc answers (H (.round i history block)).2)).point = _
  simp only [Encoding.stateAt, dif_pos next, hcodec, BackendQueries.Parent.child, BackendQueries.Parent.point]

/-- The statement compiler sees exactly the strict earlier replay answers.
In particular neither the batching coin nor the opening set can enter it. -/
theorem priorAnswers_replay :
    (parent e initialLink proof H i).point.priorAnswers H =
      fun j : Fin i.val => (H ((e.chain initialLink).point proof H j.val)).2 := by
  funext j
  have hp := parent_point e initialLink proof H i
  have h := e.point_priorPoints initialLink proof H i.val (Nat.le_of_lt i.isLt) j
  have he := priorPoints_congr hp j
  exact congrArg (fun point => (H point).2) (he.trans h)

/-- The actual target statement, compiled by a fixed public compiler from
the bound parent and strict prefix. This constructor permits a concrete affine-row compiler to be used
without assuming an equality of late and early statements. -/
def statement {Statement : Type}
    (compile : BackendQueries.Parent g.roles Context Block Digest i →
      (Fin i.val → C) → Statement) : Statement :=
  compile (parent e initialLink proof H i)
    (fun j => (H ((e.chain initialLink).point proof H j.val)).2)

theorem statement_replay {Statement : Type}
    (compile : BackendQueries.Parent g.roles Context Block Digest i →
      (Fin i.val → C) → Statement) :
    (parent e initialLink proof H i).statement compile H =
      statement e initialLink proof H i compile := by
  unfold BackendQueries.Parent.statement statement
  rw [priorAnswers_replay]

end LfzkV2.Current.BackendPath
