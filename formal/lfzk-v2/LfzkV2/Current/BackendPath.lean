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

end LfzkV2.Current.BackendPath
