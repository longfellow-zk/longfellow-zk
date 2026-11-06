import LfzkV2.Current.Prefix

/-! The two adjacent Polygero query inputs. A parent binds the completed
statements; a child adds its parent's actual link and both complete responses.
Statements are reconstructed from the parent's earlier oracle answers, so the
two-answer counting argument cannot accidentally read either charged answer. -/
namespace LfzkV2.Current.BackendQueries

variable {roles : List Role} {Context Block Link Body C Response Statement Oracle : Type}

structure Parent (roles : List Role) (Context Block Link : Type) (i : Fin roles.length) where
  history : History Context Block Link i.val
  block : Block

namespace Parent
variable {i : Fin roles.length}

def point (parent : Parent roles Context Block Link i) : Input roles Context Block Link Body :=
  .round i parent.history parent.block

def child (parent : Parent roles Context Block Link i) (next : i.val+1 < roles.length)
    (encode : Response → Block) (response : Link × Response) : Input roles Context Block Link Body :=
  .round ⟨i.val+1,next⟩ (parent.history, parent.block, response.1) (encode response.2)

theorem point_injective : Function.Injective
    (point (Body := Body) : Parent roles Context Block Link i → _) := by
  intro a b h
  cases a
  cases b
  cases h
  rfl

theorem child_parent (parent : Parent roles Context Block Link i) (next : i.val+1 < roles.length)
    (encode : Response → Block) (response : Link × Response) :
    Input.parent (parent.child (Body := Body) next encode response) = some parent.point := rfl

theorem child_link (parent : Parent roles Context Block Link i) (next : i.val+1 < roles.length)
    (encode : Response → Block) (response : Link × Response) (initial : Link) :
    Input.claimed initial (parent.child (Body := Body) next encode response) = response.1 := rfl

/-- Canonical response encoding makes a child point identify one complete
response pair. This is needed for the low-response charge at that point. -/
theorem child_injective (next : i.val+1 < roles.length)
    (encode : Response → Block) (hencode : Function.Injective encode) :
    Function.Injective (fun a : Parent roles Context Block Link i × (Link × Response) =>
      a.1.child (Body := Body) next encode a.2) := by
  intro a b heq
  have hp := congrArg Input.parent heq
  change some a.1.point = some b.1.point at hp
  have hl := congrArg (Input.claimed a.2.1) heq
  change a.2.1 = b.2.1 at hl
  have hr := congrArg (fun x : Input roles Context Block Link Body =>
    match x with | .round _ _ block => some block | .finalSeal .. => none) heq
  change some (encode a.2.2) = some (encode b.2.2) at hr
  exact Prod.ext (point_injective (Option.some.inj hp)) (Prod.ext hl (hencode (Option.some.inj hr)))

theorem point_ne_child (parent : Parent roles Context Block Link i) (next : i.val+1 < roles.length)
    (encode : Response → Block) (response : Link × Response) :
    parent.point ≠ parent.child (Body := Body) next encode response := by
  intro h
  have hr := congrArg Input.rank h
  change i.val = i.val+1 at hr
  omega

theorem child_answers (parent : Parent roles Context Block Link i) (next : i.val+1 < roles.length)
    (encode : Response → Block) (response : Link × Response)
    (H : Input roles Context Block Link Body → Link × C) :
    (parent.child next encode response).priorAnswers H =
      Fin.snoc (parent.point.priorAnswers H) (H parent.point).2 := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp [child, point, Input.priorAnswers, Input.priorPoints, Input.historyPoints]
  · simp [child, point, Input.priorAnswers, Input.priorPoints, Input.historyPoints]

def statement (derive : Parent roles Context Block Link i → (Fin i.val → C) → Statement)
    (parent : Parent roles Context Block Link i)
    (H : Input roles Context Block Link Body → Link × C) : Statement :=
  derive parent (parent.point.priorAnswers H)

/-- Fixing everything except these two answers also fixes the whole statement.
In particular no late response or opening challenge enters its reconstruction. -/
theorem statement_off (derive : Parent roles Context Block Link i → (Fin i.val → C) → Statement)
    (parent : Parent roles Context Block Link i) (next : i.val+1 < roles.length)
    (encode : Response → Block) (response : Link × Response)
    (H H' : Input roles Context Block Link Body → Link × C)
    (h : ∀ z, z ≠ parent.point → z ≠ parent.child next encode response → H z = H' z) :
    statement derive parent H = statement derive parent H' := by
  apply congrArg (derive parent)
  funext j
  apply congrArg Prod.snd
  apply h
  · intro heq
    have hr := parent.point.priorPoints_rank j
    rw [heq] at hr
    have hj := j.isLt
    change j.val < i.val at hj
    change i.val = j.val at hr
    omega
  · intro heq
    have hr := parent.point.priorPoints_rank j
    rw [heq] at hr
    have hj := j.isLt
    change j.val < i.val at hj
    change i.val+1 = j.val at hr
    omega

/-- Cut-trace extraction is invariant under changing a query of this context.
Applying that property twice gives exactly the invariance needed for the
parent/child count, rather than assuming the recovered oracle is globally fixed. -/
theorem oracle_off [DecidableEq (Input roles Context Block Link Body)]
    (oracle : (Input roles Context Block Link Body → Link × C) → Context → Oracle)
    (hoff : ∀ z H H', Bcs.TotalOracle.AgreeOff z H H' → oracle H z.context = oracle H' z.context)
    (parent : Parent roles Context Block Link i) (next : i.val+1 < roles.length)
    (encode : Response → Block) (response : Link × Response)
    (H H' : Input roles Context Block Link Body → Link × C)
    (h : ∀ z, z ≠ parent.point → z ≠ parent.child next encode response → H z = H' z) :
    oracle H (parent.point (Body := Body)).context = oracle H' (parent.point (Body := Body)).context := by
  let middle := Function.update H parent.point (H' parent.point)
  have hfirst : Bcs.TotalOracle.AgreeOff parent.point H middle := by
    intro z hz
    simp [middle, hz]
  have hsecond : Bcs.TotalOracle.AgreeOff (parent.child next encode response) middle H' := by
    intro z hz
    by_cases hp : z = parent.point
    · simp [middle, hp]
    · simpa [middle, hp] using h z hp hz
  exact (hoff parent.point H middle hfirst).trans
    (hoff (parent.child next encode response) middle H' hsecond)

end Parent
end LfzkV2.Current.BackendQueries
