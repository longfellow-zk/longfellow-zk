import LfzkV2.Current.Messages
import TranscriptV2.Links

/-! Logical query preimages. A block is the canonically framed writes since
the previous boundary, including bind-only messages. Only actual boundary
links, not challenge answers, are fed back into the prefix. This representation
proves full-parent recovery and reconstructs earlier oracle answers. `Replay`
uses it for the current schedule; byte-encoder correspondence is separate. -/
namespace LfzkV2.Current

/-- The initial bound context followed by exactly `n` completed boundaries.
The block and link at each boundary retain enough data to recover its input. -/
def History (Context Block Link : Type) : ℕ → Type
  | 0 => Context
  | n+1 => History Context Block Link n × Block × Link

instance historyFintype (Context Block Link : Type)
    [Fintype Context] [Fintype Block] [Fintype Link] :
    (n : ℕ) → Fintype (History Context Block Link n)
  | 0 => inferInstanceAs (Fintype Context)
  | n+1 => by
      letI := historyFintype Context Block Link n
      exact inferInstanceAs (Fintype (History Context Block Link n × Block × Link))

/-- The final domain binds the complete body, including authentication. There
is no slot for a caller-chosen substitute terminal message. Geometry fixes the
role at each counter; different counters remain different oracle inputs. -/
inductive Input (roles : List Role) (Context Block Link Body : Type) where
  | round (index : Fin roles.length) (history : History Context Block Link index.val) (block : Block)
  | finalSeal (history : History Context Block Link roles.length) (body : Body)

namespace Input
variable {roles : List Role} {Context Block Link Body : Type}

def rank : Input roles Context Block Link Body → ℕ
  | .round i _ _ => i.val
  | .finalSeal .. => roles.length


/-- The counter fixes the ordinary role; complete-proof finalization has a
separate constructor and no ordinary role. -/
def role : Input roles Context Block Link Body → Option Role
  | .round i .. => some (roles.get i)
  | .finalSeal .. => none

@[simp] theorem role_round (index : Fin roles.length)
    (history : History Context Block Link index.val) (block : Block) :
    (Input.round index history block : Input roles Context Block Link Body).role =
      some (roles.get index) := rfl

@[simp] theorem role_finalSeal (history : History Context Block Link roles.length) (body : Body) :
    (Input.finalSeal history body : Input roles Context Block Link Body).role = none := rfl

@[simp] theorem finalSeal_not_batching (history : History Context Block Link roles.length)
    (body : Body) :
    (Input.finalSeal history body : Input roles Context Block Link Body).role ≠ some .batching := by
  simp

@[simp] theorem finalSeal_not_opening (history : History Context Block Link roles.length)
    (body : Body) :
    (Input.finalSeal history body : Input roles Context Block Link Body).role ≠ some .opening := by
  simp


theorem role_eq_of_rank (point : Input roles Context Block Link Body)
    (i : Fin roles.length) (hrank : point.rank = i.val) :
    point.role = some (roles.get i) := by
  cases point with
  | round j history block =>
      have he : j = i := Fin.ext hrank
      subst j
      rfl
  | finalSeal history body =>
      have hi := i.isLt
      change roles.length = i.val at hrank
      omega

def domain : Input roles Context Block Link Body → Option Domain
  | .round i _ _ => some (roles.get i).domain
  | .finalSeal .. => none

/-- Recover the immediately preceding boundary from a completed history. -/
def previous : (n : ℕ) → n ≤ roles.length → History Context Block Link n →
    Option (Input roles Context Block Link Body)
  | 0, _, _ => none
  | n+1, h, history => some (.round ⟨n, by omega⟩ history.1 history.2.1)

def parent : Input roles Context Block Link Body → Option (Input roles Context Block Link Body)
  | .round i history _ => previous i.val (by omega) history
  | .finalSeal history _ => previous roles.length (by rfl) history

/-- The initial value is used only before the first boundary. -/
def lastLink (initial : Link) : (n : ℕ) → History Context Block Link n → Link
  | 0, _ => initial
  | _+1, history => history.2.2

def claimed (initial : Link) : Input roles Context Block Link Body → Link
  | .round i history _ => lastLink initial i.val history
  | .finalSeal history _ => lastLink initial roles.length history

def links (initial : Link) : TranscriptV2.Links (Input roles Context Block Link Body) Link :=
  ⟨parent, claimed initial⟩

theorem parent_round_succ {n : ℕ} (hn : n+1 < roles.length)
    (history : History Context Block Link n) (block next : Block) (link : Link) :
    parent (.round ⟨n+1, hn⟩ (history, block, link) next : Input roles Context Block Link Body) =
      some (.round ⟨n, by omega⟩ history block) := rfl

theorem claimed_round_succ {n : ℕ} (hn : n+1 < roles.length)
    (history : History Context Block Link n) (block next : Block) (link initial : Link) :
    claimed initial (.round ⟨n+1, hn⟩ (history, block, link) next :
      Input roles Context Block Link Body) = link := rfl

theorem parent_finalSeal (role : Role) (rest : List Role)
    (history : History Context Block Link rest.length) (block : Block) (link : Link) (body : Body) :
    parent (.finalSeal (history, block, link) body : Input (role :: rest) Context Block Link Body) =
      some (.round ⟨rest.length, by simp⟩ history block) := rfl

theorem claimed_finalSeal (role : Role) (rest : List Role)
    (history : History Context Block Link rest.length) (block : Block)
    (link initial : Link) (body : Body) :
    claimed initial (.finalSeal (history, block, link) body : Input (role :: rest) Context Block Link Body) =
      link := rfl

theorem parent_rank {child ancestor : Input roles Context Block Link Body}
    (h : parent child = some ancestor) : rank child = rank ancestor + 1 := by
  have previous_rank (n : ℕ) (hn : n ≤ roles.length) (history : History Context Block Link n)
      (hp : previous n hn history = some ancestor) : n = rank ancestor + 1 := by
    cases n with
    | zero => simp [previous] at hp
    | succ n =>
        have heq := Option.some.inj hp
        rw [← heq]
        rfl
  cases child with
  | round i history block => exact previous_rank i.val (by omega) history h
  | finalSeal history body => exact previous_rank roles.length (by rfl) history h

/-- Erasing the logical final body would destroy this binding property.
The concrete counterpart requires injectivity of the canonical body codec. -/
theorem finalSeal_body_bound {h₁ h₂ : History Context Block Link roles.length} {a b : Body}
    (h : (Input.finalSeal h₁ a : Input roles Context Block Link Body) = .finalSeal h₂ b) : a = b := by
  cases h
  rfl

/-- A completed history contains the exact preimage of every earlier query.
The saved challenge answers themselves are not part of those preimages. -/
def historyPoints : (n : ℕ) → n ≤ roles.length → History Context Block Link n →
    Fin n → Input roles Context Block Link Body
  | 0, _, _ => Fin.elim0
  | n+1, hn, history => Fin.snoc
      (historyPoints n (by omega) history.1) (.round ⟨n, by omega⟩ history.1 history.2.1)

theorem historyPoints_rank (n : ℕ) (hn : n ≤ roles.length)
    (history : History Context Block Link n) (i : Fin n) :
    (historyPoints (Body := Body) n hn history i).rank = i.val := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [historyPoints, rank]
      · simp only [historyPoints, Fin.snoc_castSucc, Fin.val_castSucc]
        exact ih _ history.1 j

def priorPoints (point : Input roles Context Block Link Body) :
    Fin point.rank → Input roles Context Block Link Body :=
  match point with
  | .round i history _ => historyPoints i.val (by omega) history
  | .finalSeal history _ => historyPoints roles.length (by rfl) history

theorem priorPoints_rank (point : Input roles Context Block Link Body) (i : Fin point.rank) :
    (point.priorPoints i).rank = i.val := by
  cases point <;> exact historyPoints_rank _ _ _ i

def priorAnswers {C : Type} (point : Input roles Context Block Link Body)
    (H : Input roles Context Block Link Body → Link × C) : Fin point.rank → C :=
  fun i => (H (point.priorPoints i)).2

/-- All semantic data reconstructed from earlier answers is independent of
the answer being charged. This holds even for adversarially assembled query
histories; consistency with an accepted replay is proved separately. -/
theorem priorAnswers_off {C : Type} (point : Input roles Context Block Link Body)
    {H H' : Input roles Context Block Link Body → Link × C}
    (h : Bcs.TotalOracle.AgreeOff point H H') : point.priorAnswers H = point.priorAnswers H' := by
  funext i
  apply congrArg Prod.snd
  apply h
  intro heq
  have hr := point.priorPoints_rank i
  rw [heq] at hr
  have hi := i.isLt
  omega

/-- The common prefix interface used by the local Fiat--Shamir counts. -/
def points : Bcs.TotalOracle.PrefixPoints (Input roles Context Block Link Body) where
  slot := rank
  anc point j := if h : j < point.rank then point.priorPoints ⟨j,h⟩ else point
  anc_ne point j hj := by
    rw [dif_pos hj]
    intro heq
    have hr := point.priorPoints_rank ⟨j,hj⟩
    rw [heq] at hr
    omega

theorem points_chal_samples {C : Type} (point : Input roles Context Block Link Body)
    (H : Input roles Context Block Link Body → Link × C) :
    (fun i => ((points.chal H point) i).2) = point.priorAnswers H := by
  funext i
  simp only [Bcs.TotalOracle.PrefixPoints.chal, points, priorAnswers]
  rw [dif_pos (show i.val < point.rank from i.isLt)]
  rfl

def historyContext : (n : ℕ) → History Context Block Link n → Context
  | 0, context => context
  | n+1, history => historyContext n history.1

def context : Input roles Context Block Link Body → Context
  | .round i history _ => historyContext i.val history
  | .finalSeal history _ => historyContext roles.length history

/-- Every ancestor names the same committed context. This is the key used
when extracting the tuple oracle from the trace before its first query. -/
theorem historyPoints_context (n : ℕ) (hn : n ≤ roles.length)
    (history : History Context Block Link n) (i : Fin n) :
    (historyPoints (Body := Body) n hn history i).context = historyContext n history := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [historyPoints, context, historyContext]
      · simp only [historyPoints, Fin.snoc_castSucc, historyContext]
        exact ih _ history.1 j

theorem priorPoints_context (point : Input roles Context Block Link Body) (i : Fin point.rank) :
    (point.priorPoints i).context = point.context := by
  cases point <;> exact historyPoints_context _ _ _ i

end Input

/-- Application finalization takes the parsed proof itself. Its body includes
the terminal opened rows and authentication; the supplied seal is excluded. -/
def Proof.finalSealInput {g : Geometry} {F : Fields} {Advice Authentication Context Block : Type}
    (proof : Proof g F Advice Authentication)
    (history : History Context Block Digest g.roles.length) :
    Input g.roles Context Block Digest (Body g F Advice Authentication) :=
  .finalSeal history proof.body

theorem Proof.finalSealInput_body {g : Geometry} {F : Fields}
    {Advice Authentication Context Block : Type} (p q : Proof g F Advice Authentication)
    (hp hq : History Context Block Digest g.roles.length)
    (h : p.finalSealInput hp = q.finalSealInput hq) : p.body = q.body :=
  Input.finalSeal_body_bound h

theorem Proof.finalSealInput_authentication {g : Geometry} {F : Fields}
    {Advice Authentication Context Block : Type} (p q : Proof g F Advice Authentication)
    (hp hq : History Context Block Digest g.roles.length)
    (h : p.finalSealInput hp = q.finalSealInput hq) : p.body.authentication = q.body.authentication :=
  congrArg Body.authentication (Proof.finalSealInput_body p q hp hq h)

end LfzkV2.Current
