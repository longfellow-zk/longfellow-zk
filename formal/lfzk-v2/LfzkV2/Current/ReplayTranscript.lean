import LfzkV2.Current.Prefix

/-! Replay of fixed transcript packets. This module has no challenge type
or verifier cache: each step writes its packet and feeds back one node digest.
The complete body supplies the terminal packet. -/
namespace LfzkV2.Current.Replay

variable {g : Geometry} {F : Fields} {Advice Authentication Context Block : Type}

abbrev Output (g : Geometry) (F : Fields) (Advice Authentication : Type) :=
  Proof g F Advice Authentication

abbrev Point (g : Geometry) (F : Fields) (Advice Authentication Context Block : Type) :=
  Input g.roles Context Block Digest (Body g F Advice Authentication)

abbrev TranscriptState (g : Geometry) (F : Fields) (Advice Authentication Context Block : Type) :=
  Point g F Advice Authentication Context Block

namespace TranscriptState

/-- A terminal packet contains the submitted complete body. This is a
property of the transcript alone, independent of all verifier challenges. -/
def BodyBound (point : TranscriptState g F Advice Authentication Context Block)
    (expected : Body g F Advice Authentication) : Prop :=
  ∀ history body, point = .finalSeal history body → body = expected

def atRound (body : Body g F Advice Authentication) (n : ℕ) (hn : n ≤ g.roles.length)
    (history : History Context Block Digest n) (message : n < g.roles.length → Block) :
    TranscriptState g F Advice Authentication Context Block :=
  if h : n < g.roles.length then .round ⟨n,h⟩ history (message h)
  else by
    have he : n = g.roles.length := by omega
    subst n
    exact .finalSeal history body

/-- No field challenge or verifier cache enters a transcript step. -/
def advance (body : Body g F Advice Authentication)
    (point : TranscriptState g F Advice Authentication Context Block) (digest : Digest)
    (message : point.rank+1 < g.roles.length → Block) :
    TranscriptState g F Advice Authentication Context Block :=
  match point with
  | .round i history block => atRound body (i.val+1) (by omega) (history,block,digest) message
  | .finalSeal history body => .finalSeal history body

end TranscriptState

/-- The request and submitted proof fix every packet before replay starts. -/
structure Transcript (g : Geometry) (F : Fields) (Advice Authentication Context Block : Type) where
  context : Context
  block : Fin g.roles.length → Block
  body : Body g F Advice Authentication

namespace Transcript
variable (transcript : Transcript g F Advice Authentication Context Block)

def initial : TranscriptState g F Advice Authentication Context Block :=
  TranscriptState.atRound transcript.body 0 (Nat.zero_le _) transcript.context
    (fun h => transcript.block ⟨0,h⟩)

def advance (point : TranscriptState g F Advice Authentication Context Block) (digest : Digest) :
    TranscriptState g F Advice Authentication Context Block :=
  TranscriptState.advance transcript.body point digest (fun h => transcript.block ⟨point.rank+1,h⟩)

def replay (nodes : TranscriptState g F Advice Authentication Context Block → Digest) :
    ℕ → TranscriptState g F Advice Authentication Context Block
  | 0 => transcript.initial
  | n+1 => if n < g.roles.length then
      let point := replay nodes n
      transcript.advance point (nodes point)
    else replay nodes n

/-- Replaying recorded answers recovers the actual transcript whenever
the original trace contains its preceding nodes. Nothing is assumed about
answers at unreached points or about the order in which nodes were queried. -/
theorem replay_congr_on_prefix
    (nodes nodes' : TranscriptState g F Advice Authentication Context Block → Digest)
    (n : ℕ)
    (agree : ∀ i < n, nodes (transcript.replay nodes i) = nodes' (transcript.replay nodes i)) :
    transcript.replay nodes n = transcript.replay nodes' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have previous := ih (fun i within => agree i (by omega))
      by_cases inside : n < g.roles.length
      · simp only [replay,if_pos inside,← previous,agree n (by omega)]
      · simpa only [replay,if_neg inside] using previous

end Transcript
end LfzkV2.Current.Replay
