import LfzkV2.Current.SelectionReplay
import LfzkV2.Current.ReplayPrefix

/-! Fingerprint responses are bound in the first boundary after selection's
coefficient query. Every later preimage contains that same boundary. Together
with the shared commitment context, this identifies one selected pair along
the entire accepted path, including the late backend statement. -/
noncomputable section
namespace LfzkV2.Current.Selection
open WitnessSelection

variable {roles : List Role} {Key Block Link Body C Oracle B N IB IN : Type}
variable [Field B] [Field N] [DecidableEq B] [DecidableEq N] [Fintype IB] [Fintype IN]

/-- The decoder reads the already bound fingerprint-response prefix. A
malformed preimage missing it receives a fixed default. -/
def responsesAt (decode : Input roles Key Block Link Body → (B × B) × (N × N))
    (fallback : (B × B) × (N × N)) (point : Input roles Key Block Link Body) :
    (B × B) × (N × N) :=
  (point.atRank 1).map decode |>.getD fallback

variable {g : Geometry} {F : Fields} {Advice Authentication Context : Type}

/-- This is a path identity, stronger than own-coordinate invariance. It
derives the same lists, fingerprint coefficients and responses at every later
query from the actual replay; no equality of selected witnesses is assumed. -/
theorem atPoint_replay
    (e : Replay.Encoding g F Advice Authentication Context Block C)
    (initialLink : Digest) (proof : Replay.Output g F Advice Authentication)
    (H : Replay.Point g F Advice Authentication Context Block → Digest × C)
    (lists : Context → Oracle → Finset (WitnessSelection.Candidate B IB) ×
      Finset (WitnessSelection.Candidate N IN))
    (decode : C → Coins B IB × Coins N IN)
    (responses : Replay.Point g F Advice Authentication Context Block → (B × B) × (N × N))
    (fallback : (B × B) × (N × N))
    (oracle : (Replay.Point g F Advice Authentication Context Block → Digest × C) → Context → Oracle)
    (n : ℕ) (hn : n ≤ g.roles.length) (hpos : 0 < n) :
    atPoint lists decode (responsesAt responses fallback) oracle
        ((e.chain initialLink).point proof H n) H =
      (Selection.Context.mk (lists (e.context proof) (oracle H (e.context proof))).1
        (lists (e.context proof) (oracle H (e.context proof))).2
        (decode (H ((e.chain initialLink).point proof H 0)).2).1
        (decode (H ((e.chain initialLink).point proof H 0)).2).2
        (responses ((e.chain initialLink).point proof H 1)).1
        (responses ((e.chain initialLink).point proof H 1)).2).extract := by
  have hr := (e.chain initialLink).point_rank proof H hn
  change Input.rank _ = n at hr
  have ha : ((e.chain initialLink).point proof H n).priorAnswers H
      ⟨0,by rw [hr]; exact hpos⟩ = (H ((e.chain initialLink).point proof H 0)).2 := by
    exact congrArg (fun p => (H p).2) (e.point_priorPoints initialLink proof H n hn ⟨0,hpos⟩)
  unfold atPoint
  rw [dif_pos (show 0 < ((e.chain initialLink).point proof H n).rank by omega)]
  rw [ha, e.point_context initialLink proof H n]
  unfold responsesAt
  rw [e.point_atRank initialLink proof H n 1 hn (by omega)]
  rfl

/-- In particular the frontend and backend reconstruct the very same
selected cells, despite being separated by many protocol boundaries. -/
theorem atPoint_replay_same
    (e : Replay.Encoding g F Advice Authentication Context Block C)
    (initialLink : Digest) (proof : Replay.Output g F Advice Authentication)
    (H : Replay.Point g F Advice Authentication Context Block → Digest × C)
    (lists : Context → Oracle → Finset (WitnessSelection.Candidate B IB) ×
      Finset (WitnessSelection.Candidate N IN))
    (decode : C → Coins B IB × Coins N IN)
    (responses : Replay.Point g F Advice Authentication Context Block → (B × B) × (N × N))
    (fallback : (B × B) × (N × N))
    (oracle : (Replay.Point g F Advice Authentication Context Block → Digest × C) → Context → Oracle)
    (n m : ℕ) (hn : n ≤ g.roles.length) (hm : m ≤ g.roles.length)
    (hnpos : 0 < n) (hmpos : 0 < m) :
    atPoint lists decode (responsesAt responses fallback) oracle
        ((e.chain initialLink).point proof H n) H =
      atPoint lists decode (responsesAt responses fallback) oracle
        ((e.chain initialLink).point proof H m) H :=
  (atPoint_replay e initialLink proof H lists decode responses fallback oracle n hn hnpos).trans
    (atPoint_replay e initialLink proof H lists decode responses fallback oracle m hm hmpos).symm

end LfzkV2.Current.Selection
