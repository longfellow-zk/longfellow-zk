import TranscriptV2.StrandUnfolding

/-! A submitted proof fixes the bytes written at every boundary. Replaying
those packets depends only on preceding node hashes. Numbered inputs make
that dependence strictly one-way even when two hash outputs coincide. -/
namespace TranscriptV2.StrandLinear
open Strand Framing Bcs.TotalOracle

/-- This is transcript replay only: challenge readers and arithmetic verifier
state are deliberately absent. The terminal packet may contain the full body. -/
def replay (messages : ℕ → Bytes) (H : Oracle) : ℕ → History
  | 0 => .root (messages 0)
  | n+1 =>
      let parent := replay messages H n
      .child parent (H parent.input.encode) (messages (n+1))

@[simp] theorem replay_depth (messages : ℕ → Bytes) (H : Oracle) (n : ℕ) :
    (replay messages H n).depth = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [replay,History.depth,ih]

theorem replay_consistent (messages : ℕ → Bytes) (H : Oracle) (n : ℕ) :
    (replay messages H n).Consistent H := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨ih,rfl⟩

/-- Distinct positions have distinct inputs, with no hash-collision premise. -/
theorem replay_inputs_ne (messages : ℕ → Bytes) (H : Oracle) (i j : ℕ)
    (firstFits : i < 2^64) (secondFits : j < 2^64) (different : i ≠ j) :
    (replay messages H i).input.encode ≠ (replay messages H j).input.encode := by
  apply Input.encode_ne_of_id_ne (History.valid _) (History.valid _)
  intro same
  have ids := congrArg Fin.val same
  simp only [History.input_id,History.id,replay_depth,
    Nat.mod_eq_of_lt firstFits,Nat.mod_eq_of_lt secondFits] at ids
  exact different ids

/-- Altering a node's own answer cannot alter its input. Earlier inputs have
smaller ids, so this also covers collisions among their digest values. -/
theorem replay_off (messages : ℕ → Bytes) (H H' : Oracle) (n : ℕ)
    (fits : n < 2^64)
    (agree : AgreeOff (replay messages H n).input.encode H H') :
    replay messages H n = replay messages H' n := by
  have earlier (i : ℕ) (bound : i ≤ n) :
      replay messages H i = replay messages H' i := by
    induction i with
    | zero => rfl
    | succ i ih =>
        have previous := ih (by omega)
        have answer := agree (replay messages H i).input.encode
          (replay_inputs_ne messages H i n (by omega) fits (by omega))
        simp only [replay,← previous,answer]
  exact earlier n le_rfl

/-- The same independence law in a finite address window. The coverage law
is needed only for the actual prefix: unrelated malformed inputs may use a
fallback address, but no two reached node positions can alias through it. -/
theorem replay_restrict_off {P : Type} (restrict : Bytes → P) (restore : P → Bytes)
    (messages : ℕ → Bytes) (H H' : P → Digest) (n : ℕ) (fits : n < 2^64)
    (covered : ∀ i ≤ n,
      restore (restrict (replay messages (H ∘ restrict) i).input.encode) =
        (replay messages (H ∘ restrict) i).input.encode)
    (agree : AgreeOff (restrict (replay messages (H ∘ restrict) n).input.encode) H H') :
    replay messages (H ∘ restrict) n = replay messages (H' ∘ restrict) n := by
  have earlier (i : ℕ) (bound : i ≤ n) :
      replay messages (H ∘ restrict) i = replay messages (H' ∘ restrict) i := by
    induction i with
    | zero => rfl
    | succ i ih =>
        have previous := ih (by omega)
        have different : restrict (replay messages (H ∘ restrict) i).input.encode ≠
            restrict (replay messages (H ∘ restrict) n).input.encode := by
          intro same
          have raw := (covered i (by omega)).symm.trans
            ((congrArg restore same).trans (covered n le_rfl))
          exact replay_inputs_ne messages (H ∘ restrict) i n (by omega) fits (by omega) raw
        have answer := agree _ different
        simp only [replay,← previous,Function.comp_apply,answer]
  exact earlier n le_rfl

end TranscriptV2.StrandLinear
