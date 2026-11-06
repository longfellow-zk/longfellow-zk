import WitnessSelection.IOP

/-! The early two-field extraction view. Selection takes the committed lists,
fingerprint coefficients and responses. It neither runs sumcheck nor depends
on the later Polygero statement. Backend recovery still has to supply matching
members of these lists; its extraction and outside-list errors are not removed. -/
namespace LfzkV2.Current.Selection
open Finset WitnessSelection
open scoped Classical

variable {B N IB IN : Type}

structure Context (B N IB IN : Type) where
  binaryList : Finset (Candidate B IB)
  primeList : Finset (Candidate N IN)
  binaryCoins : Coins B IB
  primeCoins : Coins N IN
  binaryResponse : B × B
  primeResponse : N × N

abbrev Pair (B N IB IN : Type) := Candidate B IB × Candidate N IN

section Fingerprints
variable [Field B] [Field N]
  [Fintype B] [Fintype N] [DecidableEq B] [DecidableEq N]
  [Fintype IB] [Fintype IN] [DecidableEq IB] [DecidableEq IN]

def Context.Matches (c : Context B N IB IN) (w : Pair B N IB IN) : Prop :=
  (w.1 ∈ c.binaryList ∧ fingerprint c.binaryCoins w.1 = c.binaryResponse) ∧
  (w.2 ∈ c.primeList ∧ fingerprint c.primeCoins w.2 = c.primeResponse)

def Context.Collision (c : Context B N IB IN) : Prop :=
  c.binaryCoins ∈ badCoins c.binaryList ∨ c.primeCoins ∈ badCoins c.primeList

noncomputable def Context.extract (c : Context B N IB IN) : Option (Pair B N IB IN) := do
  let b ← select c.binaryList c.binaryCoins c.binaryResponse
  let n ← select c.primeList c.primeCoins c.primeResponse
  pure (b,n)

omit [Fintype B] [Fintype N] [DecidableEq IB] [DecidableEq IN] in
theorem Context.extract_valid (c : Context B N IB IN) (w : Pair B N IB IN)
    (h : c.extract = some w) : c.Matches w := by
  cases hb : select c.binaryList c.binaryCoins c.binaryResponse with
  | none => simp [Context.extract, hb] at h
  | some b =>
      cases hn : select c.primeList c.primeCoins c.primeResponse with
      | none => simp [Context.extract, hb, hn] at h
      | some n =>
          have hw : (b,n) = w := by simpa [Context.extract, hb, hn] using h
          subst w
          exact ⟨select_valid _ _ _ b hb, select_valid _ _ _ n hn⟩

theorem Context.extract_of_match (c : Context B N IB IN) (w : Pair B N IB IN)
    (hgood : ¬ c.Collision) (hmatch : c.Matches w) : c.extract = some w := by
  have hb := select_of_match c.binaryList c.binaryCoins c.binaryResponse
    (fun h => hgood (Or.inl h)) w.1 hmatch.1.1 hmatch.1.2
  have hn := select_of_match c.primeList c.primeCoins c.primeResponse
    (fun h => hgood (Or.inr h)) w.2 hmatch.2.1 hmatch.2.2
  simp [Context.extract, hb, hn]

/-- A late backend witness authenticating all four fingerprint rows is the
early selected pair, except on the already-counted selection collision event. -/
theorem Context.authenticated_pair (c : Context B N IB IN) (w : Pair B N IB IN)
    (hb : w.1 ∈ c.binaryList) (hn : w.2 ∈ c.primeList)
    (hbr : dot c.binaryCoins.1 w.1.1 + w.1.2.1 - c.binaryResponse.1 = 0 ∧
      dot c.binaryCoins.2 w.1.1 + w.1.2.2 - c.binaryResponse.2 = 0)
    (hnr : dot c.primeCoins.1 w.2.1 + w.2.2.1 - c.primeResponse.1 = 0 ∧
      dot c.primeCoins.2 w.2.1 + w.2.2.2 - c.primeResponse.2 = 0) :
    c.Collision ∨ c.extract = some w := by
  by_cases h : c.Collision
  · exact Or.inl h
  · exact Or.inr (c.extract_of_match w h
      ⟨⟨hb, (affine_rows_iff _ _ _).mp hbr⟩, ⟨hn, (affine_rows_iff _ _ _).mp hnr⟩⟩)

end Fingerprints
variable [Zero N] [One N]

/-- Reconstruct the prime private inputs with the binary participant's shared
bits. `other` supplies only the remaining prime input cells, not its pads or
hiding scalar. The trusted layouts determine both projections. -/
def primeInputs {Shared Other : Type}
    (binaryBits : Candidate B IB → Shared → Bool) (other : Candidate N IN → Other → N)
    (w : Pair B N IB IN) : Shared ⊕ Other → N :=
  Sum.elim (fun i => if binaryBits w.1 i then 1 else 0) (other w.2)

theorem primeInputs_shared {Shared Other : Type}
    (binaryBits : Candidate B IB → Shared → Bool) (other : Candidate N IN → Other → N)
    (w : Pair B N IB IN) (i : Shared) :
    primeInputs binaryBits other w (.inl i) = if binaryBits w.1 i then 1 else 0 := rfl

end LfzkV2.Current.Selection
