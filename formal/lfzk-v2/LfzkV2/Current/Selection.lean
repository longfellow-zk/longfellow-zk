import WitnessSelection.Collision

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

theorem Context.extract_of_match (c : Context B N IB IN) (w : Pair B N IB IN)
    (hgood : ¬ c.Collision) (hmatch : c.Matches w) : c.extract = some w := by
  have hb := select_of_match c.binaryList c.binaryCoins c.binaryResponse
    (fun h => hgood (Or.inl h)) w.1 hmatch.1.1 hmatch.1.2
  have hn := select_of_match c.primeList c.primeCoins c.primeResponse
    (fun h => hgood (Or.inr h)) w.2 hmatch.2.1 hmatch.2.2
  simp [Context.extract, hb, hn]

end Fingerprints
end LfzkV2.Current.Selection
