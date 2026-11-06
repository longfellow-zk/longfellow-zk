import LfzkV2.Current.ApplicationCharging
import LfzkV2.Current.BackendOracle
import LfzkV2.Current.BackendPositions

/-! One charge family for the current complete protocol. Application roles
and the two backend roles are disjoint. Rank and the summed high-response mass
share the unique batching input; both fields keep one shared opening query.
Consequently composition takes one maximum over roles, rather than adding a
full adversarial query allowance for each constituent protocol. -/
noncomputable section
namespace LfzkV2.Current.GlobalCharges
open RecursivePolygero ProfileAnalysis Finset ApplicationOracle ApplicationCharging
open scoped Classical

variable {g : Geometry} {Context Block Link Body C B I J SlotB PadB Other PadN IB IN : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable [Fintype I] [DecidableEq I] [Fintype J] [Fintype Other]
variable [Fintype IB] [Fintype IN] [DecidableEq IB] [DecidableEq IN] [Fintype C]
variable {p shared maskBits M K LB LN k s n t : ℕ} [Fact p.Prime]
variable (P R : Joint.Participant k s n t)
variable (S : SelectionSource g.roles Context Block Link Body C (JointResponse.Oracle P R)
  B (ZMod p) IB IN)
variable (read : (point : Input g.roles Context Block Link Body) → (Fin point.rank → C) →
  PrefixConfiguration (I := I) (J := J) (SlotB := SlotB) (PadB := PadB)
    (Other := Other) (PadN := PadN) (shared := shared) (maskBits := maskBits)
    (M := M) (K := K) S LB LN)
variable (encode : JointResponse.Response P R → Block)
variable (derive : BackendQueries.Parent g.roles Context Block Link g.batchingIndex →
  (Fin g.batchingIndex.val → C) → JointResponse.Statement P R)
variable (decodeCoin : C → JointResponse.Coin P R)
variable (decodeQuery : C → LigeroFamily.QuerySet n t)
variable (cutoff : ℕ × ℕ) (ε : ℚ)

local notation "Point" => Input g.roles Context Block Link Body
local notation "Parent" => BackendQueries.Parent g.roles Context Block Link g.batchingIndex
local notation "Response" => Link × JointResponse.Response P R

def single (point : Point) (H : Point → Link × C) (answer : Link × C) : ℚ :=
  PrefixConfiguration.single read point H answer +
    BackendOracle.single P R g.batchingIndex_next encode derive S.oracle decodeCoin decodeQuery
      cutoff ε point H answer

def pair (parent : Parent) (response : Response) (H : Point → Link × C) (a b : Link × C) : ℚ :=
  BackendFS.high P R derive S.oracle decodeCoin decodeQuery ε parent response H a b

def openingBudget : ℚ := ε + ((cutoff.1+s-1).choose t : ℚ)/n.choose t +
  ((cutoff.2+s-1).choose t : ℚ)/n.choose t

def budget (pc : ProfileParameters P.backend) (rc : ProfileParameters R.backend) (point : Point) : ℚ :=
  PrefixConfiguration.budget (B := B) (p := p) (M := M) (K := K) (LB := LB) (LN := LN) point +
    BackendOracle.singleBudget P R g.batchingIndex_next encode
      (pc.rankError+rc.rankError) (openingBudget (s := s) (n := n) (t := t) cutoff ε) point

def pairBudget (pc : HahnSystemCertificate P.backend) (rc : HahnSystemCertificate R.backend) : ℚ :=
  NonrecursiveFS.highBudget P.backend pc + NonrecursiveFS.highBudget R.backend rc

theorem single_nonneg (point : Point) (H : Point → Link × C) (answer : Link × C) :
    0 ≤ single P R S read encode derive decodeCoin decodeQuery cutoff ε point H answer :=
  add_nonneg (PrefixConfiguration.single_nonneg read point H answer)
    (BackendOracle.single_nonneg P R g.batchingIndex_next encode derive S.oracle
      decodeCoin decodeQuery cutoff ε point H answer)

omit [Fintype B] [Algebra (ZMod 2) B] [DecidableEq IB] [DecidableEq IN] [Fintype C] in
theorem pair_nonneg (parent : Parent) (response : Response)
    (H : Point → Link × C) (a b : Link × C) :
    0 ≤ pair P R S derive decodeCoin decodeQuery ε parent response H a b :=
  BackendFS.high_nonneg P R derive S.oracle decodeCoin decodeQuery ε parent response H a b

theorem single_off [DecidableEq (Input g.roles Context Block Link Body)]
    (hencode : Function.Injective encode) (point : Point) (H H' : Point → Link × C)
    (h : Bcs.TotalOracle.AgreeOff point H H') (answer : Link × C) :
    single P R S read encode derive decodeCoin decodeQuery cutoff ε point H answer =
      single P R S read encode derive decodeCoin decodeQuery cutoff ε point H' answer := by
  unfold single
  rw [PrefixConfiguration.single_off read point H H' h answer,
    BackendOracle.single_off P R g.batchingIndex_next encode hencode derive S.oracle
      decodeCoin decodeQuery cutoff ε S.oracle_off point H H' h answer]

omit [Fintype B] [Algebra (ZMod 2) B] [DecidableEq IB] [DecidableEq IN] [Fintype C] in
theorem pair_off [DecidableEq (Input g.roles Context Block Link Body)]
    (parent : Parent) (response : Response) (H H' : Point → Link × C)
    (h : ∀ z, z ≠ parent.point → z ≠ parent.child g.batchingIndex_next encode response → H z = H' z)
    (a b : Link × C) :
    pair P R S derive decodeCoin decodeQuery ε parent response H a b =
      pair P R S derive decodeCoin decodeQuery ε parent response H' a b :=
  BackendFS.high_off P R derive S.oracle decodeCoin decodeQuery ε S.oracle_off
    g.batchingIndex_next encode parent response H H' h a b

/-- A charge established by any actual application role remains charged in
the combined family. Backend contributions are nonnegative. -/
theorem application_charged (point : Point) (H : Point → Link × C) (answer : Link × C)
    (h : 1 ≤ PrefixConfiguration.single read point H answer) :
    1 ≤ single P R S read encode derive decodeCoin decodeQuery cutoff ε point H answer :=
  h.trans (le_add_of_nonneg_right (BackendOracle.single_nonneg P R g.batchingIndex_next
    encode derive S.oracle decodeCoin decodeQuery cutoff ε point H answer))

theorem backend_charged (point : Point) (H : Point → Link × C) (answer : Link × C)
    (h : 1 ≤ BackendOracle.single P R g.batchingIndex_next encode derive S.oracle
      decodeCoin decodeQuery cutoff ε point H answer) :
    1 ≤ single P R S read encode derive decodeCoin decodeQuery cutoff ε point H answer :=
  h.trans (le_add_of_nonneg_left (PrefixConfiguration.single_nonneg read point H answer))

theorem rank_charged (parent : Parent) (H : Point → Link × C) (answer : Link × C)
    (h : 1 ≤ BackendFS.rank P R S.oracle decodeCoin parent H answer) :
    1 ≤ single P R S read encode derive decodeCoin decodeQuery cutoff ε parent.point H answer := by
  apply backend_charged P R S read encode derive decodeCoin decodeQuery cutoff ε
  simpa only [BackendOracle.single_point] using h

theorem opening_charged (hencode : Function.Injective encode) (parent : Parent)
    (response : Response) (H : Point → Link × C) (answer : Link × C)
    (h : 1 ≤ BackendFS.opening P R derive S.oracle decodeCoin decodeQuery cutoff ε
      parent response H answer) :
    1 ≤ single P R S read encode derive decodeCoin decodeQuery cutoff ε
      (parent.child g.batchingIndex_next encode response) H answer := by
  apply backend_charged P R S read encode derive decodeCoin decodeQuery cutoff ε
  simpa only [BackendOracle.single_child P R g.batchingIndex_next encode hencode] using h

section Counts
variable [Fintype Link] [DecidableEq (JointResponse.Coin P R)]
variable (kCoin kQuery : ℕ)
variable (hcoin : ∀ coin, (univ.filter fun a : C => decodeCoin a = coin).card ≤ kCoin)
variable (hquery : ∀ query, (univ.filter fun a : C => decodeQuery a = query).card ≤ kQuery)
variable (hkCoin : kCoin*Fintype.card (JointResponse.Coin P R) ≤ Fintype.card C)
variable (hkQuery : kQuery*Fintype.card (LigeroFamily.QuerySet n t) ≤ Fintype.card C)

include kCoin kQuery hcoin hquery hkCoin hkQuery in
theorem single_sum (pc : ProfileParameters P.backend) (rc : ProfileParameters R.backend)
    (hε : 0 ≤ ε) (point : Point) (H : Point → Link × C) :
    (∑ answer, single P R S read encode derive decodeCoin decodeQuery cutoff ε point H answer) ≤
      Fintype.card (Link × C) * budget (B := B) (p := p) (M := M) (K := K)
        (LB := LB) (LN := LN) P R encode cutoff ε pc rc point := by
  have ha := PrefixConfiguration.single_sum read point H
  have hb := BackendOracle.single_sum P R g.batchingIndex_next encode derive S.oracle decodeCoin
    decodeQuery cutoff ε kCoin kQuery hcoin hquery hkCoin hkQuery pc rc hε point H
  simp only [single, sum_add_distrib]
  exact (add_le_add ha hb).trans_eq (by unfold budget openingBudget; ring)

omit [Fintype B] [Algebra (ZMod 2) B] [DecidableEq IB] [DecidableEq IN] in
include kCoin kQuery hcoin hquery hkCoin hkQuery in
theorem pair_sum [Nonempty C] (pc : HahnSystemCertificate P.backend) (rc : HahnSystemCertificate R.backend)
    (hp : pc.error ≤ ε) (hr : rc.error ≤ ε) (parent : Parent) (H : Point → Link × C) :
    (∑ response : Response, ∑ a : Link × C, ∑ b : Link × C,
      pair P R S derive decodeCoin decodeQuery ε parent response H a b) ≤
      (Fintype.card (Link × C) : ℚ)^2 * pairBudget P R pc rc :=
  BackendFS.high_sum P R derive S.oracle decodeCoin decodeQuery ε kCoin kQuery
    hcoin hquery hkCoin hkQuery pc rc hp hr parent H

omit [Fintype B] [Algebra (ZMod 2) B] [DecidableEq IB] [DecidableEq IN] in
include kCoin kQuery hcoin hquery hkCoin hkQuery in
/-- The active common-column family bounds all complete response pairs.
Its cardinality certificate is independent of the two committed-witness
list caps used by the earlier fingerprint exchange. -/
theorem pair_sum_active [Nonempty C] (pc : HahnSystemCertificate P.backend)
    (rc : ProfileParameters R.backend) (hθ : pc.threshold ≤ ε)
    (hactive : CodingTheory.UniformFamilyBound n pc.columnCutoff (k+2*s-1) pc.listBound)
    (hbound : pc.listBound ≤ Nat.card P.Carrier) (parent : Parent) (H : Point → Link × C) :
    (∑ response : Response, ∑ a : Link × C, ∑ b : Link × C,
      pair P R S derive decodeCoin decodeQuery ε parent response H a b) ≤
      (Fintype.card (Link × C) : ℚ)^2 * JointResponse.activeHighBudget P R pc :=
  BackendFS.high_sum_active P R derive S.oracle decodeCoin decodeQuery ε kCoin kQuery
    hcoin hquery hkCoin hkQuery pc rc hθ hactive hbound parent H

end Counts
end LfzkV2.Current.GlobalCharges

namespace LfzkV2.Current.GlobalCharges
open RecursivePolygero ProfileAnalysis Finset ApplicationCharging
open scoped Classical

variable {g : Geometry} {Context Block Link Body B : Type} [Fintype B]
variable {p M K LB LN k s n t : ℕ}
variable [Fintype Context] [Fintype Block] [Fintype Link]
variable [DecidableEq (Input g.roles Context Block Link Body)]

local notation "Point" => Input g.roles Context Block Link Body
local notation "Parent" => BackendQueries.Parent g.roles Context Block Link g.batchingIndex

/-- Public numerical bounds suffice to close the global role maximum.
At the backend's two actual positions the application dispatch is zero;
at every other position both backend contributions are zero. Thus these
inequalities are checked separately, without adding protocol budgets. -/
theorem point_budget_le (P R : Joint.Participant k s n t)
    (encode : JointResponse.Response P R → Block) (hencode : Function.Injective encode)
    (cutoff : ℕ × ℕ) (ε : ℚ)
    (pc : ProfileParameters P.backend) (rc : ProfileParameters R.backend)
    (highBudget total : ℚ)
    (happ : ∀ role, roundBudget B p M K LB LN role ≤ total)
    (hp : pc.rankError+rc.rankError+highBudget ≤ total)
    (ho : openingBudget (s := s) (n := n) (t := t) cutoff ε ≤ total)
    (ht : 0 ≤ total) (point : Point) :
    budget (B := B) (p := p) (M := M) (K := K) (LB := LB) (LN := LN)
        P R encode cutoff ε pc rc point +
      (∑ parent : Parent, if parent.point = point then highBudget else 0) ≤ total := by
  have hb := BackendOracle.point_budget P R g.batchingIndex_next encode
    (pc.rankError+rc.rankError) (openingBudget (s := s) (n := n) (t := t) cutoff ε)
    highBudget total hp ho ht point
  have hzero (h : point.rank = g.batchingIndex.val ∨ point.rank = g.openingIndex.val) :
      PrefixConfiguration.budget (B := B) (p := p) (M := M) (K := K)
        (LB := LB) (LN := LN) point = 0 := by
    cases point with
    | round i history block =>
        rcases h with h | h
        · have hi : i = g.batchingIndex := Fin.ext h
          subst i
          simp only [PrefixConfiguration.budget, g.get_batchingIndex, roundBudget]
        · have hi : i = g.openingIndex := Fin.ext h
          subst i
          simp only [PrefixConfiguration.budget, g.get_openingIndex, roundBudget]
    | finalSeal history body => rfl
  unfold budget
  by_cases hbatch : point.rank = g.batchingIndex.val
  · rw [hzero (Or.inl hbatch), zero_add]
    exact hb
  · by_cases hopen : point.rank = g.batchingIndex.val+1
    · rw [hzero (Or.inr (hopen.trans g.openingIndex_val.symm)), zero_add]
      exact hb
    · rw [BackendOracle.singleBudget_zero_of_rank P R g.batchingIndex_next encode hencode
        (pc.rankError+rc.rankError) (openingBudget (s := s) (n := n) (t := t) cutoff ε)
        point hbatch hopen]
      have hparent := BackendOracle.parent_mass (i := g.batchingIndex) highBudget point
      rw [BackendOracle.parentOf_none_of_rank point hbatch] at hparent
      rw [hparent, add_zero, add_zero]
      cases point with
      | round i history block => exact happ (g.roles.get i)
      | finalSeal history body => exact ht

end LfzkV2.Current.GlobalCharges
