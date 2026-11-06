import LfzkV2.Current.BackendFS

/-! Lift the local backend counts to arbitrary current oracle inputs.
Canonical decoding is the partial inverse of the actual parent/child encoding.
Its injectivity gives one complete response pair at each opening input, even
for adversarial query histories. Inputs outside these two roles cost zero. -/
noncomputable section
namespace LfzkV2.Current.BackendOracle
open RecursivePolygero Finset ProfileAnalysis
open scoped Classical

variable {k s n t : ℕ} (P R : Joint.Participant k s n t)
variable {roles : List Role} {Context Block Link Body C : Type}
variable {i : Fin roles.length} (next : i.val+1 < roles.length)
variable (encode : JointResponse.Response P R → Block)
variable (hencode : Function.Injective encode)

local notation "Point" => Input roles Context Block Link Body
local notation "Parent" => BackendQueries.Parent roles Context Block Link i
local notation "Response" => Link × JointResponse.Response P R

/-- Logical partial decoders. A successful decode retains the whole parent
prefix, the claimed parent link, and both participant payloads. -/
def parentOf (z : Point) : Option Parent := Function.partialInv BackendQueries.Parent.point z

def childOf (z : Point) : Option (Parent × Response) :=
  Function.partialInv (fun a : Parent × Response => a.1.child next encode a.2) z

theorem parentOf_point (parent : Parent) :
    parentOf (i := i) (parent.point (Body := Body)) = some parent :=
  Function.partialInv_left BackendQueries.Parent.point_injective parent

include hencode in
theorem childOf_child (parent : Parent) (response : Response) :
    childOf P R next encode (parent.child (Body := Body) next encode response) = some (parent,response) :=
  Function.partialInv_left (BackendQueries.Parent.child_injective next encode hencode) (parent,response)

theorem parentOf_spec {z : Point} {parent : Parent} (h : parentOf (i := i) z = some parent) :
    parent.point = z :=
  (BackendQueries.Parent.point_injective.isPartialInv parent z).mp h

include hencode in
theorem childOf_spec {z : Point} {a : Parent × Response}
    (h : childOf P R next encode z = some a) : a.1.child next encode a.2 = z :=
  ((BackendQueries.Parent.child_injective next encode hencode).isPartialInv a z).mp h

theorem point_ne_child (parent other : Parent) (response : Response) :
    parent.point ≠ other.child (Body := Body) next encode response := by
  intro heq
  have hr := congrArg Input.rank heq
  change i.val = i.val+1 at hr
  omega

theorem parentOf_child_none (parent : Parent) (response : Response) :
    parentOf (i := i) (parent.child (Body := Body) next encode response) = none := by
  cases h : parentOf (i := i) (parent.child (Body := Body) next encode response) with
  | none => rfl
  | some other => exact (point_ne_child P R next encode other parent response (parentOf_spec h)).elim

include hencode in
theorem childOf_point_none (parent : Parent) :
    childOf P R next encode (parent.point (Body := Body)) = none := by
  cases h : childOf P R next encode (parent.point (Body := Body)) with
  | none => rfl
  | some a => exact (point_ne_child P R next encode parent a.1 a.2
      (childOf_spec P R next encode hencode h).symm).elim


theorem parentOf_none_of_rank (z : Point) (h : z.rank ≠ i.val) :
    parentOf (i := i) z = none := by
  cases hp : parentOf (i := i) z with
  | none => rfl
  | some parent =>
      have he := congrArg Input.rank (parentOf_spec hp)
      exact (h he.symm).elim

include hencode in
theorem childOf_none_of_rank (z : Point) (h : z.rank ≠ i.val+1) :
    childOf P R next encode z = none := by
  cases hc : childOf P R next encode z with
  | none => rfl
  | some a =>
      have he := congrArg Input.rank (childOf_spec P R next encode hencode hc)
      exact (h he.symm).elim

variable (derive : BackendQueries.Parent roles Context Block Link i → (Fin i.val → C) → JointResponse.Statement P R)
variable (cutOracle : (Input roles Context Block Link Body → Link × C) → Context → JointResponse.Oracle P R)
variable (decodeCoin : C → JointResponse.Coin P R)
variable (decodeQuery : C → LigeroFamily.QuerySet n t)
variable (cutoff : ℕ × ℕ) (ε : ℚ)

/-- One single-answer charge, selected by the actual canonical preimage.
The two roles are disjoint by their boundary counters. -/
def single (z : Point) (H : Point → Link × C) (answer : Link × C) : ℚ :=
  match parentOf (i := i) z with
  | some parent => BackendFS.rank P R cutOracle decodeCoin parent H answer
  | none => match childOf P R next encode z with
    | some a => BackendFS.opening P R derive cutOracle decodeCoin decodeQuery cutoff ε a.1 a.2 H answer
    | none => 0

def singleBudget (rankBudget openingBudget : ℚ) (z : Point) : ℚ :=
  match parentOf (i := i) z with
  | some _ => rankBudget
  | none => match childOf P R next encode z with
    | some _ => openingBudget
    | none => 0

theorem single_point (parent : Parent) (H : Point → Link × C) (answer : Link × C) :
    single P R next encode derive cutOracle decodeCoin decodeQuery cutoff ε parent.point H answer =
      BackendFS.rank P R cutOracle decodeCoin parent H answer := by
  simp only [single, parentOf_point]

include hencode in
theorem single_child (parent : Parent) (response : Response)
    (H : Point → Link × C) (answer : Link × C) :
    single P R next encode derive cutOracle decodeCoin decodeQuery cutoff ε
        (parent.child next encode response) H answer =
      BackendFS.opening P R derive cutOracle decodeCoin decodeQuery cutoff ε parent response H answer := by
  simp only [single, parentOf_child_none, childOf_child P R next encode hencode]

theorem single_nonneg (z : Point) (H : Point → Link × C) (answer : Link × C) :
    0 ≤ single P R next encode derive cutOracle decodeCoin decodeQuery cutoff ε z H answer := by
  unfold single
  split
  · exact BackendFS.rank_nonneg ..
  · split
    · exact BackendFS.opening_nonneg ..
    · exact le_rfl


include hencode in
theorem single_zero_of_rank (z : Point) (hparent : z.rank ≠ i.val)
    (hchild : z.rank ≠ i.val+1) (H : Point → Link × C) (answer : Link × C) :
    single P R next encode derive cutOracle decodeCoin decodeQuery cutoff ε z H answer = 0 := by
  simp only [single, parentOf_none_of_rank z hparent,
    childOf_none_of_rank P R next encode hencode z hchild]

include hencode in
theorem singleBudget_zero_of_rank (rankBudget openingBudget : ℚ) (z : Point)
    (hparent : z.rank ≠ i.val) (hchild : z.rank ≠ i.val+1) :
    singleBudget P R next encode rankBudget openingBudget z = 0 := by
  simp only [singleBudget, parentOf_none_of_rank z hparent,
    childOf_none_of_rank P R next encode hencode z hchild]

variable [DecidableEq (Input roles Context Block Link Body)]
variable (cutOff : ∀ z H H', Bcs.TotalOracle.AgreeOff z H H' →
  cutOracle H z.context = cutOracle H' z.context)

include cutOff hencode in
theorem single_off (z : Point) (H H' : Point → Link × C)
    (h : Bcs.TotalOracle.AgreeOff z H H') (answer : Link × C) :
    single P R next encode derive cutOracle decodeCoin decodeQuery cutoff ε z H answer =
      single P R next encode derive cutOracle decodeCoin decodeQuery cutoff ε z H' answer := by
  cases hp : parentOf (i := i) z with
  | some parent =>
      have he := parentOf_spec hp
      simp only [single, hp]
      apply BackendFS.rank_off P R cutOracle decodeCoin cutOff parent H H'
      simpa only [he] using h
  | none =>
      cases hc : childOf P R next encode z with
      | some a =>
          have he := childOf_spec P R next encode hencode hc
          simp only [single, hp, hc]
          apply BackendFS.opening_off P R derive cutOracle decodeCoin decodeQuery cutoff ε cutOff
            next encode a.1 a.2 H H'
          simpa only [he] using h
      | none => simp only [single, hp, hc]

section Counts
variable [Fintype Link] [Fintype C] [DecidableEq (JointResponse.Coin P R)]
variable (kCoin kQuery : ℕ)
variable (hcoin : ∀ coin, (univ.filter fun a : C => decodeCoin a = coin).card ≤ kCoin)
variable (hquery : ∀ Q, (univ.filter fun a : C => decodeQuery a = Q).card ≤ kQuery)
variable (hkCoin : kCoin*Fintype.card (JointResponse.Coin P R) ≤ Fintype.card C)
variable (hkQuery : kQuery*Fintype.card (LigeroFamily.QuerySet n t) ≤ Fintype.card C)

omit [DecidableEq (Input roles Context Block Link Body)] in
include kCoin kQuery hcoin hquery hkCoin hkQuery in
/-- Decoding an opening query fixes exactly one full response. The raw bound
therefore contains no multiplier for the number of possible responses. -/
theorem single_sum (p : ProfileParameters P.backend) (r : ProfileParameters R.backend)
    (hε : 0 ≤ ε) (z : Point) (H : Point → Link × C) :
    (∑ a : Link × C, single P R next encode derive cutOracle decodeCoin decodeQuery cutoff ε z H a) ≤
      Fintype.card (Link × C) * singleBudget P R next encode
        (p.rankError+r.rankError)
        (ε+((cutoff.1+s-1).choose t : ℚ)/n.choose t+((cutoff.2+s-1).choose t : ℚ)/n.choose t) z := by
  cases hp : parentOf (i := i) z with
  | some parent =>
      simp only [single, singleBudget, hp]
      exact BackendFS.rank_sum P R cutOracle decodeCoin kCoin hcoin hkCoin p r parent H
  | none =>
      cases hc : childOf P R next encode z with
      | some a =>
          simp only [single, singleBudget, hp, hc]
          exact BackendFS.opening_sum P R derive cutOracle decodeCoin decodeQuery cutoff ε
            kQuery hquery hkQuery hε a.1 a.2 H
      | none => simp only [single, singleBudget, hp, hc, sum_const_zero, mul_zero, le_refl]

end Counts

section ParentMass
variable [Fintype Context] [Fintype Block] [Fintype Link]

theorem parent_mass (highBudget : ℚ) (z : Point) :
    (∑ parent : Parent, if parent.point = z then highBudget else 0) =
      match parentOf (i := i) z with | some _ => highBudget | none => 0 := by
  cases hp : parentOf (i := i) z with
  | some parent =>
      have he := parentOf_spec hp
      have hi (other : Parent) : other.point = z ↔ other = parent := by
        rw [← he]
        exact BackendQueries.Parent.point_injective.eq_iff
      simp only [hi, sum_ite_eq', mem_univ, if_true]
  | none =>
      have hn (parent : Parent) : parent.point ≠ z := by
        intro he
        have hs := parentOf_point (Body := Body) parent
        rw [he, hp] at hs
        contradiction
      simp only [hn, if_false, sum_const_zero]

/-- Shared charging puts the high-response mass at its unique parent.
Consequently the local coefficient is the larger of parent and opening costs. -/
theorem point_budget (rankBudget openingBudget highBudget total : ℚ)
    (hp : rankBudget+highBudget ≤ total) (ho : openingBudget ≤ total) (ht : 0 ≤ total)
    (z : Point) :
    singleBudget P R next encode rankBudget openingBudget z +
      (∑ parent : Parent, if parent.point = z then highBudget else 0) ≤ total := by
  rw [parent_mass]
  cases hparent : parentOf (i := i) z with
  | some _ => simpa only [singleBudget, hparent] using hp
  | none =>
      cases hchild : childOf P R next encode z with
      | some _ => simpa only [singleBudget, hparent, hchild, add_zero] using ho
      | none => simpa only [singleBudget, hparent, hchild, zero_add] using ht

end ParentMass

end LfzkV2.Current.BackendOracle
