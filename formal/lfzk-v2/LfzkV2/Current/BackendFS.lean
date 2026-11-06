import LfzkV2.Current.BackendQueries
import LfzkV2.Current.BackendCharges

/-! Concrete charges at the current adjacent joint-backend boundaries.
The statement is reconstructed strictly before batching. The committed tuple
oracle is recovered from the cut belonging to that same prefix. A child names
both complete responses and the parent link; the opening set is shared. -/
noncomputable section
namespace LfzkV2.Current.BackendFS
open RecursivePolygero Finset ProfileAnalysis
open scoped Classical

variable {k s n t : ℕ} (P R : Joint.Participant k s n t)
variable {roles : List Role} {Context Block Link Body C : Type}
variable {i : Fin roles.length}

abbrev Point := Input roles Context Block Link Body
abbrev Parent := BackendQueries.Parent roles Context Block Link i
abbrev Response := Link × JointResponse.Response P R

instance parentFintype [Fintype Context] [Fintype Block] [Fintype Link] :
    Fintype (Parent (roles := roles) (Context := Context) (Block := Block)
      (Link := Link) (i := i)) :=
  Fintype.ofEquiv (History Context Block Link i.val × Block) {
    toFun := fun a => ⟨a.1,a.2⟩
    invFun := fun p => (p.history,p.block)
    left_inv := fun a => by cases a; rfl
    right_inv := fun p => by cases p; rfl }

variable (derive : Parent (roles := roles) (Context := Context) (Block := Block)
    (Link := Link) (i := i) → (Fin i.val → C) → JointResponse.Statement P R)
variable (cutOracle : (Point (roles := roles) (Context := Context) (Block := Block)
    (Link := Link) (Body := Body) → Link × C) → Context → JointResponse.Oracle P R)
variable (decodeCoin : C → JointResponse.Coin P R)
variable (decodeQuery : C → LigeroFamily.QuerySet n t)
variable (cutoff : ℕ × ℕ) (ε : ℚ)

/-- Rank is charged at the batching preimage. It reads no batching answer
through the recovered oracle: its only such dependence is the explicit coin. -/
def rank (parent : Parent (roles := roles) (Context := Context) (Block := Block)
    (Link := Link) (i := i)) (H : Point (roles := roles) (Context := Context) (Block := Block) (Link := Link) (Body := Body) → Link × C)
    (answer : Link × C) : ℚ :=
  JointResponse.rankCharge P R (cutOracle H (parent.point (Body := Body)).context) (decodeCoin answer.2)

/-- A fixed complete child response has one low-acceptance/outside-list
budget. Its parent's answer is already fixed when the opening answer varies. -/
def opening (parent : Parent (roles := roles) (Context := Context) (Block := Block)
    (Link := Link) (i := i)) (response : Response P R (Link := Link))
    (H : Point (roles := roles) (Context := Context) (Block := Block) (Link := Link) (Body := Body) → Link × C) (answer : Link × C) : ℚ :=
  JointResponse.openingCharge P R (parent.statement derive H)
    (cutOracle H (parent.point (Body := Body)).context) (decodeCoin (H parent.point).2)
    response.2 cutoff ε (decodeQuery answer.2)

/-- Summing this charge retains the complete two-field response and the
claimed parent link. The link test prevents an extra factor from link choices. -/
def high (parent : Parent (roles := roles) (Context := Context) (Block := Block)
    (Link := Link) (i := i)) (response : Response P R (Link := Link))
    (H : Point (roles := roles) (Context := Context) (Block := Block) (Link := Link) (Body := Body) → Link × C) (a b : Link × C) : ℚ :=
  JointResponse.highCharge P R (parent.statement derive H)
    (cutOracle H (parent.point (Body := Body)).context) response ε a.1 (decodeCoin a.2) (decodeQuery b.2)

variable [DecidableEq (Point (roles := roles) (Context := Context) (Block := Block)
    (Link := Link) (Body := Body))]
variable (cutOff : ∀ z H H', Bcs.TotalOracle.AgreeOff z H H' →
  cutOracle H z.context = cutOracle H' z.context)

omit [DecidableEq (Point (roles := roles) (Context := Context) (Block := Block)
    (Link := Link) (Body := Body))] in
include cutOff in
theorem rank_off (parent : Parent (roles := roles) (Context := Context) (Block := Block)
    (Link := Link) (i := i)) (H H' : Point (roles := roles) (Context := Context) (Block := Block) (Link := Link) (Body := Body) → Link × C)
    (h : Bcs.TotalOracle.AgreeOff parent.point H H') (answer : Link × C) :
    rank P R cutOracle decodeCoin parent H answer =
      rank P R cutOracle decodeCoin parent H' answer := by
  unfold rank
  rw [cutOff parent.point H H' h]

include cutOff in
theorem opening_off (next : i.val+1 < roles.length)
    (encode : JointResponse.Response P R → Block)
    (parent : Parent (roles := roles) (Context := Context) (Block := Block)
      (Link := Link) (i := i)) (response : Response P R (Link := Link))
    (H H' : Point (roles := roles) (Context := Context) (Block := Block) (Link := Link) (Body := Body) → Link × C)
    (h : Bcs.TotalOracle.AgreeOff (parent.child next encode response) H H')
    (answer : Link × C) :
    opening P R derive cutOracle decodeCoin decodeQuery cutoff ε parent response H answer =
      opening P R derive cutOracle decodeCoin decodeQuery cutoff ε parent response H' answer := by
  have htwo : ∀ z, z ≠ parent.point → z ≠ parent.child next encode response → H z = H' z :=
    fun z _ hz => h z hz
  have hs := parent.statement_off derive next encode response H H' htwo
  have hw := parent.oracle_off cutOracle cutOff next encode response H H' htwo
  have hp := h parent.point (parent.point_ne_child next encode response)
  simp only [opening, hs, hw, hp]

include cutOff in
theorem high_off (next : i.val+1 < roles.length)
    (encode : JointResponse.Response P R → Block)
    (parent : Parent (roles := roles) (Context := Context) (Block := Block)
      (Link := Link) (i := i)) (response : Response P R (Link := Link))
    (H H' : Point (roles := roles) (Context := Context) (Block := Block) (Link := Link) (Body := Body) → Link × C)
    (h : ∀ z, z ≠ parent.point → z ≠ parent.child next encode response → H z = H' z)
    (a b : Link × C) :
    high P R derive cutOracle decodeCoin decodeQuery ε parent response H a b =
      high P R derive cutOracle decodeCoin decodeQuery ε parent response H' a b := by
  have hs := parent.statement_off derive next encode response H H' h
  have hw := parent.oracle_off cutOracle cutOff next encode response H H' h
  simp only [high, hs, hw]

omit [DecidableEq (Point (roles := roles) (Context := Context) (Block := Block)
    (Link := Link) (Body := Body))] in
theorem rank_nonneg (parent : Parent (roles := roles) (Context := Context) (Block := Block)
    (Link := Link) (i := i)) (H : Point (roles := roles) (Context := Context) (Block := Block) (Link := Link) (Body := Body) → Link × C) (a : Link × C) :
    0 ≤ rank P R cutOracle decodeCoin parent H a :=
  JointResponse.rankCharge_nonneg ..

omit [DecidableEq (Point (roles := roles) (Context := Context) (Block := Block)
    (Link := Link) (Body := Body))] in
theorem opening_nonneg (parent : Parent (roles := roles) (Context := Context) (Block := Block)
    (Link := Link) (i := i)) (response : Response P R (Link := Link))
    (H : Point (roles := roles) (Context := Context) (Block := Block) (Link := Link) (Body := Body) → Link × C) (a : Link × C) :
    0 ≤ opening P R derive cutOracle decodeCoin decodeQuery cutoff ε parent response H a :=
  JointResponse.openingCharge_nonneg ..

omit [DecidableEq (Point (roles := roles) (Context := Context) (Block := Block)
    (Link := Link) (Body := Body))] in
theorem high_nonneg (parent : Parent (roles := roles) (Context := Context) (Block := Block)
    (Link := Link) (i := i)) (response : Response P R (Link := Link))
    (H : Point (roles := roles) (Context := Context) (Block := Block) (Link := Link) (Body := Body) → Link × C) (a b : Link × C) :
    0 ≤ high P R derive cutOracle decodeCoin decodeQuery ε parent response H a b :=
  JointResponse.highCharge_nonneg ..

omit [DecidableEq (Point (roles := roles) (Context := Context) (Block := Block)
    (Link := Link) (Body := Body))] in
/-- The arithmetic failure cover is applied to the two actual adjacent
answers. The child contains the parent's actual link along an accepted replay. -/
theorem failure_charged (next : i.val+1 < roles.length)
    (encode : JointResponse.Response P R → Block)
    (parent : Parent (roles := roles) (Context := Context) (Block := Block)
      (Link := Link) (i := i)) (response : Response P R (Link := Link))
    (H : Point (roles := roles) (Context := Context) (Block := Block) (Link := Link) (Body := Body) → Link × C)
    (hlink : response.1 = (H parent.point).1)
    (hv : JointResponse.Verify P R (parent.statement derive H)
      (cutOracle H (parent.point (Body := Body)).context) (decodeCoin (H parent.point).2)
      response.2 (decodeQuery (H (parent.child next encode response)).2))
    (hf : JointResponse.failure P R (parent.statement derive H)
        (cutOracle H (parent.point (Body := Body)).context) (decodeCoin (H parent.point).2) response.2 ∨
      NonrecursiveFS.decodedOutsideList P.backend (parent.statement derive H).1
        (cutOracle H (parent.point (Body := Body)).context).1
        (decodeCoin (H parent.point).2).1 response.2.1 cutoff.1 ∨
      NonrecursiveFS.decodedOutsideList R.backend (parent.statement derive H).2
        (cutOracle H (parent.point (Body := Body)).context).2
        (decodeCoin (H parent.point).2).2 response.2.2 cutoff.2) :
    1 ≤ rank P R cutOracle decodeCoin parent H (H parent.point) ∨
      1 ≤ opening P R derive cutOracle decodeCoin decodeQuery cutoff ε parent response H
        (H (parent.child next encode response)) ∨
      1 ≤ high P R derive cutOracle decodeCoin decodeQuery ε parent response H
        (H parent.point) (H (parent.child next encode response)) := by
  have h := JointResponse.failure_charged P R (parent.statement derive H)
    (cutOracle H (parent.point (Body := Body)).context) (decodeCoin (H parent.point).2)
    response.2 cutoff ε (decodeQuery (H (parent.child next encode response)).2)
    (H parent.point).1 hv hf
  simpa only [rank, opening, high, JointResponse.highCharge, hlink] using h

section Raw
variable [Fintype Link] [Fintype C] [Nonempty C] [DecidableEq (JointResponse.Coin P R)]
variable (kCoin kQuery : ℕ)
variable (hcoin : ∀ coin, (univ.filter fun a : C => decodeCoin a = coin).card ≤ kCoin)
variable (hquery : ∀ Q, (univ.filter fun a : C => decodeQuery a = Q).card ≤ kQuery)
variable (hkCoin : kCoin*Fintype.card (JointResponse.Coin P R) ≤ Fintype.card C)
variable (hkQuery : kQuery*Fintype.card (LigeroFamily.QuerySet n t) ≤ Fintype.card C)

omit [DecidableEq (Point (roles := roles) (Context := Context) (Block := Block)
    (Link := Link) (Body := Body))] [Nonempty C] in
include kCoin hcoin hkCoin in
theorem rank_sum (p : ProfileParameters P.backend) (r : ProfileParameters R.backend)
    (parent : Parent (roles := roles) (Context := Context) (Block := Block)
      (Link := Link) (i := i))
    (H : Point (roles := roles) (Context := Context) (Block := Block) (Link := Link) (Body := Body) → Link × C) :
    (∑ a : Link × C, rank P R cutOracle decodeCoin parent H a) ≤
      Fintype.card (Link × C) * (p.rankError+r.rankError) := by
  have h := JointResponse.rankCharge_sum P R decodeCoin kCoin hcoin hkCoin p r
    (cutOracle H (parent.point (Body := Body)).context)
  calc
    _ = (Fintype.card Link : ℚ) * ∑ a : C,
        JointResponse.rankCharge P R (cutOracle H (parent.point (Body := Body)).context)
          (decodeCoin a) := by
      simp only [Fintype.sum_prod_type, rank, sum_const, nsmul_eq_mul, card_univ]
    _ ≤ (Fintype.card Link : ℚ) * (Fintype.card C * (p.rankError+r.rankError)) :=
      mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)
    _ = _ := by simp only [Fintype.card_prod, Nat.cast_mul]; ring

omit [DecidableEq (Point (roles := roles) (Context := Context) (Block := Block)
    (Link := Link) (Body := Body))] [Nonempty C] [DecidableEq (JointResponse.Coin P R)] in
include kQuery hquery hkQuery in
theorem opening_sum (hε : 0 ≤ ε)
    (parent : Parent (roles := roles) (Context := Context) (Block := Block)
      (Link := Link) (i := i)) (response : Response P R (Link := Link))
    (H : Point (roles := roles) (Context := Context) (Block := Block) (Link := Link) (Body := Body) → Link × C) :
    (∑ a : Link × C, opening P R derive cutOracle decodeCoin decodeQuery cutoff ε parent response H a) ≤
      Fintype.card (Link × C) *
        (ε + ((cutoff.1+s-1).choose t : ℚ)/n.choose t +
          ((cutoff.2+s-1).choose t : ℚ)/n.choose t) := by
  have h := JointResponse.openingCharge_sum P R decodeQuery kQuery hquery hkQuery
    (parent.statement derive H) (cutOracle H (parent.point (Body := Body)).context)
    (decodeCoin (H parent.point).2) response.2 cutoff ε hε
  calc
    _ = (Fintype.card Link : ℚ) * ∑ a : C,
        JointResponse.openingCharge P R (parent.statement derive H)
          (cutOracle H (parent.point (Body := Body)).context) (decodeCoin (H parent.point).2)
          response.2 cutoff ε (decodeQuery a) := by
      simp only [Fintype.sum_prod_type, opening, sum_const, nsmul_eq_mul, card_univ]
    _ ≤ (Fintype.card Link : ℚ) * (Fintype.card C * _) :=
      mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)
    _ = _ := by simp only [Fintype.card_prod, Nat.cast_mul]; ring

omit [DecidableEq (Point (roles := roles) (Context := Context) (Block := Block)
    (Link := Link) (Body := Body))] in
include kCoin kQuery hcoin hquery hkCoin hkQuery in
theorem high_sum (p : HahnSystemCertificate P.backend) (r : HahnSystemCertificate R.backend)
    (hp : p.error ≤ ε) (hr : r.error ≤ ε)
    (parent : Parent (roles := roles) (Context := Context) (Block := Block)
      (Link := Link) (i := i))
    (H : Point (roles := roles) (Context := Context) (Block := Block) (Link := Link) (Body := Body) → Link × C) :
    (∑ response : Response P R (Link := Link), ∑ a : Link × C, ∑ b : Link × C,
      high P R derive cutOracle decodeCoin decodeQuery ε parent response H a b) ≤
      (Fintype.card (Link × C) : ℚ)^2 *
        (NonrecursiveFS.highBudget P.backend p + NonrecursiveFS.highBudget R.backend r) :=
  JointResponse.highCharge_sum P R decodeCoin decodeQuery kCoin kQuery hcoin hquery hkCoin hkQuery
    p r (parent.statement derive H) (cutOracle H (parent.point (Body := Body)).context) ε hp hr

omit [DecidableEq (Point (roles := roles) (Context := Context) (Block := Block)
    (Link := Link) (Body := Body))] in
include kCoin kQuery hcoin hquery hkCoin hkQuery in
theorem high_sum_joint (p : HahnSystemCertificate P.backend) (r : HahnSystemCertificate R.backend)
    (hp : p.error ≤ ε) (hr : r.error ≤ ε)
    (parent : Parent (roles := roles) (Context := Context) (Block := Block)
      (Link := Link) (i := i))
    (H : Point (roles := roles) (Context := Context) (Block := Block) (Link := Link) (Body := Body) → Link × C) :
    (∑ response : Response P R (Link := Link), ∑ a : Link × C, ∑ b : Link × C,
      high P R derive cutOracle decodeCoin decodeQuery ε parent response H a b) ≤
      (Fintype.card (Link × C) : ℚ)^2*JointResponse.jointHighBudget P R p :=
  JointResponse.highCharge_sum_joint P R decodeCoin decodeQuery kCoin kQuery hcoin hquery hkCoin hkQuery
    p r (parent.statement derive H) (cutOracle H (parent.point (Body := Body)).context) ε hp hr

omit [DecidableEq (Point (roles := roles) (Context := Context) (Block := Block)
    (Link := Link) (Body := Body))] in
include kCoin kQuery hcoin hquery hkCoin hkQuery in
theorem high_sum_active (p : HahnSystemCertificate P.backend) (r : ProfileParameters R.backend)
    (hθ : p.threshold ≤ ε)
    (hactive : CodingTheory.UniformFamilyBound n p.columnCutoff (k+2*s-1) p.listBound)
    (hbound : p.listBound ≤ Nat.card P.Carrier)
    (parent : Parent (roles := roles) (Context := Context) (Block := Block)
      (Link := Link) (i := i))
    (H : Point (roles := roles) (Context := Context) (Block := Block) (Link := Link) (Body := Body) → Link × C) :
    (∑ response : Response P R (Link := Link), ∑ a : Link × C, ∑ b : Link × C,
      high P R derive cutOracle decodeCoin decodeQuery ε parent response H a b) ≤
      (Fintype.card (Link × C) : ℚ)^2*JointResponse.activeHighBudget P R p :=
  JointResponse.highCharge_sum_active P R decodeCoin decodeQuery kCoin kQuery hcoin hquery hkCoin hkQuery
    p r (parent.statement derive H) (cutOracle H (parent.point (Body := Body)).context) ε hθ hactive hbound

end Raw

/-- The high-response charge is added to rank at its parent, rather than
assigned another independent query budget. -/
theorem parent_budget (p : HahnSystemCertificate P.backend) (r : HahnSystemCertificate R.backend)
    (hp : p.rankError ≤ 1/(Nat.card P.Carrier : ℚ))
    (hr : r.rankError ≤ 1/(Nat.card R.Carrier : ℚ)) :
    (p.rankError+r.rankError) +
      (NonrecursiveFS.highBudget P.backend p + NonrecursiveFS.highBudget R.backend r) ≤
        p.error+r.error := by
  have hP := NonrecursiveFS.rank_high_le_error P.backend p hp
  have hR := NonrecursiveFS.rank_high_le_error R.backend r hr
  linarith

end LfzkV2.Current.BackendFS
