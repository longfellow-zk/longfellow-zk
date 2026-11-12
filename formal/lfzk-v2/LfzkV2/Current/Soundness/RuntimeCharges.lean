import LfzkV2.Current.GlobalCharges
import LfzkV2.Current.RuntimeAdaptiveCharges

/-! One shared local maximum for adaptively parsed application statements
and the adjacent joint backend. Public values are fixed by each query's own
prefix; no fixed-public probability union is used. -/
noncomputable section
namespace LfzkV2.Current.Soundness.RuntimeCharges
open Application ApplicationSetup ApplicationOracle RecursivePolygero ProfileAnalysis Finset
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice Base Key C B Salt : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B] [Fintype C]
variable {shared maskBits adviceBits k s n t : ℕ}
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable {binary : BinaryPublic B shared maskBits adviceBits}
variable {prime : PrimePublic N shared}
variable {P : FieldBackend B k s n t} {R : FieldBackend N k s n t}
variable {cfg : RuntimeVerifier.Public (g := g) binary prime P R (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key) (C := C) (Salt := Salt)}
variable {S : RuntimeCover.Source (g := g) (fields := fields) (Advice := Advice) (Base := Base)
  (Key := Key) (C := C) binary prime (Oracle := JointResponse.Oracle (RuntimeVerifier.first binary prime P R cfg).participant (RuntimeVerifier.second binary prime P R cfg).participant)} {LB LN : ℕ}
variable (laws : RuntimeCover.SamplerLaws binary prime P R cfg S)
variable (readers : RuntimeAdaptiveCharges.Readers (g := g) (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key) (C := C) binary prime)
variable (encode : JointResponse.Response (RuntimeVerifier.first binary prime P R cfg).participant (RuntimeVerifier.second binary prime P R cfg).participant → (RuntimeVerifier.Block (g := g) (fields := fields) (Advice := Advice) (Base := Base)))
variable (derive : (BackendQueries.Parent g.roles Key (RuntimeVerifier.Block (g := g) (fields := fields) (Advice := Advice) (Base := Base)) Digest g.batchingIndex) → (Fin g.batchingIndex.val → C) → JointResponse.Statement (RuntimeVerifier.first binary prime P R cfg).participant (RuntimeVerifier.second binary prime P R cfg).participant)
variable (decodeCoin : C → JointResponse.Coin (RuntimeVerifier.first binary prime P R cfg).participant (RuntimeVerifier.second binary prime P R cfg).participant)
variable (decodeQuery : C → LigeroFamily.QuerySet n t)
variable (cutoff : ℕ × ℕ) (ε : ℚ)

def single (point : (RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key))) (H : (RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key)) → Digest × C) (answer : Digest × C) : ℚ :=
  RuntimeAdaptiveCharges.single S laws readers point H answer + BackendOracle.single (RuntimeVerifier.first binary prime P R cfg).participant (RuntimeVerifier.second binary prime P R cfg).participant g.batchingIndex_next encode derive
    S.oracle decodeCoin decodeQuery cutoff ε point H answer

def pair (parent : (BackendQueries.Parent g.roles Key (RuntimeVerifier.Block (g := g) (fields := fields) (Advice := Advice) (Base := Base)) Digest g.batchingIndex)) (response : (Digest × JointResponse.Response (RuntimeVerifier.first binary prime P R cfg).participant (RuntimeVerifier.second binary prime P R cfg).participant)) (H : (RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key)) → Digest × C)
    (a b : Digest × C) : ℚ :=
  BackendFS.high (RuntimeVerifier.first binary prime P R cfg).participant (RuntimeVerifier.second binary prime P R cfg).participant derive S.oracle decodeCoin decodeQuery ε parent response H a b

def budget (pc : ProfileParameters (RuntimeVerifier.first binary prime P R cfg).participant.backend) (rc : ProfileParameters (RuntimeVerifier.second binary prime P R cfg).participant.backend)
    (point : (RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key))) : ℚ :=
  RuntimeAdaptiveCharges.budget (B := B) LB LN point + BackendOracle.singleBudget (RuntimeVerifier.first binary prime P R cfg).participant (RuntimeVerifier.second binary prime P R cfg).participant g.batchingIndex_next encode
    (pc.rankError+rc.rankError) (GlobalCharges.openingBudget (s := s) (n := n) (t := t) cutoff ε) point

theorem single_nonneg (point : (RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key))) (H : (RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key)) → Digest × C) (answer : Digest × C) :
    0 ≤ single laws readers encode derive decodeCoin decodeQuery cutoff ε point H answer :=
  add_nonneg (RuntimeAdaptiveCharges.single_nonneg S laws readers point H answer)
    (BackendOracle.single_nonneg (RuntimeVerifier.first binary prime P R cfg).participant (RuntimeVerifier.second binary prime P R cfg).participant g.batchingIndex_next encode derive S.oracle
      decodeCoin decodeQuery cutoff ε point H answer)

theorem single_off (hencode : Function.Injective encode) (point : (RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key))) (H H' : (RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key)) → Digest × C)
    (h : Bcs.TotalOracle.AgreeOff point H H') (answer : Digest × C) :
    single laws readers encode derive decodeCoin decodeQuery cutoff ε point H answer =
      single laws readers encode derive decodeCoin decodeQuery cutoff ε point H' answer := by
  unfold single
  rw [RuntimeAdaptiveCharges.single_off S laws readers point H H' h answer,
    BackendOracle.single_off (RuntimeVerifier.first binary prime P R cfg).participant (RuntimeVerifier.second binary prime P R cfg).participant g.batchingIndex_next encode hencode derive S.oracle
      decodeCoin decodeQuery cutoff ε S.oracle_off point H H' h answer]

omit [Fintype C] in
theorem pair_nonneg (parent : (BackendQueries.Parent g.roles Key (RuntimeVerifier.Block (g := g) (fields := fields) (Advice := Advice) (Base := Base)) Digest g.batchingIndex)) (response : (Digest × JointResponse.Response (RuntimeVerifier.first binary prime P R cfg).participant (RuntimeVerifier.second binary prime P R cfg).participant)) (H : (RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key)) → Digest × C)
    (a b : Digest × C) : 0 ≤ pair (S := S) derive decodeCoin decodeQuery ε parent response H a b :=
  BackendFS.high_nonneg (RuntimeVerifier.first binary prime P R cfg).participant (RuntimeVerifier.second binary prime P R cfg).participant derive S.oracle decodeCoin decodeQuery ε parent response H a b

omit [Fintype C] in
theorem pair_off (parent : (BackendQueries.Parent g.roles Key (RuntimeVerifier.Block (g := g) (fields := fields) (Advice := Advice) (Base := Base)) Digest g.batchingIndex)) (response : (Digest × JointResponse.Response (RuntimeVerifier.first binary prime P R cfg).participant (RuntimeVerifier.second binary prime P R cfg).participant)) (H H' : (RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key)) → Digest × C)
    (h : ∀ z, z ≠ parent.point → z ≠ parent.child g.batchingIndex_next encode response → H z = H' z)
    (a b : Digest × C) :
    pair (S := S) derive decodeCoin decodeQuery ε parent response H a b =
      pair (S := S) derive decodeCoin decodeQuery ε parent response H' a b :=
  BackendFS.high_off (RuntimeVerifier.first binary prime P R cfg).participant (RuntimeVerifier.second binary prime P R cfg).participant derive S.oracle decodeCoin decodeQuery ε S.oracle_off
    g.batchingIndex_next encode parent response H H' h a b

theorem application_charged (point : (RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key))) (H : (RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key)) → Digest × C) (answer : Digest × C)
    (h : 1 ≤ RuntimeAdaptiveCharges.single S laws readers point H answer) :
    1 ≤ single laws readers encode derive decodeCoin decodeQuery cutoff ε point H answer :=
  h.trans (le_add_of_nonneg_right (BackendOracle.single_nonneg (RuntimeVerifier.first binary prime P R cfg).participant (RuntimeVerifier.second binary prime P R cfg).participant g.batchingIndex_next
    encode derive S.oracle decodeCoin decodeQuery cutoff ε point H answer))

theorem backend_charged (point : (RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key))) (H : (RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key)) → Digest × C) (answer : Digest × C)
    (h : 1 ≤ BackendOracle.single (RuntimeVerifier.first binary prime P R cfg).participant (RuntimeVerifier.second binary prime P R cfg).participant g.batchingIndex_next encode derive S.oracle
      decodeCoin decodeQuery cutoff ε point H answer) :
    1 ≤ single laws readers encode derive decodeCoin decodeQuery cutoff ε point H answer :=
  h.trans (le_add_of_nonneg_left (RuntimeAdaptiveCharges.single_nonneg S laws readers point H answer))

section Counts
variable (binaryListBound : ∀ (point : RuntimeVerifier.Point (g := g) (fields := fields)
  (Advice := Advice) (Base := Base) (Key := Key)) H,
  (S.lists point.context (S.oracle H point.context)).1.card ≤ LB)
variable (primeListBound : ∀ (point : RuntimeVerifier.Point (g := g) (fields := fields)
  (Advice := Advice) (Base := Base) (Key := Key)) H,
  (S.lists point.context (S.oracle H point.context)).2.card ≤ LN)
variable (coinDecoder : BalancedDecoder C (JointResponse.Coin (RuntimeVerifier.first binary prime P R cfg).participant (RuntimeVerifier.second binary prime P R cfg).participant))
variable (queryDecoder : BalancedDecoder C (LigeroFamily.QuerySet n t))
variable (hcoinDecode : coinDecoder.decode = decodeCoin) (hqueryDecode : queryDecoder.decode = decodeQuery)

include binaryListBound primeListBound coinDecoder queryDecoder hcoinDecode hqueryDecode in
theorem single_sum (pc : ProfileParameters (RuntimeVerifier.first binary prime P R cfg).participant.backend) (rc : ProfileParameters (RuntimeVerifier.second binary prime P R cfg).participant.backend)
    (hε : 0 ≤ ε) (point : (RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key))) (H : (RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key)) → Digest × C) :
    (∑ answer, single laws readers encode derive decodeCoin decodeQuery cutoff ε point H answer) ≤
      Fintype.card (Digest × C)*budget (LB := LB) (LN := LN) encode cutoff ε pc rc point := by
  have ha := RuntimeAdaptiveCharges.single_sum S laws readers binaryListBound primeListBound point H
  have hb := BackendOracle.single_sum (RuntimeVerifier.first binary prime P R cfg).participant (RuntimeVerifier.second binary prime P R cfg).participant g.batchingIndex_next encode derive S.oracle
    decodeCoin decodeQuery cutoff ε coinDecoder.fiber queryDecoder.fiber
    (fun coin => by simpa only [hcoinDecode] using coinDecoder.fiber_bound coin)
    (fun query => by simpa only [hqueryDecode] using queryDecoder.fiber_bound query)
    coinDecoder.balanced.le queryDecoder.balanced.le pc rc hε point H
  simp only [single,sum_add_distrib]
  exact (add_le_add ha hb).trans_eq (by unfold budget GlobalCharges.openingBudget; ring)

include coinDecoder queryDecoder hcoinDecode hqueryDecode in
theorem pair_sum [Nonempty C] (pc : HahnSystemCertificate (RuntimeVerifier.first binary prime P R cfg).participant.backend)
    (rc : ProfileParameters (RuntimeVerifier.second binary prime P R cfg).participant.backend) (hθ : pc.threshold ≤ ε)
    (hactive : CodingTheory.UniformFamilyBound n pc.columnCutoff (k+2*s-1) pc.listBound)
    (hbound : pc.listBound ≤ Nat.card (RuntimeVerifier.first binary prime P R cfg).participant.Carrier) (parent : (BackendQueries.Parent g.roles Key (RuntimeVerifier.Block (g := g) (fields := fields) (Advice := Advice) (Base := Base)) Digest g.batchingIndex)) (H : (RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key)) → Digest × C) :
    (∑ response, ∑ a, ∑ b, pair (S := S) derive decodeCoin decodeQuery ε parent response H a b) ≤
      (Fintype.card (Digest × C) : ℚ)^2 * JointResponse.activeHighBudget (RuntimeVerifier.first binary prime P R cfg).participant (RuntimeVerifier.second binary prime P R cfg).participant pc :=
  BackendFS.high_sum_active (RuntimeVerifier.first binary prime P R cfg).participant (RuntimeVerifier.second binary prime P R cfg).participant derive S.oracle decodeCoin decodeQuery ε
    coinDecoder.fiber queryDecoder.fiber
    (fun coin => by simpa only [hcoinDecode] using coinDecoder.fiber_bound coin)
    (fun query => by simpa only [hqueryDecode] using queryDecoder.fiber_bound query)
    coinDecoder.balanced.le queryDecoder.balanced.le pc rc hθ hactive hbound parent H

end Counts

variable [Fintype Key] [Fintype Base] [Fintype Advice] [∀ side, Fintype (fields side)]

omit [Fintype C] in
theorem point_budget_le (hencode : Function.Injective encode)
    (pc : ProfileParameters (RuntimeVerifier.first binary prime P R cfg).participant.backend) (rc : ProfileParameters (RuntimeVerifier.second binary prime P R cfg).participant.backend)
    (highBudget total : ℚ)
    (happ : ∀ role, ApplicationCharging.roundBudget B Adapter.Mdoc.primeOrder Adapter.Mdoc.groupOrder
      Adapter.Mdoc.quotientBound LB LN role ≤ total)
    (hp : pc.rankError+rc.rankError+highBudget ≤ total)
    (ho : GlobalCharges.openingBudget (s := s) (n := n) (t := t) cutoff ε ≤ total)
    (ht : 0 ≤ total) (point : (RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key))) :
    budget (LB := LB) (LN := LN) encode cutoff ε pc rc point +
      (∑ parent : (BackendQueries.Parent g.roles Key (RuntimeVerifier.Block (g := g) (fields := fields) (Advice := Advice) (Base := Base)) Digest g.batchingIndex), if parent.point = point then highBudget else 0) ≤ total := by
  unfold budget
  rw [show RuntimeAdaptiveCharges.budget (B := B) LB LN point = ApplicationCharging.PrefixConfiguration.budget
    (B := B) (p := Adapter.Mdoc.primeOrder) (M := Adapter.Mdoc.groupOrder)
    (K := Adapter.Mdoc.quotientBound) (LB := LB) (LN := LN) point by cases point <;> rfl]
  exact GlobalCharges.point_budget_le (B := B) (p := Adapter.Mdoc.primeOrder)
    (M := Adapter.Mdoc.groupOrder) (K := Adapter.Mdoc.quotientBound) (LB := LB) (LN := LN)
    (RuntimeVerifier.first binary prime P R cfg).participant (RuntimeVerifier.second binary prime P R cfg).participant encode hencode cutoff ε pc rc highBudget total happ hp ho ht point

end LfzkV2.Current.Soundness.RuntimeCharges
