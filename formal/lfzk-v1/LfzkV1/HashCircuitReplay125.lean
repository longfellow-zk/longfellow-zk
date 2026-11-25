import LfzkV1.HashReplayView125
import LfzkV1.HashFieldProfile125
import LfzkV1.TwoFieldCover125
import LfzkV1.ResponseDecode125

/-! Fixed-view replay on the deployed v7 hash-side circuit and schedule. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LfzkV1.HashCircuitReplay125

open Finset LigeroFamily CodingTheory Merkle.MH Merkle.RandomOracle
open Bcs.TotalOracle (AgreeOff queried)
open LfzkV1.ReplayView125 LfzkV1.ReplayDecode125 LfzkV1.ReplayFieldTape125
open LfzkV1.ResidualReplay125 LfzkV1.TwoFieldV1Rows
open LfzkV1.RbrZkLongfellow LfzkV1.Arith LfzkV1.ZkArithProfile LfzkV1.CompiledZk
open LfzkV1.LigeroHighMass125 LfzkV1.LiftOpening125
open LfzkV1.NizkDeployedHash LfzkV1.CertifiedV1 LfzkV1.SoundnessAudit
open LfzkV1.CompiledLongfellow (Col ligIdx qryIdx v1K)
open LfzkV1.CompiledLongfellowAdaptive (Sig)
open LfzkV1.NizkGrinding (indexEquiv_symm_index slot_roleAt)
open scoped Classical

section Schedule

variable {Ctx Msg Point : Type} [Inhabited Msg] {nl : ℕ} {w : ℕ → ℕ}

/-- The actual message-prefix address for each role, embedded into the full oracle. -/
noncomputable def addresses (embed : MPoint Ctx Msg nl w ↪ Point) (ctx : Ctx)
    (msgs : ℕ → Msg) : Rounds.Role nl w ↪ Point where
  toFun rl := embed (msgPoint ctx (fun ms j => ms j) msgs rl.slot)
  inj' a b he := by
    have h := congrArg MPoint.role (embed.injective he)
    apply Rounds.Role.indexEquiv.injective
    apply Fin.ext
    exact (slot_roleAt a.slot_lt).symm.trans ((congrArg Rounds.Role.slot h).trans
      (slot_roleAt b.slot_lt))

@[simp] theorem addresses_apply (embed : MPoint Ctx Msg nl w ↪ Point) (ctx : Ctx)
    (msgs : ℕ → Msg) (rl : Rounds.Role nl w) :
    addresses embed ctx msgs rl = embed (msgPoint ctx (fun ms j => ms j) msgs rl.slot) := rfl

variable {C : Type}

noncomputable def roleTape (points : Rounds.Role nl w → Point) (U : Point → C) :
    Fin (Rounds.Role.length nl w) → C :=
  fun j => U (points (Rounds.Role.indexEquiv.symm j))

theorem roleTape_eq_of_view {Out : Type} {fuel : ℕ}
    {tree : Tree Point C Out fuel} {lookups : Out → List Point} {H U : Point → C}
    (points : Rounds.Role nl w → Point) (rl : Rounds.Role nl w)
    (hseen : points rl ∈ revealed tree lookups H)
    (hview : view tree lookups U = view tree lookups H) :
    roleTape points U rl.index = roleTape points H rl.index := by
  simp only [roleTape, indexEquiv_symm_index]
  exact (view_eq_iff tree lookups H U).mp hview _ hseen

@[simp] theorem roleTape_addresses (embed : MPoint Ctx Msg nl w ↪ Point) (ctx : Ctx)
    (msgs : ℕ → Msg) (U : Point → C) :
    roleTape (addresses embed ctx msgs) U = HashFieldProfile125.pointTape ctx (U ∘ embed) msgs := by
  funext j
  have h : (Rounds.Role.indexEquiv.symm j).slot = j.val :=
    congrArg Fin.val (Rounds.Role.indexEquiv.apply_symm_apply j)
  change U (embed (msgPoint ctx (fun ms j => ms j) msgs (Rounds.Role.indexEquiv.symm j).slot)) = _
  rw [h]
  rfl

private noncomputable def slotAddresses (embed : MPoint Ctx Msg nl w ↪ Point) (ctx : Ctx)
    (msgs : ℕ → Msg) : Fin (Rounds.Role.length nl w) ↪ Point :=
  Rounds.Role.indexEquiv.symm.toEmbedding.trans (addresses embed ctx msgs)

@[simp] private theorem slotAddresses_apply (embed : MPoint Ctx Msg nl w ↪ Point) (ctx : Ctx)
    (msgs : ℕ → Msg) (j : Fin (Rounds.Role.length nl w)) :
    slotAddresses embed ctx msgs j = embed (msgPoint ctx (fun ms k => ms k) msgs j.val) :=
  congrFun (roleTape_addresses embed ctx msgs id) j

end Schedule

section Generic

variable {C F Point Out Msg : Type} [Fintype C] [Field F] [Fintype F] [DecidableEq F]
variable [SumcheckV1Interp F] {fuel k : ℕ}
variable {c : QuadCircuit F} {M L logv nl : ℕ} {w : ℕ → ℕ}
variable {r qw n nw nq nlin nt : ℕ}
variable {tree : Tree Point C Out fuel} {lookups : Out → List Point} {H : Point → C}

local notation "Role" => Rounds.Role nl w
local notation "Assignment" => LigeroAssignment c.ninp M F
local notation "Challenge" => Ligero.V1.Challenge F nw nq 1 (Equations nlin nt)
local notation "Verifier" => ZkCode C F Challenge (QuerySet n r) Msg (Fin logv → F) M c.ninp L 0

/-- The same replay predicate at the registered layer count. -/
def Pass (V : Verifier) (ms : ℕ → Msg) (tape : Fin (Rounds.Role.length nl w) → C)
    (code : MultiplicativeCode F r qw n) (pl : Encode.Placement c.ninp M qw nw nq nt)
    (oracle : Ligero.V1.Oracle F nw nq n 1) (response : Response F r qw n 1)
    (assignment : Assignment) : Prop :=
  ∃ sys, zkBuilt V ms tape = some sys ∧ sys.Sat assignment.1 assignment.2 ∧
    let query := V.decodeQuery (tape qryIdx)
    SchemeVerifier.Accepts code Ligero.V1.scheme (Encode.encodeLig pl nlin sys)
      (V.decodeChal (tape ligIdx)) response query (openSchemeOracle oracle query)

open Classical in
private theorem fixed_split_at [Fintype Point]
    (points : Role ↪ Point)
    (indices : (Σ i : HiddenRole (tree := tree) (lookups := lookups) (H := H) points,
      Fin (roleWidth logv i.val)) ≃ Fin k)
    (V : Verifier) (ms : ℕ → Msg)
    (init : ExactDecoder C ((Fin logv → F) × F × F))
    (pair : ExactDecoder C (F × F)) (scalar : ExactDecoder C F)
    (hinit : init.decode = V.decodeInit) (hpair : pair.decode = V.decodePair)
    (hscalar : scalar.decode = V.decodeF) (pub : Fin c.ninp → F)
    (hV : CodeAgreesP c pub L V)
    (hst0 : ∀ G, (V.st0 G).g0 = padG L G ∧ (V.st0 G).g1 = padG L G)
    (hpos : 0 < c.nl) {R : Row} (hR : V7HashProfile R)
    (hnl : c.nl = nl) (hprofile : nl = (R).params.nl) (hw : w = (R).params.rounds) (hlogv : logv ≤ 5)
    (hbatch : points .ligeroChallenge ∈ revealed tree lookups H)
    (hquery : points .ligeroQuery ∈ revealed tree lookups H)
    (code : MultiplicativeCode F r qw n) (pl : Encode.Placement c.ninp M qw nw nq nt)
    (oracle : Ligero.V1.Oracle F nw nq n 1) (response : Response F r qw n 1)
    (assignment : Assignment)
    (hBuilt : ∃ sys, zkBuilt V ms (roleTape points H) = some sys) :
    let pass := fun U : Point → C =>
      Pass V ms (roleTape points U) code pl oracle response assignment
    (∀ U : Point → C, view tree lookups U = view tree lookups H → (pass U ↔ pass H)) ∨
      ((univ.filter fun U : Point → C =>
        view tree lookups U = view tree lookups H ∧ pass U).card : ℚ) ≤
        (81 / Fintype.card F) *
          ((univ.filter fun U : Point → C => view tree lookups U = view tree lookups H).card : ℚ) := by
  subst nl
  exact HashReplayView125.fixed_selected_view_split points indices V ms init pair scalar hinit hpair
    hscalar pub hV hst0 hpos hR hprofile hw hlogv hbatch hquery code pl oracle response assignment hBuilt

end Generic

abbrev certificate (i : Fin 4) := (OpeningGeometry125.result i).certificate

section Terminal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {r qw n nw nq nlin nt : ℕ}
variable (i : Fin 4) (code : MultiplicativeCode F r qw n) (cut : Ligero.V1.Oracle F nw nq n 1)
variable (stmt : ConstraintSystem F nw nq qw (Equations nlin nt))
variable (ch : Ligero.V1.Challenge F nw nq 1 (Equations nlin nt))
variable (u : Response F r qw n 1) (q : QuerySet n r)

/-- Accepted low or bad-high terminal proof, stated at the code's original type. -/
def directTerminal : Prop :=
  ((columns (C := code) cut stmt ch u).card < highCutoff i ∨
    u ∈ badHighResponses (C := code) cut stmt (highCutoff i) (certificate i).e (certificate i).g ch) ∧
  SchemeVerifier.Accepts code Ligero.V1.scheme stmt ch u q (openSchemeOracle cut q)

theorem directTerminal_iff_ordered :
    directTerminal i code cut stmt ch u q ↔
      LigeroOrder125.lowEvent i code (cut, stmt) u ch q ∨
      LigeroOrder125.badHighEvent i code (cut, stmt) u ch q := by
  unfold directTerminal LigeroOrder125.lowEvent LigeroOrder125.badHighEvent
  exact or_and_right

private theorem terminal_cases (hn : n = (certificate i).n) (hr : r = (certificate i).openings)
    (hmin : HasMinimumDistanceAtLeast code.baseCode (certificate i).d)
    (hpass : SchemeVerifier.Accepts code Ligero.V1.scheme stmt ch u q (openSchemeOracle cut q)) :
    directTerminal i code cut stmt ch u q ∨
      (∃ x y : SchemeLiftCandidate code cut (HashCut125.radius i),
        x ≠ y ∧ Compatible x q (certificate i).g ∧ Compatible y q (certificate i).g) ∨
      ∃ x : SchemeLiftCandidate code cut (HashCut125.radius i),
        stmt.Satisfies x.decodedMessages ∧ Compatible x q (certificate i).g ∧
        u ∈ liftedResponses stmt x (highCutoff i) (certificate i).g ch ∧
        ∀ y : SchemeLiftCandidate code cut (HashCut125.radius i), Compatible y q (certificate i).g → x = y := by
  subst n
  subst r
  rcases TwoFieldCover125.hash_terminal_cover i code cut stmt ch u q hmin hpass with hl | hb | hs
  · exact Or.inl ⟨Or.inl hl.1, hl.2⟩
  · exact Or.inl ⟨Or.inr hb.1, hb.2⟩
  · exact Or.inr hs

end Terminal

section Hidden

attribute [local instance 10000] Classical.propDecidable

private theorem hidden_schedule_count_le {C Point Out Index : Type} [Fintype C] [Nonempty C]
    [Fintype Point] [DecidableEq Point] [Fintype Index] {fuel : ℕ}
    (tree : Tree Point C Out fuel) (lookups : Out → List Point) (H : Point → C)
    (addr : Index ↪ Point) (bad : Index → (Point → C) → C → Prop) (δ : ℚ) (hδ : 0 ≤ δ)
    (hoff : ∀ j U U', AgreeOff (addr j) U U' → ∀ c, bad j U c ↔ bad j U' c)
    (hbudget : ∀ j U, (∑ c : C, if bad j U c then (1 : ℚ) else 0) ≤ Fintype.card C * δ) :
    ((univ.filter fun U : Point → C => view tree lookups U = view tree lookups H ∧
      ∃ j, addr j ∉ revealed tree lookups H ∧ bad j U (U (addr j))).card : ℚ) ≤
      Fintype.card Index * δ *
        ((univ.filter fun U : Point → C => view tree lookups U = view tree lookups H).card : ℚ) := by
  let hidden := (univ.filter fun j : Index => addr j ∉ revealed tree lookups H).image addr
  let event (p : Point) (U : Point → C) (c : C) := ∃ j, addr j = p ∧ bad j U c
  have hm (p : Point) : p ∈ hidden ↔ ∃ j, addr j ∉ revealed tree lookups H ∧ addr j = p := by
    simp [hidden]
  have he (j : Index) (U : Point → C) (c : C) : event (addr j) U c ↔ bad j U c := by
    constructor
    · rintro ⟨j', hj', hb⟩
      rwa [addr.injective hj'] at hb
    · exact fun hb => ⟨j, rfl, hb⟩
  have hcount := hidden_events_count_le tree lookups H hidden
    (fun p hp => by obtain ⟨j, hj, rfl⟩ := (hm p).mp hp; exact hj) event δ
    (fun p hp U U' h c => by obtain ⟨j, _, rfl⟩ := (hm p).mp hp; rw [he, he]; exact hoff j U U' h c)
    (fun p hp U _ => by
      obtain ⟨j, _, rfl⟩ := (hm p).mp hp
      have h := hbudget j U
      rw [← sum_filter] at h
      simpa only [sum_const, nsmul_eq_mul, mul_one, ← he j U] using h)
  have hsame : (univ.filter fun U : Point → C => view tree lookups U = view tree lookups H ∧
        ∃ j, addr j ∉ revealed tree lookups H ∧ bad j U (U (addr j))) =
      univ.filter fun U : Point → C => view tree lookups U = view tree lookups H ∧
        ∃ p ∈ hidden, event p U (U p) := by
    ext U
    simp only [mem_filter, mem_univ, true_and]
    apply and_congr_right
    intro _
    constructor
    · rintro ⟨j, hj, hb⟩
      exact ⟨addr j, (hm _).mpr ⟨j, hj, rfl⟩, (he j U _).mpr hb⟩
    · rintro ⟨p, hp, hb⟩
      obtain ⟨j, hj, rfl⟩ := (hm p).mp hp
      exact ⟨j, hj, (he j U _).mp hb⟩
  rw [hsame]
  exact hcount.trans (by
    gcongr
    exact_mod_cast (card_image_le.trans (card_filter_le _ _)))

end Hidden

section CircuitSide

variable {C : Type} [Fintype C] {F Msg : Type} [Field F] [Fintype F] [DecidableEq F]
variable [SumcheckV1Interp F] {M nt nlin : ℕ}
variable {Enc D Salt X : Type} [Inhabited D] [DecidableEq D] [DecidableEq Enc] [Inhabited Salt]
variable {i : Fin 4} {hR : (v7HashRow i).Valid} {hr : 0 < (v7HashRow i).params.row.openings}
variable {codec : Codec Salt (Col F (v7HashRow i).params.nw (v7HashRow i).params.nq) D Enc}
variable {dec : RoleDecoders codec} {rootOfKey : D × D → D}
variable (S : CircuitSide (v7HashRow i) hR hr (v7HashLogv i) C F Msg M nt nlin X dec rootOfKey)

local notation "R" => v7HashRow i

local notation "Lift" => sideLiftAt S (HashCut125.radius i)

private def initDecoder (a : C) (x : X) : ExactDecoder C ((Fin (v7HashLogv i) → F) × F × F) where
  decode := (S.Vc a x).decodeInit
  k := S.kinit
  hbal y := by
    exact S.hbalInit a x y
  hexact := by
    simpa [Fintype.card_prod, Fintype.card_fun, pow_add, pow_two] using S.hkinit

private def pairDecoder (a : C) (x : X) : ExactDecoder C (F × F) where
  decode := (S.Vc a x).decodePair
  k := S.kpair
  hbal y := by
    exact S.hbalPair a x y
  hexact := by simpa [Fintype.card_prod] using S.hkpair

private def scalarDecoder (a : C) (x : X) : ExactDecoder C F where
  decode := (S.Vc a x).decodeF
  k := S.k
  hbal y := by
    exact S.hbalF a x y
  hexact := S.hk

/-- The scheduled v7 verifier and selected lift at the actual frozen cut. -/
def accepts (σ : Sig D C X Enc) (msgs : ℕ → Msg)
    (tape : Fin (Rounds.Role.length (R).params.nl (R).params.rounds) → C) (lift : Lift σ) : Prop :=
  Pass (S.Vc σ.2.1 σ.2.2) msgs tape ((R).params.row.code (Row.rowValid hR) S.dom (Row.hkrow hR)) S.pl
    (extOracle nlin nt (Row.rowValid hR) S.dom (Row.hkrow hR) hr dec (rootOfKey σ.1.1, σ.1.2))
    (S.respOf (msgs (Rounds.Role.layerBase (R).params.rounds (R).params.nl + 2)))
    ((HashCut125.side S).asg σ lift)

/-- Remove the Merkle wrapper from an actual accepted terminal opening explained by the cut. -/
theorem terminal_of_compiled (σ : Sig D C X Enc) (msgs : ℕ → Msg)
    (tape : Fin (Rounds.Role.length (R).params.nl (R).params.rounds) → C)
    (sys : LigeroSystem S.c.ninp M F) (mo : Enc → D)
    (claim : OpeningClaim (R).params.row.n Salt (Col F (R).params.nw (R).params.nq) D)
    (hagrees : ∀ j ∈ claim.I,
      (v1K (Equations := Equations nlin nt) (Row.rowValid hR) S.dom (Row.hkrow hR) hr).columns
        (extOracle nlin nt (Row.rowValid hR) S.dom (Row.hkrow hR) hr dec (rootOfKey σ.1.1, σ.1.2)) j
        = claim.a j)
    (haccept :
      (v1K (Equations := Equations nlin nt) (Row.rowValid hR) S.dom (Row.hkrow hR) hr).Accepts
        (codec.withOracle mo) (Encode.encodeLig S.pl nlin sys) (rootOfKey σ.1.1)
        ((S.Vc σ.2.1 σ.2.2).decodeChal (tape ligIdx))
        (S.respOf (msgs (Rounds.Role.layerBase (R).params.rounds (R).params.nl + 2)))
        ((S.Vc σ.2.1 σ.2.2).decodeQuery (tape qryIdx)) claim) :
    let query := (S.Vc σ.2.1 σ.2.2).decodeQuery (tape qryIdx)
    let cut := extOracle nlin nt (Row.rowValid hR) S.dom (Row.hkrow hR) hr dec
      (rootOfKey σ.1.1, σ.1.2)
    SchemeVerifier.Accepts ((R).params.row.code (Row.rowValid hR) S.dom (Row.hkrow hR))
      Ligero.V1.scheme (Encode.encodeLig S.pl nlin sys) ((S.Vc σ.2.1 σ.2.2).decodeChal (tape ligIdx))
      (S.respOf (msgs (Rounds.Role.layerBase (R).params.rounds (R).params.nl + 2)))
      query (openSchemeOracle cut query) := by
  let K := v1K (Equations := Equations nlin nt) (nw := (R).params.nw) (nq := (R).params.nq) (Row.rowValid hR) S.dom (Row.hkrow hR) hr
  let query := (S.Vc σ.2.1 σ.2.2).decodeQuery (tape qryIdx)
  let cut := extOracle nlin nt (Row.rowValid hR) S.dom (Row.hkrow hR) hr dec (rootOfKey σ.1.1, σ.1.2)
  exact of_decide_eq_true (K.verify_of_accepts (codec.withOracle mo) (Encode.encodeLig S.pl nlin sys)
    (rootOfKey σ.1.1) ((S.Vc σ.2.1 σ.2.2).decodeChal (tape ligIdx))
    (S.respOf (msgs (Rounds.Role.layerBase (R).params.rounds (R).params.nl + 2))) query
    claim cut hagrees haccept)

/-- The actual hash side's evaluation code has the certificate's minimum distance. -/
theorem code_distance :
    HasMinimumDistanceAtLeast
      ((R).params.row.code (Row.rowValid hR) S.dom (Row.hkrow hR)).baseCode (certificate i).d := by
  obtain ⟨hn, hk, _, _⟩ := OpeningGeometry125.deployedGeometry i
  have hp := OpeningGeometry125.parameters i
  have hkrow := Row.hkrow hR
  have hkpos : 1 ≤ (R).params.row.openings + (R).params.q :=
    (Nat.succ_le_of_lt hr).trans (Nat.le_add_right _ _)
  have hkn : (R).params.row.openings + (R).params.q ≤ (R).params.row.n := by
    rw [hkrow, ← hk, ← hn]
    exact hp.2.1
  have hd : (certificate i).d = (R).params.row.n - ((R).params.row.openings + (R).params.q) + 1 := by
    rw [hkrow, ← hk, ← hn]
    exact hp.2.2.1
  rw [hd]
  exact LigeroFamily.ReedSolomon.baseCode_minimum_distance S.dom hkpos hkn

/-- A successful registered build with an authenticated and explained opening either incurs a
terminal charge or fixes the unique compatible lift and proves its replay predicate. -/
def TerminalCover (σ : Sig D C X Enc) (msgs : ℕ → Msg)
    (tape : Fin (Rounds.Role.length (R).params.nl (R).params.rounds) → C)
    (sys : LigeroSystem S.c.ninp M F) : Prop :=
  let V := S.Vc σ.2.1 σ.2.2
  let code := (R).params.row.code (Row.rowValid hR) S.dom (Row.hkrow hR)
  let cut := extOracle nlin nt (Row.rowValid hR) S.dom (Row.hkrow hR) hr dec (rootOfKey σ.1.1, σ.1.2)
  let q := V.decodeQuery (tape qryIdx)
  let ch := V.decodeChal (tape ligIdx)
  let u := S.respOf (msgs (Rounds.Role.layerBase (R).params.rounds (R).params.nl + 2))
  let stmt := Encode.encodeLig S.pl nlin sys
  directTerminal i code cut stmt ch u q ∨
    (∃ x y : Lift σ, x ≠ y ∧ Compatible x q (certificate i).g ∧ Compatible y q (certificate i).g) ∨
    ∃ x : Lift σ, accepts S σ msgs tape x ∧ Compatible x q (certificate i).g ∧
      u ∈ liftedResponses stmt x (highCutoff i) (certificate i).g ch ∧
      ∀ y : Lift σ, Compatible y q (certificate i).g → x = y

set_option maxHeartbeats 2000000 in
/-- Recover the hash-side matrix from the Merkle cut and the submitted
Ligero challenge and response. -/
noncomputable def responseLift (σ : Sig D C X Enc) (msgs : ℕ → Msg)
    (tape : Fin (Rounds.Role.length (R).params.nl (R).params.rounds) → C) :
    Option (Lift σ) := by
  unfold sideLiftAt
  let code := (R).params.row.code (Row.rowValid hR) S.dom (Row.hkrow hR)
  let cut := extOracle nlin nt (Row.rowValid hR) S.dom (Row.hkrow hR) hr dec
    (rootOfKey σ.1.1, σ.1.2)
  let ch := (S.Vc σ.2.1 σ.2.2).decodeChal (tape ligIdx)
  let u := S.respOf (msgs (Rounds.Role.layerBase (R).params.rounds (R).params.nl + 2))
  exact ResponseDecode125.decode code cut (ch 0).proximity (u.proximity 0)
    (certificate i).g (HashCut125.radius i)

set_option maxHeartbeats 2000000 in
theorem responseLift_eq_some (σ : Sig D C X Enc) (msgs : ℕ → Msg)
    (tape : Fin (Rounds.Role.length (R).params.nl (R).params.rounds) → C)
    (sys : LigeroSystem S.c.ninp M F) (x : Lift σ)
    (h : let ch := (S.Vc σ.2.1 σ.2.2).decodeChal (tape ligIdx)
      let u := S.respOf (msgs (Rounds.Role.layerBase (R).params.rounds (R).params.nl + 2))
      u ∈ liftedResponses (Encode.encodeLig S.pl nlin sys) x (highCutoff i) (certificate i).g ch) :
    responseLift S σ msgs tape = some x := by
  dsimp only at h
  obtain ⟨hhigh, _, hrem⟩ := mem_filter.mp h
  unfold responseLift
  dsimp only
  apply ResponseDecode125.decode_eq_some _ _ _ _ _ _ x _ hrem
  refine le_trans ?_ ((mem_filter.mp hhigh).2.2.trans (card_le_card (columns_subset_proximity _ _ _ _)))
  rw [MultiplicativeCode.k_eq, Row.hkrow hR, ← (OpeningGeometry125.deployedGeometry i).2.1]
  fin_cases i <;> decide +kernel

/-- Return the decoded circuit witness after checking the circuit's
constraints against the actual public input. -/
noncomputable def responseWitness (σ : Sig D C X Enc) (msgs : ℕ → Msg)
    (tape : Fin (Rounds.Role.length (R).params.nl (R).params.rounds) → C) :
    Option (Fin S.c.ninp → F) :=
  (responseLift S σ msgs tape).bind fun x =>
    if (HashCut125.side S).Sat σ x then some ((HashCut125.side S).wit σ x) else none

theorem responseWitness_good (σ : Sig D C X Enc) (msgs : ℕ → Msg)
    (tape : Fin (Rounds.Role.length (R).params.nl (R).params.rounds) → C)
    (a : Fin S.c.ninp → F) (ha : responseWitness S σ msgs tape = some a) :
    (HashCut125.side S).Good σ a := by
  obtain ⟨x, _, hx⟩ := Option.bind_eq_some_iff.mp ha
  split_ifs at hx with hsat
  exact ⟨x, hsat, Option.some.inj hx⟩

private theorem terminal_cover_of_opened (σ : Sig D C X Enc) (msgs : ℕ → Msg)
    (tape : Fin (Rounds.Role.length (R).params.nl (R).params.rounds) → C)
    (sys : LigeroSystem S.c.ninp M F) (hBuilt : zkBuilt (S.Vc σ.2.1 σ.2.2) msgs tape = some sys)
    (hp :
      let query := (S.Vc σ.2.1 σ.2.2).decodeQuery (tape qryIdx)
      let cut := extOracle nlin nt (Row.rowValid hR) S.dom (Row.hkrow hR) hr dec
        (rootOfKey σ.1.1, σ.1.2)
      SchemeVerifier.Accepts ((R).params.row.code (Row.rowValid hR) S.dom (Row.hkrow hR))
        Ligero.V1.scheme (Encode.encodeLig S.pl nlin sys) ((S.Vc σ.2.1 σ.2.2).decodeChal (tape ligIdx))
        (S.respOf (msgs (Rounds.Role.layerBase (R).params.rounds (R).params.nl + 2)))
        query (openSchemeOracle cut query)) : TerminalCover S σ msgs tape sys := by
  obtain ⟨hn, _, hr', _⟩ := OpeningGeometry125.deployedGeometry i
  rcases terminal_cases i _ _ _ _ _ _ hn.symm hr'.symm (code_distance S) hp with hd | ha | hx
  · exact Or.inl hd
  · exact Or.inr (Or.inl ha)
  · obtain ⟨x, hs, hc, hu, huniq⟩ := hx
    obtain ⟨hlin, hquad⟩ := zkBuilt_fits (S.Vc σ.2.1 σ.2.2) msgs tape hBuilt
    rw [S.hnlin] at hlin
    rw [S.hnt] at hquad
    have hsat := Encode.sat_decode_encodeLig S.pl hlin hquad _ hs
    exact Or.inr (Or.inr ⟨x, ⟨sys, hBuilt, hsat, hp⟩, hc, hu, huniq⟩)

/-- Reclassify the terminal transcript on an accepting replay completion. -/
theorem terminal_cover_of_replay (σ : Sig D C X Enc) (msgs : ℕ → Msg)
    (tape : Fin (Rounds.Role.length (R).params.nl (R).params.rounds) → C)
    (lift : Lift σ) (hpass : accepts S σ msgs tape lift) :
    ∃ sys, zkBuilt (S.Vc σ.2.1 σ.2.2) msgs tape = some sys ∧ TerminalCover S σ msgs tape sys := by
  obtain ⟨sys, hb, _, hp⟩ := hpass
  exact ⟨sys, hb, terminal_cover_of_opened S σ msgs tape sys hb hp⟩

theorem terminal_cover (σ : Sig D C X Enc) (msgs : ℕ → Msg)
    (tape : Fin (Rounds.Role.length (R).params.nl (R).params.rounds) → C)
    (sys : LigeroSystem S.c.ninp M F) (mo : Enc → D)
    (claim : OpeningClaim (R).params.row.n Salt (Col F (R).params.nw (R).params.nq) D)
    (hBuilt : zkBuilt (S.Vc σ.2.1 σ.2.2) msgs tape = some sys)
    (hagrees : ∀ j ∈ claim.I,
      (v1K (Equations := Equations nlin nt) (Row.rowValid hR) S.dom (Row.hkrow hR) hr).columns
        (extOracle nlin nt (Row.rowValid hR) S.dom (Row.hkrow hR) hr dec (rootOfKey σ.1.1, σ.1.2)) j
        = claim.a j)
    (haccept :
      (v1K (Equations := Equations nlin nt) (Row.rowValid hR) S.dom (Row.hkrow hR) hr).Accepts
        (codec.withOracle mo) (Encode.encodeLig S.pl nlin sys) (rootOfKey σ.1.1)
        ((S.Vc σ.2.1 σ.2.2).decodeChal (tape ligIdx))
        (S.respOf (msgs (Rounds.Role.layerBase (R).params.rounds (R).params.nl + 2)))
        ((S.Vc σ.2.1 σ.2.2).decodeQuery (tape qryIdx)) claim) :
    TerminalCover S σ msgs tape sys :=
  terminal_cover_of_opened S σ msgs tape sys hBuilt
    (terminal_of_compiled S σ msgs tape sys mo claim hagrees haccept)

/-- Run terminal classification on one side of the deployed two-field verifier. -/
theorem terminal_cover_of_acceptsDH {Pt Out : Type} [DecidableEq Pt] {tA N L fc TM : ℕ}
    (A : Bcs.TotalOracleCommit.Setup Enc D Pt C Out (D × D) tA N L)
    (check : Out → Tree Enc D Unit fc) (rootOf : Out → D)
    (hroot : ∀ out, rootOfKey (A.keyOut out) = rootOf out)
    (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim (R).params.row.n Salt (Col F (R).params.nw (R).params.nq) D)
    (avOf : Out → C) (pubOf : Out → X)
    (slice : (Fin L → C) → Fin (Rounds.Role.length (R).params.nl (R).params.rounds) → C)
    (mt : Fin TM → D) (H : Pt → C)
    (hacc : S.toSide.acceptsDH A check rootOf msgOf claimOf avOf pubOf slice mt H)
    (hexp : A.Explains dec rootOfKey claimOf mt H) :
    let out := A.proof mt H
    let σ := LfzkV1.NizkDeployedHashTwoField.sideCtx A avOf pubOf mt H
    let tape := slice (A.challenges mt H)
    ∃ sys, zkBuilt (S.Vc σ.2.1 σ.2.2) (msgOf out) tape = some sys ∧
      TerminalCover S σ (msgOf out) tape sys := by
  let out := A.proof mt H
  let σ := LfzkV1.NizkDeployedHashTwoField.sideCtx A avOf pubOf mt H
  let tape := slice (A.challenges mt H)
  obtain ⟨sys, hb, ha⟩ := hacc
  obtain ⟨e, he, hc, _⟩ := hexp
  have ha' :
      (v1K (Equations := Equations nlin nt) (Row.rowValid hR) S.dom (Row.hkrow hR) hr).Accepts
        (codec.withOracle (A.merkleOracle check mt H)) (Encode.encodeLig S.pl nlin sys) (rootOfKey σ.1.1)
        ((S.Vc σ.2.1 σ.2.2).decodeChal (tape ligIdx))
        (S.respOf (msgOf out (Rounds.Role.layerBase (R).params.rounds (R).params.nl + 2)))
        ((S.Vc σ.2.1 σ.2.2).decodeQuery (tape qryIdx)) (claimOf out) := by
    have hk : σ.1.1 = A.keyOut out := rfl
    rw [hk, hroot out]
    exact ha
  refine ⟨sys, hb, terminal_cover S σ (msgOf out) tape sys _ (claimOf out) hb ?_ ha'⟩
  intro j hj
  unfold extOracle
  rw [Bcs.Compiler.columns_oracleOfClaim]
  change (((extract dec (R).params.row.n (rootOfKey σ.1.1) σ.1.2).map Extracted.message).getD default) j
    = (claimOf out).a j
  have hcut : extract dec (R).params.row.n (rootOfKey σ.1.1) σ.1.2 = some e := he
  rw [hcut]
  exact hc j hj

variable {Point Out : Type} {fuel k : ℕ}
variable {tree : Tree Point C Out fuel} {lookups : Out → List Point} {H : Point → C}

open Classical in
/-- Replay uses the circuit side's registered schedule, decoders, code, and lift. -/
theorem selected_view_split [Fintype Point] (σ : Sig D C X Enc) (msgs : ℕ → Msg)
    (points : Rounds.Role (R).params.nl (R).params.rounds ↪ Point)
    (indices : (Σ j : HiddenRole (tree := tree) (lookups := lookups) (H := H) points,
      Fin (roleWidth (v7HashLogv i) j.val)) ≃ Fin k)
    (hbatch : points .ligeroChallenge ∈ revealed tree lookups H)
    (hquery : points .ligeroQuery ∈ revealed tree lookups H)
    (lift : Lift σ) (hpass : accepts S σ msgs (roleTape points H) lift) :
    let pass := fun U : Point → C => accepts S σ msgs (roleTape points U) lift
    (∀ U : Point → C, view tree lookups U = view tree lookups H → pass U) ∨
      ((univ.filter fun U : Point → C =>
        view tree lookups U = view tree lookups H ∧ pass U).card : ℚ) ≤
        (81 / Fintype.card F) *
          ((univ.filter fun U : Point → C => view tree lookups U = view tree lookups H).card : ℚ) := by
  have hpos : 0 < S.c.nl := by rw [S.hnl]; fin_cases i <;> decide
  have hprofile : V7HashProfile R := by fin_cases i <;> simp [V7HashProfile, v7HashRow]
  have hlogv : v7HashLogv i ≤ 5 := by fin_cases i <;> decide
  have hBuilt := let ⟨sys, h, _⟩ := hpass; Exists.intro sys h
  rcases fixed_split_at points indices (S.Vc σ.2.1 σ.2.2) msgs
      (initDecoder S σ.2.1 σ.2.2) (pairDecoder S σ.2.1 σ.2.2) (scalarDecoder S σ.2.1 σ.2.2)
      rfl rfl rfl (S.pubIn σ.2.1 σ.2.2) (S.hV _ _) (S.hst0 _ _) hpos hprofile S.hnl rfl rfl hlogv
      hbatch hquery _ _ _ _ _ hBuilt with hi | hn
  · exact Or.inl fun U hv => (hi U hv).mpr hpass
  · exact Or.inr hn

section Field


private abbrev slots (i : Fin 4) := Fin (Rounds.Role.length (v7HashRow i).params.nl (v7HashRow i).params.rounds)

variable [Inhabited Msg] {Ctx : Type}
variable (σ : Sig D C X Enc)
variable (embed : MPoint Ctx Msg (v7HashRow i).params.nl (v7HashRow i).params.rounds ↪ Point)
variable (ctx : Ctx) (msgs : ℕ → Msg)

local notation "HashPoint" => HashFieldProfile125.HashPoint i Ctx Msg
local notation "Slots" => slots i

private noncomputable def prefixPoint (j : ℕ) : HashPoint := msgPoint ctx (fun ms k => ms k) msgs j

/-- A hidden ordinary field charge, or a hidden initial escape by the secondary lift. -/
def hiddenFieldBad (seen : List Point) (U : Point → C) : Prop :=
  (∃ j : Slots, let p := prefixPoint (i := i) ctx msgs j.val
    embed p ∉ seen ∧ HashFieldProfile125.bad S σ p (mpoints.chal (U ∘ embed) p) (U (embed p))) ∨
  let p := prefixPoint (i := i) ctx msgs 0
  embed p ∉ seen ∧ HashFieldProfile125.secondaryEscape S σ (U (embed p))

/-- A healthy accepting replay exposes a regular field charge in the original trace,
or a canonical secondary run whose initial point is in that trace. -/
theorem healthy_pass_cover (U : Point → C) (lift : Lift σ)
    (hfalse : ¬ (HashCut125.side S).Sat σ lift)
    (hpass : accepts S σ msgs (roleTape (addresses embed ctx msgs) U) lift)
    (hlookup : ∀ j < Rounds.Role.layerBase (R).params.rounds (R).params.nl + 1,
      embed (msgPoint ctx (fun ms k => ms k) msgs j) ∉ lookups (tree.run H).1)
    (healthy : ¬ hiddenFieldBad S σ embed ctx msgs (revealed tree lookups H) U) :
    (∃ j : Slots, let p := msgPoint ctx (fun ms k => ms k) msgs j.val
      embed p ∈ queried tree H ∧ HashFieldProfile125.bad S σ p (mpoints.chal (U ∘ embed) p) (U (embed p))) ∨
    (embed (msgPoint ctx (fun ms k => ms k) msgs 0) ∈ queried tree H ∧
      HashFieldProfile125.canonicalSecondary S σ msgs
        (HashFieldProfile125.pointTape ctx (U ∘ embed) msgs) lift) := by
  rw [roleTape_addresses] at hpass
  obtain ⟨sys, hb, hs, _⟩ := hpass
  rcases HashFieldProfile125.bad_or_canonicalSecondary S σ ctx (U ∘ embed) msgs lift hfalse sys hb hs with
    ⟨j, hbad⟩ | hsec
  · left
    let p := prefixPoint (i := i) ctx msgs j.val
    change HashFieldProfile125.bad S σ p (mpoints.chal (U ∘ embed) p) (U (embed p)) at hbad
    have hseen : embed p ∈ revealed tree lookups H := by
      by_contra hn
      exact healthy (Or.inl ⟨j, hn, hbad⟩)
    have hf := HashFieldProfile125.bad_field_slot S σ p _ _ hbad
    have hslot : p.role.slot = j.val := slot_msgPoint ctx (fun ms k => ms k) msgs j.isLt
    rw [hslot] at hf
    exact ⟨j, (List.mem_append.mp hseen).resolve_right (hlookup _ hf), hbad⟩
  · right
    let p := prefixPoint (i := i) ctx msgs 0
    have hzero := HashFieldProfile125.secondaryEscape_of_canonicalSecondary S σ msgs _ lift hsec
    have hseen : embed p ∈ revealed tree lookups H := by
      by_contra hn
      exact healthy (Or.inr ⟨hn, hzero⟩)
    exact ⟨(List.mem_append.mp hseen).resolve_right (hlookup 0 (Nat.zero_lt_succ _)), hsec⟩

attribute [local instance 10000] Classical.propDecidable in
/-- Conditional charge for the unseen regular points and the independent initial-secondary case. -/
theorem hidden_field_count_le [Fintype Point] [DecidableEq Point] [Nonempty C] :
    ((univ.filter fun U : Point → C => view tree lookups U = view tree lookups H ∧
      hiddenFieldBad S σ embed ctx msgs (revealed tree lookups H) U).card : ℚ) ≤
      ((Rounds.Role.length (R).params.nl (R).params.rounds : ℚ) + 1) * (7 / 2^128) *
        ((univ.filter fun U : Point → C => view tree lookups U = view tree lookups H).card : ℚ) := by
  let addr := slotAddresses embed ctx msgs
  let regular (j : Slots) (U : Point → C) (coin : C) :=
    let p := prefixPoint (i := i) ctx msgs j.val
    HashFieldProfile125.bad S σ p (mpoints.chal (U ∘ embed) p) coin
  have hoff (j : Slots) (U U' : Point → C) (h : AgreeOff (addr j) U U') (coin : C) :
      regular j U coin ↔ regular j U' coin := by
    let p := prefixPoint (i := i) ctx msgs j.val
    have ha : addr j = embed p := slotAddresses_apply embed ctx msgs j
    have hp : AgreeOff p (U ∘ embed) (U' ∘ embed) := fun q hq =>
      h (embed q) (fun he => hq (embed.injective (he.trans ha)))
    change HashFieldProfile125.bad S σ p (mpoints.chal (U ∘ embed) p) coin ↔
      HashFieldProfile125.bad S σ p (mpoints.chal (U' ∘ embed) p) coin
    rw [mpoints.chal_congr hp]
  have hbudget (j : Slots) (U : Point → C) :
      (∑ coin : C, if regular j U coin then (1 : ℚ) else 0) ≤ Fintype.card C * (7 / 2^128) := by
    refine (HashFieldProfile125.bad_sum_le S σ (prefixPoint (i := i) ctx msgs j.val) _).trans ?_
    split_ifs
    · rfl
    · gcongr
      norm_num
  have hr := hidden_schedule_count_le tree lookups H addr regular (7 / 2^128) (by positivity) hoff hbudget
  let first : Unit ↪ Point := ⟨fun _ => embed (prefixPoint (i := i) ctx msgs 0), fun _ _ _ => Subsingleton.elim _ _⟩
  let second (_ : Unit) (_ : Point → C) (coin : C) := HashFieldProfile125.secondaryEscape S σ coin
  have hs := hidden_schedule_count_le tree lookups H first second (7 / 2^128) (by positivity)
    (fun _ _ _ _ _ => Iff.rfl) (fun _ _ => HashFieldProfile125.secondaryEscape_sum_le S σ)
  let fiber (U : Point → C) := view tree lookups U = view tree lookups H
  let A := univ.filter fun U => fiber U ∧ ∃ j, addr j ∉ revealed tree lookups H ∧ regular j U (U (addr j))
  let B := univ.filter fun U => fiber U ∧ ∃ j, first j ∉ revealed tree lookups H ∧ second j U (U (first j))
  have he : (univ.filter fun U : Point → C => fiber U ∧
      hiddenFieldBad S σ embed ctx msgs (revealed tree lookups H) U) = A ∪ B := by
    ext U
    simp [A, B, hiddenFieldBad, and_or_left, addr, regular, prefixPoint, first, second]
  change ((univ.filter fun U => fiber U ∧ hiddenFieldBad S σ embed ctx msgs
      (revealed tree lookups H) U).card : ℚ) ≤ _
  rw [he]
  have hcard : ((A ∪ B).card : ℚ) ≤ (A.card : ℚ) + B.card := by exact_mod_cast card_union_le A B
  have hsum := hcard.trans (add_le_add hr hs)
  simpa only [Fintype.card_fin, Fintype.card_unit, Nat.cast_one, add_mul, one_mul, fiber] using hsum

end Field

end CircuitSide

end LfzkV1.HashCircuitReplay125
