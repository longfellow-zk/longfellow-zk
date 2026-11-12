import LfzkV2.Linear.Runtime.FiatShamir

/-!
# A native compiled side at the commitment boundary

`Data` contains the frontend messages and, on the binary side, the packing
response U. The scalar response A is added only after the packing challenge.
The compiler supplies the algebraic transfer from its rows; the probability
of its prefix-local packing event is counted separately. The explicit
precheck retains the verifier's trace check on U, including malformed proofs.
-/

namespace LfzkV2.Linear.Runtime

open SumcheckV2 RecursivePolygero NonrecursiveFS Finset Bcs.TotalOracle
open scoped Classical

structure CompiledSide (F C Context : Type) [Field F] [Fintype F] [DecidableEq F] [Fintype C]
    {out input : ℕ} (circuit : Native.Circuit F out input) (I : Instance F) where
  /-- The runtime commits only ordinary rows; the shared backend has no product rows. -/
  linearOnly : I.nq = 0
  Pad : Type
  Data : Type
  frontend : Data → LfzkV2.Linear.Replay.Payload circuit
  plan : LfzkV2.Linear.Replay.PadPlan (Pad := Pad) circuit
  sampling : LfzkV2.Linear.Replay.Sampling (C := C) circuit
  dflt : C
  packed : Bool
  cutoff : ℕ
  bound : ℕ
  cutoff_gt : I.r + I.w - 1 < cutoff
  packing : CodingTheory.UniformFamilyBound I.n cutoff (I.r + I.w - 1) bound
  inputOf : Context → (Counting.tupleCounts I).Index → Cube input → F
  padOf : (Counting.tupleCounts I).Index → Pad → F
  statement : ((Context × Data) × F) → (ℕ → C) → I.layer.Statement
  statement_prefix : ∀ p first second,
    (∀ j, j < LfzkV2.Linear.Replay.slots circuit + Replay.packingSlots packed → first j = second j) →
    statement p first = statement p second
  precheck : Context × Data → Prop
  packingBad : I.layer.Oracle → Context × Data →
    (Fin (LfzkV2.Linear.Replay.slots circuit) → C) → C → Prop
  packingBudget : ℚ
  packingBudget_nonneg : 0 ≤ packingBudget
  packing_count : ∀ W p pref,
    (∑ c : C, indicator (packingBad W p pref c)) ≤ packingBudget
  decodeCoin : C → I.layer.Coin
  decodeQuery : C → I.layer.Query
  potential : TerminalPotential I cutoff decodeCoin decodeQuery
  transfer : ∀ (W : I.layer.Oracle)
      (H : Replay.Domain Context circuit I (Context × Data) → C)
      (s : Replay.Selected I (Context × Data)) (candidate : Fin bound),
    precheck s.1.1 →
    I.layer.satisfies
      (FiatShamir.statementAt circuit I Prod.fst (frontend ∘ Prod.snd) statement H s.1)
      ((Counting.tupleCounts I).witness (Counting.committedCandidate I W cutoff bound candidate)) →
    FiatShamir.frontendAccepts circuit I plan sampling Prod.fst (frontend ∘ Prod.snd)
      (fun W i => inputOf s.1.1.1 (Counting.committedCandidate I W cutoff bound i))
      (fun W i => padOf (Counting.committedCandidate I W cutoff bound i)) W H s.1.1 candidate ∨
    FiatShamir.packingEvent circuit I packed Prod.fst (frontend ∘ Prod.snd) packingBad W H s.1.1

namespace CompiledSide

variable {F C Context : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype C]
variable {out input : ℕ} {circuit : Native.Circuit F out input} {I : Instance F}
variable (S : CompiledSide F C Context circuit I)

abbrev Parent := Context × S.Data
abbrev Domain := Replay.Domain Context circuit I S.Parent
abbrev Selected := Replay.Selected I S.Parent

def slots : ℕ := LfzkV2.Linear.Replay.slots circuit + Replay.packingSlots S.packed + 2
def points : PrefixPoints S.Domain :=
  Replay.points circuit I S.packed Prod.fst (S.frontend ∘ Prod.snd)
def key : S.Domain → Context := Replay.key circuit I Prod.fst
def context (s : S.Selected) : Context := s.1.1.1
def hashInput : S.Selected → ℕ → S.Domain :=
  Replay.hashInput circuit I S.packed Prod.fst (S.frontend ∘ Prod.snd)

theorem hashInput_key (s : S.Selected) (j : ℕ) : S.key (S.hashInput s j) = S.context s :=
  Replay.hashInput_key circuit I S.packed Prod.fst (S.frontend ∘ Prod.snd) s j

theorem slot_hashInput (s : S.Selected) (j : ℕ) (hj : j < S.slots) :
    S.points.slot (S.hashInput s j) = j :=
  Replay.slot_hashInput circuit I S.packed Prod.fst (S.frontend ∘ Prod.snd) s j hj

noncomputable def candidateInput (ctx : Context) (W : I.layer.Oracle) (i : Fin S.bound) : Cube input → F :=
  S.inputOf ctx (Counting.committedCandidate I W S.cutoff S.bound i)

noncomputable def candidatePads (W : I.layer.Oracle) (i : Fin S.bound) : S.Pad → F :=
  S.padOf (Counting.committedCandidate I W S.cutoff S.bound i)

def Good (ctx : Context) (W : I.layer.Oracle) (g : (Counting.tupleCounts I).Index) : Prop :=
  g ∈ Counting.committedCandidates I W S.cutoff ∧ circuit.Satisfies (S.inputOf ctx g)

noncomputable def charge (W : I.layer.Oracle) (x : S.Domain)
    (pref : Fin (S.points.slot x) → C) (c : C) : ℚ :=
  FiatShamir.charge circuit I S.plan S.sampling S.dflt S.packed Prod.fst (S.frontend ∘ Prod.snd)
    (S.candidateInput (S.key x)) S.candidatePads S.statement S.packingBad S.potential W x pref c

noncomputable def budget (x : S.Domain) : ℚ :=
  FiatShamir.budget (bound := S.bound) circuit I S.sampling S.packed S.packingBudget S.potential x

noncomputable def maxBudget : ℚ :=
  FiatShamir.maxBudget (bound := S.bound) circuit I S.sampling S.packed S.packingBudget S.potential

noncomputable def slotBudget (i : Fin S.slots) : ℚ :=
  FiatShamir.slotBudget (bound := S.bound) circuit I S.sampling S.packed S.packingBudget S.potential i

theorem charge_nonneg (W : I.layer.Oracle) (x : S.Domain)
    (pref : Fin (S.points.slot x) → C) (c : C) : 0 ≤ S.charge W x pref c :=
  FiatShamir.charge_nonneg circuit I S.plan S.sampling S.dflt S.packed Prod.fst (S.frontend ∘ Prod.snd)
    (S.candidateInput _) S.candidatePads S.statement S.packingBad S.potential W x pref c

theorem budget_nonneg (x : S.Domain) : 0 ≤ S.budget x :=
  FiatShamir.budget_nonneg (bound := S.bound) circuit I S.sampling S.packed S.packingBudget S.potential
    S.packingBudget_nonneg x

theorem maxBudget_nonneg : 0 ≤ S.maxBudget :=
  FiatShamir.maxBudget_nonneg (bound := S.bound) circuit I S.sampling S.packed S.packingBudget S.potential

theorem budget_le_max (x : S.Domain) : S.budget x ≤ S.maxBudget :=
  FiatShamir.budget_le_max (bound := S.bound) circuit I S.sampling S.packed S.packingBudget S.potential x

theorem budget_hashInput (s : S.Selected) (i : Fin S.slots) :
    S.budget (S.hashInput s i.val) = S.slotBudget i :=
  FiatShamir.budget_hashInput (bound := S.bound) circuit I S.sampling S.packed Prod.fst
    (S.frontend ∘ Prod.snd) S.packingBudget S.potential s i

theorem charge_sum_le (W : I.layer.Oracle) (x : S.Domain)
    (pref : Fin (S.points.slot x) → C) : (∑ c : C, S.charge W x pref c) ≤ S.budget x :=
  FiatShamir.charge_sum_le circuit I S.plan S.sampling S.dflt S.packed Prod.fst (S.frontend ∘ Prod.snd)
    (S.candidateInput _) S.candidatePads S.statement S.packingBad S.packingBudget S.potential
    S.packing_count W x pref

noncomputable def statementAt (H : S.Domain → C) (s : S.Selected) : I.layer.Statement :=
  FiatShamir.statementAt circuit I Prod.fst (S.frontend ∘ Prod.snd) S.statement H s.1

noncomputable def Accepts (W : I.layer.Oracle) (H : S.Domain → C) (s : S.Selected) : Prop :=
  S.precheck s.1.1 ∧ I.layer.verify (S.statementAt H s) W
    (S.decodeCoin (H (Replay.backend circuit I s.1))) s.2
    (S.decodeQuery (H (Replay.opening circuit I s.1 s.2)))

theorem path_charge_ge_one (W : I.layer.Oracle) (H : S.Domain → C) (s : S.Selected)
    (hbad : ¬ ∃ g, S.Good (S.context s) W g) (haccept : S.Accepts W H s) :
    1 ≤ ∑ i : Fin S.slots, S.charge W (S.hashInput s i.val)
      (S.points.chal H (S.hashInput s i.val)) (H (S.hashInput s i.val)) := by
  have hp := FiatShamir.path_charge_ge_one circuit I S.plan S.sampling S.dflt S.packed Prod.fst
    (S.frontend ∘ Prod.snd) (S.candidateInput (S.context s)) S.candidatePads S.statement S.packingBad
    S.potential S.statement_prefix W H s
    (Counting.committedCandidates_card_le I W S.cutoff S.bound S.cutoff_gt S.packing)
    (by intro i hmem hsat; exact hbad ⟨_,hmem,hsat⟩)
    (fun i hsat => S.transfer W H s i haccept.1 hsat) haccept.2
  refine hp.trans_eq ?_
  apply sum_congr rfl
  intro i _
  dsimp only [charge]
  rw [S.hashInput_key]
  rfl

noncomputable def CompiledAccepts {Salt D Enc : Type} [Inhabited D] (ht : 0 < I.t)
    (scheme : Merkle.MH.Scheme Salt (MerkleCompiler.Leaf F I.nw I.nq) D Enc)
    (H : S.Domain → C) (s : S.Selected) (root : D)
    (claim : Merkle.MH.OpeningClaim I.n Salt (MerkleCompiler.Leaf F I.nw I.nq) D) : Prop :=
  S.precheck s.1.1 ∧ (MerkleCompiler.compiler I ht).Accepts scheme (S.statementAt H s) root
    (S.decodeCoin (H (Replay.backend circuit I s.1))) s.2
    (S.decodeQuery (H (Replay.opening circuit I s.1 s.2))) claim

theorem accepts_of_extraction {Salt D Enc : Type} [DecidableEq D] [Inhabited D] [Inhabited Salt]
    [Inhabited (MerkleCompiler.Leaf F I.nw I.nq)]
    (ht : 0 < I.t) {codec : Merkle.MH.Codec Salt (MerkleCompiler.Leaf F I.nw I.nq) D Enc}
    (dec : Merkle.MH.RoleDecoders codec)
    (scheme : Merkle.MH.Scheme Salt (MerkleCompiler.Leaf F I.nw I.nq) D Enc)
    (H : S.Domain → C) (s : S.Selected) (root : D) (trace : List (Enc × D))
    (claim : Merkle.MH.OpeningClaim I.n Salt (MerkleCompiler.Leaf F I.nw I.nq) D)
    (e : Merkle.MH.Extracted I.n Salt (MerkleCompiler.Leaf F I.nw I.nq) D)
    (hext : Merkle.MH.extract dec I.n root trace = some e)
    (hagree : ∀ j ∈ claim.I, e.message j = claim.a j)
    (haccept : S.CompiledAccepts ht scheme H s root claim) :
    S.Accepts (MerkleCompiler.extractedOracle I dec root trace) H s :=
  ⟨haccept.1, MerkleCompiler.verify_of_extraction I ht dec scheme _ root trace _ s.2 _ claim e
    hext hagree haccept.2⟩

end CompiledSide
end LfzkV2.Linear.Runtime
