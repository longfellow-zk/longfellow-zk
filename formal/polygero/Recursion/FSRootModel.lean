import polygero.Recursion.FSTerminalBlock
import polygero.Recursion.FSJointCompletion
import Bcs.ContextualCompletion
import Bcs.CutContext
import Bcs.PotentialCommit

/-! The two-level transform with actual digest-valued commitments. -/
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
namespace RecursivePolygero.FiatShamir.MerkleFS
open Finset ProfileAnalysis Local Local.Polygero Bcs.TotalOracle Bcs.TotalOracle.Footprint
open TwoLevel
open scoped Classical
variable {F D : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype D] [DecidableEq D]
variable {I : Instance F} (child : Child I)

abbrev Candidate := TwoLevel.Candidate D D I.layer.Query child.instance.layer.Payload
abbrev Point := TwoLevel.Input D D I.layer.Query child.instance.layer.Payload
abbrev Answer := TwoLevel.Answer child
abbrev Leaf (J : Instance F) := Column F J.nw J.nq × F

def oracleOfLeaves (J : Instance F) (m : Fin J.n → Leaf J) : J.layer.Oracle :=
  ⟨⟨fun b i j => (m j).1.core b i, fun k j => (m j).1.checkedMask k⟩, fun j => (m j).2⟩

def leaves (J : Instance F) (W : J.layer.Oracle) (j : Fin J.n) : Leaf J :=
  (W.ordinary.column j,W.proximityMask j)

@[simp] theorem oracleOfLeaves_leaves (J : Instance F) (W : J.layer.Oracle) :
    oracleOfLeaves J (leaves J W) = W := by cases W; rfl

@[simp] theorem leaves_oracleOfLeaves (J : Instance F) (m : Fin J.n → Leaf J) :
    leaves J (oracleOfLeaves J m) = m := by
  funext j
  rfl

def childCommitment : Point child (D := D) → Option (D × D)
  | .inl _ => none
  | .inr (.inl ab) => some ab
  | .inr (.inr (.inl b)) => some (b.1,b.2.1)
  | .inr (.inr (.inr d)) => some (d.1,d.2.1)

def childPrefix (d : Candidate child (D := D)) := (d.1,d.2.1,d.2.2.1)

def blockKey : Point child (D := D) → Option (D × D × I.layer.Query)
  | .inl _ => none
  | .inr (.inl _) => none
  | .inr (.inr (.inl b)) => some b
  | .inr (.inr (.inr d)) => some (childPrefix child d)

noncomputable def childBlock (b : D × D × I.layer.Query) : Finset (Point child (D := D)) :=
  univ.filter (fun x => blockKey child x = some b)

def role : Point child (D := D) → Fin 4
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr (.inl _)) => 2
  | .inr (.inr (.inr _)) => 3

noncomputable def queryDomain : Finset (Point child (D := D)) := univ.filter (fun x => role child x < 2)
noncomputable def terminalDomain : Finset (Point child (D := D)) := univ.filter (fun x => 2 ≤ role child x)

/-- The two oracle extractions may depend on all answers outside their
commitment fibers. Cut-trace extraction will instantiate these invariances. -/
structure Context where
  parent : D → (Point child (D := D) → Answer child) → I.layer.Oracle
  descendant : D × D → (Point child (D := D) → Answer child) → child.instance.layer.Oracle
  parent_off : ∀ a H H', (∀ x, TwoLevel.root x ≠ a → H x = H' x) → parent a H = parent a H'
  descendant_off : ∀ ab H H', (∀ x, childCommitment child x ≠ some ab → H x = H' x) →
    descendant ab H = descendant ab H'

variable (ctx : Context child (D := D))

def liftOracle (a b : D) (H : Point child (D := D) → Answer child) : TwoLevel.HashInput child → Answer child
  | .inl _ => H (gamma a)
  | .inr (.inl _) => H (query a b)
  | .inr (.inr (.inl c)) => H (childGamma a b c.2.2)
  | .inr (.inr (.inr d)) => H (terminal (a,b,d.2.2.1,d.2.2.2))

noncomputable def extractedCandidate (d : Candidate child (D := D)) (H : Point child (D := D) → Answer child) : TwoLevel.Proof child :=
  (ctx.parent d.1 H,ctx.descendant (d.1,d.2.1) H,d.2.2.1,d.2.2.2)

noncomputable def failure (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)
    (σ : I.layer.Statement) (d : Candidate child (D := D)) (H : Point child (D := D) → Answer child) : Prop :=
  TwoLevel.failure child p cp σ (fun _ => False) (liftOracle child d.1 d.2.1 H)
    (extractedCandidate child (D := D) ctx d H)

noncomputable def queryRisk (cp : HahnSystemCertificate child.instance) (σ : I.layer.Statement)
    (a b : D) (H : Point child (D := D) → Answer child) : Prop :=
  queryCapacityRisk child cp σ (ctx.parent a H) (ctx.descendant (a,b) H)
    (H (gamma a)).1.1 (H (query a b)).1.2

noncomputable def capacity (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)
    (σ : I.layer.Statement) (a : D) (H : Point child (D := D) → Answer child) (coin : Answer child) : ℚ :=
  queryCapacity child p cp σ (ctx.parent a H) coin.1.1

theorem parent_off_point (a : D) (x : Point child (D := D)) (hx : TwoLevel.root x = a)
    (H H' : Point child (D := D) → Answer child) (ho : AgreeOff x H H') : ctx.parent a H = ctx.parent a H' := by
  apply ctx.parent_off
  intro y hy
  exact ho y (fun h => hy (h ▸ hx))

theorem descendant_off_point (ab : D × D) (x : Point child (D := D))
    (hx : childCommitment child x = some ab) (H H' : Point child (D := D) → Answer child)
    (ho : AgreeOff x H H') : ctx.descendant ab H = ctx.descendant ab H' := by
  apply ctx.descendant_off
  intro y hy
  exact ho y (fun h => hy (h ▸ hx))

/-- A complete parent/query resampling fixes the extracted parent, while
allowing the child extraction to depend on the parent challenge. -/
theorem parent_off_pair (a b : D) (H H' : Point child (D := D) → Answer child)
    (ho : ∀ x, x ∉ ({gamma a,query a b} : Finset (Point child (D := D))) → H x = H' x) :
    ctx.parent a H = ctx.parent a H' := by
  apply ctx.parent_off
  intro x hx
  apply ho
  simp only [mem_insert,mem_singleton,not_or]
  exact ⟨fun he => hx (he ▸ rfl),fun he => hx (he ▸ rfl)⟩

end RecursivePolygero.FiatShamir.MerkleFS
