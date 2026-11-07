import Mathlib.Data.Set.Function
import Mathlib.Data.Option.Basic

/-! Observable results at an oracle boundary. These interfaces contain
the public output and oracle agreement only; circuit descriptions, private
states and transcript implementations are absent. An abort retains the
original oracles. Successful completion retains the returned oracle. -/
namespace LfzkV2.Current.ZeroKnowledge.OracleResults
variable {Point Answer MerkleQuery MerkleAnswer Public : Type}

/-- Equality of public results with the same Merkle oracle and the same
answers at every transcript coordinate available to an observer. -/
structure Same (valid : Set Point)
    (first second : Public × ((MerkleQuery → MerkleAnswer) × (Point → Answer))) : Prop where
  public_eq : first.1 = second.1
  merkle_eq : first.2.1 = second.2.1
  transcript_eq : Set.EqOn first.2.2 second.2.2 valid

/-- Completion either aborts on both sides or returns the same public
output with the same observable transcript oracle. -/
structure SameCompletion (valid : Set Point)
    (first second : Option (Public × (Point → Answer))) : Prop where
  relation : Option.Rel (fun a b => a.1 = b.1 ∧ Set.EqOn a.2 b.2 valid) first second

def totalize (HM : MerkleQuery → MerkleAnswer) (H : Point → Answer)
    (result : Option (Public × (Point → Answer))) :
    Option Public × ((MerkleQuery → MerkleAnswer) × (Point → Answer)) :=
  match result with
  | none => (none,(HM,H))
  | some result => (some result.1,(HM,result.2))

theorem Same.refl (valid : Set Point)
    (result : Public × ((MerkleQuery → MerkleAnswer) × (Point → Answer))) : Same valid result result :=
  ⟨rfl,rfl,fun _ _ => rfl⟩

theorem Same.symm {valid : Set Point}
    {first second : Public × ((MerkleQuery → MerkleAnswer) × (Point → Answer))}
    (same : Same valid first second) : Same valid second first :=
  ⟨same.public_eq.symm,same.merkle_eq.symm,fun _ member => (same.transcript_eq member).symm⟩

theorem Same.trans {valid : Set Point}
    {first middle last : Public × ((MerkleQuery → MerkleAnswer) × (Point → Answer))}
    (one : Same valid first middle) (two : Same valid middle last) : Same valid first last :=
  ⟨one.public_eq.trans two.public_eq,one.merkle_eq.trans two.merkle_eq,
    fun _ member => (one.transcript_eq member).trans (two.transcript_eq member)⟩

theorem Same.visible_eq {valid : Set Point}
    {first second : Public × ((MerkleQuery → MerkleAnswer) × (Point → Answer))}
    (same : Same valid first second) :
    (fun point : valid => first.2.2 point.val) = (fun point : valid => second.2.2 point.val) := by
  funext point
  exact same.transcript_eq point.property

theorem SameCompletion.none (valid : Set Point) :
    SameCompletion (Public := Public) (Answer := Answer) valid none none := ⟨.none⟩

theorem SameCompletion.some {valid : Set Point}
    {first second : Public × (Point → Answer)}
    (output : first.1 = second.1) (oracle : Set.EqOn first.2 second.2 valid) :
    SameCompletion valid (some first) (some second) := ⟨.some ⟨output,oracle⟩⟩

theorem SameCompletion.mono {valid larger : Set Point}
    {first second : Option (Public × (Point → Answer))}
    (same : SameCompletion larger first second) (subset : valid ⊆ larger) :
    SameCompletion valid first second := by
  cases same.relation with
  | none => exact .none _
  | some success => exact .some success.1 (fun _ member => success.2 (subset member))

theorem SameCompletion.public_eq {valid : Set Point}
    {first second : Option (Public × (Point → Answer))}
    (same : SameCompletion valid first second) : first.map Prod.fst = second.map Prod.fst := by
  cases same.relation with
  | none => rfl
  | some success => exact congrArg Option.some success.1

theorem SameCompletion.abort_eq {valid : Set Point}
    {first second : Option (Public × (Point → Answer))}
    (same : SameCompletion valid first second) : first.isSome = second.isSome := by
  cases same.relation <;> rfl

/-- Totalizing a partial completion preserves the original oracle on an
abort. No concrete completion program needs to be unfolded by callers. -/
theorem SameCompletion.totalize {valid : Set Point}
    {first second : Option (Public × (Point → Answer))}
    (same : SameCompletion valid first second) (HM : MerkleQuery → MerkleAnswer)
    (H H' : Point → Answer) (fallback : Set.EqOn H H' valid) :
    Same valid (totalize HM H first) (totalize HM H' second) := by
  cases same.relation with
  | none => exact ⟨rfl,rfl,fallback⟩
  | some success => exact ⟨congrArg Option.some success.1,rfl,success.2⟩

end LfzkV2.Current.ZeroKnowledge.OracleResults
