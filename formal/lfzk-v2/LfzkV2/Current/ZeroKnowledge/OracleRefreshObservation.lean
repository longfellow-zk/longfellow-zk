import LfzkV2.Current.ZeroKnowledge.OracleResults

/-! Aborting completion and one whole-answer update commute with observing
the public result. The proof packets are abstract here, so branch selection
does not inspect a circuit or normalize a concrete proof body. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.OracleRefreshObservation
open scoped Classical
variable {Packet Public Point Answer MerkleQuery MerkleAnswer View : Type}

theorem totalize_map_selected (response : Option Packet) (HM : MerkleQuery → MerkleAnswer) (H : Point → Answer)
    (answer : Answer) (key : Packet → Point) (finish : Packet → (Point → Answer) → Public)
    (observe : Option Public → (Point → Answer) → View) (selected : Point → Answer)
    (abort : response = none → selected = H)
    (success : ∀ proof, response = some proof → selected = Function.update H (key proof) answer) :
    let completed := response.map fun proof =>
      let oracle := Function.update H (key proof) answer
      (finish proof oracle,oracle)
    let total := OracleResults.totalize HM H completed
    observe total.1 total.2.2 = observe (response.map fun proof => finish proof selected) selected := by
  cases response with
  | none => rw [abort rfl]; rfl
  | some proof => rw [success proof rfl]; rfl

theorem totalize_map (response : Option Packet) (HM : MerkleQuery → MerkleAnswer) (H : Point → Answer)
    (answer : Answer) (sourceKey : Point) (key : Packet → Point)
    (finish : Packet → (Point → Answer) → Public)
    (observe : Option Public → (Point → Answer) → View)
    (correct : ∀ proof, response = some proof → sourceKey = key proof) :
    let completed := response.map fun proof =>
      let oracle := Function.update H (key proof) answer
      (finish proof oracle,oracle)
    let total := OracleResults.totalize HM H completed
    observe total.1 total.2.2 =
      let oracle := if response.isSome then Function.update H sourceKey answer else H
      observe (response.map fun proof => finish proof oracle) oracle := by
  cases response with
  | none => rfl
  | some proof =>
      have same := correct proof rfl
      simp only [Option.map_some,Option.isSome_some,↓reduceIte,OracleResults.totalize]
      rw [same]

end LfzkV2.Current.ZeroKnowledge.OracleRefreshObservation
