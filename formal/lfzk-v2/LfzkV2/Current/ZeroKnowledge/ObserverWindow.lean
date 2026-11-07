import LfzkV2.Current.ZeroKnowledge.MerkleOracleWindow

/-! One static Merkle window for an entire adaptive observer experiment.
It covers the prior program and every request/proof branch of the later
program. In particular it is fixed before private coins, an opening answer,
or a resulting programmed transcript oracle are selected. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.ObserverWindow
open Merkle Merkle.MH Merkle.RandomOracle
open scoped Classical

variable {Raw D QT AT Request Proof Observed Salt Leaf : Type}
variable [Fintype D] [Fintype AT] [DecidableEq Raw]
variable [Fintype Request] [Fintype Proof] [Fintype Salt] [Fintype Leaf]
variable {preM preT postM postT : ℕ}
variable (codec : Codec Salt Leaf D Raw)
variable (prior : TwoOracleTree Raw D QT AT Request preM preT)
variable (after : Request → Proof → TwoOracleTree Raw D QT AT Observed postM postT)

abbrev Index (Request Proof : Type) := Unit ⊕ (Request × Proof)

def Results : Index Request Proof → Type
  | .inl _ => Request
  | .inr _ => Observed

def budget : Index Request Proof → Nat × Nat
  | .inl _ => (preM,preT)
  | .inr _ => (postM,postT)

def trees : (index : Index Request Proof) →
    TwoOracleTree Raw D QT AT (Results (Observed := Observed) index)
      (budget (preM := preM) (preT := preT) (postM := postM) (postT := postT) index).1
      (budget (preM := preM) (preT := preT) (postM := postM) (postT := postT) index).2
  | .inl _ => prior
  | .inr pair => after pair.1 pair.2

def window : Finset Raw :=
  MerkleOracleWindow.window codec _ (trees prior after)

def finiteCodec : Codec Salt Leaf D {raw // raw ∈ window codec prior after} :=
  MerkleOracleWindow.finiteCodec codec _ (trees prior after)

theorem finiteCodec_inj (injective : codec.Inj) : (finiteCodec codec prior after).Inj :=
  MerkleOracleWindow.finiteCodec_inj codec _ (trees prior after) injective

def before (HT : QT → AT) :=
  MerkleOracleWindow.finiteResidual codec _ (trees prior after) (.inl ()) HT

def later (request : Request) (proof : Proof) (HT : QT → AT) :=
  MerkleOracleWindow.finiteResidual codec _ (trees prior after) (.inr (request,proof)) HT

theorem before_output
    (HM : {raw // raw ∈ window codec prior after} → D) (outside : Raw → D) (HT : QT → AT) :
    ((before codec prior after HT).run HM).1 =
      Observer.run (OracleWindow.extend (window codec prior after) HM outside) HT prior :=
  MerkleOracleWindow.finiteResidual_output codec _ (trees prior after) (.inl ()) HM outside HT

theorem later_output (request : Request) (proof : Proof)
    (HM : {raw // raw ∈ window codec prior after} → D) (outside : Raw → D) (HT : QT → AT) :
    ((later codec prior after request proof HT).run HM).1 =
      Observer.run (OracleWindow.extend (window codec prior after) HM outside) HT (after request proof) :=
  MerkleOracleWindow.finiteResidual_output codec _ (trees prior after) (.inr (request,proof)) HM outside HT

end LfzkV2.Current.ZeroKnowledge.ObserverWindow
