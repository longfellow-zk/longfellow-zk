import LfzkV2.Current.ApplicationOracle
import Mathlib.Data.ZMod.Basic

noncomputable section
namespace LfzkV2.Current.Tests.BatchPacket
open ApplicationOracle
open scoped Classical
private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private def data : BatchData (ZMod 3) Unit Unit where
  rows := [⟨0,[]⟩]
  values _ _ := 0

private abbrev Raw := Fin data.rows.length → ZMod 3

/-- This finite nonempty answer type supports exactly the actual row vector.
Constructing this packet never requires decoding arbitrary row dimensions. -/
private def packet : BatchPacket (ZMod 3) Unit Unit Raw where
  data := data
  decoder := {
    decode := id
    fiber := 1
    fiber_bound := by
      intro z
      apply Finset.card_le_one.mpr
      intro a ha b hb
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at ha hb
      exact ha.trans hb.symm
    balanced := by simp }

example : packet.data.rows.length = 1 := rfl
example : Fintype.card Raw = 3 := by simp [Raw,data]
example (answer : Raw) : packet.decoder.decode answer = answer := rfl
example (answer : Raw) : (packet.decoderAt rfl).decode answer = answer := rfl
example : (Finset.univ.filter (packet.bad ())).card * Fintype.card (ZMod 3) ≤
    Fintype.card Raw := packet.bad_card_mul_le ()

end LfzkV2.Current.Tests.BatchPacket
