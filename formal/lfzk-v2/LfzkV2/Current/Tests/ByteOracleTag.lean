import LfzkV2.Current.ByteOracleTransport
import Lean.Util.CollectAxioms

namespace LfzkV2.Current.Tests.ByteOracleTag

def codec : ByteOracleTransport.Codec (Fin 2) Bool (fun point => point = 0) where
  encode _ := false
  decode raw := if raw then none else some ⟨0,rfl⟩
  decode_encode point := by
    have same : point = ⟨0,rfl⟩ := Subtype.ext point.property
    subst point
    rfl
  encode_decode raw point found := by cases raw <;> simp_all

example : codec.tag false = Sum.inl 0 := by simp [codec,ByteOracleTransport.Codec.tag]
example : codec.tag true = Sum.inr true := by simp [codec,ByteOracleTransport.Codec.tag]

-- Padding an invalid typed coordinate cannot invent a raw oracle entry.
example : codec.untag (Sum.inl 1) = none := by simp [ByteOracleTransport.Codec.untag]

example (raw : Bool) : codec.untag (codec.tag raw) = some raw := codec.untag_tag raw

open Lean Elab Command in
run_cmd do
  for endpoint in #[``ByteOracleTransport.Codec.tag_injective,
      ``ByteOracleTransport.Codec.untag_tag, ``ByteOracleTransport.Codec.tag_label] do
    for ax in ← collectAxioms endpoint do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {endpoint}"

end LfzkV2.Current.Tests.ByteOracleTag
