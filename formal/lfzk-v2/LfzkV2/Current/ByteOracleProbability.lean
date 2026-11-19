import LfzkV2.Current.ByteOracleTransport
import Mathlib.SetTheory.Cardinal.Finite

/-! Uniform finite marginals of the byte oracle split into canonical query
answers and independent outside-image answers. The final window theorem
uses only the finite set of possible program queries and canonical inputs;
the full byte-string type may remain infinite. -/
noncomputable section
namespace LfzkV2.Current.ByteOracleTransport
open Finset
open scoped Classical

/-- Reindexing preserves a finite uniform probability exactly. -/
theorem ratio_equiv {X Y : Type} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (event : Y → Prop) :
    ((univ.filter fun x => event (e x)).card : ℚ)/Fintype.card X =
      ((univ.filter event).card : ℚ)/Fintype.card Y := by
  have hc : (univ.filter fun x : X => event (e x)).card = (univ.filter event).card :=
    Finset.card_equiv e (fun _ => by simp)
  rw [hc,Fintype.card_congr e]

/-- A bound uniform in independent auxiliary coins also bounds their average. -/
theorem product_ratio_le {X Y : Type} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    (event : X × Y → Prop) (bound : ℚ)
    (h : ∀ y, ((univ.filter fun x => event (x,y)).card : ℚ)/Fintype.card X ≤ bound) :
    ((univ.filter event).card : ℚ)/Fintype.card (X × Y) ≤ bound := by
  have hc : (univ.filter event).card = ∑ y : Y, (univ.filter fun x : X => event (x,y)).card := by
    simp only [card_eq_sum_ones,sum_filter]
    rw [Fintype.sum_prod_type]
    exact sum_comm
  have hp : (0 : ℚ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hq : (0 : ℚ) < Fintype.card Y := by exact_mod_cast Fintype.card_pos
  rw [Fintype.card_prod,Nat.cast_mul,div_le_iff₀ (mul_pos hp hq),hc,Nat.cast_sum]
  calc
    ∑ y : Y, ((univ.filter fun x : X => event (x,y)).card : ℚ) ≤
        ∑ _y : Y, bound*Fintype.card X := by
      apply sum_le_sum
      intro y _
      exact (div_le_iff₀ hp).mp (h y)
    _ = bound*(Fintype.card X*Fintype.card Y) := by simp; ring

namespace Codec
variable {Point Raw A : Type} {valid : Point → Prop} (codec : Codec Point Raw valid)

/-- Restriction to the two disjoint input classes gives an equivalence of
whole oracle tables, including every outside-image answer. -/
def oracleEquiv : (Raw → A) ≃
    ({point // valid point} → A) × ({raw // codec.decode raw = none} → A) where
  toFun H := (fun point => H (codec.encode point),fun raw => H raw.val)
  invFun pair raw := match h : codec.decode raw with
    | some point => pair.1 point
    | none => pair.2 ⟨raw,h⟩
  left_inv H := by
    funext raw
    dsimp only
    split
    · rename_i point hp
      exact congrArg H (codec.encode_decode raw point hp)
    · rfl
  right_inv pair := by
    apply Prod.ext
    · funext point
      dsimp only
      split
      · rename_i other hp
        have he : other = point := Option.some.inj (hp.symm.trans (codec.decode_encode point))
        cases he
        rfl
      · rename_i hn
        have hp := codec.decode_encode point
        rw [hn] at hp
        contradiction
    · funext raw
      dsimp only
      split
      · rename_i point hp
        rw [raw.property] at hp
        contradiction
      · rfl

def canonicalOracle (outside : Raw → A) (H : {point // valid point} → A) (raw : Raw) : A :=
  match codec.decode raw with
  | some point => H point
  | none => outside raw

/-- Complete an arbitrary outside-image table. The value on canonical
bytes is unused by the combined oracle. -/
def outsideOracle (dflt : A) (outside : {raw // codec.decode raw = none} → A) (raw : Raw) : A :=
  if h : codec.decode raw = none then outside ⟨raw,h⟩ else dflt

theorem oracleEquiv_symm (dflt : A) (inside : {point // valid point} → A)
    (outside : {raw // codec.decode raw = none} → A) :
    codec.oracleEquiv.symm (inside,outside) = codec.canonicalOracle (codec.outsideOracle dflt outside) inside := by
  funext raw
  dsimp only [oracleEquiv,Equiv.coe_fn_symm_mk]
  split
  · rename_i point hp
    simp only [canonicalOracle,hp]
  · rename_i hn
    simp [canonicalOracle,hn,outsideOracle]

/-- Conditioning on every outside-image answer leaves the canonical
answers uniform. A bound uniform in that conditioning is therefore a bound
for the complete finite raw-oracle experiment. -/
theorem finite_ratio_le [Fintype Raw] [Fintype {point // valid point}] [Fintype A]
    (dflt : A) (event : (Raw → A) → Prop) (bound : ℚ)
    (h : ∀ outside : Raw → A,
      ((univ.filter fun H : {point // valid point} → A => event (codec.canonicalOracle outside H)).card : ℚ) /
        Fintype.card ({point // valid point} → A) ≤ bound) :
    ((univ.filter event).card : ℚ)/Fintype.card (Raw → A) ≤ bound := by
  letI : Nonempty A := ⟨dflt⟩
  rw [← ratio_equiv codec.oracleEquiv.symm event]
  apply product_ratio_le
  intro outside
  simpa only [codec.oracleEquiv_symm dflt] using h (codec.outsideOracle dflt outside)


section Window
variable {QL DL Out : Type} [Fintype A] [Fintype DL] [DecidableEq Raw]
variable [Fintype {point // valid point}]

/-- Extend a finite oracle table by arbitrary fixed answers elsewhere. -/
def extendWindow (window : Finset Raw) (table : {raw // raw ∈ window} → A)
    (fallback : Raw → A) (raw : Raw) : A :=
  if h : raw ∈ window then table ⟨raw,h⟩ else fallback raw

/-- The finite window contains every canonical encoding. Its conditional
oracle therefore extends to precisely the same raw oracle as the original
partial codec, including inputs outside the window. -/
theorem extendWindow_canonical {left right : ℕ}
    (body : Merkle.RandomOracle.TwoOracleTree QL DL Raw A Out left right)
    (outside : {raw // raw ∈ codec.window body} → A)
    (fallback : Raw → A) (H : {point // valid point} → A) :
    extendWindow (codec.window body) ((codec.windowCodec body).canonicalOracle outside H) fallback =
      codec.canonicalOracle (extendWindow (codec.window body) outside fallback) H := by
  funext raw
  by_cases hmem : raw ∈ codec.window body
  · simp only [extendWindow,dif_pos hmem,canonicalOracle,windowCodec]
  · have hdecode : codec.decode raw = none := by
      cases hd : codec.decode raw with
      | none => rfl
      | some point =>
          apply False.elim
          apply hmem
          rw [← codec.encode_decode raw point hd]
          exact codec.encode_mem_window body point
    simp only [extendWindow,dif_neg hmem,canonicalOracle,hdecode]

/-- A bound uniform in the outside oracle lifts to the finite raw-query
marginal for any bounded adaptive program. `Raw` itself can be infinite.
The window is chosen from the entire program syntax before any answers,
and its extra coordinates are averaged, not charged as protocol queries. -/
theorem window_ratio_le {left right : ℕ}
    (body : Merkle.RandomOracle.TwoOracleTree QL DL Raw A Out left right)
    (dflt : A) (fallback : Raw → A) (event : (Raw → A) → Prop) (bound : ℚ)
    (h : ∀ outside : Raw → A,
      ((univ.filter fun H : {point // valid point} → A => event (codec.canonicalOracle outside H)).card : ℚ) /
        Fintype.card ({point // valid point} → A) ≤ bound) :
    ((univ.filter fun table : {raw // raw ∈ codec.window body} → A =>
      event (extendWindow (codec.window body) table fallback)).card : ℚ) /
      Fintype.card ({raw // raw ∈ codec.window body} → A) ≤ bound := by
  have hlocal (outside : {raw // raw ∈ codec.window body} → A) :
      ((univ.filter fun H : {point // valid point} → A => event
        (extendWindow (codec.window body) ((codec.windowCodec body).canonicalOracle outside H) fallback)).card : ℚ) /
        Fintype.card ({point // valid point} → A) ≤ bound := by
    simpa only [extendWindow_canonical] using h (extendWindow (codec.window body) outside fallback)
  have result := (codec.windowCodec body).finite_ratio_le dflt
    (fun table => event (extendWindow (codec.window body) table fallback)) bound hlocal
  simpa only [← Fintype.card_subtype,← Nat.card_eq_fintype_card] using result

end Window

end Codec
end LfzkV2.Current.ByteOracleTransport
