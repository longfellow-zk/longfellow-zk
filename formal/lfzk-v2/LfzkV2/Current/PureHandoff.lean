import LfzkV2.Current.Adapter
import LfzkV2.Current.BalancedDecoder
import LfzkV2.Current.RowBatching

/-! The pure-foreign handoff: the batched claim of `RowBatching` is the
adapter's modular claim. Every value of the participant, pads included, is a
group of bits of the binary commitment, read modulo `p`; the participant
commits nothing and hands on no prime statement. The row weights and the
conversion pair are read from one answer, the row weights first, so the
claim is fixed before the conversion challenges and the conversion count of
`Adapter` applies unchanged. The only escapes are the row-batching event and
the two-challenge conversion event. -/
noncomputable section
namespace LfzkV2.Current.PureHandoff
open Finset SumcheckV2
open scoped Classical

variable {p bits n : ℕ} [Fact p.Prime] {Value : Type}

/-- Foreign storage of every value: bit `i` of the claim's bit vector is bit
`place i` of value `owner i` (`Storage::Foreign` groups, in claim order). -/
structure Groups (Value : Type) (bits : ℕ) where
  owner : Fin bits → Value
  place : Fin bits → ℕ

namespace Groups
variable (g : Groups Value bits)

/-- The residue modulo `p` of the integer whose bits are a value's group. -/
def value (b : Fin bits → Bool) (v : Value) : ZMod p :=
  ∑ i, if g.owner i = v ∧ b i = true then (2 : ZMod p) ^ g.place i else 0

/-- The adapter's per-bit coefficients `c_v * 2^r` for bit `r` of value `v`. -/
def weights (c : Value → ZMod p) : Fin bits → ZMod p :=
  fun i => c (g.owner i) * 2 ^ g.place i

/-- The adapter's residual over the bits is the dense claim's residual over
the decoded values. -/
theorem residual_eq [Fintype Value] (claim : RowBatching.Claim Value (ZMod p))
    (b : Fin bits → Bool) :
    Adapter.residual (g.weights claim.weights) b claim.target =
      claim.residual (g.value b) := by
  unfold Adapter.residual RowBatching.Claim.residual weights value
  congr 1
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  by_cases hb : b i <;> simp [hb, mul_ite]

end Groups

abbrev Conversion (p : ℕ) := Fin 2 → Linear.TerminalSampling.Nonzero (ZMod p)

/-- The conversion event of the pure claim: a false modular claim that both
conversion challenges accept for some permitted quotient. -/
def ConversionBad (g : Groups Value bits) (claim : RowBatching.Claim Value (ZMod p))
    (b : Fin bits → Bool) (M K : ℕ) (alpha : Conversion p) : Prop :=
  Adapter.residual (g.weights claim.weights) b claim.target ≠ 0 ∧
    ∀ j, Adapter.Bad (g.weights claim.weights) b claim.target M K (alpha j)

variable [Fintype Value] {G : Type} [CommGroup G]

/-- The pure-foreign counterpart of `Handoff.split_handoff`. Both product
checks on the batched claim give every row on the decoded values, the
row-batching event, or the conversion event. Quotients may depend on both
conversion challenges. -/
theorem pure_handoff (generator : G) {M K : ℕ} (horder : orderOf generator = M)
    (rows : Fin n → LinearRow Value (ZMod p)) (g : Groups Value bits) (b : Fin bits → Bool)
    (rho : Fin n → ZMod p) (alpha : Conversion p)
    (quotient : Fin 2 → ℕ) (hquotient : ∀ j, quotient j < K)
    (hproducts : ∀ j, Adapter.ProductCheck generator
      (g.weights (RowBatching.batch rows rho).weights) b (RowBatching.batch rows rho).target
      (alpha j).val (quotient j)) :
    RowBatching.Holds rows (g.value b) ∨ RowBatching.Bad rows (g.value b) rho ∨
      ConversionBad g (RowBatching.batch rows rho) b M K alpha := by
  by_cases hzero : Adapter.residual (g.weights (RowBatching.batch rows rho).weights) b
      (RowBatching.batch rows rho).target = 0
  · rw [g.residual_eq] at hzero
    rcases RowBatching.holds_or_bad rows (g.value b) rho hzero with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr ⟨hzero, fun j => ?_⟩)
    exact ⟨quotient j, hquotient j,
      (Adapter.product_check_iff generator horder _ _ _ _ _).mp (hproducts j)⟩

/-- One answer of the pure schedule: the row weights, then the conversion pair. -/
abbrev Sample (p n : ℕ) := (Fin n → ZMod p) × Conversion p

/-- Either escape of the pure handoff at one sample. -/
def Bad (rows : Fin n → LinearRow Value (ZMod p)) (g : Groups Value bits) (b : Fin bits → Bool)
    (M K : ℕ) (x : Sample p n) : Prop :=
  RowBatching.Bad rows (g.value b) x.1 ∨ ConversionBad g (RowBatching.batch rows x.1) b M K x.2

theorem sample_card : Fintype.card (Sample p n) = p ^ n * (p-1) ^ 2 := by
  simp [Sample, Conversion, Fintype.card_prod, ZMod.card]

omit [Fintype Value] in
/-- For a fixed claim, both conversion challenges are bad for at most
`(2*floor(K*p/M)+1)^2` pairs (`Adapter.bad_card`). -/
theorem conversion_card_le (g : Groups Value bits) (claim : RowBatching.Claim Value (ZMod p))
    (b : Fin bits → Bool) {M K : ℕ} (hM : 0 < M) (hbits : bits ≤ K) :
    (univ.filter (ConversionBad g claim b M K)).card ≤ (2 * (K*p/M) + 1) ^ 2 := by
  by_cases hfalse : Adapter.residual (g.weights claim.weights) b claim.target = 0
  · simp [ConversionBad, hfalse]
  · have hsub : univ.filter (ConversionBad g claim b M K) ⊆
        Fintype.piFinset fun _ : Fin 2 =>
          univ.filter (Adapter.Bad (g.weights claim.weights) b claim.target M K) := by
      intro alpha h
      exact Fintype.mem_piFinset.mpr fun j =>
        mem_filter.mpr ⟨mem_univ _, (mem_filter.mp h).2.2 j⟩
    refine (card_le_card hsub).trans ?_
    rw [Fintype.card_piFinset, Fin.prod_univ_two, ← sq]
    exact Nat.pow_le_pow_left (Adapter.bad_card _ b claim.target hM hbits hfalse) 2

/-- The joint count over the answer's row weights and conversion pair, for
fixed rows and committed bits. -/
theorem bad_card_mul_le (rows : Fin n → LinearRow Value (ZMod p)) (g : Groups Value bits)
    (b : Fin bits → Bool) {M K : ℕ} (hM : 0 < M) (hbits : bits ≤ K) :
    (univ.filter (Bad rows g b M K)).card * (p * (p-1) ^ 2) ≤
      ((p-1) ^ 2 + p * (2 * (K*p/M) + 1) ^ 2) * Fintype.card (Sample p n) := by
  set A := (univ.filter (RowBatching.Bad rows (g.value b))).card
  set E := (2 * (K*p/M) + 1) ^ 2
  have hA : A * p ≤ p ^ n := by
    simpa [A, ZMod.card] using RowBatching.bad_card_mul_le rows (g.value b)
  have hrow : (univ.filter fun x : Sample p n => RowBatching.Bad rows (g.value b) x.1).card =
      A * (p-1) ^ 2 := by
    have : (univ.filter fun x : Sample p n => RowBatching.Bad rows (g.value b) x.1) =
        univ.filter (RowBatching.Bad rows (g.value b)) ×ˢ (univ : Finset (Conversion p)) := by
      ext x; simp
    rw [this, card_product, card_univ]
    simp [Conversion, ZMod.card, A]
  have hconv : (univ.filter fun x : Sample p n =>
      ConversionBad g (RowBatching.batch rows x.1) b M K x.2).card ≤ p ^ n * E := by
    rw [card_filter, Fintype.sum_prod_type]
    simp only [← card_filter]
    calc _ ≤ ∑ _rho : Fin n → ZMod p, E :=
          sum_le_sum fun rho _ => conversion_card_le g _ b hM hbits
      _ = p ^ n * E := by simp [ZMod.card]
  have hunion : univ.filter (Bad rows g b M K) ⊆
      (univ.filter fun x : Sample p n => RowBatching.Bad rows (g.value b) x.1) ∪
        univ.filter fun x : Sample p n =>
          ConversionBad g (RowBatching.batch rows x.1) b M K x.2 := by
    intro x h
    rcases (mem_filter.mp h).2 with h | h
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, h⟩)
  have hcard := (card_le_card hunion).trans (card_union_le _ _)
  rw [hrow] at hcard
  rw [sample_card]
  calc _ ≤ (A * (p-1) ^ 2 + p ^ n * E) * (p * (p-1) ^ 2) :=
        Nat.mul_le_mul_right _ (hcard.trans (Nat.add_le_add_left hconv _))
    _ = (A * p) * ((p-1) ^ 2 * (p-1) ^ 2) + p ^ n * E * p * (p-1) ^ 2 := by ring
    _ ≤ p ^ n * ((p-1) ^ 2 * (p-1) ^ 2) + p ^ n * E * p * (p-1) ^ 2 :=
        Nat.add_le_add_right (Nat.mul_le_mul_right _ hA) _
    _ = _ := by ring

/-- The pure handoff's error: `1/p` for row batching plus the conversion
error `(2*floor(K*p/M)+1)^2/(p-1)^2` of `Adapter.two_bad_probability_le`. -/
theorem bad_probability_le (rows : Fin n → LinearRow Value (ZMod p)) (g : Groups Value bits)
    (b : Fin bits → Bool) {M K : ℕ} (hM : 0 < M) (hbits : bits ≤ K) :
    ((univ.filter (Bad rows g b M K)).card : ℚ) / Fintype.card (Sample p n) ≤
      1 / p + ((2 * (K*p/M) + 1 : ℕ) : ℚ) ^ 2 / ((p-1 : ℕ) : ℚ) ^ 2 := by
  have hp := (Fact.out : p.Prime).two_le
  have hp0 : (0 : ℚ) < p := by exact_mod_cast (by omega : 0 < p)
  have hq0 : (0 : ℚ) < ((p-1 : ℕ) : ℚ) := by exact_mod_cast (by omega : 0 < p-1)
  have hX : (0 : ℚ) < Fintype.card (Sample p n) := by
    rw [sample_card]; exact_mod_cast Nat.mul_pos (pow_pos (by omega) n) (pow_pos (by omega) 2)
  have hc : ((univ.filter (Bad rows g b M K)).card : ℚ) * (p * ((p-1 : ℕ) : ℚ) ^ 2) ≤
      (((p-1 : ℕ) : ℚ) ^ 2 + p * ((2 * (K*p/M) + 1 : ℕ) : ℚ) ^ 2) *
        Fintype.card (Sample p n) := by
    exact_mod_cast bad_card_mul_le rows g b hM hbits
  have hsplit : 1 / (p : ℚ) + ((2 * (K*p/M) + 1 : ℕ) : ℚ) ^ 2 / ((p-1 : ℕ) : ℚ) ^ 2 =
      (((p-1 : ℕ) : ℚ) ^ 2 + p * ((2 * (K*p/M) + 1 : ℕ) : ℚ) ^ 2) /
        (p * ((p-1 : ℕ) : ℚ) ^ 2) := by
    field_simp
  rw [hsplit, div_le_div_iff₀ hX (by positivity)]
  linarith

/-- Query-local form, as `ApplicationOracle.RescaleData` for the mixed split.
The rows are a function of the answer's earlier coordinates (alpha and the
input weights of the frontend's last answer) and of strict-prefix data; the
row weights and the conversion pair follow in the same answer. -/
structure Data (p bits n : ℕ) (Value W Raw : Type) where
  rows : Raw → Fin n → LinearRow Value (ZMod p)
  groups : Groups Value bits
  values : W → Fin bits → Bool

def Data.bad {W Raw : Type} (d : Data p bits n Value W Raw) (M K : ℕ) (w : W) (raw : Raw)
    (x : Sample p n) : Prop :=
  Bad (d.rows raw) d.groups (d.values w) M K x

theorem Data.bad_card_mul_le {W Raw V : Type} [Fintype Raw] [Fintype V]
    (d : Data p bits n Value W Raw) (w : W) {M K : ℕ} (hM : 0 < M) (hbits : bits ≤ K)
    (decoder : BalancedDecoder Raw (V × Sample p n))
    (hrows : ∀ a b, (decoder.decode a).1 = (decoder.decode b).1 → d.rows a = d.rows b) :
    (univ.filter fun raw => d.bad M K w raw (decoder.decode raw).2).card * (p * (p-1) ^ 2) ≤
      ((p-1) ^ 2 + p * (2 * (K*p/M) + 1) ^ 2) * Fintype.card Raw := by
  let bad' : V × Sample p n → Prop := fun s => ∃ a, (decoder.decode a).1 = s.1 ∧ d.bad M K w a s.2
  letI : DecidablePred bad' := fun s => Classical.propDecidable (bad' s)
  have hsub : (univ.filter fun raw => d.bad M K w raw (decoder.decode raw).2) ⊆
      univ.filter fun raw => bad' (decoder.decode raw) := by
    intro raw hraw
    exact mem_filter.mpr ⟨mem_univ _, raw, rfl, (mem_filter.mp hraw).2⟩
  have hfiber : ∀ v : V, (univ.filter fun x : Sample p n => bad' (v, x)).card * (p * (p-1) ^ 2) ≤
      ((p-1) ^ 2 + p * (2 * (K*p/M) + 1) ^ 2) * Fintype.card (Sample p n) := by
    intro v
    by_cases hv : ∃ a, (decoder.decode a).1 = v
    · obtain ⟨a, ha⟩ := hv
      have hs : (univ.filter fun x : Sample p n => bad' (v, x)) ⊆
          univ.filter (Bad (d.rows a) d.groups (d.values w) M K) := by
        intro x hx
        obtain ⟨a', ha', hbad⟩ := (mem_filter.mp hx).2
        have hr := hrows a' a (ha'.trans ha.symm)
        exact mem_filter.mpr ⟨mem_univ _, by simpa only [Data.bad, hr] using hbad⟩
      exact (Nat.mul_le_mul_right _ (card_le_card hs)).trans
        (PureHandoff.bad_card_mul_le (d.rows a) d.groups (d.values w) hM hbits)
    · have hempty : (univ.filter fun x : Sample p n => bad' (v, x)) = ∅ := by
        apply filter_false_of_mem
        rintro x - ⟨a, ha, -⟩
        exact hv ⟨a, ha⟩
      simp [hempty]
  have hlocal : (univ.filter bad').card * (p * (p-1) ^ 2) ≤
      ((p-1) ^ 2 + p * (2 * (K*p/M) + 1) ^ 2) * Fintype.card (V × Sample p n) := by
    have hsplit : (univ.filter bad').card =
        ∑ v : V, (univ.filter fun x : Sample p n => bad' (v, x)).card := by
      rw [card_filter, Fintype.sum_prod_type]
      exact sum_congr rfl fun v _ => (card_filter _ _).symm
    rw [hsplit, sum_mul, Fintype.card_prod]
    calc _ ≤ ∑ _v : V, ((p-1) ^ 2 + p * (2 * (K*p/M) + 1) ^ 2) * Fintype.card (Sample p n) :=
          sum_le_sum fun v _ => hfiber v
      _ = _ := by simp only [sum_const, card_univ, smul_eq_mul]; ring
  exact (Nat.mul_le_mul_right _ (card_le_card hsub)).trans
    (decoder.bad_card_mul_le bad' ((p-1) ^ 2 + p * (2 * (K*p/M) + 1) ^ 2) (p * (p-1) ^ 2) hlocal)

end LfzkV2.Current.PureHandoff
