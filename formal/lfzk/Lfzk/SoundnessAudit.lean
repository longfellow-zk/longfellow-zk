import Lfzk.CertifiedHahn
import Lfzk.TSec
import Lfzk.Mac

/-!
# Checks behind the soundness audit

The lower bounds below are on this analysis's error expressions, not on an adversary's success.
They prevent interpreting a failed numerical certificate as an attack or a security upper bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.SoundnessAudit

open Polynomial Finset Lfzk.CertifiedV1 Lfzk.NizkZk Lfzk.NizkAdaptiveTwoField

/-- Equal public tags at a nonzero multiplier do not force equal messages when the two
private blinds differ. This refutes dropping the shared-blind premise from the existing MAC
composition, not the security of the protocol with blinds committed before the challenge. -/
theorem separate_blinds_collision {F : Type} [Field F] :
    Lfzk.Mac.macTag (1 : F) (fun _ : Fin 1 => 0) (fun _ => 0) =
      Lfzk.Mac.macTag (1 : F) (fun _ : Fin 1 => -1) (fun _ => 1) ∧
    (fun _ : Fin 1 => (0 : F)) ≠ (fun _ => 1) ∧ (1 : F) ≠ 0 := by
  simp [Lfzk.Mac.macTag, funext_iff]

/-- The initial hash-side decoder cannot meet the theorem's exact-balance premises if
its raw coin is just a 256-bit digest. Even the smallest v7 output point needs five
GF(2^128) elements. This concerns exact uniformity, not computational pseudorandomness. -/
theorem no_256bit_init_decoder {C F : Type*} [Fintype C] [Nonempty C] [Fintype F] [DecidableEq F]
    (hC : Fintype.card C = 2 ^ 256) (hF : Fintype.card F = 2 ^ 128)
    (decode : C → (Fin 3 → F) × F × F) (k : ℕ)
    (hbal : ∀ y, (univ.filter fun c => decode c = y).card ≤ k) :
    ¬ k * Fintype.card F ^ (3 + 2) ≤ Fintype.card C := by
  classical
  let c : C := Classical.choice inferInstance
  have hpos : 0 < (univ.filter fun c' => decode c' = decode c).card :=
    card_pos.mpr ⟨c, by simp⟩
  have hk : 0 < k := hpos.trans_le (hbal (decode c))
  intro h
  rw [hC, hF] at h
  norm_num at h
  omega

/-- A quadratic can have two distinct roots while its Boolean sum is nonzero, even in
characteristic two. Thus the generic sumcheck root count cannot be reduced from two to one
merely because a false incoming claim forces a nonzero Boolean sum. -/
theorem quadratic_two_roots {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (a : F) (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    let p : Polynomial F := X * (X - C a)
    p.eval 0 + p.eval 1 ≠ 0 ∧ (univ.filter fun r : F => p.eval r = 0).card = 2 := by
  dsimp only
  constructor
  · simpa using sub_ne_zero.mpr (Ne.symm ha1)
  · have hroots : (univ.filter fun r : F => (X * (X - C a) : Polynomial F).eval r = 0)
        = {0, a} := by
      ext r
      simp [mul_eq_zero, sub_eq_zero]
    rw [hroots]
    simp [Ne.symm ha0]

/-- The current hash cores all exceed 2^-116: the 115-bit two-field headline cannot be
rounded up by improving the signature side alone. -/
theorem hash_core_exceeds_116 :
    (1 : ℚ) / 2 ^ 116 < zkCoreAt v7Hash1 3 v7Hash1.cardCand ∧
    (1 : ℚ) / 2 ^ 116 < zkCoreAt v7Hash2 4 v7Hash2.cardCand ∧
    (1 : ℚ) / 2 ^ 116 < zkCoreAt v7Hash3 4 v7Hash3.cardCand ∧
    (1 : ℚ) / 2 ^ 116 < zkCoreAt v7Hash4 5 v7Hash4.cardCand := by
  native_decide

/-- The often quoted `117.27` is the **challenge escape term alone** in the first
v7 hash row.  It is not the Ligero error or the Longfellow error.  The numerator is
the certified line bound `m - 1 = 1694`; the optimized denominator cancels one
factor of `|F|` from the challenge profile. -/
theorem v7Hash1_challenge_escape_exact :
    v7Hash1.params.row.fail = (1694 : ℚ) / (2 ^ 128 - 36) := by
  native_decide

/-- The complete Ligero charge also includes the unchecked arithmetic profile and
the query cover; the whole core additionally includes the list-weighted field checks.
The strict bounds establish the actual integer bit level of this accounting. -/
theorem v7Hash1_cost_chain :
    v7Hash1.params.row.fail < v7Hash1.params.ligeroDensity ∧
    v7Hash1.params.ligeroDensity < zkCoreAt v7Hash1 3 v7Hash1.cardCand ∧
    (1 : ℚ) / 2 ^ 116 < zkCoreAt v7Hash1 3 v7Hash1.cardCand ∧
    zkCoreAt v7Hash1 3 v7Hash1.cardCand < (1 : ℚ) / 2 ^ 115 := by
  native_decide

/-- Even with zero Ligero error, the present list-weighted sumcheck union bound alone
exceeds 2^-117 at every hash profile. Improving only Ligero can at best reach 116 integer bits
with this accounting. This is a limitation of the bound, not a security upper bound. -/
theorem hash_round_charge_exceeds_117 :
    ∀ R ∈ [v7Hash1, v7Hash2, v7Hash3, v7Hash4],
      (1 : ℚ) / 2 ^ 117 <
        (R.cardCand * R.params.totalRounds * 2 : ℕ) / (R.params.row.fieldSize : ℚ) := by
  native_decide

/-- The new row strictly improves the signature summand of the two-field core. -/
theorem signature_core_improves :
    zkCoreAt v7SigHahn 8 v7SigHahn.cardCand < zkCoreAt v7Sig 8 v7Sig.cardCand := by
  native_decide

/-- The four deployed hash profiles, indexed by the number of attributes minus one. -/
def v7HashRow (i : Fin 4) : Row :=
  match i.val with
  | 0 => v7Hash1
  | 1 => v7Hash2
  | 2 => v7Hash3
  | _ => v7Hash4

def v7HashLogv (i : Fin 4) : ℕ :=
  match i.val with
  | 0 => 3
  | 3 => 5
  | _ => 4

/-- Exact slack for the full separate-MAC FS expression, with the Hahn signature
row and every deployed v7 hash row.  The third inequality uses the large
Merkle-query cutoff `tA ≤ 2^115`. -/
theorem hahn_twofield_linear_slack (i : Fin 4) :
    let H := v7HashRow i
    let logv := v7HashLogv i
    let fc := 2 * H.params.row.n + 2 * v7SigHahn.params.row.n
    let L := len2 H v7SigHahn
    let A := zkCoreAt H logv H.cardCand + zkCoreAt v7SigHahn 8 v7SigHahn.cardCand +
      (4 : ℚ) / 2 ^ 128
    let K := max (max (H.zkCoefficient logv) (v7SigHahn.zkCoefficient 8))
      ((4 : ℚ) / 2 ^ 128)
    A + 2 * ((fc * (1 + L) : ℕ) : ℚ) / 2 ^ 256 ≤
        (651 : ℚ) / (1000 * 2 ^ 115) ∧
    K + 2 * ((fc + 2 ^ 115 : ℕ) : ℚ) / 2 ^ 256 ≤ (1 : ℚ) / 2 ^ 117 ∧
    2 * ((3 * 2 ^ 115 + 2 * fc + 1 + L : ℕ) : ℚ) / 2 ^ 256 ≤
        (1 : ℚ) / 2 ^ 138 := by
  fin_cases i <;> native_decide

/-- The coarser Merkle slope needed to cover every nontrivial 116-bit
query budget.  At `tA ≥ 2^116` the target T-security bound is already at
least one, so this is the full useful range. -/
theorem flat125_twofield_uncapped_slack (i : Fin 4) :
    let H := v7HashRow i
    let logv := v7HashLogv i
    let fc := 2 * H.params.row.n + 2 * v7SigHahn.params.row.n
    let L := len2 H v7SigHahn
    let K := max (max (H.zkCoefficient logv) (v7SigHahn.zkCoefficient 8))
      ((4 : ℚ) / 2 ^ 128)
    K + 2 * ((fc + 2 ^ 116 : ℕ) : ℚ) / 2 ^ 256 ≤ (1 : ℚ) / 2 ^ 117 ∧
    2 * ((3 * 2 ^ 116 + 2 * fc + 1 + L : ℕ) : ℚ) / 2 ^ 256 ≤
      (1 : ℚ) / 2 ^ 116 := by
  fin_cases i <;> native_decide

/-- Numerical target for the separate flat terminal-pair compiler.  The hash-side
Ligero term here is the certified flat V1 `2^-125` envelope, while the
round-by-round field charge, the signature side, MAC, and Merkle charge stay
as in the deployed two-field theorem.  This is an arithmetic certificate,
not by itself a bound on the compiled protocol; the deployed-event coupling
is proved separately in `FlatV7Deployed` and its generated geometry adapters. -/
theorem flat125_twofield_constant_slack (i : Fin 4) :
    let H := v7HashRow i
    let logv := v7HashLogv i
    let fc := 2 * H.params.row.n + 2 * v7SigHahn.params.row.n
    let L := len2 H v7SigHahn
    (H.cardCand : ℚ) * zkFieldDensity H logv + (1 : ℚ) / 2 ^ 125 +
      zkCoreAt v7SigHahn 8 v7SigHahn.cardCand + (4 : ℚ) / 2 ^ 128 +
      2 * ((fc * (1 + L) : ℕ) : ℚ) / 2 ^ 256 < (1 : ℚ) / 2 ^ 116 := by
  fin_cases i <;> native_decide

/-- The flat hash terminal bound gives 116-bit zero-query T-security after
charging the two Merkle explanations and every Merkle-tape query.  The
positive-query branch is handled separately by
`hahn_twofield_116_of_pos_queries`. -/
theorem flat125_twofield_116_zero_query (i : Fin 4) (tA : ℕ)
    (htA : tA ≤ 2 ^ 116) :
    let H := v7HashRow i
    let logv := v7HashLogv i
    let fc := 2 * H.params.row.n + 2 * v7SigHahn.params.row.n
    let L := len2 H v7SigHahn
    (H.cardCand : ℚ) * zkFieldDensity H logv + (1 : ℚ) / 2 ^ 125 +
      zkCoreAt v7SigHahn 8 v7SigHahn.cardCand + (4 : ℚ) / 2 ^ 128 +
      2 * ((Bcs.AdaptiveCommit.adaptiveNumerator fc tA L : ℕ) : ℚ) /
        2 ^ 256 ≤ (1 + tA : ℚ) / 2 ^ 116 := by
  dsimp only
  let H := v7HashRow i
  let logv := v7HashLogv i
  let fc := 2 * H.params.row.n + 2 * v7SigHahn.params.row.n
  let L := len2 H v7SigHahn
  have hbase := flat125_twofield_constant_slack i
  dsimp only at hbase
  have hnum := Lfzk.TSec.adaptiveNumerator_le_linear
    (fc := fc) (L := L) (N := 0) (G := 2 ^ 116) htA
  obtain ⟨_, htail⟩ := flat125_twofield_uncapped_slack i
  calc
    (H.cardCand : ℚ) * zkFieldDensity H logv + (1 : ℚ) / 2 ^ 125 +
        zkCoreAt v7SigHahn 8 v7SigHahn.cardCand + (4 : ℚ) / 2 ^ 128 +
        2 * ((Bcs.AdaptiveCommit.adaptiveNumerator fc tA L : ℕ) : ℚ) /
          2 ^ 256
      ≤ (H.cardCand : ℚ) * zkFieldDensity H logv + (1 : ℚ) / 2 ^ 125 +
        zkCoreAt v7SigHahn 8 v7SigHahn.cardCand + (4 : ℚ) / 2 ^ 128 +
        2 * (((fc * (1 + L) +
          tA * (3 * 2 ^ 116 + 2 * fc + 1 + L) : ℕ) : ℚ)) / 2 ^ 256 := by
          gcongr
          simpa only [Nat.add_zero, Nat.zero_mul, Nat.zero_add] using hnum
    _ = ((H.cardCand : ℚ) * zkFieldDensity H logv + (1 : ℚ) / 2 ^ 125 +
        zkCoreAt v7SigHahn 8 v7SigHahn.cardCand + (4 : ℚ) / 2 ^ 128 +
        2 * ((fc * (1 + L) : ℕ) : ℚ) / 2 ^ 256) +
        tA * (2 * ((3 * 2 ^ 116 + 2 * fc + 1 + L : ℕ) : ℚ) / 2 ^ 256) := by
          push_cast
          ring
    _ ≤ (1 : ℚ) / 2 ^ 116 + tA * ((1 : ℚ) / 2 ^ 116) := by
          exact add_le_add (le_of_lt hbase)
            (mul_le_mul_of_nonneg_left htail (by positivity))
    _ = (1 + tA : ℚ) / 2 ^ 116 := by ring

/-- The exact two-field FS right-hand side of
`CompiledZkProfileSepMac.twofield_circuit_ratio_leT_sep`, specialized to the
Hahn signature row, is below this three-term bound for every deployed v7 hash
profile.  The restriction on Merkle queries is only used for the sharper
linearization; the existing 115-bit T-security theorem handles larger budgets. -/
theorem hahn_twofield_linear_rhs (i : Fin 4) (N tA : ℕ) (htA : tA ≤ 2 ^ 115) :
    let H := v7HashRow i
    let logv := v7HashLogv i
    let fc := 2 * H.params.row.n + 2 * v7SigHahn.params.row.n
    let L := len2 H v7SigHahn
    let A := zkCoreAt H logv H.cardCand + zkCoreAt v7SigHahn 8 v7SigHahn.cardCand +
      (4 : ℚ) / 2 ^ 128
    let K := max (max (H.zkCoefficient logv) (v7SigHahn.zkCoefficient 8))
      ((4 : ℚ) / 2 ^ 128)
    A + N * K +
        2 * (Bcs.AdaptiveCommit.adaptiveNumerator fc tA (L + N) : ℚ) / 2 ^ 256 ≤
          (651 : ℚ) / (1000 * 2 ^ 115) +
            N * ((1 : ℚ) / 2 ^ 117) + tA * ((1 : ℚ) / 2 ^ 138) := by
  dsimp only
  let H := v7HashRow i
  let logv := v7HashLogv i
  let fc := 2 * H.params.row.n + 2 * v7SigHahn.params.row.n
  let L := len2 H v7SigHahn
  let A := zkCoreAt H logv H.cardCand + zkCoreAt v7SigHahn 8 v7SigHahn.cardCand +
    (4 : ℚ) / 2 ^ 128
  let K := max (max (H.zkCoefficient logv) (v7SigHahn.zkCoefficient 8))
    ((4 : ℚ) / 2 ^ 128)
  obtain ⟨hA, hK, hT⟩ := hahn_twofield_linear_slack i
  have hnum := Lfzk.TSec.adaptiveNumerator_le_linear (fc := fc) (L := L)
    (N := N) (G := 2 ^ 115) htA
  calc
    A + N * K + 2 * (Bcs.AdaptiveCommit.adaptiveNumerator fc tA (L + N) : ℚ) / 2 ^ 256
        ≤ A + N * K +
          2 * ((fc * (1 + L) + N * (fc + 2 ^ 115) +
            tA * (3 * 2 ^ 115 + 2 * fc + 1 + L) : ℕ) : ℚ) / 2 ^ 256 := by
              gcongr
    _ = (A + 2 * ((fc * (1 + L) : ℕ) : ℚ) / 2 ^ 256) +
          N * (K + 2 * ((fc + 2 ^ 115 : ℕ) : ℚ) / 2 ^ 256) +
          tA * (2 * ((3 * 2 ^ 115 + 2 * fc + 1 + L : ℕ) : ℚ) / 2 ^ 256) := by
            push_cast
            ring
    _ ≤ (651 : ℚ) / (1000 * 2 ^ 115) +
          N * ((1 : ℚ) / 2 ^ 117) + tA * ((1 : ℚ) / 2 ^ 138) := by
            gcongr

/-- Once the adversary makes at least one transcript-hash query, the existing
adaptive bound already has 116-bit T-security. The separate flat terminal
Ligero pair handles the zero-query constant. -/
theorem hahn_twofield_116_of_pos_queries (i : Fin 4) (N tA : ℕ)
    (hN : 0 < N) (htA : tA ≤ 2 ^ 115) :
    let H := v7HashRow i
    let logv := v7HashLogv i
    let fc := 2 * H.params.row.n + 2 * v7SigHahn.params.row.n
    let L := len2 H v7SigHahn
    let A := zkCoreAt H logv H.cardCand + zkCoreAt v7SigHahn 8 v7SigHahn.cardCand +
      (4 : ℚ) / 2 ^ 128
    let K := max (max (H.zkCoefficient logv) (v7SigHahn.zkCoefficient 8))
      ((4 : ℚ) / 2 ^ 128)
    A + N * K +
        2 * (Bcs.AdaptiveCommit.adaptiveNumerator fc tA (L + N) : ℚ) / 2 ^ 256 ≤
          (1 + N + tA : ℚ) / 2 ^ 116 := by
  have hbase := hahn_twofield_linear_rhs i N tA htA
  dsimp only at hbase ⊢
  apply le_trans hbase
  have hNq : (1 : ℚ) ≤ N := by exact_mod_cast hN
  have hconst : (651 : ℚ) / (1000 * 2 ^ 115) ≤
      (3 : ℚ) / (2 * 2 ^ 116) := by norm_num
  have htail : (1 : ℚ) / 2 ^ 138 ≤ (1 : ℚ) / 2 ^ 116 := by norm_num
  calc
    (651 : ℚ) / (1000 * 2 ^ 115) +
        N * ((1 : ℚ) / 2 ^ 117) + tA * ((1 : ℚ) / 2 ^ 138)
        ≤ (3 : ℚ) / (2 * 2 ^ 116) +
            N * ((1 : ℚ) / 2 ^ 117) + tA * ((1 : ℚ) / 2 ^ 116) := by
          gcongr
    _ ≤ (1 + N + tA : ℚ) / 2 ^ 116 := by
          norm_num
          nlinarith [hNq]

/-- The positive-query branch at every Merkle budget for which the
116-bit T-security right-hand side can be below one. -/
theorem hahn_twofield_116_of_pos_queries_extended (i : Fin 4) (N tA : ℕ)
    (hN : 0 < N) (htA : tA ≤ 2 ^ 116) :
    let H := v7HashRow i
    let logv := v7HashLogv i
    let fc := 2 * H.params.row.n + 2 * v7SigHahn.params.row.n
    let L := len2 H v7SigHahn
    let A := zkCoreAt H logv H.cardCand + zkCoreAt v7SigHahn 8 v7SigHahn.cardCand +
      (4 : ℚ) / 2 ^ 128
    let K := max (max (H.zkCoefficient logv) (v7SigHahn.zkCoefficient 8))
      ((4 : ℚ) / 2 ^ 128)
    A + N * K +
        2 * (Bcs.AdaptiveCommit.adaptiveNumerator fc tA (L + N) : ℚ) / 2 ^ 256 ≤
          (1 + N + tA : ℚ) / 2 ^ 116 := by
  dsimp only
  let H := v7HashRow i
  let logv := v7HashLogv i
  let fc := 2 * H.params.row.n + 2 * v7SigHahn.params.row.n
  let L := len2 H v7SigHahn
  let A := zkCoreAt H logv H.cardCand + zkCoreAt v7SigHahn 8 v7SigHahn.cardCand +
    (4 : ℚ) / 2 ^ 128
  let K := max (max (H.zkCoefficient logv) (v7SigHahn.zkCoefficient 8))
    ((4 : ℚ) / 2 ^ 128)
  obtain ⟨hA, _, _⟩ := hahn_twofield_linear_slack i
  obtain ⟨hK, hT⟩ := flat125_twofield_uncapped_slack i
  have hnum := Lfzk.TSec.adaptiveNumerator_le_linear
    (fc := fc) (L := L) (N := N) (G := 2 ^ 116) htA
  have hNq : (1 : ℚ) ≤ N := by exact_mod_cast hN
  calc
    A + N * K + 2 * (Bcs.AdaptiveCommit.adaptiveNumerator fc tA (L + N) : ℚ) / 2 ^ 256
        ≤ A + N * K +
          2 * ((fc * (1 + L) + N * (fc + 2 ^ 116) +
            tA * (3 * 2 ^ 116 + 2 * fc + 1 + L) : ℕ) : ℚ) / 2 ^ 256 := by
              gcongr
    _ = (A + 2 * ((fc * (1 + L) : ℕ) : ℚ) / 2 ^ 256) +
          N * (K + 2 * ((fc + 2 ^ 116 : ℕ) : ℚ) / 2 ^ 256) +
          tA * (2 * ((3 * 2 ^ 116 + 2 * fc + 1 + L : ℕ) : ℚ) / 2 ^ 256) := by
            push_cast
            ring
    _ ≤ (651 : ℚ) / (1000 * 2 ^ 115) +
          N * ((1 : ℚ) / 2 ^ 117) + tA * ((1 : ℚ) / 2 ^ 116) := by
            gcongr
    _ ≤ (1 + N + tA : ℚ) / 2 ^ 116 := by
          norm_num
          nlinarith [hNq]

/-- The numerical envelope used by the deployed compiler: the flat
extraction constant at zero transcript queries, and the existing graded
bound once the adversary has made a transcript query.  This is an
arithmetic interface for all four v7 hash geometries; the protocol event
must be related to the corresponding branch separately. -/
theorem v7_twofield_hybrid_116 (i : Fin 4) (N tA : ℕ)
    (htA : tA ≤ 2 ^ 116) :
    let H := v7HashRow i
    let logv := v7HashLogv i
    let fc := 2 * H.params.row.n + 2 * v7SigHahn.params.row.n
    let L := len2 H v7SigHahn
    let A := zkCoreAt H logv H.cardCand + zkCoreAt v7SigHahn 8 v7SigHahn.cardCand +
      (4 : ℚ) / 2 ^ 128
    let K := max (max (H.zkCoefficient logv) (v7SigHahn.zkCoefficient 8))
      ((4 : ℚ) / 2 ^ 128)
    (if N = 0 then
      (H.cardCand : ℚ) * zkFieldDensity H logv + (1 : ℚ) / 2 ^ 125 +
        zkCoreAt v7SigHahn 8 v7SigHahn.cardCand + (4 : ℚ) / 2 ^ 128 +
        2 * (Bcs.AdaptiveCommit.adaptiveNumerator fc tA L : ℚ) / 2 ^ 256
     else
      A + N * K +
        2 * (Bcs.AdaptiveCommit.adaptiveNumerator fc tA (L + N) : ℚ) / 2 ^ 256)
      ≤ (1 + N + tA : ℚ) / 2 ^ 116 := by
  by_cases hN : N = 0
  · subst N
    simpa using flat125_twofield_116_zero_query i tA htA
  · simpa [hN] using hahn_twofield_116_of_pos_queries_extended i N tA
      (Nat.pos_of_ne_zero hN) htA

end Lfzk.SoundnessAudit
