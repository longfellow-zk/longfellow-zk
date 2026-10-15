import Lfzk.Layers
import Lfzk.ZkMultilinear

/-!
# The arithmetization, constructed from a deployed layered quadratic circuit

`Lfzk.LayeredCircuit` (`Layers.lean`) takes the circuit's arithmetization as abstract data with
three assumed properties — `Quad_affine_beta`, `V_local`, `layer_rel` (README gap 2).  This file
**constructs** it from a concrete circuit in the deployed format and **proves** all three.

## The format (`QuadCircuit`)

`sumcheck/circuit.h` `Circuit<Field>` / Rust `core_proto::circuit::RawCircuit`: per layer a sparse
list of terms `⟨g, h0, h1, v⟩` (`GateTerm`, `Circuit.lean`), `v = 0` marking an assert-zero term;
the input wires are `wCol npub pub priv` (public wires first).  `wires pub priv betas ly j` is wire
`j` of layer `ly` under the beta schedule: at the zero schedule it is `ProverLayers::eval_circuit`
(assert-zero terms add nothing), and at a general schedule every assert-zero term adds
`betas ly · W[h0] · W[h1]`, which is what `prep_v` (`quad.h:L213`, `HQuad::bind_g`'s
`if k == 0 { beta * dot }`) makes the verifier sumcheck.

## The construction (`QuadCircuit.toLayered`)

`V ly` is the MLE of layer `ly`'s wires (`mle`), `Quad ly beta` is `quadMle` of the layer's sparse
terms.  Proved:

* `Quad_affine_beta` — `quadMle_affine_beta` (`prepV_affine`);
* `V_local` — `wires_local`: layer `ly` reads only `betas i`, `i ≥ ly`;
* `layer_rel` — `layer_rel_gates`: on the cube the sumcheck summand picks out each stored term
  (`eq_bv`: `eq_mle_basis` at a cube point is an indicator), and `bind_g_sum` is `Quad::bind_g`
  in closed form;
* `V ly` is **affine in `betas ly`** (`toLayered_V_affine`);
* the input layer is the committed-column MLE (`toLayered_input`, `toLayered_input_wMle`: the
  interface law `LayeredInputMLE` of `proofs/lfzk/Lfzk/LigeroBridge.lean`, discharged).

Work is at `logc = 0`, `nc = 1` (the ZK path asserts it, `zk_common.h:L72`) and, as everywhere in
`Layers.lean`, at one `logw` for all layers (a compiled circuit is padded to the widest layer).
`layer_rel` is quantified over **every** `ly : ℕ`; below the input layer the construction copies the
inputs through the constant-one wire (`copyGates`, the compiler's own copy-wire shape), which is why
`OneWire` (input wire `0` is the public `1`) is a hypothesis.  Without a constant wire `layer_rel` at
`ly = nl` would ask the input MLE to be a quadratic form in some vector, which over an
odd-characteristic field fails for most inputs.

## Satisfaction and compiler correctness

* `Satisfied` — every assert-zero term's hand product is zero and every output wire is zero, at the
  honest wires;  `toLayered_V0_of_satisfied`: **`Satisfied → V 0 = 0` at every schedule**
  (`toLayered_V_of_satisfied`: every `V ly` is then schedule-free).
* **The output-only converse is false for compiled circuits** (`Cex.output_only_false`): the
  compiler gives each assertion its own wire and never reads it again (`DeadEnd`), so a violated
  assertion in an intermediate layer moves that layer's `V` with its `beta` but never reaches the
  output.  `Cex.cex` is `assert0(x); output((w·w)·w)` compiled, at `x = 1, w = 0`.
* **The true form** (`unsat_iff`, `toLayered_unsat_iff`): for isolated, dead-end assertions (both
  decidable, both what `compiler.h`/`schedule.h` emit),

      ¬ Satisfied ↔ V 0 is not identically 0 as a function of the schedule
                    ∨ ∃ 0 < ly < nl, V ly moves with betas ly,

  and under `DeadEnd` the schedule enters layer `ly` only through `betas ly`, linearly:
  `wires betas ly = honest ly + betas ly · assertVec ly` (`wires_decomp`, `toLayered_V_decomp`).
* On the registered v7 circuits (`lfzk/scripts/inspect_v7_assertions.py`, read-only) `DeadEnd`
  and `Isolated` hold, and the assertions are almost all intermediate: the signature circuit's
  5196 assertion terms have 144 in layer 0; the hash circuits' 284453–332351 have 3–12 in
  layer 0.

## The output point

`mle_zero_card`: a cube vector non-zero on the cube has an MLE vanishing on at most
`n · |F|^(n-1)` points (`ZkMultilinear.mlin_zero_card`); `toLayered_out_zero_card` for `V 0`;
`toLayered_init_card`/`toLayered_init_card_of_top`: layer 0's slot over `(G, beta₀, alpha₀)` costs
`(logw + 2) · |F|^(logw + 1)` when the output layer is not identically zero in `beta₀`
(`ZkMultilinear.init_bad_card`).

## Hypotheses that remain

`WellFormed` (indices in range; decidable), `OneWire` (for the construction), and `DeadEnd`,
`Isolated` (decidable; only for the compiler-correctness characterisation).  The equivalence between
`QuadCircuit` and the bytes of a deployed circuit artifact is transliteration, not proved here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.Arith
open Finset Sumcheck

lemma bit_value_lt_two (i k : ℕ) : bit_value i k < 2 := Nat.mod_lt _ (by norm_num)

/-- The bit `k < n` of `i` is the bit `k` of `i mod 2^n`. -/
lemma bit_value_mod (n i k : ℕ) (hk : k < n) : bit_value (i % 2 ^ n) k = bit_value i k := by
  unfold bit_value
  have h2 : 2 ^ n = 2 ^ k * 2 ^ (n - k) := by rw [← pow_add]; congr 1; omega
  rw [h2, Nat.mod_mul_right_div_self]
  refine Nat.mod_mod_of_dvd _ ?_
  exact dvd_pow_self 2 (by omega)

/-- Bit `n + k` of `i` is bit `k` of `i / 2^n`. -/
lemma bit_value_div (n i k : ℕ) : bit_value (i / 2 ^ n) k = bit_value i (n + k) := by
  unfold bit_value
  rw [Nat.div_div_eq_div_mul, ← pow_add]

/-- The bits below `n` determine `i mod 2^n`. -/
lemma mod_eq_of_bits : ∀ (n i j : ℕ), (∀ k < n, bit_value i k = bit_value j k) →
    i % 2 ^ n = j % 2 ^ n
  | 0, i, j, _ => by simp [Nat.mod_one]
  | n + 1, i, j, h => by
      have h0 : i % 2 = j % 2 := by simpa [bit_value] using h 0 (by omega)
      have ih := mod_eq_of_bits n (i / 2) (j / 2) (fun k hk => by
        have := h (k + 1) (by omega)
        have e1 := bit_value_div 1 i k
        have e2 := bit_value_div 1 j k
        rw [pow_one] at e1 e2
        rw [e1, e2, Nat.add_comm 1 k]
        exact this)
      rw [pow_succ', Nat.mod_mul, Nat.mod_mul, h0, ih]

variable {F : Type} [Field F]

/-- **`eq_mle_basis` at a cube point is an indicator** (modulo `2^n`: `eq_mle_basis` reads only
the low `n` bits of its index, as `Eqs<Field>::at` does). -/
lemma eq_bv {n : ℕ} (i j : ℕ) :
    eq_mle_basis i (boolean_vector j : Vector F n) = if i % 2 ^ n = j % 2 ^ n then 1 else 0 := by
  unfold eq_mle_basis
  have hfac : ∀ k : Fin n, (if bit_value i k.val = 1 then (boolean_vector j : Vector F n).get k
        else 1 - (boolean_vector j : Vector F n).get k)
      = if bit_value i k.val = bit_value j k.val then 1 else 0 := by
    intro k
    have hget : (boolean_vector j : Vector F n).get k = if bit_value j k.val = 1 then 1 else 0 := by
      simp [boolean_vector, Vector.get]
    rw [hget]
    have hi := bit_value_lt_two i k.val
    have hj := bit_value_lt_two j k.val
    by_cases h1 : bit_value i k.val = 1 <;> by_cases h2 : bit_value j k.val = 1 <;>
      simp [h1, h2] <;> omega
  rw [Finset.prod_congr rfl (fun k _ => hfac k), Finset.prod_boole]
  by_cases h : i % 2 ^ n = j % 2 ^ n
  · rw [if_pos h, if_pos]
    intro k _
    rw [← bit_value_mod n i k.val k.isLt, ← bit_value_mod n j k.val k.isLt, h]
  · rw [if_neg h, if_neg]
    intro hall
    exact h (mod_eq_of_bits n i j (fun k hk => hall ⟨k, hk⟩ (Finset.mem_univ _)))

lemma eq_bv_of_lt {n : ℕ} {i j : ℕ} (hi : i < 2 ^ n) (hj : j < 2 ^ n) :
    eq_mle_basis i (boolean_vector j : Vector F n) = if i = j then 1 else 0 := by
  rw [eq_bv, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj]

/-- `boolean_vector` reads only the low `n` bits. -/
lemma bv_mod {n : ℕ} (j : ℕ) :
    (boolean_vector (j % 2 ^ n) : Vector F n) = boolean_vector j := by
  ext k hk
  simp [boolean_vector, bit_value_mod n j k hk]

/-- `eq_mle_basis` reads only the low `n` bits of its index. -/
lemma eq_mle_basis_mod {n : ℕ} (i : ℕ) (g : Vector F n) :
    eq_mle_basis (i % 2 ^ n) g = eq_mle_basis i g := by
  unfold eq_mle_basis
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rw [bit_value_mod n i k.val k.isLt]


variable [DecidableEq F]

/-! ## Gate evaluation and multilinear extensions -/

/-- **One layer's gate evaluation**, `ProverLayers::eval_quad` with `prep_v` applied: wire `j`
collects `prep_v(v, β) · W[h0] · W[h1]` over the layer's stored terms with output corner `j`.
At `β = 0` an assert-zero term (`v = 0`) contributes nothing, which is `eval_quad`'s output. -/
def evalGates (gates : List (GateTerm F)) (b : F) (W : ℕ → F) (j : ℕ) : F :=
  ∑ i : Fin gates.length, if (gates.get i).g = j then
    prepV (gates.get i).v b * W (gates.get i).h0 * W (gates.get i).h1 else 0

omit [DecidableEq F] in
/-- The multilinear extension of a cube vector `c : ℕ → F` (entries `0 ≤ j < 2^n`), the
`Dense<Field>` array as `Eqs<Field>::at` reads it. -/
def mle (n : ℕ) (c : ℕ → F) (g : Vector F n) : F :=
  ∑ j ∈ range (2 ^ n), eq_mle_basis j g * c j

omit [DecidableEq F] in
/-- An MLE agrees with its vector at the cube points. -/
lemma mle_bv {n : ℕ} (c : ℕ → F) {j : ℕ} (hj : j < 2 ^ n) :
    mle n c (boolean_vector j) = c j := by
  unfold mle
  rw [Finset.sum_eq_single j]
  · rw [eq_bv_of_lt hj hj, if_pos rfl, one_mul]
  · intro i hi hne
    rw [eq_bv_of_lt (mem_range.mp hi) hj, if_neg hne, zero_mul]
  · intro h
    exact absurd (mem_range.mpr hj) h

/-- **The MLE of a gate evaluation, in gate-sum form**: `∑_t prep_v(v_t, β) · W[h0_t] · W[h1_t] ·
EQ[g_t, G]`.  Needs the output corners to lie in the cube. -/
lemma mle_evalGates {n : ℕ} (gates : List (GateTerm F)) (b : F) (W : ℕ → F)
    (hg : ∀ t ∈ gates, t.g < 2 ^ n) (g : Vector F n) :
    mle n (evalGates gates b W) g
      = ∑ i : Fin gates.length, prepV (gates.get i).v b * W (gates.get i).h0
          * W (gates.get i).h1 * eq_mle_basis (gates.get i).g g := by
  unfold mle evalGates
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq (range (2 ^ n)) (gates.get i).g,
    if_pos (mem_range.mpr (hg _ (List.get_mem _ _)))]
  ring

/-! ## The layer polynomial on the cube -/

omit [DecidableEq F] in
lemma extract_bv_l {n : ℕ} (j : ℕ) :
    (extract_vars (logc := 0) (logw := n) (boolean_vector j : Vector F (0 + 2 * n))).2.1
      = boolean_vector j := by
  ext k hk
  simp [extract_vars, boolean_vector, Vector.get]

omit [DecidableEq F] in
lemma extract_bv_r {n : ℕ} (j : ℕ) :
    (extract_vars (logc := 0) (logw := n) (boolean_vector j : Vector F (0 + 2 * n))).2.2
      = boolean_vector (j / 2 ^ n) := by
  ext k hk
  simp [extract_vars, boolean_vector, Vector.get, bit_value_div]

omit [DecidableEq F] in
/-- With one copy and no copy variables, `EQ[Q,C] = 1`. -/
lemma eqMat_one (q c : Vector F 0) : eq_matrix_mle 1 0 q c = 1 := by
  simp [eq_matrix_mle, eq_mle_basis]

/--
**`Quad::bind_g`, in closed form.**  Binding the output corner of `quadMle` against
`dot[i] = EQ[i, G0] + alpha · EQ[i, G1]` over the `nv` gate corners leaves, per stored term,
`prep_v(v, β) · dot[g]`, times the two hand indicators — exactly the `vcorner` `bind_g` writes.
-/
lemma bind_g_sum {nv n : ℕ} (gates : List (GateTerm F)) (b alpha : F)
    (hg : ∀ t ∈ gates, t.g < nv) (hnv : nv ≤ 2 ^ n) (g0 g1 l r : Vector F n) :
    ∑ i ∈ range nv, quadMle (logv := n) (logw := n) gates b (boolean_vector i) l r
        * (eq_mle_basis i g0 + alpha * eq_mle_basis i g1)
      = ∑ k : Fin gates.length, prepV (gates.get k).v b
          * (eq_mle_basis (gates.get k).g g0 + alpha * eq_mle_basis (gates.get k).g g1)
          * eq_mle_basis (gates.get k).h0 l * eq_mle_basis (gates.get k).h1 r := by
  unfold quadMle
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hgk : (gates.get k).g < nv := hg _ (List.get_mem _ _)
  rw [Finset.sum_eq_single (gates.get k).g]
  · rw [eq_bv_of_lt (by omega) (by omega), if_pos rfl]
    ring
  · intro i hi hne
    rw [eq_bv_of_lt (by omega) (by have := mem_range.mp hi; omega), if_neg (Ne.symm hne)]
    ring
  · intro h
    exact absurd (mem_range.mpr hgk) h

omit [DecidableEq F] in
/-- The pair-of-hands sum over the `2n`-cube picks out the corner `(h0, h1)`. -/
lemma hands_sum {n h0 h1 : ℕ} (hh0 : h0 < 2 ^ n) (hh1 : h1 < 2 ^ n) (X : ℕ → ℕ → F) :
    ∑ j ∈ range (2 ^ (0 + 2 * n)),
        eq_mle_basis h0 (boolean_vector j : Vector F n)
          * eq_mle_basis h1 (boolean_vector (j / 2 ^ n) : Vector F n) * X (j % 2 ^ n) (j / 2 ^ n)
      = X h0 h1 := by
  set N := 2 ^ n with hN
  have hNpos : 0 < N := by positivity
  have hpow : 2 ^ (0 + 2 * n) = N * N := by rw [hN, ← pow_add]; ring_nf
  rw [hpow, Finset.sum_eq_single (h0 + N * h1)]
  · have hm : (h0 + N * h1) % N = h0 := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hh0]
    have hd : (h0 + N * h1) / N = h1 := by
      rw [Nat.add_mul_div_left _ _ hNpos, Nat.div_eq_of_lt hh0, zero_add]
    rw [hd, hm, eq_bv, hm, Nat.mod_eq_of_lt hh0, if_pos rfl, eq_bv_of_lt hh1 hh1, if_pos rfl]
    ring
  · intro j hj hne
    have hjN : j < N * N := mem_range.mp hj
    have hdiv : j / N < N := (Nat.div_lt_iff_lt_mul hNpos).mpr hjN
    rw [eq_bv, Nat.mod_eq_of_lt hh0, eq_bv_of_lt hh1 hdiv]
    by_cases hc1 : h0 = j % N
    · by_cases hc2 : h1 = j / N
      · exfalso
        apply hne
        rw [hc1, hc2]
        exact (Nat.mod_add_div j N).symm
      · rw [if_neg hc2]; ring
    · rw [if_neg hc1]; ring
  · intro h
    exfalso
    apply h
    rw [mem_range]
    have : h0 + N * h1 < N + N * h1 := by omega
    have : N + N * h1 ≤ N * N := by
      have : N * (h1 + 1) ≤ N * N := Nat.mul_le_mul_left _ hh1
      linarith
    omega

/--
**The layer relation for one layer of gates, from the gate evaluation.**

The sumcheck of layer `ly` is about `EQ[Q,C] · QUAD[G|L,R] · W[L,C] · W[R,C]` summed over the
hand cube (`logc = 0`, one copy).  If `Wv` agrees with the wire vector `W` of the next layer on
the cube, the sum is the `alpha`-combination of the MLE of this layer's gate evaluation at the two
points.  Only the next layer's **cube values** enter, so `Wv` need not be multilinear.
-/
theorem layer_rel_gates [Fintype F] {nv n : ℕ} (gates : List (GateTerm F)) (b alpha : F)
    (hg : ∀ t ∈ gates, t.g < nv ∧ t.h0 < 2 ^ n ∧ t.h1 < 2 ^ n) (hnv : nv ≤ 2 ^ n)
    (Wv : Vector F n → Vector F 0 → F) (W : ℕ → F)
    (hW : ∀ j < 2 ^ n, ∀ q, Wv (boolean_vector j) q = W j) (st : LayerState n 0 F) :
    ∑ j ∈ range (2 ^ (0 + 2 * n)),
        layer_poly_of (nc := 1) (nv := nv) (quadMle gates b) Wv alpha st (boolean_vector j)
      = mle n (evalGates gates b W) st.g0 + alpha * mle n (evalGates gates b W) st.g1 := by
  have hgv : ∀ t ∈ gates, t.g < nv := fun t ht => (hg t ht).1
  have hg2 : ∀ t ∈ gates, t.g < 2 ^ n := fun t ht => lt_of_lt_of_le (hg t ht).1 hnv
  have hNpos : 0 < 2 ^ n := by positivity
  -- each summand, in gate-sum form
  have hterm : ∀ j ∈ range (2 ^ (0 + 2 * n)),
      layer_poly_of (nc := 1) (nv := nv) (quadMle gates b) Wv alpha st (boolean_vector j)
        = ∑ k : Fin gates.length, prepV (gates.get k).v b
            * (eq_mle_basis (gates.get k).g st.g0 + alpha * eq_mle_basis (gates.get k).g st.g1)
            * (eq_mle_basis (gates.get k).h0 (boolean_vector j : Vector F n)
              * eq_mle_basis (gates.get k).h1 (boolean_vector (j / 2 ^ n) : Vector F n)
              * (W (j % 2 ^ n) * W (j / 2 ^ n))) := by
    intro j hj
    have hjN : j < 2 ^ n * 2 ^ n := by
      have := mem_range.mp hj
      rwa [show 2 ^ (0 + 2 * n) = 2 ^ n * 2 ^ n by rw [← pow_add]; ring_nf] at this
    have hdiv : j / 2 ^ n < 2 ^ n := (Nat.div_lt_iff_lt_mul hNpos).mpr hjN
    have hl : ∀ q, Wv (boolean_vector j) q = W (j % 2 ^ n) := fun q => by
      rw [← bv_mod (F := F) (n := n) j]
      exact hW _ (Nat.mod_lt _ hNpos) q
    have hr : ∀ q, Wv (boolean_vector (j / 2 ^ n)) q = W (j / 2 ^ n) := fun q => hW _ hdiv q
    unfold layer_poly_of
    rw [layer_sumcheck_poly_concat_eq, extract_bv_l, extract_bv_r]
    unfold layer_sumcheck_poly
    rw [eqMat_one, bind_g_sum gates b alpha hgv hnv, hl, hr, one_mul, Finset.sum_mul,
      Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  rw [mle_evalGates gates b W hg2, mle_evalGates gates b W hg2, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hk := hg _ (List.get_mem gates k)
  simp_rw [← Finset.mul_sum]
  rw [hands_sum (F := F) hk.2.1 hk.2.2 (fun a c => W a * W c)]
  ring

/-! ## The deployed circuit format -/

/--
**A layered quadratic circuit in the deployed format** (`sumcheck/circuit.h`
`Circuit<Field>`, Rust `core_proto::circuit::RawCircuit`).

* `layers` — `Circuit::l`, one sparse term list per layer (`Layer::quad`).  Layer `0` is the
  output layer; layer `ly` reads the wires of layer `ly + 1`; the last layer reads the input
  wires.  A term `⟨g, h0, h1, v⟩` adds `v · W[h0] · W[h1]` to output wire `g`; `v = 0` marks an
  assert-zero term (`compiler.h` `assert0`, the node `0 * (1 * op)`), which `eval_quad` checks
  instead of adding and `prep_v` replaces by the layer's `beta`.
* `ninp` — `Circuit::ninputs`;  `npub` — `Circuit::npub_in`, the index of the first private
  input.  The input wire vector is `wCol npub pub priv` (public wires first, `zk_common.h`
  `input_constraint`).
-/
structure QuadCircuit (F : Type) where
  layers : List (List (GateTerm F))
  ninp : ℕ
  npub : ℕ

namespace QuadCircuit

variable (c : QuadCircuit F)

/-- `Circuit::nl`. -/
def nl : ℕ := c.layers.length

/-- Layer `ly`'s stored terms (`[]` past the last layer). -/
def gates (ly : ℕ) : List (GateTerm F) := c.layers.getD ly []

/-- The input wire vector as a cube vector: `wCol npub pub priv` on `[0, ninp)`, zero above. -/
def inputVec (pub priv : Fin c.ninp → F) (j : ℕ) : F :=
  if h : j < c.ninp then wCol c.npub pub priv ⟨j, h⟩ else 0

/--
**The wire values of every layer under a beta schedule.**  `wires pub priv betas ly j` is wire
`j` of layer `ly` (`ly = 0` the outputs, `ly = nl` the inputs): `evalGates` of layer `ly` at
`betas ly` on layer `ly + 1`'s wires.  At the all-zero schedule this is `ProverLayers::eval_circuit`
(assert-zero terms contribute nothing); at a general schedule every assert-zero term contributes
`betas ly · W[h0] · W[h1]`, which is what the verifier's `prep_v` sumchecks.
-/
def wires (pub priv : Fin c.ninp → F) (betas : ℕ → F) (ly : ℕ) : ℕ → F :=
  if h : ly < c.nl then evalGates (c.gates ly) (betas ly) (wires pub priv betas (ly + 1))
  else c.inputVec pub priv
termination_by c.nl - ly

variable {c}

lemma wires_lt {pub priv : Fin c.ninp → F} {betas : ℕ → F} {ly : ℕ} (h : ly < c.nl) :
    c.wires pub priv betas ly
      = evalGates (c.gates ly) (betas ly) (c.wires pub priv betas (ly + 1)) := by
  rw [wires, dif_pos h]

lemma wires_ge {pub priv : Fin c.ninp → F} {betas : ℕ → F} {ly : ℕ} (h : c.nl ≤ ly) :
    c.wires pub priv betas ly = c.inputVec pub priv := by
  rw [wires, dif_neg (by omega)]

/-- **Layer `ly`'s wires read only `betas i` for `i ≥ ly`.** -/
lemma wires_local (pub priv : Fin c.ninp → F) : ∀ (k ly : ℕ), c.nl - ly = k →
    ∀ (betas betas' : ℕ → F), (∀ i, ly ≤ i → betas i = betas' i) →
      c.wires pub priv betas ly = c.wires pub priv betas' ly
  | 0, ly, hk, betas, betas', _ => by
      rw [wires_ge (by omega), wires_ge (by omega)]
  | k + 1, ly, hk, betas, betas', h => by
      have hlt : ly < c.nl := by omega
      rw [wires_lt hlt, wires_lt hlt, h ly le_rfl,
        wires_local pub priv k (ly + 1) (by omega) betas betas' (fun i hi => h i (by omega))]

/-! ### Below the input layer: copies through the constant-one wire

`LayeredCircuit.layer_rel` is quantified over **every** `ly : ℕ`, not only `ly < nl`, so the
construction has to continue below the input layer.  It does so the way the compiler copies a wire
across a layer (`schedule.h`: a copy wire is the term `1 · W[0] · W[op]`, wire `0` being the
constant one, `compiler.h` `input_wire()` in the constructor): every layer `ly ≥ nl` is
`copyGates ninp`, which maps the input vector to itself.  This needs input wire `0` to be the
public constant `1` — the deployed convention.  Nothing downstream reads these layers. -/

omit [DecidableEq F] in
/-- The copy layer: `⟨j, j, 0, 1⟩` for every input wire `j`. -/
def copyGates (n : ℕ) : List (GateTerm F) := List.ofFn (fun j : Fin n => ⟨j.val, j.val, 0, 1⟩)

variable (c) in
/-- The gate list the constructed `LayeredCircuit` uses at layer `ly`. -/
def qgates (ly : ℕ) : List (GateTerm F) := if ly < c.nl then c.gates ly else copyGates c.ninp

/-- `evalGates` as a list sum. -/
lemma evalGates_eq_list (gates : List (GateTerm F)) (b : F) (W : ℕ → F) (j : ℕ) :
    evalGates gates b W j
      = (gates.map fun t => if t.g = j then prepV t.v b * W t.h0 * W t.h1 else 0).sum := by
  unfold evalGates
  rw [← Fin.sum_univ_fun_getElem gates
    (fun t => if t.g = j then prepV t.v b * W t.h0 * W t.h1 else 0)]
  rfl

/-- The copy layer maps any vector `W` with `W 0 = 1` and support in `[0, n)` to itself. -/
lemma evalGates_copy (n : ℕ) (b : F) (W : ℕ → F) (h0 : W 0 = 1) (hsupp : ∀ j, n ≤ j → W j = 0)
    (j : ℕ) : evalGates (copyGates n) b W j = W j := by
  rw [evalGates_eq_list, copyGates, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_apply]
  have h1 : prepV (1 : F) b = 1 := by simp [prepV]
  rw [h1, h0]
  rw [Fin.sum_univ_eq_sum_range (fun i => if i = j then 1 * W i * 1 else 0) n,
    Finset.sum_ite_eq']
  by_cases hj : j < n
  · rw [if_pos (mem_range.mpr hj)]; ring
  · rw [if_neg (by simpa using hj), hsupp j (by omega)]


/-! ### Well-formedness, and the constant-one wire -/

variable (c) in
/--
**The structural hypotheses** the construction needs, all decidable (`instDecidableWellFormed`):
the bind range `nv` fits the cube, the inputs fit the bind range, wire `0` is public, and every
stored term's output corner is below `nv` and its hand corners are in the cube.  The compiler
emits `nv = 2^logv` corners (`bind_g`'s `raw_eq2(logv, 1 << logv, …)`) and dense layers, so a
compiled circuit padded to a common `logw` meets them.
-/
def WellFormed (nv logw : ℕ) : Prop :=
  nv ≤ 2 ^ logw ∧ c.ninp ≤ nv ∧ 0 < c.npub ∧ c.npub ≤ c.ninp ∧
    ∀ ly < c.nl, ∀ t ∈ c.gates ly, t.g < nv ∧ t.h0 < 2 ^ logw ∧ t.h1 < 2 ^ logw

instance instDecidableWellFormed (nv logw : ℕ) : Decidable (c.WellFormed nv logw) := by
  unfold WellFormed; infer_instance

variable (c) in
/-- Input wire `0` is the public constant `1` (`compiler.h`: `input[0] = F.one()`). -/
def OneWire (pub : Fin c.ninp → F) : Prop := ∀ h : 0 < c.ninp, pub ⟨0, h⟩ = 1

omit [DecidableEq F] in
lemma inputVec_zero {nv logw : ℕ} (hwf : c.WellFormed nv logw) {pub : Fin c.ninp → F}
    (hone : c.OneWire pub) (priv : Fin c.ninp → F) : c.inputVec pub priv 0 = 1 := by
  have h0 : 0 < c.ninp := lt_of_lt_of_le hwf.2.2.1 hwf.2.2.2.1
  simp [inputVec, h0, wCol, hwf.2.2.1, hone h0]

omit [DecidableEq F] in
lemma inputVec_supp (pub priv : Fin c.ninp → F) (j : ℕ) (hj : c.ninp ≤ j) :
    c.inputVec pub priv j = 0 := by
  simp [inputVec, show ¬ j < c.ninp by omega]

omit [DecidableEq F] in
/-- Every gate list the construction uses is in range: the circuit's by `WellFormed`, the copy
layers because the inputs fit. -/
lemma qgates_lt {nv logw : ℕ} (hwf : c.WellFormed nv logw) (ly : ℕ) :
    ∀ t ∈ c.qgates ly, t.g < nv ∧ t.h0 < 2 ^ logw ∧ t.h1 < 2 ^ logw := by
  intro t ht
  unfold qgates at ht
  split_ifs at ht with hly
  · exact hwf.2.2.2.2 ly hly t ht
  · simp only [copyGates, List.mem_ofFn] at ht
    obtain ⟨j, rfl⟩ := ht
    have := hwf.1; have := hwf.2.1
    refine ⟨by simp; omega, by simp; omega, by simp⟩

/-- **One step of the wire recursion, at every layer**, including the copy layers below the
inputs. -/
lemma wires_step {nv logw : ℕ} (hwf : c.WellFormed nv logw) {pub : Fin c.ninp → F}
    (hone : c.OneWire pub) (priv : Fin c.ninp → F) (betas : ℕ → F) (ly : ℕ) :
    c.wires pub priv betas ly
      = evalGates (c.qgates ly) (betas ly) (c.wires pub priv betas (ly + 1)) := by
  by_cases hly : ly < c.nl
  · rw [wires_lt hly, qgates, if_pos hly]
  · rw [wires_ge (by omega), wires_ge (by omega), qgates, if_neg hly]
    funext j
    rw [evalGates_copy c.ninp _ _ (inputVec_zero hwf hone priv) (inputVec_supp pub priv)]

/-! ## The constructed `LayeredCircuit` -/

variable [Fintype F]

variable (c) in
/-- `V ly`: the MLE of layer `ly`'s wire values under the schedule. -/
noncomputable def V (pub : Fin c.ninp → F) (logw ly : ℕ) (priv : Fin c.ninp → F)
    (betas : ℕ → F) (g : Vector F logw) : F :=
  mle logw (c.wires pub priv betas ly) g

omit [DecidableEq F] [Fintype F] in
lemma mle_congr {n : ℕ} {c₁ c₂ : ℕ → F} (h : ∀ j < 2 ^ n, c₁ j = c₂ j) (g : Vector F n) :
    mle n c₁ g = mle n c₂ g := by
  unfold mle
  exact Finset.sum_congr rfl (fun j hj => by rw [h j (mem_range.mp hj)])

omit [Fintype F] in
/-- `QUAD` is affine in `beta`, because `prep_v` is. -/
lemma quadMle_affine_beta {logv logw : ℕ} (gates : List (GateTerm F)) (b : F) (g : Vector F logv)
    (l r : Vector F logw) :
    quadMle gates b g l r = quadMle gates 0 g l r + b * (quadMle gates 1 g l r - quadMle gates 0 g l r) := by
  simp only [quadMle, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [prepV_affine ((gates.get i).v) b]; ring

variable (c) in
/--
**The arithmetization of a deployed circuit, constructed.**

`V ly` is the MLE of layer `ly`'s wire values under the schedule (`wires`), `Quad ly beta` the MLE
of layer `ly`'s sparse term list after `prep_v` (`quadMle`).  All three facts `LayeredCircuit`
assumes are proved: `Quad_affine_beta` from `prepV_affine`, `V_local` from `wires_local`, and
`layer_rel` from `layer_rel_gates`.  One copy, no copy variables (`logc = 0`, `nc = 1`: the ZK
path, `zk_common.h:L72`).  The witness is the private half of the input vector.
-/
noncomputable def toLayered (pub : Fin c.ninp → F) {nv logw : ℕ} (hwf : c.WellFormed nv logw)
    (hone : c.OneWire pub) : LayeredCircuit (Fin c.ninp → F) 1 nv logw 0 F where
  V ly priv betas g _ := c.V pub logw ly priv betas g
  Quad ly b := quadMle (c.qgates ly) b
  Quad_affine_beta ly b g l r := quadMle_affine_beta (c.qgates ly) b g l r
  V_local ly w betas betas' h := by
    funext g q
    simp only [V, wires_local pub w (c.nl - ly) ly rfl betas betas' h]
  layer_rel ly w alpha betas st := by
    have hW : ∀ j < 2 ^ logw, ∀ q : Vector F 0,
        c.V pub logw (ly + 1) w betas (boolean_vector j) = c.wires pub w betas (ly + 1) j :=
      fun j hj _ => mle_bv _ hj
    rw [layer_rel_gates (c.qgates ly) (betas ly) alpha (qgates_lt hwf ly) hwf.1
      (fun g _ => c.V pub logw (ly + 1) w betas g) (c.wires pub w betas (ly + 1)) hW st]
    simp only [V, wires_step hwf hone w betas ly]


/-! ## The input layer is the committed column MLE (`LayeredInputMLE`) -/

omit [DecidableEq F] [Fintype F] in
/-- The MLE of the input cube vector is `wMle`, the committed-column MLE of `Circuit.lean`. -/
lemma mle_inputVec {logw : ℕ} (hle : c.ninp ≤ 2 ^ logw) (pub priv : Fin c.ninp → F)
    (g : Vector F logw) :
    mle logw (c.inputVec pub priv) g = ∑ i : Fin c.ninp, eq_mle_basis i.val g * wCol c.npub pub priv i := by
  unfold mle
  rw [Finset.sum_fin_eq_sum_range]
  symm
  refine Finset.sum_subset (Finset.range_subset_range.mpr hle) (fun j _ hj => ?_) |>.trans ?_
  · rw [mem_range] at hj
    rw [dif_neg hj]
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    unfold inputVec
    split_ifs with h
    · rfl
    · simp

/--
**`LayeredInputMLE`, discharged.**  At every layer at or below the input layer the constructed
`V` is the multilinear extension of the committed columns `wCol npub pub priv`, at every schedule.
This is `proofs/lfzk/Lfzk/LigeroBridge.lean`'s interface law `LayeredInputMLE LC nl betas colOf`
at `colOf _ priv = wCol npub pub priv`, and it is `wMle`.
-/
theorem toLayered_input (pub : Fin c.ninp → F) {nv logw : ℕ} (hwf : c.WellFormed nv logw)
    (hone : c.OneWire pub) (ly : ℕ) (hly : c.nl ≤ ly) (priv : Fin c.ninp → F) (betas : ℕ → F)
    (g : Vector F logw) (q : Vector F 0) :
    (c.toLayered pub hwf hone).V ly priv betas g q
      = ∑ i : Fin c.ninp, eq_mle_basis i.val g * wCol c.npub pub priv i := by
  show mle logw (c.wires pub priv betas ly) g = _
  rw [wires_ge hly]
  exact mle_inputVec (le_trans hwf.2.1 hwf.1) pub priv g

theorem toLayered_input_wMle (pub : Fin c.ninp → F) {nv logw : ℕ} (hwf : c.WellFormed nv logw)
    (hone : c.OneWire pub) (priv : Fin c.ninp → F) (betas : ℕ → F) (g : Vector F logw)
    (q : Vector F 0) :
    (c.toLayered pub hwf hone).V c.nl priv betas g q = wMle c.npub pub priv g :=
  toLayered_input pub hwf hone c.nl le_rfl priv betas g q

/-! ## Each layer is affine in its own `beta` -/

omit [Fintype F] in
/-- `evalGates` is affine in `beta`. -/
lemma evalGates_affine (gates : List (GateTerm F)) (b : F) (W : ℕ → F) (j : ℕ) :
    evalGates gates b W j
      = evalGates gates 0 W j + b * (evalGates gates 1 W j - evalGates gates 0 W j) := by
  unfold evalGates
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs
  · rw [prepV_affine ((gates.get i).v) b]; ring
  · ring

omit [Fintype F] in
/-- **Layer `ly`'s wires are affine in `betas ly`**: replacing `betas ly` by `b` moves them along a
line, with every other coordinate of the schedule held.  (`V_local`: they do not read
`betas i` for `i < ly`; this: they read `betas ly` affinely.  They are *not* affine in the deeper
`betas i`, `i > ly`, in general: those enter through products of hands.) -/
lemma wires_affine_beta (pub priv : Fin c.ninp → F) (betas : ℕ → F) (ly : ℕ) (b : F) (j : ℕ) :
    c.wires pub priv (Function.update betas ly b) ly j
      = c.wires pub priv (Function.update betas ly 0) ly j
        + b * (c.wires pub priv (Function.update betas ly 1) ly j
               - c.wires pub priv (Function.update betas ly 0) ly j) := by
  by_cases hly : ly < c.nl
  · have hnext : ∀ x : F, c.wires pub priv (Function.update betas ly x) (ly + 1)
        = c.wires pub priv betas (ly + 1) := fun x =>
      wires_local pub priv _ (ly + 1) rfl _ _ (fun i hi => by
        rw [Function.update_of_ne (by omega)])
    simp only [wires_lt hly, hnext, Function.update_self]
    exact evalGates_affine _ b _ j
  · simp only [wires_ge (show c.nl ≤ ly by omega)]
    ring

/-- **`V ly` is affine in `betas ly`.** -/
theorem toLayered_V_affine (pub : Fin c.ninp → F) {nv logw : ℕ} (hwf : c.WellFormed nv logw)
    (hone : c.OneWire pub) (ly : ℕ) (priv : Fin c.ninp → F) (betas : ℕ → F) (b : F)
    (g : Vector F logw) (q : Vector F 0) :
    (c.toLayered pub hwf hone).V ly priv (Function.update betas ly b) g q
      = (c.toLayered pub hwf hone).V ly priv (Function.update betas ly 0) g q
        + b * ((c.toLayered pub hwf hone).V ly priv (Function.update betas ly 1) g q
               - (c.toLayered pub hwf hone).V ly priv (Function.update betas ly 0) g q) := by
  show mle logw _ g = mle logw _ g + b * (mle logw _ g - mle logw _ g)
  unfold mle
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [wires_affine_beta pub priv betas ly b j]
  ring


/-! ## Semantic satisfaction -/

variable (c) in
/-- **The honest wire values**: the all-zero schedule, which is `ProverLayers::eval_circuit`
(`prep_v(v, 0) = v` for `v ≠ 0`, and an assert-zero term contributes nothing). -/
def honest (pub priv : Fin c.ninp → F) : ℕ → ℕ → F := c.wires pub priv (fun _ => 0)

variable (c) in
/--
**The circuit is satisfied** by the input `pub ++ priv`: every assert-zero term's hand product
is zero at the honest wires (`eval_quad`'s `y != F.zero()` check) and every output wire is zero
(the verifier starts from claims of zero, `verifier_layers.h:L70`).
-/
def Satisfied (pub priv : Fin c.ninp → F) : Prop :=
  (∀ ly < c.nl, ∀ t ∈ c.gates ly, t.v = 0 →
      c.honest pub priv (ly + 1) t.h0 * c.honest pub priv (ly + 1) t.h1 = 0) ∧
    ∀ j, c.honest pub priv 0 j = 0

omit [Fintype F] in
/-- A layer none of whose assertions fires evaluates the same at every `beta`. -/
lemma evalGates_of_asserts (gates : List (GateTerm F)) (b : F) (W : ℕ → F)
    (h : ∀ t ∈ gates, t.v = 0 → W t.h0 * W t.h1 = 0) (j : ℕ) :
    evalGates gates b W j = evalGates gates 0 W j := by
  unfold evalGates
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs
  · by_cases hv : (gates.get i).v = 0
    · have hz := h _ (List.get_mem _ _) hv
      simp only [prepV, hv, if_true]
      rw [mul_assoc, mul_assoc, hz]; ring
    · simp only [prepV]
      rw [if_neg hv, if_neg hv]
  · rfl

omit [Fintype F] in
/-- **A satisfied circuit's wires do not depend on the schedule**, at any layer. -/
theorem wires_of_satisfied {pub priv : Fin c.ninp → F} (hs : c.Satisfied pub priv)
    (betas : ℕ → F) : ∀ (k ly : ℕ), c.nl - ly = k →
      c.wires pub priv betas ly = c.honest pub priv ly
  | 0, ly, hk => by
      unfold honest
      rw [wires_ge (by omega), wires_ge (by omega)]
  | k + 1, ly, hk => by
      have hlt : ly < c.nl := by omega
      have ih := wires_of_satisfied hs betas k (ly + 1) (by omega)
      unfold honest at ih ⊢
      rw [wires_lt hlt, wires_lt hlt, ih]
      funext j
      exact evalGates_of_asserts _ _ _ (fun t ht hv => hs.1 ly hlt t ht hv) j

/-- **`Satisfied → V 0 = 0`, at every beta schedule** (and every point). -/
theorem toLayered_V0_of_satisfied (pub : Fin c.ninp → F) {nv logw : ℕ}
    (hwf : c.WellFormed nv logw) (hone : c.OneWire pub) {priv : Fin c.ninp → F}
    (hs : c.Satisfied pub priv) (betas : ℕ → F) (g : Vector F logw) (q : Vector F 0) :
    (c.toLayered pub hwf hone).V 0 priv betas g q = 0 := by
  show mle logw (c.wires pub priv betas 0) g = 0
  rw [wires_of_satisfied hs betas _ 0 rfl]
  unfold mle
  exact Finset.sum_eq_zero (fun j _ => by rw [hs.2 j, mul_zero])

/-- More generally, a satisfied circuit's `V ly` is schedule-free at every layer. -/
theorem toLayered_V_of_satisfied (pub : Fin c.ninp → F) {nv logw : ℕ}
    (hwf : c.WellFormed nv logw) (hone : c.OneWire pub) {priv : Fin c.ninp → F}
    (hs : c.Satisfied pub priv) (ly : ℕ) (betas betas' : ℕ → F) :
    (c.toLayered pub hwf hone).V ly priv betas = (c.toLayered pub hwf hone).V ly priv betas' := by
  funext g q
  show mle logw (c.wires pub priv betas ly) g = mle logw (c.wires pub priv betas' ly) g
  rw [wires_of_satisfied hs betas _ ly rfl, wires_of_satisfied hs betas' _ ly rfl]


/-! ## Where the schedule enters: assertion wires, and compiler correctness

`eval_quad` *checks* an assert-zero term and adds nothing; `prep_v` puts `betas ly · W[h0]·W[h1]`
on its output wire.  The compiler (`compiler.h`) gives every `assert0` node its own wire (a node
`0 * (1 * op)` with one term, `schedule.h` `order_by_layer`), needed at `depth + 1` only so that no
copy wire is made (`compute_needed`), and an assertion used as an operand degenerates to `0`
(`mul`'s `linearp` case with `k1 = 0`, `merge`'s `push_back_unless_zero`).  So in a compiled
circuit an assertion wire is **isolated** (the only term on its wire) and a **dead end** (no term
of the layer above reads it).  Only an assertion in the *last* compiler layer is turned into an
output (`fixup_last_layer_assertions`); every other one sits in an intermediate layer.
-/

variable (c) in
/-- Wire `j` of layer `ly` carries an assert-zero term. -/
def AssertWire (ly j : ℕ) : Prop := ∃ t ∈ c.gates ly, t.v = 0 ∧ t.g = j

variable (c) in
/-- **Assertions are dead ends**: no term reads an assert-zero wire of the layer below it. -/
def DeadEnd : Prop :=
  ∀ ly < c.nl, ∀ t ∈ c.gates ly, ¬ c.AssertWire (ly + 1) t.h0 ∧ ¬ c.AssertWire (ly + 1) t.h1

variable (c) in
/-- **Assertions are isolated**: an assert-zero term is the only term on its output wire. -/
def Isolated : Prop :=
  ∀ ly < c.nl, ∀ i k : Fin (c.gates ly).length, ((c.gates ly).get i).v = 0 →
    ((c.gates ly).get k).g = ((c.gates ly).get i).g → k = i

instance instDecidableDeadEnd : Decidable c.DeadEnd := by
  unfold DeadEnd AssertWire; infer_instance

instance instDecidableIsolated : Decidable c.Isolated := by
  unfold Isolated; infer_instance

omit [Fintype F] in
/-- The assertion part of a layer: wire `j` collects the hand products of its assert-zero terms.
This is the slope of `evalGates` in `beta`. -/
def assertSum (gates : List (GateTerm F)) (W : ℕ → F) (j : ℕ) : F :=
  ∑ i : Fin gates.length, if (gates.get i).g = j ∧ (gates.get i).v = 0 then
    W (gates.get i).h0 * W (gates.get i).h1 else 0

omit [Fintype F] in
lemma evalGates_split (gates : List (GateTerm F)) (b : F) (W : ℕ → F) (j : ℕ) :
    evalGates gates b W j = evalGates gates 0 W j + b * assertSum gates W j := by
  unfold evalGates assertSum
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hg : (gates.get i).g = j
  · by_cases hv : (gates.get i).v = 0
    · simp only [hg, hv, prepV, if_true, and_self]; ring
    · simp only [prepV]
      rw [if_pos hg, if_pos hg, if_neg hv, if_neg hv, if_neg (fun h => hv h.2)]; ring
  · rw [if_neg hg, if_neg hg, if_neg (fun h => hg h.1)]; ring

omit [Fintype F] in
/-- `evalGates` reads `W` only at the hands of its terms. -/
lemma evalGates_congr (gates : List (GateTerm F)) (b : F) {W W' : ℕ → F}
    (h : ∀ t ∈ gates, W t.h0 = W' t.h0 ∧ W t.h1 = W' t.h1) (j : ℕ) :
    evalGates gates b W j = evalGates gates b W' j := by
  unfold evalGates
  refine Finset.sum_congr rfl (fun i _ => ?_)
  obtain ⟨h0, h1⟩ := h _ (List.get_mem gates i)
  rw [h0, h1]

omit [Fintype F] in
/-- A wire with no assert-zero term has no slope. -/
lemma assertSum_eq_zero (gates : List (GateTerm F)) (W : ℕ → F) (j : ℕ)
    (h : ¬ ∃ t ∈ gates, t.v = 0 ∧ t.g = j) : assertSum gates W j = 0 := by
  unfold assertSum
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [if_neg]
  rintro ⟨hg, hv⟩
  exact h ⟨_, List.get_mem gates i, hv, hg⟩

omit [Fintype F] in
/-- **Under `DeadEnd`, every non-assertion wire is schedule-free**: it equals the honest value. -/
theorem wires_nonassert (hde : c.DeadEnd) (pub priv : Fin c.ninp → F) (betas : ℕ → F) :
    ∀ (k ly : ℕ), c.nl - ly = k → ∀ j, ¬ c.AssertWire ly j →
      c.wires pub priv betas ly j = c.honest pub priv ly j
  | 0, ly, hk, j, _ => by
      unfold honest
      rw [wires_ge (by omega), wires_ge (by omega)]
  | k + 1, ly, hk, j, hj => by
      have hlt : ly < c.nl := by omega
      have ih := wires_nonassert hde pub priv betas k (ly + 1) (by omega)
      have hhands : ∀ t ∈ c.gates ly, c.wires pub priv betas (ly + 1) t.h0
          = c.honest pub priv (ly + 1) t.h0 ∧
          c.wires pub priv betas (ly + 1) t.h1 = c.honest pub priv (ly + 1) t.h1 :=
        fun t ht => ⟨ih t.h0 (hde ly hlt t ht).1, ih t.h1 (hde ly hlt t ht).2⟩
      unfold honest at hhands ⊢
      rw [wires_lt hlt, wires_lt hlt, evalGates_congr _ _ hhands, evalGates_split,
        assertSum_eq_zero _ _ _ hj, mul_zero, add_zero]

variable (c) in
/-- **The assertion vector of layer `ly`** at the honest wires: wire `j` carries the hand
products of the assert-zero terms on it.  Schedule-free. -/
def assertVec (pub priv : Fin c.ninp → F) (ly : ℕ) : ℕ → F :=
  assertSum (c.gates ly) (c.honest pub priv (ly + 1))

omit [Fintype F] in
/--
**How the schedule enters a compiled circuit.**  Under `DeadEnd`, layer `ly`'s wires are the honest
(β-free) wires plus `betas ly` times the assertion vector, which is schedule-free:

    wires betas ly = honest ly + betas ly · assertVec ly.

So layer `ly` reads the schedule **only** through `betas ly`, and affinely.
-/
theorem wires_decomp (hde : c.DeadEnd) (pub priv : Fin c.ninp → F) (betas : ℕ → F) {ly : ℕ}
    (hly : ly < c.nl) (j : ℕ) :
    c.wires pub priv betas ly j = c.honest pub priv ly j + betas ly * c.assertVec pub priv ly j := by
  have hhands : ∀ t ∈ c.gates ly, c.wires pub priv betas (ly + 1) t.h0
      = c.honest pub priv (ly + 1) t.h0 ∧
      c.wires pub priv betas (ly + 1) t.h1 = c.honest pub priv (ly + 1) t.h1 :=
    fun t ht => ⟨wires_nonassert hde pub priv betas _ (ly + 1) rfl t.h0 (hde ly hly t ht).1,
      wires_nonassert hde pub priv betas _ (ly + 1) rfl t.h1 (hde ly hly t ht).2⟩
  rw [wires_lt hly, evalGates_congr _ _ hhands, evalGates_split, assertVec]
  congr 1
  unfold honest
  rw [wires_lt hly]

omit [Fintype F] in
/--
**Compiler correctness, in the form that is true.**  For a circuit whose assertions are isolated
(as compiled), the input is rejected exactly when an output wire is non-zero or some layer's
assertion vector is non-zero:

    ¬ Satisfied  ↔  (∃ j, honest 0 j ≠ 0)  ∨  ∃ ly < nl, ∃ j, assertVec ly j ≠ 0.

The `←` direction needs no hypothesis.
-/
theorem unsat_iff (hiso : c.Isolated) (pub priv : Fin c.ninp → F) :
    ¬ c.Satisfied pub priv ↔
      (∃ j, c.honest pub priv 0 j ≠ 0) ∨ ∃ ly < c.nl, ∃ j, c.assertVec pub priv ly j ≠ 0 := by
  constructor
  · intro hns
    by_contra hc
    push Not at hc
    obtain ⟨hout, hass⟩ := hc
    refine hns ⟨fun ly hly t ht hv => ?_, hout⟩
    obtain ⟨i, rfl⟩ := List.get_of_mem ht
    have h := hass ly hly ((c.gates ly).get i).g
    unfold assertVec assertSum at h
    rw [Finset.sum_eq_single i] at h
    · rwa [if_pos ⟨rfl, hv⟩] at h
    · intro k _ hki
      rw [if_neg]
      rintro ⟨hg, hvk⟩
      exact hki (hiso ly hly i k hv hg)
    · intro h'; exact absurd (Finset.mem_univ i) h'
  · rintro hor ⟨hs1, hs2⟩
    rcases hor with ⟨j, hj⟩ | ⟨ly, hly, j, hj⟩
    · exact hj (hs2 j)
    · apply hj
      unfold assertVec assertSum
      refine Finset.sum_eq_zero (fun i _ => ?_)
      split_ifs with h
      · exact hs1 ly hly _ (List.get_mem _ _) h.2
      · rfl


/-! ### The same statement about the constructed `V` -/

omit [DecidableEq F] [Fintype F] in
/-- An MLE is non-zero somewhere iff its vector is non-zero on the cube. -/
lemma mle_ne_zero_iff {n : ℕ} (v : ℕ → F) :
    (∃ g : Vector F n, mle n v g ≠ 0) ↔ ∃ j < 2 ^ n, v j ≠ 0 := by
  constructor
  · rintro ⟨g, hg⟩
    by_contra hc
    push Not at hc
    exact hg (Finset.sum_eq_zero (fun j hj => by rw [hc j (mem_range.mp hj), mul_zero]))
  · rintro ⟨j, hj, hv⟩
    exact ⟨boolean_vector j, by rwa [mle_bv v hj]⟩

omit [Fintype F] in
lemma evalGates_supp {nv : ℕ} (gates : List (GateTerm F)) (hg : ∀ t ∈ gates, t.g < nv) (b : F)
    (W : ℕ → F) {j : ℕ} (hj : nv ≤ j) : evalGates gates b W j = 0 := by
  unfold evalGates
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [if_neg]
  have := hg _ (List.get_mem gates i)
  omega

omit [Fintype F] in
/-- Every layer's wires vanish at and above `nv`. -/
lemma wires_supp {nv logw : ℕ} (hwf : c.WellFormed nv logw) (pub priv : Fin c.ninp → F)
    (betas : ℕ → F) (ly : ℕ) {j : ℕ} (hj : nv ≤ j) : c.wires pub priv betas ly j = 0 := by
  by_cases hly : ly < c.nl
  · rw [wires_lt hly]
    exact evalGates_supp _ (fun t ht => (hwf.2.2.2.2 ly hly t ht).1) _ _ hj
  · rw [wires_ge (by omega)]
    exact inputVec_supp pub priv j (le_trans hwf.2.1 hj)

omit [Fintype F] in
lemma assertVec_supp {nv logw : ℕ} (hwf : c.WellFormed nv logw) (pub priv : Fin c.ninp → F)
    {ly : ℕ} (hly : ly < c.nl) {j : ℕ} (hj : nv ≤ j) : c.assertVec pub priv ly j = 0 := by
  unfold assertVec assertSum
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [if_neg]
  have := (hwf.2.2.2.2 ly hly _ (List.get_mem _ i)).1
  omega

/-- Under `DeadEnd`, the constructed `V ly` is `V ly` at the zero schedule plus `betas ly` times the
MLE of the assertion vector. -/
theorem toLayered_V_decomp (pub : Fin c.ninp → F) {nv logw : ℕ} (hwf : c.WellFormed nv logw)
    (hone : c.OneWire pub) (hde : c.DeadEnd) {ly : ℕ} (hly : ly < c.nl) (priv : Fin c.ninp → F)
    (betas : ℕ → F) (g : Vector F logw) (q : Vector F 0) :
    (c.toLayered pub hwf hone).V ly priv betas g q
      = (c.toLayered pub hwf hone).V ly priv (fun _ => 0) g q
        + betas ly * mle logw (c.assertVec pub priv ly) g := by
  show mle logw (c.wires pub priv betas ly) g
    = mle logw (c.wires pub priv (fun _ => 0) ly) g + betas ly * mle logw _ g
  unfold mle
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [wires_decomp hde pub priv betas hly j]
  unfold honest
  ring

/--
**Compiler correctness, about the constructed `V`.**  For a compiled circuit (assertions isolated
and dead ends), the input is rejected exactly when

* the **output** layer's `V 0` is not identically zero as a function of the schedule (this covers
  the outputs and the assertions of layer `0`), or
* some **intermediate** layer `0 < ly < nl` has a `V ly` that moves with `betas ly`.

The second disjunct cannot be dropped: `cex_unsat`, `cex_V0` below.
-/
theorem toLayered_unsat_iff (pub : Fin c.ninp → F) {nv logw : ℕ} (hwf : c.WellFormed nv logw)
    (hone : c.OneWire pub) (hde : c.DeadEnd) (hiso : c.Isolated) (hnl : 0 < c.nl)
    (priv : Fin c.ninp → F) :
    ¬ c.Satisfied pub priv ↔
      (∃ (betas : ℕ → F) (g : Vector F logw),
          (c.toLayered pub hwf hone).V 0 priv betas g 0 ≠ 0) ∨
        ∃ ly, 0 < ly ∧ ly < c.nl ∧ ∃ (betas : ℕ → F) (g : Vector F logw),
          (c.toLayered pub hwf hone).V ly priv (Function.update betas ly 1) g 0
            ≠ (c.toLayered pub hwf hone).V ly priv (Function.update betas ly 0) g 0 := by
  have hcube : ∀ v : ℕ → F, (∀ j, nv ≤ j → v j = 0) →
      ((∃ j, v j ≠ 0) ↔ ∃ g : Vector F logw, mle logw v g ≠ 0) := by
    intro v hv
    rw [mle_ne_zero_iff]
    constructor
    · rintro ⟨j, hj⟩
      refine ⟨j, ?_, hj⟩
      by_contra hlt
      exact hj (hv j (le_trans hwf.1 (by omega)))
    · rintro ⟨j, _, hj⟩; exact ⟨j, hj⟩
  have hdec := fun ly hly betas g =>
    toLayered_V_decomp pub hwf hone hde (ly := ly) hly priv betas g 0
  rw [unsat_iff hiso]
  constructor
  · rintro (⟨j, hj⟩ | ⟨ly, hly, j, hj⟩)
    · left
      obtain ⟨g, hg⟩ := (hcube _ (fun j hj => wires_supp hwf pub priv _ 0 hj)).mp ⟨j, hj⟩
      exact ⟨fun _ => 0, g, hg⟩
    · obtain ⟨g, hg⟩ := (hcube _ (fun j hj => assertVec_supp hwf pub priv hly hj)).mp ⟨j, hj⟩
      rcases Nat.eq_zero_or_pos ly with h0 | hpos
      · subst h0
        left
        by_cases hz : (c.toLayered pub hwf hone).V 0 priv (fun _ => 0) g 0 = 0
        · refine ⟨fun _ => 1, g, ?_⟩
          rw [hdec 0 hly _ g, hz, zero_add, one_mul]
          exact hg
        · exact ⟨fun _ => 0, g, hz⟩
      · right
        refine ⟨ly, hpos, hly, fun _ => 0, g, ?_⟩
        have e1 := hdec ly hly (Function.update (fun _ => 0) ly 1) g
        have e0 := hdec ly hly (Function.update (fun _ => 0) ly 0) g
        rw [Function.update_self] at e1 e0
        rw [e1, e0]
        intro h
        apply hg
        linear_combination h
  · rintro (⟨betas, g, hg⟩ | ⟨ly, _, hly, betas, g, hg⟩)
    · rw [hdec 0 hnl betas g] at hg
      by_cases hz : mle logw (c.assertVec pub priv 0) g = 0
      · left
        rw [hz, mul_zero, add_zero] at hg
        exact (hcube _ (fun j hj => wires_supp hwf pub priv _ 0 hj)).mpr ⟨g, hg⟩
      · right
        exact ⟨0, hnl, (hcube _ (fun j hj => assertVec_supp hwf pub priv hnl hj)).mpr ⟨g, hz⟩⟩
    · right
      refine ⟨ly, hly, (hcube _ (fun j hj => assertVec_supp hwf pub priv hly hj)).mpr ⟨g, ?_⟩⟩
      intro hz
      apply hg
      have e1 := hdec ly hly (Function.update betas ly 1) g
      have e0 := hdec ly hly (Function.update betas ly 0) g
      rw [Function.update_self] at e1 e0
      rw [e1, e0, hz]
      ring

end QuadCircuit

/-! ## The output-only form of compiler correctness is false

"An unsatisfied input makes the **output** layer's wire vector non-zero for some schedule" fails
for compiled circuits as soon as an assertion sits in an intermediate layer, because the assertion
wire is a dead end: nothing above it reads `betas ly · (violation)`.  The deployed verifier still
rejects such an input — the claims it carries into that layer were fixed before `betas ly` is
drawn, and `V ly` moves with `betas ly` — but the evidence is at layer `ly`, not at the output.

`cex` is the circuit the compiler makes from `assert0(x); output((w·w)·w)` (inputs `1, x, w`):
depth `1` holds the copy `1·w`, the assertion `0·(1·x)` and `w·w`; depth `2` the output.  The
assertion has depth `1 < depth_ub = 3`, so `fixup_last_layer_assertions` leaves it in place.
-/

namespace Cex

/-- `assert0(x); output((w·w)·w)`, compiled.  Inputs: wire `0` = `1` (public), `1` = `x`,
`2` = `w`.  Layer `1`: `⟨0, 0, 2, 1⟩` (copy `w`), `⟨1, 0, 1, 0⟩` (assert `x = 0`),
`⟨2, 2, 2, 1⟩` (`w²`).  Layer `0`: `⟨0, 2, 0, 1⟩` (`w² · w`). -/
def cex : QuadCircuit F :=
  ⟨[[⟨0, 2, 0, 1⟩], [⟨0, 0, 2, 1⟩, ⟨1, 0, 1, 0⟩, ⟨2, 2, 2, 1⟩]], 3, 1⟩

/-- The public input: the constant one. -/
def cexPub : Fin (cex (F := F)).ninp → F := fun _ => 1

/-- The private input `x = 1`, `w = 0`: the output `w³ = 0` holds, the assertion `x = 0` fails. -/
def cexPriv : Fin (cex (F := F)).ninp → F := fun i => if i.val = 2 then 0 else 1

omit [DecidableEq F] in
lemma cex_nl : (cex (F := F)).nl = 2 := rfl
omit [DecidableEq F] in
lemma cex_gates0 : (cex (F := F)).gates 0 = [⟨0, 2, 0, 1⟩] := rfl
omit [DecidableEq F] in
lemma cex_gates1 :
    (cex (F := F)).gates 1 = [⟨0, 0, 2, 1⟩, ⟨1, 0, 1, 0⟩, ⟨2, 2, 2, 1⟩] := rfl
omit [DecidableEq F] in
lemma cex_gates2 : (cex (F := F)).gates 2 = [] := rfl
omit [DecidableEq F] in
lemma cex_npub : (cex (F := F)).npub = 1 := rfl

omit [DecidableEq F] in
theorem cex_wf : (cex (F := F)).WellFormed 4 2 := by
  refine ⟨by norm_num, by norm_num [cex], by norm_num [cex], by norm_num [cex], ?_⟩
  intro ly hly t ht
  rw [cex_nl] at hly
  interval_cases ly
  · rw [cex_gates0] at ht
    simp only [List.mem_singleton] at ht
    subst ht; simp
  · rw [cex_gates1] at ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> simp

omit [DecidableEq F] in
theorem cex_one : (cex (F := F)).OneWire cexPub := fun _ => rfl

omit [DecidableEq F] in
theorem cex_deadEnd : (cex (F := F)).DeadEnd := by
  intro ly hly t ht
  rw [cex_nl] at hly
  interval_cases ly
  · rw [cex_gates0] at ht
    simp only [List.mem_singleton] at ht
    subst ht
    simp [QuadCircuit.AssertWire, cex_gates1]
  · simp [QuadCircuit.AssertWire, cex_gates2]

omit [DecidableEq F] in
theorem cex_isolated : (cex (F := F)).Isolated := by
  intro ly hly i k hv hg
  rw [cex_nl] at hly
  obtain ⟨i, hi⟩ := i
  obtain ⟨k, hk⟩ := k
  apply Fin.ext
  simp only at hv hg ⊢
  interval_cases ly
  · have hi' : i < 1 := hi
    have hk' : k < 1 := hk
    omega
  · have hi' : i < 3 := hi
    have hk' : k < 3 := hk
    simp only [cex_gates1] at hv hg
    interval_cases i <;> interval_cases k <;> simp_all

omit [DecidableEq F] in
lemma cex_input (j : ℕ) :
    (cex (F := F)).inputVec cexPub cexPriv j
      = if j = 0 then 1 else if j = 1 then 1 else 0 := by
  unfold QuadCircuit.inputVec
  by_cases h : j < 3
  · rw [dif_pos (show j < (cex (F := F)).ninp from h)]
    interval_cases j <;> simp [wCol, cex_npub, cexPub, cexPriv]
  · rw [dif_neg (show ¬ j < (cex (F := F)).ninp from h), if_neg (by omega), if_neg (by omega)]

lemma prepV_one (b : F) : prepV (1 : F) b = 1 := by simp [prepV]

/-- **The input is rejected**: the assertion `x = 0` fails. -/
theorem cex_unsat : ¬ (cex (F := F)).Satisfied cexPub cexPriv := by
  rintro ⟨hass, -⟩
  have h := hass 1 (by rw [cex_nl]; norm_num) ⟨1, 0, 1, 0⟩ (by rw [cex_gates1]; simp) rfl
  unfold QuadCircuit.honest at h
  rw [QuadCircuit.wires_ge (show (cex (F := F)).nl ≤ 1 + 1 from le_rfl), cex_input,
    cex_input] at h
  simp at h

/-- **…but the output layer is zero at every schedule.** -/
theorem cex_wires0 (betas : ℕ → F) (j : ℕ) :
    (cex (F := F)).wires cexPub cexPriv betas 0 j = 0 := by
  have hw2 : (cex (F := F)).wires cexPub cexPriv betas 1 2 = 0 := by
    rw [QuadCircuit.wires_lt (show 1 < (cex (F := F)).nl by rw [cex_nl]; norm_num),
      QuadCircuit.evalGates_eq_list,
      QuadCircuit.wires_ge (show (cex (F := F)).nl ≤ 1 + 1 from le_rfl), cex_gates1]
    simp [cex_input]
  rw [QuadCircuit.wires_lt (show 0 < (cex (F := F)).nl by rw [cex_nl]; norm_num),
    QuadCircuit.evalGates_eq_list, cex_gates0]
  simp [hw2]

/-- `V 0 = 0` at every schedule and every point, although the input is rejected. -/
theorem cex_V0 [Fintype F] (betas : ℕ → F) (g : Vector F 2) (q : Vector F 0) :
    ((cex (F := F)).toLayered cexPub cex_wf cex_one).V 0 cexPriv betas g q = 0 := by
  show mle 2 _ g = 0
  unfold mle
  exact Finset.sum_eq_zero (fun j _ => by rw [cex_wires0, mul_zero])

/--
**The output-only form of compiler correctness is refuted**, on a well-formed circuit whose
assertions are isolated dead ends — exactly the shape the compiler emits.
-/
theorem output_only_false [Fintype F] :
    ¬ ∀ (c : QuadCircuit F) (pub priv : Fin c.ninp → F) {nv logw : ℕ}
        (hwf : c.WellFormed nv logw) (hone : c.OneWire pub),
        c.DeadEnd → c.Isolated → ¬ c.Satisfied pub priv →
          ∃ (betas : ℕ → F) (g : Vector F logw), (c.toLayered pub hwf hone).V 0 priv betas g 0 ≠ 0 := by
  intro h
  obtain ⟨betas, g, hg⟩ := h cex cexPub cexPriv cex_wf cex_one cex_deadEnd cex_isolated cex_unsat
  exact hg (cex_V0 betas g 0)

end Cex

/-! ## The initial point, counted (multilinear Schwartz–Zippel)

The deployed verifier draws the output point `G` at random (`begin_circuit`, `zk_common.h:L59`).
`Lfzk.ZkMultilinear.mlin_zero_card` counts the zeros of a non-zero multilinear function on
`Fin n → F`; the constructed `V` is one, through `Vector.ofFn`. -/

omit [Field F] [DecidableEq F] in
lemma ofFn_update {n : ℕ} (v : Fin n → F) (k : Fin n) (X : F) :
    Vector.ofFn (Function.update v k X) = (Vector.ofFn v).set k.val X k.isLt := by
  ext m hm
  rw [Vector.getElem_ofFn, Vector.getElem_set]
  by_cases h : k.val = m
  · rw [if_pos h]
    have : (⟨m, hm⟩ : Fin n) = k := Fin.ext h.symm
    rw [this, Function.update_self]
  · rw [if_neg h, Vector.getElem_ofFn, Function.update_of_ne]
    exact fun h' => h (by rw [← h'])

omit [DecidableEq F] in
/-- **An MLE is multilinear**, in `ZkMultilinear`'s sense. -/
lemma mle_mlin {n : ℕ} (c : ℕ → F) :
    ZkMultilinear.MLin (fun v : Fin n → F => mle n c (Vector.ofFn v)) := by
  intro v k
  have hml : IsMultilinear (fun g : Vector F n => mle n c g) :=
    IsMultilinear.sum _ _ (fun j => (eq_mle_basis_multilinear j).mul_const (c j))
  obtain ⟨a, b, hab⟩ := hml (Vector.ofFn v) k.val k.isLt
  exact ⟨a, b, fun X => by simp only [ofFn_update]; exact hab X⟩

omit [DecidableEq F] in
/-- The cube point `j` as a function `Fin n → F`. -/
lemma ofFn_bit {n : ℕ} (j : ℕ) :
    Vector.ofFn (fun k : Fin n => if bit_value j k.val = 1 then (1 : F) else 0)
      = boolean_vector j := rfl

/--
**The initial point's Schwartz–Zippel bound.**  If a cube vector is non-zero somewhere on the
cube, its MLE vanishes on at most `n · |F|^(n-1)` of the `|F|^n` points.
-/
theorem mle_zero_card [Fintype F] {n : ℕ} (c : ℕ → F)
    (hne : ∃ j < 2 ^ n, c j ≠ 0) :
    (univ.filter fun v : Fin n → F => mle n c (Vector.ofFn v) = 0).card
      ≤ n * Fintype.card F ^ (n - 1) := by
  obtain ⟨j, hj, hcj⟩ := hne
  refine ZkMultilinear.mlin_zero_card n _ (mle_mlin c)
    ⟨fun k => if bit_value j k.val = 1 then 1 else 0, ?_⟩
  show mle n c (Vector.ofFn _) ≠ 0
  rw [ofFn_bit, mle_bv c hj]
  exact hcj

namespace QuadCircuit

variable {c : QuadCircuit F} [Fintype F]

/-- **The output point, for the constructed circuit**: if the output layer's wires are non-zero on
the cube at a schedule, `V 0` vanishes on at most `logw · |F|^(logw-1)` output points. -/
theorem toLayered_out_zero_card (pub : Fin c.ninp → F) {nv logw : ℕ}
    (hwf : c.WellFormed nv logw) (hone : c.OneWire pub) (priv : Fin c.ninp → F) (betas : ℕ → F)
    (hne : ∃ j < 2 ^ logw, c.wires pub priv betas 0 j ≠ 0) :
    (univ.filter fun G : Fin logw → F =>
        (c.toLayered pub hwf hone).V 0 priv betas (Vector.ofFn G) 0 = 0).card
      ≤ logw * Fintype.card F ^ (logw - 1) :=
  mle_zero_card _ hne

/--
**Layer 0's slot over `(G, beta₀, alpha₀)`**, for the constructed circuit: the claim layer 0 starts
from at output point `G` (both claims at `G`, as `begin_circuit` sets them) is
`V₀(G) + alpha · V₀(G)` at the schedule `update tail 0 beta`; if the output layer is not identically
zero as a function of `beta₀` (the rest of the schedule held at `tail`), it vanishes on at most
`(logw + 2) · |F|^(logw + 1)` triples.  `ZkMultilinear.init_bad_card`, with multilinearity from
`mle_mlin` and the affine `beta₀` from `toLayered_V_affine`.
-/
theorem toLayered_init_card (pub : Fin c.ninp → F) {nv logw : ℕ}
    (hwf : c.WellFormed nv logw) (hone : c.OneWire pub) (priv : Fin c.ninp → F) (tail : ℕ → F)
    (hne : ∃ (b : F), ∃ j < 2 ^ logw, c.wires pub priv (Function.update tail 0 b) 0 j ≠ 0) :
    (univ.filter fun p : (Fin logw → F) × F × F =>
        (c.toLayered pub hwf hone).V 0 priv (Function.update tail 0 p.2.1) (Vector.ofFn p.1) 0
          + p.2.2 * (c.toLayered pub hwf hone).V 0 priv (Function.update tail 0 p.2.1)
              (Vector.ofFn p.1) 0 = 0).card
      ≤ (logw + 2) * Fintype.card F ^ (logw + 1) := by
  refine ZkMultilinear.init_bad_card
    (fun b G => (c.toLayered pub hwf hone).V 0 priv (Function.update tail 0 b) (Vector.ofFn G) 0)
    (fun b => mle_mlin _) (fun b G => ?_) ?_
  · have h := toLayered_V_affine pub hwf hone 0 priv tail b (Vector.ofFn G) 0
    simpa only [Function.update_idem] using h
  · obtain ⟨b, j, hj, hw⟩ := hne
    refine ⟨b, fun k => if bit_value j k.val = 1 then 1 else 0, ?_⟩
    show mle logw _ (Vector.ofFn _) ≠ 0
    rw [ofFn_bit, mle_bv _ hj]
    exact hw

/-- Under `DeadEnd`, layer 0's wires are `honest 0 + beta₀ · assertVec 0` whatever the tail, so the
non-degeneracy `toLayered_init_card` needs is exactly "an output wire or a layer-0 assertion is
violated". -/
theorem toLayered_init_card_of_top (pub : Fin c.ninp → F) {nv logw : ℕ}
    (hwf : c.WellFormed nv logw) (hone : c.OneWire pub) (hde : c.DeadEnd) (hnl : 0 < c.nl)
    (priv : Fin c.ninp → F) (tail : ℕ → F)
    (htop : (∃ j, c.honest pub priv 0 j ≠ 0) ∨ ∃ j, c.assertVec pub priv 0 j ≠ 0) :
    (univ.filter fun p : (Fin logw → F) × F × F =>
        (c.toLayered pub hwf hone).V 0 priv (Function.update tail 0 p.2.1) (Vector.ofFn p.1) 0
          + p.2.2 * (c.toLayered pub hwf hone).V 0 priv (Function.update tail 0 p.2.1)
              (Vector.ofFn p.1) 0 = 0).card
      ≤ (logw + 2) * Fintype.card F ^ (logw + 1) := by
  refine toLayered_init_card pub hwf hone priv tail ?_
  have hdec : ∀ b j, c.wires pub priv (Function.update tail 0 b) 0 j
      = c.honest pub priv 0 j + b * c.assertVec pub priv 0 j := fun b j => by
    rw [wires_decomp hde pub priv _ hnl j, Function.update_self]
  have hlt : ∀ j, (c.honest pub priv 0 j ≠ 0 ∨ c.assertVec pub priv 0 j ≠ 0) → j < 2 ^ logw := by
    intro j hj
    by_contra hge
    have hge' : nv ≤ j := le_trans hwf.1 (by omega)
    rcases hj with h | h
    · exact h (wires_supp hwf pub priv _ 0 hge')
    · exact h (assertVec_supp hwf pub priv hnl hge')
  rcases htop with ⟨j, hj⟩ | ⟨j, hj⟩
  · exact ⟨0, j, hlt j (Or.inl hj), by rw [hdec, zero_mul, add_zero]; exact hj⟩
  · by_cases h0 : c.honest pub priv 0 j = 0
    · exact ⟨1, j, hlt j (Or.inr hj), by rw [hdec, h0, zero_add, one_mul]; exact hj⟩
    · exact ⟨0, j, hlt j (Or.inl h0), by rw [hdec, zero_mul, add_zero]; exact h0⟩

end QuadCircuit
end Lfzk.Arith
