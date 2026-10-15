import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring.RingNF
import Merkle.CommitCollision

/-!
# Hiding simulator

This file gives the exact simulator, finite counting kernels, and normalized
real/sim coupling theorems.  All oracle, commitment, simulator, and adversary
coins live in one explicit finite sample space `Ω`.  Bounds are stated by
cross multiplication, so adding unrelated coins to `Ω` cannot change the
claimed probability.
-/

open Finset

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Merkle

namespace MH

universe uSalt uMsg uDigest uEnc uView

variable {Salt : Type uSalt} {M : Type uMsg} {D : Type uDigest}
variable {Enc : Type uEnc}
variable (S : Scheme Salt M D Enc) [Inhabited D]

/-- Opening simulator coins: fresh nonces for opened leaves and simulated
roots for every frontier subtree. -/
structure SimulatorCoins (n : ℕ) (I : Finset (Fin n))
    (Salt : Type uSalt) (D : Type uDigest) where
  nonce : (i : {i : Fin n // i ∈ I}) → Salt
  frontierRoot : (v : {v : ℕ // v ∈ Heap.frontier n I}) → D

/-- The simulator's exact proof is just its sampled coordinates. -/
def simulateProof (n : ℕ) (I : Finset (Fin n))
    (coins : SimulatorCoins n I Salt D) : Opening n I Salt D where
  nonce := coins.nonce
  frontierValue := coins.frontierRoot

/-- The simulator derives the root by running the same deterministic
bottom-up recurrence as the verifier. -/
noncomputable def simulateRoot (n : ℕ) (I : Finset (Fin n))
    (a : Fin n → M) (coins : SimulatorCoins n I Salt D) : D :=
  checkValues S n I a (simulateProof n I coins) 1

/-- Every simulated nonempty opening verifies, for every oracle and every
choice of simulator coins. -/
theorem mh_simulated_opening_accepts (n : ℕ) (I : Finset (Fin n))
    (hI : I.Nonempty) (a : Fin n → M)
    (coins : SimulatorCoins n I Salt D) :
    Accepts S n
      (simulateRoot S n I a coins) I a
      (simulateProof n I coins) := by
  exact ⟨hI, rfl⟩

/-- The root together with the exact opening data is the view exposed by the
Merkle commitment/opening interface. -/
structure OpeningView (n : ℕ) (I : Finset (Fin n))
    (Salt : Type uSalt) (D : Type uDigest) where
  rt : D
  proof : Opening n I Salt D

/-! ## Root hiding: the two-message statement

The view a distinguisher gets is *(oracle access, root)*.  The experiment runs the honest commitment
first, from an empty seen-list, so off the commitment-collision events its `j`-th distinct query is
slot `j`: `commitPass_root_eq_tape` puts each honest root at the constant slot `2n-2`, and an input
queried by neither of two commitments gets slot `2n-1` under both.  The distinguisher's execution is
then replayed verbatim, and the remaining bad event — the distinguisher querying a commitment input —
is costed by nonce guessing and the first-collision induction of `CommitCollision.lean`. -/

section RootHiding

variable {V : Type uView}

/-- The commitment's own occupied slots. -/
def commitSeen [DecidableEq Enc] (C : Codec Salt M D Enc) (n : ℕ) (nonce : Fin n → Salt)
    (m : Fin n → M) {T : ℕ} (answers : Fin T → D) : List Enc :=
  (RandomOracle.lazyRun answers default
    (commitPass C n nonce m (2 * n - 1) fun _ => default) []).2.1

/-- Off the collision events the commitment occupies exactly `2n-1` slots. -/
theorem commitSeen_length [DecidableEq Enc] (C : Codec Salt M D Enc) (n : ℕ) (hn : 0 < n)
    (nonce : Fin n → Salt) (m : Fin n → M) {T : ℕ} (answers : Fin T → D)
    (hinj : commitInputsInjective C n nonce m (commitOracle C n nonce m answers)) :
    (commitSeen C n nonce m answers).length = 2 * n - 1 := by
  classical
  have hinvinit : ∀ v, 2 * n - 1 < v →
      (fun _ => (default : D)) v =
        commitLabels (C.withOracle (commitOracle C n nonce m answers)) n nonce m v :=
    fun v hv => (commitLabels_of_ge (S := C.withOracle (commitOracle C n nonce m answers))
      n nonce m v (by omega)).symm
  have hrun : (commitPass C n nonce m (2 * n - 1) fun _ => default).run
        (commitOracle C n nonce m answers) =
      ((RandomOracle.lazyRun answers default
          (commitPass C n nonce m (2 * n - 1) fun _ => default) []).1,
        (RandomOracle.lazyRun answers default
          (commitPass C n nonce m (2 * n - 1) fun _ => default) []).2.2) :=
    RandomOracle.lazyRun_eq_run answers default _ [] _ fun _ => rfl
  have htr : ((commitPass C n nonce m (2 * n - 1) fun _ => default).run
        (commitOracle C n nonce m answers)).2 =
      (RandomOracle.lazyRun answers default
        (commitPass C n nonce m (2 * n - 1) fun _ => default) []).2.2 := by
    rw [hrun]
  have hnd := commitPass_trace_nodup C n nonce m (commitOracle C n nonce m answers) hinj
    (2 * n - 1) _ (by omega) hinvinit
  rw [commitSeen, RandomOracle.lazyRun_seen_eq_of_nodup answers default _ []
    (by rw [← htr]; exact hnd) (by simp), List.nil_append, List.length_map, ← htr]
  exact commitPass_trace_length C n hn nonce m _ (2 * n - 1) _ (le_refl _)

/-- Membership in the commitment's seen-list identifies a heap vertex. -/
theorem mem_commitSeen_vertex [DecidableEq Enc] (C : Codec Salt M D Enc) (n : ℕ)
    (nonce : Fin n → Salt) (m : Fin n → M) {T : ℕ} (answers : Fin T → D) (x : Enc)
    (hx : x ∈ commitSeen C n nonce m answers) :
    ∃ v, 0 < v ∧ v ≤ 2 * n - 1 ∧
      commitInput C n nonce m (commitOracle C n nonce m answers) v = some x := by
  classical
  have hinvinit : ∀ v, 2 * n - 1 < v →
      (fun _ => (default : D)) v =
        commitLabels (C.withOracle (commitOracle C n nonce m answers)) n nonce m v :=
    fun v hv => (commitLabels_of_ge (S := C.withOracle (commitOracle C n nonce m answers))
      n nonce m v (by omega)).symm
  have hrun : (commitPass C n nonce m (2 * n - 1) fun _ => default).run
        (commitOracle C n nonce m answers) =
      ((RandomOracle.lazyRun answers default
          (commitPass C n nonce m (2 * n - 1) fun _ => default) []).1,
        (RandomOracle.lazyRun answers default
          (commitPass C n nonce m (2 * n - 1) fun _ => default) []).2.2) :=
    RandomOracle.lazyRun_eq_run answers default _ [] _ fun _ => rfl
  have htr : ((commitPass C n nonce m (2 * n - 1) fun _ => default).run
        (commitOracle C n nonce m answers)).2 =
      (RandomOracle.lazyRun answers default
        (commitPass C n nonce m (2 * n - 1) fun _ => default) []).2.2 := by
    rw [hrun]
  obtain ⟨y, hy⟩ := RandomOracle.lazyRun_mem_trace_of_mem_seen answers default
    (commitPass C n nonce m (2 * n - 1) fun _ => default) [] x hx (by simp)
  exact mem_commitPass_trace_vertex C n nonce m (commitOracle C n nonce m answers)
    (2 * n - 1) _ hinvinit x (by rw [htr]; exact List.mem_map.mpr ⟨(x, y), hy, rfl⟩)

/-- The hiding sample space: a nonce schedule and an answer tape. -/
abbrev HidingSample (n T : ℕ) (Salt : Type uSalt) (D : Type uDigest) :=
  (Fin n → Salt) × (Fin T → D)

/-! ### Two commitments with a partially shared seen-list

`lazyRun_congr_of_base` asks the distinguisher to avoid *both* commitments' inputs.  For root hiding
that is the right hypothesis, but for **opening** hiding it is unsatisfiable in practice: the opening
reveals the opened nonces and the frontier digests, so a distinguisher can recompute an opened leaf's
input and query it deliberately.  Those queries are harmless — the two commitments present the *same*
input there — and `RandomOracle.BaseCompat` is what makes that precise.

The two seen-lists agree except at the leaves where the messages differ: leaf inputs elsewhere are
literally equal, and node inputs are equal because `commitLabels_eq_tape` makes every honest label a
message-independent tape entry.  So a query outside that difference set sees the two bases identically,
and the runs stay in lockstep. -/

/-- **A commitment input's slot.**  Vertex `v`'s input occupies slot `2n-1-v` of the commitment's
seen-list — the query counterpart of `commitLabels_eq_tape`. -/
theorem commitSeen_idxOf_eq [DecidableEq Enc] (C : Codec Salt M D Enc) (n : ℕ) (hn : 0 < n)
    (nonce : Fin n → Salt) (m : Fin n → M) {T : ℕ} (answers : Fin T → D)
    (hinj : commitInputsInjective C n nonce m (commitOracle C n nonce m answers))
    (v : ℕ) (hv1 : 1 ≤ v) (hv : v ≤ 2 * n - 1) (q : Enc)
    (hq : commitInput C n nonce m (commitOracle C n nonce m answers) v = some q) :
    (commitSeen C n nonce m answers).idxOf q = 2 * n - 1 - v := by
  classical
  have hinvinit : ∀ w, 2 * n - 1 < w →
      (fun _ => (default : D)) w =
        commitLabels (C.withOracle (commitOracle C n nonce m answers)) n nonce m w :=
    fun w hw => (commitLabels_of_ge (S := C.withOracle (commitOracle C n nonce m answers))
      n nonce m w (by omega)).symm
  have hrun : (commitPass C n nonce m (2 * n - 1) fun _ => default).run
        (commitOracle C n nonce m answers) =
      ((RandomOracle.lazyRun answers default
          (commitPass C n nonce m (2 * n - 1) fun _ => default) []).1,
        (RandomOracle.lazyRun answers default
          (commitPass C n nonce m (2 * n - 1) fun _ => default) []).2.2) :=
    RandomOracle.lazyRun_eq_run answers default _ [] _ fun _ => rfl
  have htr : ((commitPass C n nonce m (2 * n - 1) fun _ => default).run
        (commitOracle C n nonce m answers)).2 =
      (RandomOracle.lazyRun answers default
        (commitPass C n nonce m (2 * n - 1) fun _ => default) []).2.2 := by
    rw [hrun]
  have hlen : ((commitPass C n nonce m (2 * n - 1) fun _ => default).run
      (commitOracle C n nonce m answers)).2.length = 2 * n - 1 :=
    commitPass_trace_length C n hn nonce m _ (2 * n - 1) _ (le_refl _)
  have hnd : ((((commitPass C n nonce m (2 * n - 1) fun _ => default).run
      (commitOracle C n nonce m answers)).2.map Prod.fst).Nodup) :=
    commitPass_trace_nodup C n nonce m _ hinj (2 * n - 1) _ (by omega) hinvinit
  have hfst := commitPass_trace_getElem_fst C n nonce m (commitOracle C n nonce m answers)
    (2 * n - 1) _ (le_refl _) hinvinit v hv1 hv
  rw [hq] at hfst
  obtain ⟨qa, hqamem, hqafst⟩ := Option.map_eq_some_iff.mp hfst
  have hlt : 2 * n - 1 - v < ((RandomOracle.lazyRun answers default
      (commitPass C n nonce m (2 * n - 1) fun _ => default) []).2.2.map Prod.fst).length := by
    rw [List.length_map, ← htr, hlen]
    omega
  have hget : ((RandomOracle.lazyRun answers default
      (commitPass C n nonce m (2 * n - 1) fun _ => default) []).2.2.map
        Prod.fst)[2 * n - 1 - v] = q := by
    rw [← Option.some_inj, ← List.getElem?_eq_getElem hlt, ← htr, List.getElem?_map, hqamem,
      Option.map_some, hqafst]
  show (RandomOracle.lazyRun answers default
      (commitPass C n nonce m (2 * n - 1) fun _ => default) []).2.1.idxOf q = 2 * n - 1 - v
  rw [← hget]
  exact RandomOracle.lazyRun_slot_eq_of_nodup answers default _ (by rw [← htr]; exact hnd) _ hlt

/-- A vertex's input is in the commitment's seen-list. -/
theorem mem_commitSeen_of_commitInput [DecidableEq Enc] (C : Codec Salt M D Enc) (n : ℕ)
    (hn : 0 < n) (nonce : Fin n → Salt) (m : Fin n → M) {T : ℕ} (answers : Fin T → D)
    (hinj : commitInputsInjective C n nonce m (commitOracle C n nonce m answers))
    (v : ℕ) (hv1 : 1 ≤ v) (hv : v ≤ 2 * n - 1) (q : Enc)
    (hq : commitInput C n nonce m (commitOracle C n nonce m answers) v = some q) :
    q ∈ commitSeen C n nonce m answers := by
  by_contra hc
  have h1 : (commitSeen C n nonce m answers).idxOf q =
      (commitSeen C n nonce m answers).length := List.idxOf_eq_length hc
  rw [commitSeen_length C n hn nonce m answers hinj,
    commitSeen_idxOf_eq C n hn nonce m answers hinj v hv1 hv q hq] at h1
  omega

/-- **The two commitments present the same input at every vertex outside `E`.**  Leaves outside `E`
carry equal nonce-message pairs; every internal vertex's node input is the same tape pair for both, by
`commitLabels_eq_tape`.  Both the nonce and the message may vary — the nonce case is what a
per-coordinate nonce count needs. -/
theorem commitInput_congr_off [DecidableEq Enc] (C : Codec Salt M D Enc) (n : ℕ) (hn : 0 < n)
    (nonce₀ nonce₁ : Fin n → Salt) (m₀ m₁ : Fin n → M) {T : ℕ} (answers : Fin T → D)
    (hinj₀ : commitInputsInjective C n nonce₀ m₀ (commitOracle C n nonce₀ m₀ answers))
    (hinj₁ : commitInputsInjective C n nonce₁ m₁ (commitOracle C n nonce₁ m₁ answers))
    (hT : 2 * n - 2 < T)
    (E : Finset (Fin n)) (hagree : ∀ i : Fin n, i ∉ E → nonce₀ i = nonce₁ i ∧ m₀ i = m₁ i)
    (v : ℕ) (hv1 : 1 ≤ v)
    (hvE : ∀ i ∈ E, v ≠ n + i.val) :
    commitInput C n nonce₀ m₀ (commitOracle C n nonce₀ m₀ answers) v =
      commitInput C n nonce₁ m₁ (commitOracle C n nonce₁ m₁ answers) v := by
  rw [commitInput, commitInput]
  split
  · rename_i hleaf
    have hiE : (⟨v - n, by omega⟩ : Fin n) ∉ E := by
      intro hc
      refine hvE _ hc ?_
      show v = n + (v - n)
      omega
    rw [(hagree _ hiE).1, (hagree _ hiE).2]
  · split
    · rename_i hint
      have hlab : ∀ w : ℕ, 1 ≤ w → w ≤ 2 * n - 1 →
          commitLabels (C.withOracle (commitOracle C n nonce₀ m₀ answers)) n nonce₀ m₀ w =
            commitLabels (C.withOracle (commitOracle C n nonce₁ m₁ answers)) n nonce₁ m₁ w := by
        intro w hw1 hw
        rw [commitLabels_eq_tape C n hn nonce₀ m₀ answers hinj₀ w hw1 hw (by omega),
          commitLabels_eq_tape C n hn nonce₁ m₁ answers hinj₁ w hw1 hw (by omega)]
      rw [hlab (2 * v) (by omega) (by omega), hlab (2 * v + 1) (by omega) (by omega)]
    · rfl

/-- **The seen-lists are interchangeable outside the differing leaves' inputs.**  This is the
hypothesis `RandomOracle.lazyRun_congr_of_base_compat` consumes.  It lets an opening-hiding
distinguisher query the *shared* commitment inputs — which it can always do — without the argument
breaking, and it is also what makes two nonce schedules differing at one coordinate interchangeable. -/
theorem commitSeen_baseCompat [DecidableEq Enc] (C : Codec Salt M D Enc) (n : ℕ) (hn : 0 < n)
    (nonce₀ nonce₁ : Fin n → Salt) (m₀ m₁ : Fin n → M) {T : ℕ} (answers : Fin T → D)
    (hinj₀ : commitInputsInjective C n nonce₀ m₀ (commitOracle C n nonce₀ m₀ answers))
    (hinj₁ : commitInputsInjective C n nonce₁ m₁ (commitOracle C n nonce₁ m₁ answers))
    (hT : 2 * n - 2 < T)
    (E : Finset (Fin n)) (hagree : ∀ i : Fin n, i ∉ E → nonce₀ i = nonce₁ i ∧ m₀ i = m₁ i)
    (q : Enc)
    (hq : ∀ i ∈ E, q ≠ C.leafEnc (nonce₀ i, m₀ i) ∧ q ≠ C.leafEnc (nonce₁ i, m₁ i)) :
    RandomOracle.BaseCompat (commitSeen C n nonce₀ m₀ answers)
      (commitSeen C n nonce₁ m₁ answers) q := by
  classical
  have hwit : ∀ (nA : Fin n → Salt) (mA : Fin n → M),
      (∀ i ∈ E, q ≠ C.leafEnc (nA i, mA i)) →
      ∀ v, n ≤ v → v < 2 * n →
        commitInput C n nA mA (commitOracle C n nA mA answers) v = some q →
        ∀ i ∈ E, v ≠ n + i.val := by
    intro nA mA hqA v hv1 hv2 hvq i hi hveq
    refine hqA i hi ?_
    rw [commitInput, dif_pos (show n ≤ v ∧ v < 2 * n from ⟨hv1, hv2⟩)] at hvq
    have hvi : (⟨v - n, by omega⟩ : Fin n) = i := by
      refine Fin.ext ?_
      show v - n = i.val
      omega
    rw [← hvi]
    exact (Option.some_inj.mp hvq).symm
  have hstep : ∀ (nA nB : Fin n → Salt) (mA mB : Fin n → M),
      commitInputsInjective C n nA mA (commitOracle C n nA mA answers) →
      commitInputsInjective C n nB mB (commitOracle C n nB mB answers) →
      (∀ i : Fin n, i ∉ E → nA i = nB i ∧ mA i = mB i) →
      (∀ i ∈ E, q ≠ C.leafEnc (nA i, mA i)) →
      q ∈ commitSeen C n nA mA answers →
      ∃ v, 1 ≤ v ∧ v ≤ 2 * n - 1 ∧
        commitInput C n nA mA (commitOracle C n nA mA answers) v = some q ∧
        commitInput C n nB mB (commitOracle C n nB mB answers) v = some q := by
    intro nA nB mA mB hA hB hab hqA hqmem
    obtain ⟨v, hv0, hv1, hvq⟩ := mem_commitSeen_vertex C n nA mA answers q hqmem
    refine ⟨v, by omega, hv1, hvq, ?_⟩
    have hvE : ∀ i ∈ E, v ≠ n + i.val := by
      intro i hi
      by_cases hleaf : n ≤ v ∧ v < 2 * n
      · exact hwit nA mA hqA v hleaf.1 hleaf.2 hvq i hi
      · have := i.isLt
        intro hc
        omega
    rw [← commitInput_congr_off C n hn nA nB mA mB answers hA hB hT E hab v (by omega) hvE]
    exact hvq
  have hq₀ : ∀ i ∈ E, q ≠ C.leafEnc (nonce₀ i, m₀ i) := fun i hi => (hq i hi).1
  have hq₁ : ∀ i ∈ E, q ≠ C.leafEnc (nonce₁ i, m₁ i) := fun i hi => (hq i hi).2
  have hagree' : ∀ i : Fin n, i ∉ E → nonce₁ i = nonce₀ i ∧ m₁ i = m₀ i :=
    fun i hi => ⟨(hagree i hi).1.symm, (hagree i hi).2.symm⟩
  constructor
  · constructor
    · intro h
      obtain ⟨v, hv1, hv, -, hvB⟩ := hstep nonce₀ nonce₁ m₀ m₁ hinj₀ hinj₁ hagree hq₀ h
      exact mem_commitSeen_of_commitInput C n hn nonce₁ m₁ answers hinj₁ v hv1 hv q hvB
    · intro h
      obtain ⟨v, hv1, hv, -, hvB⟩ := hstep nonce₁ nonce₀ m₁ m₀ hinj₁ hinj₀ hagree' hq₁ h
      exact mem_commitSeen_of_commitInput C n hn nonce₀ m₀ answers hinj₀ v hv1 hv q hvB
  · by_cases h : q ∈ commitSeen C n nonce₀ m₀ answers
    · obtain ⟨v, hv1, hv, hvA, hvB⟩ := hstep nonce₀ nonce₁ m₀ m₁ hinj₀ hinj₁ hagree hq₀ h
      rw [commitSeen_idxOf_eq C n hn nonce₀ m₀ answers hinj₀ v hv1 hv q hvA,
        commitSeen_idxOf_eq C n hn nonce₁ m₁ answers hinj₁ v hv1 hv q hvB]
    · have h₁ : q ∉ commitSeen C n nonce₁ m₁ answers := by
        intro hc
        obtain ⟨v, hv1, hv, -, hvB⟩ := hstep nonce₁ nonce₀ m₁ m₀ hinj₁ hinj₀ hagree' hq₁ hc
        exact h (mem_commitSeen_of_commitInput C n hn nonce₀ m₀ answers hinj₀ v hv1 hv q hvB)
      rw [List.idxOf_eq_length h, List.idxOf_eq_length h₁,
        commitSeen_length C n hn nonce₀ m₀ answers hinj₀,
        commitSeen_length C n hn nonce₁ m₁ answers hinj₁]

/-- **One coordinate's nonce is caught at most `2f` times.**  With the tape and every other nonce
fixed, at most `2f` values of `nonce i` lead the distinguisher to query that leaf's own input under
*either* message.

`RandomOracle.caught_card_le` instantiated: the candidate space is `Salt`, the two markers are the leaf
encodings under `m₀` and `m₁` — each injective, so one query is a marker for at most two candidates —
and `commitSeen_baseCompat` supplies the interchangeability, needing only the `m₀` markers avoided
since the base family is `m₀`'s.  There is no guess *list*: the run's queries genuinely depend on the
secret, and the count survives that. -/
theorem leafCatch_card_le [Fintype Salt] [DecidableEq Salt] [DecidableEq Enc]
    {V : Type uView} (C : Codec Salt M D Enc) (n : ℕ) (hn : 0 < n) (m₀ m₁ : Fin n → M) {T : ℕ}
    (answers : Fin T → D) (hT : 2 * n - 2 < T) (i : Fin n)
    (nonceOf : Salt → Fin n → Salt)
    (hoff : ∀ s t : Salt, ∀ j : Fin n, j ≠ i → nonceOf s j = nonceOf t j)
    (hat : ∀ s : Salt, nonceOf s i = s)
    (hsalt₀ : Function.Injective fun s : Salt => C.leafEnc (s, m₀ i))
    (hsalt₁ : Function.Injective fun s : Salt => C.leafEnc (s, m₁ i))
    (G : Finset Salt)
    (hinj : ∀ s ∈ G,
      commitInputsInjective C n (nonceOf s) m₀ (commitOracle C n (nonceOf s) m₀ answers))
    {f : ℕ} (c : RandomOracle.Tree Enc D V f)
    (hG : ∀ s ∈ G,
      C.leafEnc (s, m₀ i) ∈ (RandomOracle.lazyRun answers default c
          (commitSeen C n (nonceOf s) m₀ answers)).2.2.map Prod.fst ∨
        C.leafEnc (s, m₁ i) ∈ (RandomOracle.lazyRun answers default c
          (commitSeen C n (nonceOf s) m₀ answers)).2.2.map Prod.fst) :
    G.card ≤ 2 * f := by
  refine RandomOracle.caught_card_le answers default c _ _ _ hsalt₀ hsalt₁ G ?_ ?_ hG
  · intro s hs t ht
    rw [commitSeen_length C n hn (nonceOf s) m₀ answers (hinj s hs),
      commitSeen_length C n hn (nonceOf t) m₀ answers (hinj t ht)]
  · intro s hs t ht q hqs _ hqt _
    refine commitSeen_baseCompat C n hn (nonceOf s) (nonceOf t) m₀ m₀ answers (hinj s hs)
      (hinj t ht) hT {i} (fun j hj => ⟨hoff s t j (by simpa using hj), rfl⟩) q ?_
    intro j hj
    rw [Finset.mem_singleton] at hj
    subst hj
    exact ⟨by rw [hat]; exact hqs, by rw [hat]; exact hqt⟩

/-- **The per-coordinate hit, over the whole sample space.**  Fibering by (all other nonces, tape) and
applying `leafCatch_card_le` on each fibre: at most `2f` of the `|Salt|` values of `nonce i` are caught,
so a `2f/|Salt|` fraction, per coordinate.

`tree` is the distinguisher's execution as a function of the fibre — which is what makes this usable:
for an *unopened* coordinate the view it is given does not mention `nonce i`. -/
theorem leafCatch_prod_card_le [Fintype Salt] [DecidableEq Salt] [Fintype D] [DecidableEq D]
    [DecidableEq Enc] {V : Type uView} (C : Codec Salt M D Enc) (n : ℕ) (hn : 0 < n) {T : ℕ}
    (m₀ m₁ : (Fin T → D) → Fin n → M) (hT : 2 * n - 2 < T) (i : Fin n) {f : ℕ}
    (tree : ({j : Fin n // j ≠ i} → Salt) → (Fin T → D) → RandomOracle.Tree Enc D V f)
    (hsalt₀ : ∀ tape : Fin T → D, Function.Injective fun s : Salt => C.leafEnc (s, m₀ tape i))
    (hsalt₁ : ∀ tape : Fin T → D, Function.Injective fun s : Salt => C.leafEnc (s, m₁ tape i))
    (bad : Finset (HidingSample n T Salt D))
    (hinj : ∀ ω ∈ bad,
      commitInputsInjective C n ω.1 (m₀ ω.2) (commitOracle C n ω.1 (m₀ ω.2) ω.2))
    (hbad : ∀ ω ∈ bad,
      C.leafEnc (ω.1 i, m₀ ω.2 i) ∈ (RandomOracle.lazyRun ω.2 default
          (tree (fun j => ω.1 j.val) ω.2) (commitSeen C n ω.1 (m₀ ω.2) ω.2)).2.2.map Prod.fst ∨
        C.leafEnc (ω.1 i, m₁ ω.2 i) ∈ (RandomOracle.lazyRun ω.2 default
          (tree (fun j => ω.1 j.val) ω.2)
          (commitSeen C n ω.1 (m₀ ω.2) ω.2)).2.2.map Prod.fst) :
    bad.card ≤ (Fintype.card Salt) ^ (n - 1) * (Fintype.card D) ^ T * (2 * f) := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun ω : HidingSample n T Salt D => ((fun j : {j : Fin n // j ≠ i} => ω.1 j.val), ω.2))
    (t := (Finset.univ : Finset (({j : Fin n // j ≠ i} → Salt) × (Fin T → D))))
    (fun _ _ => Finset.mem_univ _)]
  calc ∑ p : ({j : Fin n // j ≠ i} → Salt) × (Fin T → D),
        (bad.filter fun ω => ((fun j : {j : Fin n // j ≠ i} => ω.1 j.val), ω.2) = p).card
      ≤ ∑ _p : ({j : Fin n // j ≠ i} → Salt) × (Fin T → D), 2 * f := by
        refine Finset.sum_le_sum fun p _ => ?_
        set nonceOf : Salt → Fin n → Salt :=
          fun s j => if h : j = i then s else p.1 ⟨j, h⟩ with hnonceOf
        have hfib : ∀ ω ∈ bad.filter
            (fun ω : HidingSample n T Salt D =>
              ((fun j : {j : Fin n // j ≠ i} => ω.1 j.val), ω.2) = p),
            ω.1 = nonceOf (ω.1 i) ∧ ω.2 = p.2 := by
          intro ω hω
          obtain ⟨-, hp⟩ := Finset.mem_filter.mp hω
          refine ⟨?_, (congrArg Prod.snd hp)⟩
          funext j
          simp only [hnonceOf]
          by_cases hj : j = i
          · rw [dif_pos hj, hj]
          · rw [dif_neg hj]
            exact congrFun (congrArg Prod.fst hp) ⟨j, hj⟩
        refine le_trans (le_of_eq (Finset.card_image_of_injOn (f := fun ω => ω.1 i) ?_).symm) ?_
        · intro x hx y hy hxy
          have hxy' : x.1 i = y.1 i := hxy
          obtain ⟨hx1, hx2⟩ := hfib x hx
          obtain ⟨hy1, hy2⟩ := hfib y hy
          exact Prod.ext (by rw [hx1, hy1, hxy']) (by rw [hx2, hy2])
        · refine leafCatch_card_le C n hn (m₀ p.2) (m₁ p.2) p.2 hT i nonceOf ?_ ?_
            (hsalt₀ p.2) (hsalt₁ p.2) _ ?_ (tree p.1 p.2) ?_
          · intro s t j hj
            simp only [hnonceOf, dif_neg hj]
          · intro s
            simp only [hnonceOf, dif_pos rfl]
          · intro s hs
            obtain ⟨ω, hω, hωs⟩ := Finset.mem_image.mp hs
            obtain ⟨h1, h2⟩ := hfib ω hω
            rw [← hωs, ← h1, ← h2]
            exact hinj ω (Finset.mem_filter.mp hω).1
          · intro s hs
            obtain ⟨ω, hω, hωs⟩ := Finset.mem_image.mp hs
            obtain ⟨h1, h2⟩ := hfib ω hω
            have hp1 : (fun j : {j : Fin n // j ≠ i} => ω.1 j.val) = p.1 :=
              congrArg Prod.fst (Finset.mem_filter.mp hω).2
            rw [← hωs, ← h1, ← h2, ← hp1]
            exact hbad ω (Finset.mem_filter.mp hω).1
    _ = (Fintype.card Salt) ^ (n - 1) * (Fintype.card D) ^ T * (2 * f) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_prod,
          Fintype.card_fun, Fintype.card_fun]
        congr 2
        · congr 1
          rw [Fintype.card_subtype_compl]
          simp
        · simp

end RootHiding

/-! ## The commit-then-distinguish experiment

The faithful model: one lazy execution in which the honest commitment runs **first** — taking slots
`0 … 2n-2` — and the distinguisher then receives the root and queries the *same* tape, taking
genuinely fresh slots `2n-1, 2n, …`.  For opening hiding, off the collision events every honest
label is the tape entry at index `2n-1-v` (`commitLabels_eq_tape`), a function of the vertex alone,
so two commitments agreeing on the opened indices produce identical openings.  `lazyRun_bind`
decomposes the run into its two phases, and `lazyRun_congr_of_base` is what makes the distinguisher
unable to tell the two commitments' slot layouts apart. -/

section CommitThenDistinguish

variable {V : Type uView}

/-- Commitment first, then the distinguisher on the root it produced. -/
def hidingRun [DecidableEq Enc] (C : Codec Salt M D Enc) (n : ℕ) (nonce : Fin n → Salt)
    (m : Fin n → M) {f : ℕ} (dist : D → RandomOracle.Tree Enc D V f) :
    RandomOracle.Tree Enc D V (f + (2 * n - 1)) :=
  (commitPass C n nonce m (2 * n - 1) fun _ => default).bind fun vals => dist (vals 1)

/-- The root the commitment hands the distinguisher is the tape at slot `2n-2`. -/
theorem hidingRun_root [DecidableEq Enc] (C : Codec Salt M D Enc) (n : ℕ) (hn : 0 < n)
    (nonce : Fin n → Salt) (m : Fin n → M) {T : ℕ} (answers : Fin T → D)
    (hinj : commitInputsInjective C n nonce m (commitOracle C n nonce m answers))
    (hT : 2 * n - 2 < T) :
    (RandomOracle.lazyRun answers default
      (commitPass C n nonce m (2 * n - 1) fun _ => default) []).1 1 = answers ⟨2 * n - 2, hT⟩ := by
  have hrun := RandomOracle.lazyRun_eq_run answers default
    (commitPass C n nonce m (2 * n - 1) fun _ => default) []
    (commitOracle C n nonce m answers) fun _ => rfl
  have h1 : (RandomOracle.lazyRun answers default
        (commitPass C n nonce m (2 * n - 1) fun _ => default) []).1 =
      ((commitPass C n nonce m (2 * n - 1) fun _ => default).run
        (commitOracle C n nonce m answers)).1 := by
    rw [hrun]
  have hinvinit : ∀ v, 2 * n - 1 < v →
      (fun _ => (default : D)) v =
        commitLabels (C.withOracle (commitOracle C n nonce m answers)) n nonce m v :=
    fun v hv => (commitLabels_of_ge (S := C.withOracle (commitOracle C n nonce m answers))
      n nonce m v (by omega)).symm
  rw [h1, commitPass_run C n nonce m (commitOracle C n nonce m answers) (2 * n - 1) _
    hinvinit 1 (by omega)]
  exact commitPass_root_eq_tape C n hn nonce m answers hinj hT

/-- **Root hiding against a distinguisher with genuine oracle access.**  Two commitments of different
messages give the same view, provided neither commitment's own inputs collide and the distinguisher
queries neither commitment's inputs. The distinguisher runs inside the lazy
execution, so its queries take fresh slots. -/
theorem rootHiding_lazyView_eq [DecidableEq Enc] (C : Codec Salt M D Enc) (n : ℕ) (hn : 0 < n)
    (nonce : Fin n → Salt) (m₀ m₁ : Fin n → M) {T : ℕ} (answers : Fin T → D)
    {f : ℕ} (dist : D → RandomOracle.Tree Enc D V f) (hT : 2 * n - 2 < T)
    (hinj₀ : commitInputsInjective C n nonce m₀ (commitOracle C n nonce m₀ answers))
    (hinj₁ : commitInputsInjective C n nonce m₁ (commitOracle C n nonce m₁ answers))
    (hmiss : ∀ qa ∈ (RandomOracle.lazyRun answers default (dist (answers ⟨2 * n - 2, hT⟩))
        (commitSeen C n nonce m₀ answers)).2.2,
      qa.1 ∉ commitSeen C n nonce m₀ answers ∧ qa.1 ∉ commitSeen C n nonce m₁ answers) :
    (RandomOracle.lazyRun answers default (hidingRun C n nonce m₀ dist) []).1 =
      (RandomOracle.lazyRun answers default (hidingRun C n nonce m₁ dist) []).1 := by
  classical
  rw [hidingRun, hidingRun, RandomOracle.lazyRun_bind, RandomOracle.lazyRun_bind]
  dsimp only
  rw [hidingRun_root C n hn nonce m₀ answers hinj₀ hT,
    hidingRun_root C n hn nonce m₁ answers hinj₁ hT]
  have hlen : (commitSeen C n nonce m₀ answers).length =
      (commitSeen C n nonce m₁ answers).length := by
    rw [commitSeen_length C n hn nonce m₀ answers hinj₀,
      commitSeen_length C n hn nonce m₁ answers hinj₁]
  have hcongr := RandomOracle.lazyRun_congr_of_base answers default
    (commitSeen C n nonce m₀ answers) (commitSeen C n nonce m₁ answers) hlen
    (dist (answers ⟨2 * n - 2, hT⟩)) [] (by simpa [commitSeen] using hmiss)
  simpa [commitSeen] using hcongr.1

/-- Commitment first, then the distinguisher on the *whole* view — root and opening. -/
def openingHidingRun [DecidableEq Enc] (C : Codec Salt M D Enc) (n : ℕ) (I : Finset (Fin n))
    (nonce : Fin n → Salt) (m : Fin n → M) {f : ℕ}
    (dist : OpeningView n I Salt D → RandomOracle.Tree Enc D V f) :
    RandomOracle.Tree Enc D V (f + (2 * n - 1)) :=
  (commitPass C n nonce m (2 * n - 1) fun _ => default).bind fun vals =>
    dist { rt := vals 1
           proof := { nonce := fun i => nonce i.val
                      frontierValue := fun v => vals v.val } }

/-- The view the commitment hands the distinguisher is built from fixed tape slots: the root at
`2n-2` and each frontier digest at `2n-1-v`. -/
theorem openingHidingRun_view [DecidableEq Enc] (C : Codec Salt M D Enc) (n : ℕ) (hn : 0 < n)
    (I : Finset (Fin n)) (nonce : Fin n → Salt) (m : Fin n → M) {T : ℕ} (answers : Fin T → D)
    (hinj : commitInputsInjective C n nonce m (commitOracle C n nonce m answers))
    (hT : 2 * n - 2 < T) (hTn : 2 * n - 1 ≤ T) :
    (⟨(RandomOracle.lazyRun answers default
          (commitPass C n nonce m (2 * n - 1) fun _ => default) []).1 1,
        { nonce := fun i => nonce i.val
          frontierValue := fun v =>
            (RandomOracle.lazyRun answers default
              (commitPass C n nonce m (2 * n - 1) fun _ => default) []).1 v.val }⟩ :
        OpeningView n I Salt D) =
      ⟨answers ⟨2 * n - 2, hT⟩,
        { nonce := fun i => nonce i.val
          frontierValue := fun v => answers ⟨2 * n - 1 - v.val, by
            have := Heap.mem_frontier_iff.mp v.property
            rw [Heap.mem_nodes] at this
            omega⟩ }⟩ := by
  have hrun := RandomOracle.lazyRun_eq_run answers default
    (commitPass C n nonce m (2 * n - 1) fun _ => default) []
    (commitOracle C n nonce m answers) fun _ => rfl
  have h1 : (RandomOracle.lazyRun answers default
        (commitPass C n nonce m (2 * n - 1) fun _ => default) []).1 =
      ((commitPass C n nonce m (2 * n - 1) fun _ => default).run
        (commitOracle C n nonce m answers)).1 := by
    rw [hrun]
  have hinvinit : ∀ v, 2 * n - 1 < v →
      (fun _ => (default : D)) v =
        commitLabels (C.withOracle (commitOracle C n nonce m answers)) n nonce m v :=
    fun v hv => (commitLabels_of_ge (S := C.withOracle (commitOracle C n nonce m answers))
      n nonce m v (by omega)).symm
  have hvals : ∀ v, 0 < v →
      (RandomOracle.lazyRun answers default
        (commitPass C n nonce m (2 * n - 1) fun _ => default) []).1 v =
        commitLabels (C.withOracle (commitOracle C n nonce m answers)) n nonce m v := by
    intro v hv
    rw [h1]
    exact commitPass_run C n nonce m (commitOracle C n nonce m answers) (2 * n - 1) _
      hinvinit v hv
  refine congrArg₂ OpeningView.mk ?_ ?_
  · rw [hvals 1 (by omega)]
    exact commitPass_root_eq_tape C n hn nonce m answers hinj hT
  · refine congrArg₂ Opening.mk rfl ?_
    funext v
    have hv := Heap.mem_frontier_iff.mp v.property
    rw [Heap.mem_nodes] at hv
    rw [hvals v.val (by omega)]
    exact commitLabels_eq_tape C n hn nonce m answers hinj v.val (by omega) (by omega) (by omega)

/-- **Opening hiding, with the honest bad event.**  Asking the distinguisher to avoid *every*
commitment input is the wrong hypothesis for opening hiding: the opening hands
over the opened nonces and the frontier digests, so a distinguisher can reconstruct an opened leaf's
input — and the whole opened path's node inputs — and query them on purpose.  Bounding *that* is
hopeless, and it does not need bounding: at those inputs the two commitments agree, so the runs stay in
lockstep anyway.

What must be avoided is only an input on which the two commitments *differ*: a leaf encoding at a
coordinate where the messages differ.  With `m₀` and `m₁` agreeing on the opened set, those are the
**unopened** leaves, whose nonces the opening never reveals — so this is a nonce-guessing event, and
there is no digest-guessing term for opening hiding at all. -/
theorem openingHiding_lazyView_eq_off_diff [DecidableEq Enc] (C : Codec Salt M D Enc) (n : ℕ)
    (hn : 0 < n) (I : Finset (Fin n)) (nonce : Fin n → Salt) (m₀ m₁ : Fin n → M) {T : ℕ}
    (answers : Fin T → D) {f : ℕ}
    (dist : OpeningView n I Salt D → RandomOracle.Tree Enc D V f)
    (hT : 2 * n - 2 < T) (hTn : 2 * n - 1 ≤ T)
    (hinj₀ : commitInputsInjective C n nonce m₀ (commitOracle C n nonce m₀ answers))
    (hinj₁ : commitInputsInjective C n nonce m₁ (commitOracle C n nonce m₁ answers))
    (E : Finset (Fin n)) (hagree : ∀ i : Fin n, i ∉ E → m₀ i = m₁ i)
    (hmiss : ∀ qa ∈ (RandomOracle.lazyRun answers default
        (dist ⟨answers ⟨2 * n - 2, hT⟩,
          { nonce := fun i => nonce i.val
            frontierValue := fun v => answers ⟨2 * n - 1 - v.val, by
              have := Heap.mem_frontier_iff.mp v.property
              rw [Heap.mem_nodes] at this
              omega⟩ }⟩)
        (commitSeen C n nonce m₀ answers)).2.2,
      ∀ i ∈ E, qa.1 ≠ C.leafEnc (nonce i, m₀ i) ∧ qa.1 ≠ C.leafEnc (nonce i, m₁ i)) :
    (RandomOracle.lazyRun answers default (openingHidingRun C n I nonce m₀ dist) []).1 =
      (RandomOracle.lazyRun answers default (openingHidingRun C n I nonce m₁ dist) []).1 := by
  classical
  rw [openingHidingRun, openingHidingRun, RandomOracle.lazyRun_bind,
    RandomOracle.lazyRun_bind]
  dsimp only
  rw [openingHidingRun_view C n hn I nonce m₀ answers hinj₀ hT hTn,
    openingHidingRun_view C n hn I nonce m₁ answers hinj₁ hT hTn]
  have hlen : (commitSeen C n nonce m₀ answers).length =
      (commitSeen C n nonce m₁ answers).length := by
    rw [commitSeen_length C n hn nonce m₀ answers hinj₀,
      commitSeen_length C n hn nonce m₁ answers hinj₁]
  have hcompat := RandomOracle.lazyRun_congr_of_base_compat answers default
    (commitSeen C n nonce m₀ answers) (commitSeen C n nonce m₁ answers) hlen _ []
    (by
      simpa [commitSeen] using fun qa hqa =>
        commitSeen_baseCompat C n hn nonce nonce m₀ m₁ answers hinj₀ hinj₁ hT E
          (fun i hi => ⟨rfl, hagree i hi⟩) qa.1 (hmiss qa hqa))
  simpa [commitSeen] using hcompat.1

end CommitThenDistinguish

/-! ## A message-free simulator, and the nonce-guessing count -/

/-- **The hiding simulator needs no message.**  It reads the tape at the fixed slots — the root at
`2n-2`, frontier digest `v` at `2n-1-v` — and the opened nonces, which the opening reveals anyway.
SPEC.md §9.2's simulator is given `I` and `m[I]`; this one is given no message at all. -/
def simulateViewFromTape (n : ℕ) (I : Finset (Fin n)) (nonce : Fin n → Salt) {T : ℕ}
    (answers : Fin T → D) (hT : 2 * n - 2 < T) : OpeningView n I Salt D where
  rt := answers ⟨2 * n - 2, hT⟩
  proof :=
    { nonce := fun i => nonce i.val
      frontierValue := fun v => answers ⟨2 * n - 1 - v.val, by
        have := Heap.mem_frontier_iff.mp v.property
        rw [Heap.mem_nodes] at this
        omega⟩ }

omit [Inhabited D] in
/-- One leaf's nonce is guessed by at most a `|G|/|Salt|` fraction of nonce schedules, by
injectivity of the leaf encoding in its salt. -/
theorem nonceGuess_leaf_card_le [Fintype Salt] [DecidableEq Salt] [DecidableEq Enc]
    (C : Codec Salt M D Enc) (n : ℕ) (m : Fin n → M) (i : Fin n)
    (hsalt : Function.Injective (fun s : Salt => C.leafEnc (s, m i)))
    (G : Finset Enc) :
    (Finset.univ.filter fun nonce : Fin n → Salt =>
        C.leafEnc (nonce i, m i) ∈ G).card ≤
      G.card * (Fintype.card Salt) ^ (n - 1) := by
  classical
  have hmaps : ∀ nonce ∈ Finset.univ.filter
      (fun nonce : Fin n → Salt => C.leafEnc (nonce i, m i) ∈ G),
      (nonce i, fun j : {j : Fin n // j ≠ i} => nonce j.val) ∈
        (Finset.univ.filter fun s : Salt => C.leafEnc (s, m i) ∈ G) ×ˢ
          (Finset.univ : Finset ({j : Fin n // j ≠ i} → Salt)) := by
    intro nonce hnonce
    obtain ⟨-, hin⟩ := Finset.mem_filter.mp hnonce
    exact Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hin⟩, Finset.mem_univ _⟩
  have hinj : Set.InjOn
      (fun nonce : Fin n → Salt => (nonce i, fun j : {j : Fin n // j ≠ i} => nonce j.val))
      (Finset.univ.filter fun nonce : Fin n → Salt => C.leafEnc (nonce i, m i) ∈ G) := by
    intro a _ b _ hab
    funext j
    by_cases hj : j = i
    · rw [hj]
      exact congrArg Prod.fst hab
    · exact congrFun (congrArg Prod.snd hab) ⟨j, hj⟩
  calc (Finset.univ.filter fun nonce : Fin n → Salt =>
          C.leafEnc (nonce i, m i) ∈ G).card
      ≤ ((Finset.univ.filter fun s : Salt => C.leafEnc (s, m i) ∈ G) ×ˢ
          (Finset.univ : Finset ({j : Fin n // j ≠ i} → Salt))).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ = (Finset.univ.filter fun s : Salt => C.leafEnc (s, m i) ∈ G).card *
          (Fintype.card Salt) ^ (n - 1) := by
        rw [Finset.card_product, Finset.card_univ, Fintype.card_fun]
        congr 2
        rw [Fintype.card_subtype_compl]
        simp
    _ ≤ G.card * (Fintype.card Salt) ^ (n - 1) := by
        refine Nat.mul_le_mul_right _ ?_
        refine Finset.card_le_card_of_injOn (fun s => C.leafEnc (s, m i)) ?_ ?_
        · intro s hs
          exact (Finset.mem_filter.mp hs).2
        · intro a _ b _ hab
          exact hsalt hab

omit [Inhabited D] in
/-- **The nonce-guessing count.**  A guess set of size `|G|` hits some leaf's nonce on at most an
`n·|G| / |Salt|` fraction of nonce schedules.

`G` must not depend on the nonces — otherwise the bound is meaningless, since an adaptive guesser
could always include the right value.  In the commit-then-distinguish experiment that independence is
supplied by `RandomOracle.lazyRun_congr_of_base`: off the bad event the distinguisher's execution, and
so its query set, is the same under any two nonce schedules whose commitments have equally many
slots. -/
theorem nonceGuess_card_le [Fintype Salt] [DecidableEq Salt] [DecidableEq Enc]
    (C : Codec Salt M D Enc) (n : ℕ) (m : Fin n → M)
    (hsalt : ∀ i : Fin n, Function.Injective (fun s : Salt => C.leafEnc (s, m i)))
    (G : Finset Enc) :
    (Finset.univ.filter fun nonce : Fin n → Salt =>
        ∃ i : Fin n, C.leafEnc (nonce i, m i) ∈ G).card ≤
      n * (G.card * (Fintype.card Salt) ^ (n - 1)) := by
  classical
  calc (Finset.univ.filter fun nonce : Fin n → Salt =>
          ∃ i : Fin n, C.leafEnc (nonce i, m i) ∈ G).card
      ≤ ∑ i : Fin n, (Finset.univ.filter fun nonce : Fin n → Salt =>
          C.leafEnc (nonce i, m i) ∈ G).card := by
        have heq : (Finset.univ.filter fun nonce : Fin n → Salt =>
              ∃ i : Fin n, C.leafEnc (nonce i, m i) ∈ G) =
            (Finset.univ : Finset (Fin n)).biUnion fun i =>
              Finset.univ.filter fun nonce : Fin n → Salt =>
                C.leafEnc (nonce i, m i) ∈ G := by
          ext nonce
          simp
        rw [heq]
        exact Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin n, G.card * (Fintype.card Salt) ^ (n - 1) :=
        Finset.sum_le_sum fun i _ => nonceGuess_leaf_card_le C n m i (hsalt i) G
    _ = n * (G.card * (Fintype.card Salt) ^ (n - 1)) := by simp

/-! ### The splice: a `CountingClose` statement with no leftover hypotheses

The view-equality theorems carry their side conditions as hypotheses.  Here they are packaged into a
*defined* bad set, so the conclusion is a single closeness statement in the normalized
`RandomOracle.CountingClose` form, with the coupling proved. -/

section Splice

variable {V : Type uView}

/-- The distinguisher's view of an honest commitment to `m`. -/
noncomputable def hidingView [DecidableEq Enc] (C : Codec Salt M D Enc) (n : ℕ) {T f : ℕ}
    (m : (Fin T → D) → Fin n → M) (dist : D → RandomOracle.Tree Enc D V f)
    (ω : HidingSample n T Salt D) : V :=
  (RandomOracle.lazyRun ω.2 default (hidingRun C n ω.1 (m ω.2) dist) []).1

/-- The bad set: either commitment's inputs collide, or the distinguisher queries a commitment
input.  Both disjuncts are the events the counting sections bound. -/
noncomputable def hidingBad [DecidableEq Enc] [Fintype Salt] [DecidableEq Salt] [Fintype D]
    [DecidableEq D] (C : Codec Salt M D Enc) (n : ℕ) {T f : ℕ}
    (m₀ m₁ : (Fin T → D) → Fin n → M)
    (dist : D → RandomOracle.Tree Enc D V f) (hT : 2 * n - 2 < T) :
    Finset (HidingSample n T Salt D) := by
  classical
  exact Finset.univ.filter fun ω =>
    ¬ commitInputsInjective C n ω.1 (m₀ ω.2) (commitOracle C n ω.1 (m₀ ω.2) ω.2) ∨
      ¬ commitInputsInjective C n ω.1 (m₁ ω.2) (commitOracle C n ω.1 (m₁ ω.2) ω.2) ∨
      ∃ qa ∈ (RandomOracle.lazyRun ω.2 default (dist (ω.2 ⟨2 * n - 2, hT⟩))
          (commitSeen C n ω.1 (m₀ ω.2) ω.2)).2.2,
        qa.1 ∈ commitSeen C n ω.1 (m₀ ω.2) ω.2 ∨ qa.1 ∈ commitSeen C n ω.1 (m₁ ω.2) ω.2

/-- Off the bad set the two views are equal. -/
theorem hidingView_eq_off_bad [DecidableEq Enc] [Fintype Salt] [DecidableEq Salt] [Fintype D]
    [DecidableEq D] (C : Codec Salt M D Enc) (n : ℕ) (hn : 0 < n) {T f : ℕ}
    (m₀ m₁ : (Fin T → D) → Fin n → M)
    (dist : D → RandomOracle.Tree Enc D V f) (hT : 2 * n - 2 < T)
    (ω : HidingSample n T Salt D) (hω : ω ∉ hidingBad C n m₀ m₁ dist hT) :
    hidingView C n m₀ dist ω = hidingView C n m₁ dist ω := by
  classical
  rw [hidingBad] at hω
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hω
  obtain ⟨h₀, h₁, hhit⟩ := hω
  refine rootHiding_lazyView_eq C n hn ω.1 (m₀ ω.2) (m₁ ω.2) ω.2 dist hT
    (not_not.mp h₀) (not_not.mp h₁) ?_
  intro qa hqa
  by_contra hc
  rw [not_and_or, not_not, not_not] at hc
  exact hhit ⟨qa, hqa, hc⟩

/-- **Root hiding as a closeness statement.**  The two views differ on at most `hidingBad` many
sample points. -/
theorem rootHiding_countingClose [DecidableEq Enc] [Fintype Salt] [DecidableEq Salt] [Fintype D]
    [DecidableEq D] [DecidableEq V] (C : Codec Salt M D Enc) (n : ℕ) (hn : 0 < n)
    (T : ℕ) {f : ℕ} (m₀ m₁ : (Fin T → D) → Fin n → M)
    (dist : D → RandomOracle.Tree Enc D V f)
    (hT : 2 * n - 2 < T) :
    RandomOracle.CountingClose (hidingBad C n m₀ m₁ dist hT).card
      (hidingView (T := T) C n m₀ dist) (hidingView (T := T) C n m₁ dist) :=
  RandomOracle.CountingClose.of_certificate
    { bad := hidingBad C n m₀ m₁ dist hT
      bad_card := le_refl _
      agrees := fun ω hω => hidingView_eq_off_bad C n hn m₀ m₁ dist hT ω hω }

end Splice

/-! ### Costing the node and cross collisions

Two internal vertices, or a leaf and an internal vertex, presenting the same input cannot be costed
by a direct birthday argument on labels: that would need the labels to sit at distinct slots, which
is what is being established.  `CommitCollision.lean` inducts downwards on a threshold instead, so
at the first repeat everything above is distinct and the coincidence is a leaf birthday collision,
a repeat between two of the commitment's own slots, or a leaf input hitting a tape-determined node
input.  `commitSlotPairCollision_card_le` counts the middle case and
`commitInjective_failure_card_le` sums all three. -/

omit [Inhabited D] in
/-- **The numerator the reduction would land in.**  The commitment occupies at most `2n-1` slots, so
"two of its slots carry the same digest" costs the sharp birthday term
`(2n-1)(2n-2)/2` in `|D|` — the same shape as the binding and extraction bounds. -/
theorem commitSlotPairCollision_card_le [Fintype D] [DecidableEq D] (n T : ℕ) :
    (Finset.filter (RandomOracle.PairCollision (D := D) T
        (RandomOracle.slotPairs T (2 * n - 1))) Finset.univ).card ≤
      (2 * n - 1) * (2 * n - 2) / 2 * (Fintype.card D) ^ (T - 1) := by
  refine le_trans (RandomOracle.answerTape_pairCollision_card_le T
    (RandomOracle.slotPairs T (2 * n - 1)) RandomOracle.slotPairs_distinct) ?_
  refine Nat.mul_le_mul_right _ (le_trans (RandomOracle.slotPairs_card_le T (2 * n - 1)) ?_)
  exact Nat.div_le_div_right (Nat.mul_le_mul_left _ (by omega))

/-! ### Costing the three commitment-collision events

`CommitCollision.lean` reduces the failure of `commitInputsInjective` — the hypothesis carried through
every statement in this file — to three events over the nonce/tape sample space.  Here each gets its
count, and they are summed into one numerator.

The `leafInputCollision` count is the `n²/|Salt|` birthday term: for a fixed ordered pair of leaves, injectivity of `leafEnc` in
the salt slot leaves at most one colliding nonce per assignment of the other `n-1`, so each of the at
most `n²` pairs costs a `1/|Salt|` fraction. -/

omit [Inhabited D] in
/-- One ordered pair of leaves collides on at most a `1/|Salt|` fraction of schedules. -/
theorem leafInputCollision_pair_card_le [Fintype Salt] [DecidableEq Salt] [DecidableEq Enc]
    (C : Codec Salt M D Enc) (n : ℕ) (m : Fin n → M) (i j : Fin n) (hij : i ≠ j)
    (hsalt : Function.Injective (fun s : Salt => C.leafEnc (s, m i))) :
    (Finset.univ.filter fun nonce : Fin n → Salt =>
        C.leafEnc (nonce i, m i) = C.leafEnc (nonce j, m j)).card ≤
      (Fintype.card Salt) ^ (n - 1) := by
  classical
  have hcard : Fintype.card {k : Fin n // k ≠ i} = n - 1 := by
    rw [Fintype.card_subtype_compl]; simp
  refine le_trans (Finset.card_le_card_of_injOn
    (fun nonce : Fin n → Salt => fun k : {k : Fin n // k ≠ i} => nonce k.val)
    (fun _ _ => Finset.mem_univ _) ?_) ?_
  · intro a ha b hb hab
    have hane : C.leafEnc (a i, m i) = C.leafEnc (a j, m j) := (Finset.mem_filter.mp ha).2
    have hbne : C.leafEnc (b i, m i) = C.leafEnc (b j, m j) := (Finset.mem_filter.mp hb).2
    have h2 : a j = b j := congrFun hab ⟨j, fun h => hij h.symm⟩
    funext k
    by_cases hk : k = i
    · subst hk
      exact hsalt (hane.trans (h2 ▸ hbne.symm))
    · exact congrFun hab ⟨k, hk⟩
  · rw [Finset.card_univ, Fintype.card_fun, hcard]

omit [Inhabited D] in
/-- **The leaf birthday count.**  At most `n²/|Salt|` of all nonce schedules make two honest leaf
inputs coincide. -/
theorem leafInputCollision_card_le [Fintype Salt] [DecidableEq Salt] [DecidableEq Enc]
    (C : Codec Salt M D Enc) (n : ℕ) (m : Fin n → M)
    (hsalt : ∀ i : Fin n, Function.Injective (fun s : Salt => C.leafEnc (s, m i))) :
    (Finset.univ.filter fun nonce : Fin n → Salt => leafInputCollision C n nonce m).card ≤
      n ^ 2 * (Fintype.card Salt) ^ (n - 1) := by
  classical
  set idx := Finset.univ.filter fun p : Fin n × Fin n => p.1 ≠ p.2 with hidx
  have hsub : (Finset.univ.filter fun nonce : Fin n → Salt => leafInputCollision C n nonce m) ⊆
      idx.biUnion fun p => Finset.univ.filter fun nonce : Fin n → Salt =>
        C.leafEnc (nonce p.1, m p.1) = C.leafEnc (nonce p.2, m p.2) := by
    intro nonce hnonce
    obtain ⟨i, j, hij, heq⟩ := (Finset.mem_filter.mp hnonce).2
    exact Finset.mem_biUnion.mpr ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩⟩
  calc (Finset.univ.filter fun nonce : Fin n → Salt => leafInputCollision C n nonce m).card
      ≤ (idx.biUnion fun p => Finset.univ.filter fun nonce : Fin n → Salt =>
          C.leafEnc (nonce p.1, m p.1) = C.leafEnc (nonce p.2, m p.2)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ p ∈ idx, (Finset.univ.filter fun nonce : Fin n → Salt =>
          C.leafEnc (nonce p.1, m p.1) = C.leafEnc (nonce p.2, m p.2)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ idx, (Fintype.card Salt) ^ (n - 1) :=
        Finset.sum_le_sum fun p hp => leafInputCollision_pair_card_le C n m p.1 p.2
          (Finset.mem_filter.mp hp).2 (hsalt p.1)
    _ = idx.card * (Fintype.card Salt) ^ (n - 1) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ n ^ 2 * (Fintype.card Salt) ^ (n - 1) := by
        refine Nat.mul_le_mul_right _ ?_
        calc idx.card ≤ (Finset.univ : Finset (Fin n × Fin n)).card := by
              rw [hidx]; exact Finset.card_filter_le _ _
          _ = n ^ 2 := by simp [Finset.card_univ, pow_two]

/-- **The cross event costs a nonce guess.**  Off the threshold injectivity the internal vertices'
inputs are functions of the tape alone, so `nodeInputs` is a legitimate — nonce-independent — guess
set of at most `n` targets, and the count is the same `n·|G|/|Salt|` as any other guess. -/
theorem nodeInputHit_card_le [Fintype Salt] [DecidableEq Salt] [DecidableEq Enc]
    (C : Codec Salt M D Enc) (n : ℕ) (m : Fin n → M) {T : ℕ} (answers : Fin T → D)
    (hsalt : ∀ i : Fin n, Function.Injective (fun s : Salt => C.leafEnc (s, m i))) :
    (Finset.univ.filter fun nonce : Fin n → Salt =>
        nodeInputHit C n nonce m answers).card ≤
      n ^ 2 * (Fintype.card Salt) ^ (n - 1) := by
  classical
  refine le_trans (le_trans (Finset.card_le_card ?_)
    (nonceGuess_card_le C n m hsalt (nodeInputs C n answers))) ?_
  · intro nonce hnonce
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hnonce ⊢
    exact hnonce
  · rw [pow_two, mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (nodeInputs_card_le C n answers))

/-! ### Summing over the joint sample space

The three events live on different halves of `HidingSample`: two are nonce events at a fixed tape,
one is a tape event at a fixed nonce.  Fibering the product over whichever half the predicate ignores
turns a per-fibre bound into a bound on the whole filter. -/

/-- A predicate bounded uniformly on every `β`-fibre is bounded by `|β|` times that. -/
theorem card_filter_prod_le_of_snd {α : Type*} {β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (P : α × β → Prop) [DecidablePred P] (c : ℕ)
    (h : ∀ b : β, (Finset.univ.filter fun a : α => P (a, b)).card ≤ c) :
    (Finset.univ.filter P).card ≤ Fintype.card β * c := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun ω : α × β => ω.2) (t := (Finset.univ : Finset β)) (fun _ _ => Finset.mem_univ _)]
  calc ∑ b : β, ((Finset.univ.filter P).filter fun ω : α × β => ω.2 = b).card
      ≤ ∑ _b : β, c := by
        refine Finset.sum_le_sum fun b _ => le_trans ?_ (h b)
        refine Finset.card_le_card_of_injOn (fun ω => ω.1) ?_ ?_
        · intro ω hω
          obtain ⟨hωP, hωb⟩ := Finset.mem_filter.mp hω
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          rw [← hωb]
          exact (Finset.mem_filter.mp hωP).2
        · intro x hx y hy hxy
          obtain ⟨-, hxb⟩ := Finset.mem_filter.mp hx
          obtain ⟨-, hyb⟩ := Finset.mem_filter.mp hy
          exact Prod.ext hxy (hxb.trans hyb.symm)
    _ = Fintype.card β * c := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- Fibre bound for an *arbitrary* subset of a product: if each `β`-fibre's `α`-projection lands in a
set of size at most `c`, the subset has at most `|β|·c` elements.  Stated for a subset rather than a
`filter` so that it applies to bad sets carried as hypotheses, where no decidable predicate is
available. -/
theorem card_le_of_fiber_snd {α : Type*} {β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (s : Finset (α × β)) (g : β → Finset α) (c : ℕ)
    (hmem : ∀ ω ∈ s, ω.1 ∈ g ω.2) (hg : ∀ b : β, (g b).card ≤ c) :
    s.card ≤ Fintype.card β * c := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun ω : α × β => ω.2) (t := (Finset.univ : Finset β)) (fun _ _ => Finset.mem_univ _)]
  calc ∑ b : β, (s.filter fun ω : α × β => ω.2 = b).card
      ≤ ∑ b : β, (g b).card := by
        refine Finset.sum_le_sum fun b _ => Finset.card_le_card_of_injOn (fun ω => ω.1) ?_ ?_
        · intro ω hω
          obtain ⟨hωs, hωb⟩ := Finset.mem_filter.mp hω
          rw [← hωb]
          exact hmem ω hωs
        · intro x hx y hy hxy
          obtain ⟨-, hxb⟩ := Finset.mem_filter.mp hx
          obtain ⟨-, hyb⟩ := Finset.mem_filter.mp hy
          exact Prod.ext hxy (hxb.trans hyb.symm)
    _ ≤ ∑ _b : β, c := Finset.sum_le_sum fun b _ => hg b
    _ = Fintype.card β * c := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- The subset form of `card_le_of_fiber_snd`, fibering the other way. -/
theorem card_le_of_fiber_fst {α : Type*} {β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (s : Finset (α × β)) (g : α → Finset β) (c : ℕ)
    (hmem : ∀ ω ∈ s, ω.2 ∈ g ω.1) (hg : ∀ a : α, (g a).card ≤ c) :
    s.card ≤ Fintype.card α * c := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun ω : α × β => ω.1) (t := (Finset.univ : Finset α)) (fun _ _ => Finset.mem_univ _)]
  calc ∑ a : α, (s.filter fun ω : α × β => ω.1 = a).card
      ≤ ∑ a : α, (g a).card := by
        refine Finset.sum_le_sum fun a _ => Finset.card_le_card_of_injOn (fun ω => ω.2) ?_ ?_
        · intro ω hω
          obtain ⟨hωs, hωa⟩ := Finset.mem_filter.mp hω
          rw [← hωa]
          exact hmem ω hωs
        · intro x hx y hy hxy
          obtain ⟨-, hxa⟩ := Finset.mem_filter.mp hx
          obtain ⟨-, hya⟩ := Finset.mem_filter.mp hy
          exact Prod.ext (hxa.trans hya.symm) hxy
    _ ≤ ∑ _a : α, c := Finset.sum_le_sum fun a _ => hg a
    _ = Fintype.card α * c := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- The mirror image: uniform on every `α`-fibre. -/
theorem card_filter_prod_le_of_fst {α : Type*} {β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (P : α × β → Prop) [DecidablePred P] (c : ℕ)
    (h : ∀ a : α, (Finset.univ.filter fun b : β => P (a, b)).card ≤ c) :
    (Finset.univ.filter P).card ≤ Fintype.card α * c := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun ω : α × β => ω.1) (t := (Finset.univ : Finset α)) (fun _ _ => Finset.mem_univ _)]
  calc ∑ a : α, ((Finset.univ.filter P).filter fun ω : α × β => ω.1 = a).card
      ≤ ∑ _a : α, c := by
        refine Finset.sum_le_sum fun a _ => le_trans ?_ (h a)
        refine Finset.card_le_card_of_injOn (fun ω => ω.2) ?_ ?_
        · intro ω hω
          obtain ⟨hωP, hωa⟩ := Finset.mem_filter.mp hω
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          rw [← hωa]
          exact (Finset.mem_filter.mp hωP).2
        · intro x hx y hy hxy
          obtain ⟨-, hxa⟩ := Finset.mem_filter.mp hx
          obtain ⟨-, hya⟩ := Finset.mem_filter.mp hy
          exact Prod.ext (hxa.trans hya.symm) hxy
    _ = Fintype.card α * c := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- **The commitment's slot layout, costed.**  The nonce/tape pairs on which the honest commitment's
inputs are *not* pairwise distinct — the hypothesis `commitInputsInjective` that every statement in
this file carries — number at most

    2·|D|^T·n²·|Salt|^(n-1)  +  |Salt|^n·(2n-1)(2n-2)/2·|D|^(T-1),

i.e. a `2n²/|Salt| + (2n)²/(2|D|)` fraction of the sample space.  Both terms are birthday terms in
the two independent halves of the sample space, and neither was available before the
first-collision induction: the events are stated in terms of the labels, and only the induction
makes the labels tape entries at known indices. -/
noncomputable def commitInjectiveFailure [Fintype Salt] [DecidableEq Salt] [Fintype D]
    [DecidableEq D] [DecidableEq Enc] (C : Codec Salt M D Enc) (n : ℕ) (T : ℕ)
    (m : (Fin T → D) → Fin n → M) : Finset (HidingSample n T Salt D) := by
  classical
  exact Finset.univ.filter fun ω =>
    ¬ commitInputsInjective C n ω.1 (m ω.2) (commitOracle C n ω.1 (m ω.2) ω.2)

theorem commitInjective_failure_card_le [Fintype Salt] [DecidableEq Salt] [Fintype D]
    [DecidableEq D] [DecidableEq Enc] (C : Codec Salt M D Enc) (n : ℕ) (hn : 0 < n)
    (T : ℕ) (m : (Fin T → D) → Fin n → M) (hT : 2 * n - 1 ≤ T) (hinjC : C.Inj)
    (hsalt : ∀ (tape : Fin T → D) (i : Fin n),
      Function.Injective (fun s : Salt => C.leafEnc (s, m tape i))) :
    (commitInjectiveFailure C n T m).card ≤
      2 * ((Fintype.card D) ^ T * (n ^ 2 * (Fintype.card Salt) ^ (n - 1))) +
        (Fintype.card Salt) ^ n *
          ((2 * n - 1) * (2 * n - 2) / 2 * (Fintype.card D) ^ (T - 1)) := by
  classical
  rw [commitInjectiveFailure]
  have hsub : (Finset.univ.filter fun ω : HidingSample n T Salt D =>
        ¬ commitInputsInjective C n ω.1 (m ω.2) (commitOracle C n ω.1 (m ω.2) ω.2)) ⊆
      (Finset.univ.filter fun ω : HidingSample n T Salt D =>
        leafInputCollision C n ω.1 (m ω.2)) ∪
      (Finset.univ.filter fun ω : HidingSample n T Salt D =>
        nodeInputHit C n ω.1 (m ω.2) ω.2) ∪
      (Finset.univ.filter fun ω : HidingSample n T Salt D =>
        RandomOracle.PairCollision T (RandomOracle.slotPairs T (2 * n - 1)) ω.2) := by
    intro ω hω
    have h := commitInputsInjective_failure_disj C n hn ω.1 (m ω.2) ω.2 hT hinjC
      (Finset.mem_filter.mp hω).2
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases h with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
    · exact Or.inl (Or.inr h)
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (le_trans (Finset.card_union_le _ _)
    (Nat.add_le_add_right (Finset.card_union_le _ _) _)) ?_
  have hleaf : (Finset.univ.filter fun ω : HidingSample n T Salt D =>
      leafInputCollision C n ω.1 (m ω.2)).card ≤
      (Fintype.card D) ^ T * (n ^ 2 * (Fintype.card Salt) ^ (n - 1)) := by
    refine le_trans (card_filter_prod_le_of_snd _ (n ^ 2 * (Fintype.card Salt) ^ (n - 1))
      fun tape => leafInputCollision_card_le C n (m tape) (hsalt tape)) ?_
    exact Nat.mul_le_mul_right _ (by rw [Fintype.card_fun]; simp)
  have hcross : (Finset.univ.filter fun ω : HidingSample n T Salt D =>
      nodeInputHit C n ω.1 (m ω.2) ω.2).card ≤
      (Fintype.card D) ^ T * (n ^ 2 * (Fintype.card Salt) ^ (n - 1)) := by
    refine le_trans (card_filter_prod_le_of_snd _ (n ^ 2 * (Fintype.card Salt) ^ (n - 1))
      fun tape => nodeInputHit_card_le C n (m tape) tape (hsalt tape)) ?_
    exact Nat.mul_le_mul_right _ (by rw [Fintype.card_fun]; simp)
  have hnode : (Finset.univ.filter fun ω : HidingSample n T Salt D =>
      RandomOracle.PairCollision T (RandomOracle.slotPairs T (2 * n - 1)) ω.2).card ≤
      (Fintype.card Salt) ^ n *
        ((2 * n - 1) * (2 * n - 2) / 2 * (Fintype.card D) ^ (T - 1)) := by
    refine le_trans (card_filter_prod_le_of_fst _
      ((2 * n - 1) * (2 * n - 2) / 2 * (Fintype.card D) ^ (T - 1))
      fun _ => commitSlotPairCollision_card_le n T) ?_
    exact Nat.mul_le_mul_right _ (by rw [Fintype.card_fun]; simp)
  omega

/-! ### The distinguisher's node-input hit

The last event: the distinguisher queries an *internal* vertex's input.  This is not a nonce event —
node inputs are tape-determined — so it is a **digest-guessing** event, and counting it needs the
distinguisher's query list to be independent of the very digests it has to guess.

`RandomOracle.lazyRun_shift_take_congr` supplies that independence in the only form available: up to
the first query that lands in the commitment's seen-list, the run coincides with a run from the *empty*
base against the tape shifted past slot `2n-2`.  `distQueries` is that run's query list, so it is a
function of the root slot and the slots from `2n-1` up alone — independent of every label the
commitment produced, and of the nonces too, which is why it also serves as the guess set for the leaf
term without any reference schedule.
-/

section NodeHit

variable {V : Type uView}

/-- The distinguisher's queries, replayed against the tape shifted past the commitment's slots.  By
construction this reads only the root slot `2n-2` and the slots from `2n-1` upwards. -/
noncomputable def distQueries [DecidableEq Enc] (n : ℕ) {T : ℕ} (answers : Fin T → D) {f : ℕ}
    (dist : D → RandomOracle.Tree Enc D V f) (hT : 2 * n - 2 < T) : List Enc :=
  (RandomOracle.lazyRun (RandomOracle.shiftTape (2 * n - 1) answers default) default
    (dist (answers ⟨2 * n - 2, hT⟩)) []).2.2.map Prod.fst

theorem distQueries_length_le [DecidableEq Enc] (n : ℕ) {T : ℕ} (answers : Fin T → D) {f : ℕ}
    (dist : D → RandomOracle.Tree Enc D V f) (hT : 2 * n - 2 < T) :
    (distQueries n answers dist hT).length ≤ f := by
  rw [distQueries, List.length_map]
  exact RandomOracle.lazyRun_trace_length_le _ _ _ _

/-- The distinguisher's queries read only the root slot and the slots above it. -/
theorem distQueries_congr_of_high [DecidableEq Enc] (n : ℕ) {T : ℕ} (a b : Fin T → D) {f : ℕ}
    (dist : D → RandomOracle.Tree Enc D V f) (hT : 2 * n - 2 < T)
    (hhigh : ∀ i : Fin T, 2 * n - 2 ≤ i.val → a i = b i) :
    distQueries n a dist hT = distQueries n b dist hT := by
  have hroot : a ⟨2 * n - 2, hT⟩ = b ⟨2 * n - 2, hT⟩ := hhigh _ le_rfl
  have hshift : RandomOracle.shiftTape (2 * n - 1) a default =
      RandomOracle.shiftTape (2 * n - 1) b default :=
    RandomOracle.shiftTape_congr (2 * n - 1) a b default fun i hi => hhigh i (by omega)
  rw [distQueries, distQueries, hroot, hshift]

/-- Internal vertex `c`'s node input, read off the tape.  Off the commitment's collision events this
is the honest one, by `commitLabels_eq_tape`. -/
def tapeNodeInput (C : Codec Salt M D Enc) (n : ℕ) {T : ℕ} (answers : Fin T → D) (c : ℕ) : Enc :=
  C.nodeEnc (RandomOracle.tapeAt answers default (2 * n - 1 - 2 * c),
    RandomOracle.tapeAt answers default (2 * n - 2 - 2 * c))

/-- The event indexed by (internal vertex, query index): the distinguisher's `k`-th query is vertex
`c`'s node input. -/
def nodeHitAt [DecidableEq Enc] (C : Codec Salt M D Enc) (n : ℕ) {T : ℕ} (answers : Fin T → D)
    {f : ℕ} (dist : D → RandomOracle.Tree Enc D V f) (hT : 2 * n - 2 < T) (ck : ℕ × ℕ) : Prop :=
  (distQueries n answers dist hT)[ck.2]? = some (tapeNodeInput C n answers ck.1)

noncomputable instance nodeHitAtDecidable [DecidableEq Enc] (C : Codec Salt M D Enc) (n : ℕ) {T : ℕ}
    {f : ℕ} (dist : D → RandomOracle.Tree Enc D V f) (hT : 2 * n - 2 < T) (ck : ℕ × ℕ) :
    DecidablePred fun answers : Fin T → D => nodeHitAt C n answers dist hT ck := by
  intro answers
  unfold nodeHitAt
  infer_instance

/-- The fixed family: the `n-1` internal vertices against the distinguisher's `f` query slots. -/
def nodeHitFamily (n f : ℕ) : Finset (ℕ × ℕ) := Finset.Ico 1 n ×ˢ Finset.range f

theorem nodeHitFamily_card (n f : ℕ) : (nodeHitFamily n f).card = (n - 1) * f := by
  rw [nodeHitFamily, Finset.card_product, Nat.card_Ico, Finset.card_range]

/-- The slot each event pins down: internal vertex `c`'s left child's, `2n-1-2c`.  Clamped so the
function is total; on the family itself the clamp is inactive (`nodeHitSlot_val`). -/
def nodeHitSlot (n T : ℕ) (hT : 2 * n - 2 < T) (ck : ℕ × ℕ) : Fin T :=
  ⟨min (2 * n - 1 - 2 * ck.1) (2 * n - 2), by omega⟩

theorem nodeHitSlot_val (n T : ℕ) (hT : 2 * n - 2 < T) (ck : ℕ × ℕ) (hc : 1 ≤ ck.1) :
    (nodeHitSlot n T hT ck).val = 2 * n - 1 - 2 * ck.1 := by
  simp only [nodeHitSlot]
  omega

/-- The second slot each event pins down: the right child's, `2n-2-2c`. -/
def nodeHitSlotR (n T : ℕ) (hT : 2 * n - 2 < T) (ck : ℕ × ℕ) : Fin T :=
  ⟨min (2 * n - 2 - 2 * ck.1) (2 * n - 2), by omega⟩

theorem nodeHitSlotR_val (n T : ℕ) (hT : 2 * n - 2 < T) (ck : ℕ × ℕ) :
    (nodeHitSlotR n T hT ck).val = 2 * n - 2 - 2 * ck.1 := by
  simp only [nodeHitSlotR]
  omega

/-- **The digest-guessing event.** -/
def nodeHit [DecidableEq Enc] (C : Codec Salt M D Enc) (n : ℕ) {T : ℕ} (answers : Fin T → D)
    {f : ℕ} (dist : D → RandomOracle.Tree Enc D V f) (hT : 2 * n - 2 < T) : Prop :=
  ∃ ck ∈ nodeHitFamily n f, nodeHitAt C n answers dist hT ck

/-- **The digest-guessing count.**  Each (vertex, query index) pair pins down *two* tape slots: the
query is fixed by the root slot and the slots above it, so injectivity of `nodeEnc` recovers both
children's labels from it — and both lie strictly below the root.  There are `(n-1)·f` pairs, so the
event costs `(n-1)·f / |D|²`: a node input is `2σ` bits the distinguisher has to guess, which is the
SNARGs book's `ζ_CM(σ, 0, 2σ, t)` per internal vertex.

Stated for an arbitrary set of tapes on which the event holds, which is what the composition needs and
what keeps the statement free of a decidability side condition. -/
theorem nodeHit_card_le [Fintype D] [DecidableEq D] [DecidableEq Enc] (C : Codec Salt M D Enc)
    (n : ℕ) {T : ℕ} {f : ℕ} (dist : D → RandomOracle.Tree Enc D V f) (hT : 2 * n - 2 < T)
    (hinjC : C.Inj) (bad : Finset (Fin T → D))
    (hbad : ∀ answers ∈ bad, nodeHit C n answers dist hT) :
    bad.card ≤ (n - 1) * f * (Fintype.card D) ^ (T - 2) := by
  classical
  refine le_trans (le_trans (Finset.card_le_card ?_)
    (RandomOracle.answerTape_determinedFamily₂_card_le T (nodeHitFamily n f) (nodeHitSlot n T hT)
      (nodeHitSlotR n T hT) ?_ (fun ck answers => nodeHitAt C n answers dist hT ck) ?_)) ?_
  · intro answers h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hbad answers h
  · intro ck hck heq
    rw [nodeHitFamily, Finset.mem_product, Finset.mem_Ico, Finset.mem_range] at hck
    have h := congrArg Fin.val heq
    rw [nodeHitSlot_val n T hT ck hck.1.1, nodeHitSlotR_val n T hT ck] at h
    omega
  · intro ck hck a b hoff hA hB
    rw [nodeHitFamily, Finset.mem_product, Finset.mem_Ico, Finset.mem_range] at hck
    obtain ⟨⟨hc1, hcn⟩, hkf⟩ := hck
    have hslotL : (nodeHitSlot n T hT ck).val = 2 * n - 1 - 2 * ck.1 :=
      nodeHitSlot_val n T hT ck hc1
    have hslotR : (nodeHitSlotR n T hT ck).val = 2 * n - 2 - 2 * ck.1 :=
      nodeHitSlotR_val n T hT ck
    have hQ : distQueries n a dist hT = distQueries n b dist hT := by
      refine distQueries_congr_of_high n a b dist hT fun i hi => hoff i ?_ ?_
      · intro hc; have := congrArg Fin.val hc; rw [hslotL] at this; omega
      · intro hc; have := congrArg Fin.val hc; rw [hslotR] at this; omega
    simp only [nodeHitAt] at hA hB
    rw [hQ] at hA
    have heq : tapeNodeInput C n a ck.1 = tapeNodeInput C n b ck.1 :=
      Option.some_inj.mp (hA.symm.trans hB)
    rw [tapeNodeInput, tapeNodeInput] at heq
    have hpair := hinjC.node heq
    have hfst := congrArg Prod.fst hpair
    have hsnd := congrArg Prod.snd hpair
    simp only at hfst hsnd
    have hltL : 2 * n - 1 - 2 * ck.1 < T := by omega
    have hltR : 2 * n - 2 - 2 * ck.1 < T := by omega
    rw [RandomOracle.tapeAt, dif_pos hltL, RandomOracle.tapeAt, dif_pos hltL] at hfst
    rw [RandomOracle.tapeAt, dif_pos hltR, RandomOracle.tapeAt, dif_pos hltR] at hsnd
    rw [show nodeHitSlot n T hT ck = ⟨2 * n - 1 - 2 * ck.1, hltL⟩ from Fin.ext hslotL,
      show nodeHitSlotR n T hT ck = ⟨2 * n - 2 - 2 * ck.1, hltR⟩ from Fin.ext hslotR]
    exact ⟨hfst, hsnd⟩
  · simp [nodeHitFamily_card]

/-- **Identifying the first hit inside `distQueries`.**  For any query property `P` that includes the
run's own base, the first query satisfying `P` is `distQueries`'s `k`-th, for some `k < f`.  Before that
query the run has read only slots at or above `2n-1`, which is exactly what
`RandomOracle.lazyRun_shift_take_congr` needs; the `take (N+1)` in that lemma is what puts the hitting
query itself inside the identified prefix.

The generality in `P` is what lets one run's trace be tested against a *different* commitment's inputs
— the two-message statement — while the base stays the first commitment's. -/
theorem distQueries_getElem_of_hit [DecidableEq Enc] (C : Codec Salt M D Enc) (n : ℕ) (hn : 0 < n)
    (nonce : Fin n → Salt) (m : Fin n → M) {T : ℕ} (answers : Fin T → D) {f : ℕ}
    (dist : D → RandomOracle.Tree Enc D V f) (hT : 2 * n - 2 < T)
    (hinj : commitInputsInjective C n nonce m (commitOracle C n nonce m answers))
    (P : Enc → Prop) (hPB : ∀ x ∈ commitSeen C n nonce m answers, P x)
    (hhit : ∃ qa ∈ (RandomOracle.lazyRun answers default (dist (answers ⟨2 * n - 2, hT⟩))
        (commitSeen C n nonce m answers)).2.2, P qa.1) :
    ∃ k, ∃ _ : k < (distQueries n answers dist hT).length,
      k < f ∧ P ((distQueries n answers dist hT)[k]) := by
  classical
  set B := commitSeen C n nonce m answers with hBdef
  set L := ((RandomOracle.lazyRun answers default (dist (answers ⟨2 * n - 2, hT⟩)) B).2.2.map
    Prod.fst) with hLdef
  have hex : ∃ k, ∃ _ : k < L.length, P L[k] := by
    obtain ⟨qa, hqa, hqaP⟩ := hhit
    obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp
      (show qa.1 ∈ L from List.mem_map.mpr ⟨qa, hqa, rfl⟩)
    exact ⟨k, hk, by rw [hget]; exact hqaP⟩
  obtain ⟨hklt, hkP⟩ := Nat.find_spec hex
  have havoid : ∀ x ∈ L.take (Nat.find hex), x ∉ B := by
    intro x hx
    obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hx
    rw [List.length_take] at hj
    have hjk : j < Nat.find hex := by omega
    have hjL : j < L.length := by omega
    have hxL : x = L[j] := by rw [← hget]; simp
    intro hc
    exact Nat.find_min hex hjk ⟨hjL, hxL ▸ hPB x hc⟩
  have hBlen : B.length = 2 * n - 1 := commitSeen_length C n hn nonce m answers hinj
  have hcongr : L.take (Nat.find hex + 1) =
      (distQueries n answers dist hT).take (Nat.find hex + 1) := by
    have hshift := RandomOracle.lazyRun_shift_take_congr answers default B
      (dist (answers ⟨2 * n - 2, hT⟩)) [] (Nat.find hex) (by simpa [hLdef] using havoid)
    rw [distQueries, ← hBlen]
    simpa [hLdef] using hshift
  have hdlen : Nat.find hex < (distQueries n answers dist hT).length := by
    have hl := congrArg List.length hcongr
    rw [List.length_take, List.length_take] at hl
    omega
  have hgetk : (distQueries n answers dist hT)[Nat.find hex] = L[Nat.find hex] := by
    have h1 : ((distQueries n answers dist hT).take (Nat.find hex + 1))[Nat.find hex]?
        = (L.take (Nat.find hex + 1))[Nat.find hex]? := by rw [hcongr]
    rw [List.getElem?_take, List.getElem?_take] at h1
    simp only [if_pos (Nat.lt_succ_self _)] at h1
    rw [List.getElem?_eq_getElem hdlen, List.getElem?_eq_getElem hklt] at h1
    exact Option.some_inj.mp h1
  exact ⟨Nat.find hex, hdlen, lt_of_lt_of_le hdlen (distQueries_length_le n answers dist hT),
    by rw [hgetk]; exact hkP⟩

/-- **Case analysis at an identified query.**  A commitment input is either a leaf encoding — a nonce
guess, witnessed inside the nonce-independent `distQueries` — or an internal vertex's node input.

The node case lands in `nodeHit`, which mentions no message: `commitLabels_eq_tape` makes the honest
labels tape entries at message-independent indices, so *both* commitments present the very same node
inputs.  That is what makes the two-message composition cost only one extra leaf term. -/
theorem leafHit_or_nodeHit_of_getElem [DecidableEq Enc] (C : Codec Salt M D Enc) (n : ℕ) (hn : 0 < n)
    (nonce : Fin n → Salt) (m : Fin n → M) {T : ℕ} (answers : Fin T → D) {f : ℕ}
    (dist : D → RandomOracle.Tree Enc D V f) (hT : 2 * n - 2 < T)
    (hinj : commitInputsInjective C n nonce m (commitOracle C n nonce m answers))
    (k : ℕ) (hk : k < (distQueries n answers dist hT).length) (hkf : k < f)
    (hmem : (distQueries n answers dist hT)[k] ∈ commitSeen C n nonce m answers) :
    (∃ i : Fin n, C.leafEnc (nonce i, m i) ∈ distQueries n answers dist hT) ∨
      nodeHit C n answers dist hT := by
  obtain ⟨v, hv0, hv1, hvx⟩ := mem_commitSeen_vertex C n nonce m answers _ hmem
  unfold commitInput at hvx
  split at hvx
  · rename_i hleaf
    left
    refine ⟨⟨v - n, by omega⟩, ?_⟩
    rw [Option.some_inj.mp hvx]
    exact List.getElem_mem hk
  · split at hvx
    · rename_i hint
      right
      refine ⟨(v, k), ?_, ?_⟩
      · rw [nodeHitFamily, Finset.mem_product, Finset.mem_Ico, Finset.mem_range]
        exact ⟨⟨by omega, hint.2⟩, hkf⟩
      · have h1 : commitLabels (C.withOracle (commitOracle C n nonce m answers)) n nonce m (2 * v) =
            RandomOracle.tapeAt answers default (2 * n - 1 - 2 * v) := by
          have hlt : 2 * n - 1 - 2 * v < T := by omega
          rw [commitLabels_eq_tape C n hn nonce m answers hinj (2 * v) (by omega) (by omega) hlt,
            RandomOracle.tapeAt, dif_pos hlt]
        have h2 : commitLabels (C.withOracle (commitOracle C n nonce m answers)) n nonce m
            (2 * v + 1) = RandomOracle.tapeAt answers default (2 * n - 2 - 2 * v) := by
          have hlt : 2 * n - 1 - (2 * v + 1) < T := by omega
          rw [commitLabels_eq_tape C n hn nonce m answers hinj (2 * v + 1) (by omega) (by omega) hlt,
            show (2 : ℕ) * n - 2 - 2 * v = 2 * n - 1 - (2 * v + 1) by omega,
            RandomOracle.tapeAt, dif_pos hlt]
        simp only [nodeHitAt, tapeNodeInput]
        rw [List.getElem?_eq_getElem hk, ← Option.some_inj.mp hvx, h1, h2]
    · exact absurd hvx (by simp)

/-- **Coverage, two messages.**  `hidingBad` lets the distinguisher hit *either* commitment's inputs
while its own base is the first one's, and this is that statement: the hit is a nonce guess against
`m₀`, a nonce guess against `m₁`, or a digest guess — the last being the *same* event either way.

The base stays `m₀`'s throughout; only the tested property widens, which is precisely the generality
`distQueries_getElem_of_hit` was stated with. -/
theorem leafHit_or_nodeHit_of_hit₂ [DecidableEq Enc] (C : Codec Salt M D Enc) (n : ℕ) (hn : 0 < n)
    (nonce : Fin n → Salt) (m₀ m₁ : Fin n → M) {T : ℕ} (answers : Fin T → D) {f : ℕ}
    (dist : D → RandomOracle.Tree Enc D V f) (hT : 2 * n - 2 < T)
    (hinj₀ : commitInputsInjective C n nonce m₀ (commitOracle C n nonce m₀ answers))
    (hinj₁ : commitInputsInjective C n nonce m₁ (commitOracle C n nonce m₁ answers))
    (hhit : ∃ qa ∈ (RandomOracle.lazyRun answers default (dist (answers ⟨2 * n - 2, hT⟩))
        (commitSeen C n nonce m₀ answers)).2.2,
      qa.1 ∈ commitSeen C n nonce m₀ answers ∨ qa.1 ∈ commitSeen C n nonce m₁ answers) :
    (∃ i : Fin n, C.leafEnc (nonce i, m₀ i) ∈ distQueries n answers dist hT) ∨
      (∃ i : Fin n, C.leafEnc (nonce i, m₁ i) ∈ distQueries n answers dist hT) ∨
      nodeHit C n answers dist hT := by
  obtain ⟨k, hk, hkf, hP⟩ := distQueries_getElem_of_hit C n hn nonce m₀ answers dist hT hinj₀
    (fun x => x ∈ commitSeen C n nonce m₀ answers ∨ x ∈ commitSeen C n nonce m₁ answers)
    (fun _ hx => Or.inl hx) hhit
  rcases hP with h | h
  · rcases leafHit_or_nodeHit_of_getElem C n hn nonce m₀ answers dist hT hinj₀ k hk hkf h with
      h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inr h')
  · rcases leafHit_or_nodeHit_of_getElem C n hn nonce m₁ answers dist hT hinj₁ k hk hkf h with
      h' | h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr h')

/-! ### Costing the hit

The leaf half and the node half live on opposite halves of the sample space — the leaf event is a nonce
event at a fixed tape, the node event a tape event at a fixed schedule — so each is fibred over the
half it ignores.  Both use `distQueries` as the guess set, and it earns that role twice over: being
independent of the nonces, it needs no reference schedule for the leaf term; being independent of the
labels, it makes the node term countable at all. -/

/-- The leaf half: nonce guessing against `distQueries`, summed over tapes. -/
theorem leafHit_prod_card_le [Fintype Salt] [DecidableEq Salt] [Fintype D] [DecidableEq D]
    [DecidableEq Enc] (C : Codec Salt M D Enc) (n : ℕ) {T : ℕ} (m : (Fin T → D) → Fin n → M)
    {f : ℕ} (dist : D → RandomOracle.Tree Enc D V f) (hT : 2 * n - 2 < T)
    (hsalt : ∀ (tape : Fin T → D) (i : Fin n),
      Function.Injective (fun s : Salt => C.leafEnc (s, m tape i)))
    (bad : Finset (HidingSample n T Salt D))
    (hbad : ∀ ω ∈ bad, ∃ i : Fin n, C.leafEnc (ω.1 i, m ω.2 i) ∈ distQueries n ω.2 dist hT) :
    bad.card ≤ (Fintype.card D) ^ T * (n * (f * (Fintype.card Salt) ^ (n - 1))) := by
  classical
  refine le_trans (card_le_of_fiber_snd _
    (fun tape => Finset.univ.filter fun nonce : Fin n → Salt =>
      ∃ i : Fin n, C.leafEnc (nonce i, m tape i) ∈ (distQueries n tape dist hT).toFinset)
    (n * (f * (Fintype.card Salt) ^ (n - 1))) ?_ ?_) ?_
  · intro ω hω
    obtain ⟨i, hi⟩ := hbad ω hω
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨i, List.mem_toFinset.mpr hi⟩⟩
  · intro tape
    refine le_trans (nonceGuess_card_le C n (m tape) (hsalt tape)
      (distQueries n tape dist hT).toFinset) ?_
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _
      (le_trans (List.toFinset_card_le _) (distQueries_length_le n tape dist hT)))
  · exact Nat.mul_le_mul_right _ (by rw [Fintype.card_fun]; simp)

/-- The node half: digest guessing, summed over nonce schedules. -/
theorem nodeHit_prod_card_le [Fintype Salt] [DecidableEq Salt] [Fintype D] [DecidableEq D]
    [DecidableEq Enc] (C : Codec Salt M D Enc) (n : ℕ) {T : ℕ} {f : ℕ}
    (dist : D → RandomOracle.Tree Enc D V f) (hT : 2 * n - 2 < T) (hinjC : C.Inj)
    (bad : Finset (HidingSample n T Salt D))
    (hbad : ∀ ω ∈ bad, nodeHit C n ω.2 dist hT) :
    bad.card ≤ (Fintype.card Salt) ^ n * ((n - 1) * f * (Fintype.card D) ^ (T - 2)) := by
  classical
  refine le_trans (card_le_of_fiber_fst _
    (fun nonce => (bad.filter fun ω => ω.1 = nonce).image Prod.snd)
    ((n - 1) * f * (Fintype.card D) ^ (T - 2)) ?_ ?_) ?_
  · intro ω hω
    exact Finset.mem_image.mpr ⟨ω, Finset.mem_filter.mpr ⟨hω, rfl⟩, rfl⟩
  · intro nonce
    refine nodeHit_card_le C n dist hT hinjC _ ?_
    intro tape htape
    obtain ⟨ω, hω, hωt⟩ := Finset.mem_image.mp htape
    rw [← hωt]
    exact hbad ω (Finset.mem_filter.mp hω).1
  · exact Nat.mul_le_mul_right _ (by rw [Fintype.card_fun]; simp)

/-- **The distinguisher's hit, costed (two messages).**  The shape `hidingBad` actually needs: the run's
base is `m₀`'s commitment but the hit may land in either commitment's inputs.  The cost is one extra
*leaf* term and nothing else — the node term is shared, because the two commitments present the same
node inputs. -/
theorem distinguisherHit₂_card_le [Fintype Salt] [DecidableEq Salt] [Fintype D] [DecidableEq D]
    [DecidableEq Enc] (C : Codec Salt M D Enc) (n : ℕ) (hn : 0 < n) {T : ℕ}
    (m₀ m₁ : (Fin T → D) → Fin n → M)
    {f : ℕ} (dist : D → RandomOracle.Tree Enc D V f) (hT : 2 * n - 2 < T)
    (hinjC : C.Inj)
    (hsalt₀ : ∀ (tape : Fin T → D) (i : Fin n),
      Function.Injective (fun s : Salt => C.leafEnc (s, m₀ tape i)))
    (hsalt₁ : ∀ (tape : Fin T → D) (i : Fin n),
      Function.Injective (fun s : Salt => C.leafEnc (s, m₁ tape i)))
    (bad : Finset (HidingSample n T Salt D))
    (hinj₀ : ∀ ω ∈ bad,
      commitInputsInjective C n ω.1 (m₀ ω.2) (commitOracle C n ω.1 (m₀ ω.2) ω.2))
    (hinj₁ : ∀ ω ∈ bad,
      commitInputsInjective C n ω.1 (m₁ ω.2) (commitOracle C n ω.1 (m₁ ω.2) ω.2))
    (hbad : ∀ ω ∈ bad, ∃ qa ∈ (RandomOracle.lazyRun ω.2 default (dist (ω.2 ⟨2 * n - 2, hT⟩))
        (commitSeen C n ω.1 (m₀ ω.2) ω.2)).2.2,
      qa.1 ∈ commitSeen C n ω.1 (m₀ ω.2) ω.2 ∨ qa.1 ∈ commitSeen C n ω.1 (m₁ ω.2) ω.2) :
    bad.card ≤ 2 * ((Fintype.card D) ^ T * (n * (f * (Fintype.card Salt) ^ (n - 1)))) +
      (Fintype.card Salt) ^ n * ((n - 1) * f * (Fintype.card D) ^ (T - 2)) := by
  classical
  have hcover : bad ⊆
      ((bad.filter fun ω =>
          ∃ i : Fin n, C.leafEnc (ω.1 i, m₀ ω.2 i) ∈ distQueries n ω.2 dist hT) ∪
        (bad.filter fun ω =>
          ∃ i : Fin n, C.leafEnc (ω.1 i, m₁ ω.2 i) ∈ distQueries n ω.2 dist hT)) ∪
      (bad.filter fun ω => nodeHit C n ω.2 dist hT) := by
    intro ω hω
    rcases leafHit_or_nodeHit_of_hit₂ C n hn ω.1 (m₀ ω.2) (m₁ ω.2) ω.2 dist hT
      (hinj₀ ω hω) (hinj₁ ω hω)
      (hbad ω hω) with h | h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hω, h⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hω, h⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hω, h⟩)
  have h₀ := leafHit_prod_card_le C n m₀ dist hT hsalt₀
    (bad.filter fun ω => ∃ i : Fin n, C.leafEnc (ω.1 i, m₀ ω.2 i) ∈ distQueries n ω.2 dist hT)
    fun ω hω => (Finset.mem_filter.mp hω).2
  have h₁ := leafHit_prod_card_le C n m₁ dist hT hsalt₁
    (bad.filter fun ω => ∃ i : Fin n, C.leafEnc (ω.1 i, m₁ ω.2 i) ∈ distQueries n ω.2 dist hT)
    fun ω hω => (Finset.mem_filter.mp hω).2
  have h₂ := nodeHit_prod_card_le C n dist hT hinjC
    (bad.filter fun ω => nodeHit C n ω.2 dist hT)
    fun ω hω => (Finset.mem_filter.mp hω).2
  refine le_trans (le_trans (Finset.card_le_card hcover)
    (le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right (Finset.card_union_le _ _) _))) ?_
  omega

/-! ### The closed numerator

Everything above assembles into a single number.  `hidingBad`'s three disjuncts are the two
commitments' input-distinctness failures and the distinguisher's hit; the first two are counted by
`commitInjective_failure_card_le`, the third by `distinguisherHit₂_card_le` — which needs the
commitments to be collision-free, so the hit part is taken *conjoined* with that, the standard
identical-until-bad split. -/

/-- The closed root-hiding numerator over the `|Salt|^n · |D|^T` sample points: two
commitment-collision terms and one distinguisher-hit term. -/
def hidingNumerator (saltCard digestCard n f T : ℕ) : ℕ :=
  2 * (2 * (digestCard ^ T * (n ^ 2 * saltCard ^ (n - 1))) +
      saltCard ^ n * ((2 * n - 1) * (2 * n - 2) / 2 * digestCard ^ (T - 1))) +
    (2 * (digestCard ^ T * (n * (f * saltCard ^ (n - 1)))) +
      saltCard ^ n * ((n - 1) * f * digestCard ^ (T - 2)))

/-- **The numerator, normalized.**  Collecting the `|Salt|` terms, the `|D|` terms and the `|D|²`
term.  Over the `|Salt|^n · |D|^T` sample points this reads as

    (4n² + 2n·f)/|Salt|  +  (2n-1)(2n-2)/|D|  +  (n-1)·f/|D|²

with the `/2` of the sharp birthday count absorbed by the two commitments.  The last term is the
distinguisher guessing a whole node input — both children's labels. -/
theorem hidingNumerator_eq (saltCard digestCard n f T : ℕ) (hn : 0 < n) :
    hidingNumerator saltCard digestCard n f T =
      (4 * n ^ 2 + 2 * n * f) * (saltCard ^ (n - 1) * digestCard ^ T) +
        (2 * n - 1) * (2 * n - 2) * (saltCard ^ n * digestCard ^ (T - 1)) +
        (n - 1) * f * (saltCard ^ n * digestCard ^ (T - 2)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [hidingNumerator]
  have h1 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  have h2 : 2 * (k + 1) - 2 = 2 * k := by omega
  have h3 : (2 * k + 1) * (2 * k) / 2 = (2 * k + 1) * k := by
    rw [show (2 * k + 1) * (2 * k) = (2 * k + 1) * k * 2 by ring, Nat.mul_div_cancel _ (by omega)]
  rw [h1, h2, h3]
  simp only [Nat.add_sub_cancel]
  ring

/-- **The hiding bad set is bounded by a closed expression.** -/
theorem hidingBad_card_le [Fintype Salt] [DecidableEq Salt] [Fintype D] [DecidableEq D]
    [DecidableEq Enc] (C : Codec Salt M D Enc) (n : ℕ) (hn : 0 < n) {T : ℕ}
    (m₀ m₁ : (Fin T → D) → Fin n → M)
    {f : ℕ} (dist : D → RandomOracle.Tree Enc D V f) (hT : 2 * n - 2 < T)
    (hinjC : C.Inj)
    (hsalt₀ : ∀ (tape : Fin T → D) (i : Fin n),
      Function.Injective (fun s : Salt => C.leafEnc (s, m₀ tape i)))
    (hsalt₁ : ∀ (tape : Fin T → D) (i : Fin n),
      Function.Injective (fun s : Salt => C.leafEnc (s, m₁ tape i))) :
    (hidingBad C n m₀ m₁ dist hT).card ≤
      hidingNumerator (Fintype.card Salt) (Fintype.card D) n f T := by
  classical
  have hcover : hidingBad C n m₀ m₁ dist hT ⊆
      ((Finset.univ.filter fun ω : HidingSample n T Salt D =>
          ¬ commitInputsInjective C n ω.1 (m₀ ω.2) (commitOracle C n ω.1 (m₀ ω.2) ω.2)) ∪
        (Finset.univ.filter fun ω : HidingSample n T Salt D =>
          ¬ commitInputsInjective C n ω.1 (m₁ ω.2) (commitOracle C n ω.1 (m₁ ω.2) ω.2))) ∪
      (Finset.univ.filter fun ω : HidingSample n T Salt D =>
        (∃ qa ∈ (RandomOracle.lazyRun ω.2 default (dist (ω.2 ⟨2 * n - 2, hT⟩))
            (commitSeen C n ω.1 (m₀ ω.2) ω.2)).2.2,
          qa.1 ∈ commitSeen C n ω.1 (m₀ ω.2) ω.2 ∨ qa.1 ∈ commitSeen C n ω.1 (m₁ ω.2) ω.2) ∧
        commitInputsInjective C n ω.1 (m₀ ω.2) (commitOracle C n ω.1 (m₀ ω.2) ω.2) ∧
        commitInputsInjective C n ω.1 (m₁ ω.2) (commitOracle C n ω.1 (m₁ ω.2) ω.2)) := by
    rw [hidingBad]
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
    by_cases h0 : commitInputsInjective C n ω.1 (m₀ ω.2) (commitOracle C n ω.1 (m₀ ω.2) ω.2)
    · by_cases h1 : commitInputsInjective C n ω.1 (m₁ ω.2) (commitOracle C n ω.1 (m₁ ω.2) ω.2)
      · rcases hω with h | h | h
        · exact absurd h0 h
        · exact absurd h1 h
        · exact Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h, h0, h1⟩)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩))
  have h₀ : (Finset.univ.filter fun ω : HidingSample n T Salt D =>
      ¬ commitInputsInjective C n ω.1 (m₀ ω.2) (commitOracle C n ω.1 (m₀ ω.2) ω.2)).card ≤
      2 * ((Fintype.card D) ^ T * (n ^ 2 * (Fintype.card Salt) ^ (n - 1))) +
        (Fintype.card Salt) ^ n *
          ((2 * n - 1) * (2 * n - 2) / 2 * (Fintype.card D) ^ (T - 1)) := by
    refine le_trans (Finset.card_le_card ?_)
      (commitInjective_failure_card_le C n hn T m₀ (by omega) hinjC hsalt₀)
    intro ω hω
    rw [commitInjectiveFailure]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (Finset.mem_filter.mp hω).2
  have h₁ : (Finset.univ.filter fun ω : HidingSample n T Salt D =>
      ¬ commitInputsInjective C n ω.1 (m₁ ω.2) (commitOracle C n ω.1 (m₁ ω.2) ω.2)).card ≤
      2 * ((Fintype.card D) ^ T * (n ^ 2 * (Fintype.card Salt) ^ (n - 1))) +
        (Fintype.card Salt) ^ n *
          ((2 * n - 1) * (2 * n - 2) / 2 * (Fintype.card D) ^ (T - 1)) := by
    refine le_trans (Finset.card_le_card ?_)
      (commitInjective_failure_card_le C n hn T m₁ (by omega) hinjC hsalt₁)
    intro ω hω
    rw [commitInjectiveFailure]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (Finset.mem_filter.mp hω).2
  have h₂ := distinguisherHit₂_card_le C n hn m₀ m₁ dist hT hinjC hsalt₀ hsalt₁
    (Finset.univ.filter fun ω : HidingSample n T Salt D =>
      (∃ qa ∈ (RandomOracle.lazyRun ω.2 default (dist (ω.2 ⟨2 * n - 2, hT⟩))
          (commitSeen C n ω.1 (m₀ ω.2) ω.2)).2.2,
        qa.1 ∈ commitSeen C n ω.1 (m₀ ω.2) ω.2 ∨ qa.1 ∈ commitSeen C n ω.1 (m₁ ω.2) ω.2) ∧
      commitInputsInjective C n ω.1 (m₀ ω.2) (commitOracle C n ω.1 (m₀ ω.2) ω.2) ∧
      commitInputsInjective C n ω.1 (m₁ ω.2) (commitOracle C n ω.1 (m₁ ω.2) ω.2))
    (fun ω hω => (Finset.mem_filter.mp hω).2.2.1)
    (fun ω hω => (Finset.mem_filter.mp hω).2.2.2)
    (fun ω hω => (Finset.mem_filter.mp hω).2.1)
  refine le_trans (le_trans (Finset.card_le_card hcover)
    (le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right (Finset.card_union_le _ _) _))) ?_
  rw [hidingNumerator]
  omega

/-- **Root hiding, with a number.**  `rootHiding_countingClose` with `hidingBad.card` discharged: the
two views of two different messages disagree on at most `hidingNumerator` of the `|Salt|^n · |D|^T`
sample points, and every term in that numerator is proved here — no certificate, no assumed coupling,
no residual hypothesis beyond injective encodings and injectivity of `leafEnc` in the salt slot. -/
theorem rootHiding_countingClose_closed [Fintype Salt] [DecidableEq Salt] [Fintype D]
    [DecidableEq D] [DecidableEq V] [DecidableEq Enc] (C : Codec Salt M D Enc) (n : ℕ) (hn : 0 < n)
    (T : ℕ) {f : ℕ} (m₀ m₁ : (Fin T → D) → Fin n → M)
    (dist : D → RandomOracle.Tree Enc D V f)
    (hT : 2 * n - 2 < T) (hinjC : C.Inj)
    (hsalt₀ : ∀ (tape : Fin T → D) (i : Fin n),
      Function.Injective (fun s : Salt => C.leafEnc (s, m₀ tape i)))
    (hsalt₁ : ∀ (tape : Fin T → D) (i : Fin n),
      Function.Injective (fun s : Salt => C.leafEnc (s, m₁ tape i))) :
    RandomOracle.CountingClose (hidingNumerator (Fintype.card Salt) (Fintype.card D) n f T)
      (hidingView (T := T) C n m₀ dist) (hidingView (T := T) C n m₁ dist) :=
  le_trans (rootHiding_countingClose C n hn T m₀ m₁ dist hT)
    (hidingBad_card_le C n hn m₀ m₁ dist hT hinjC hsalt₀ hsalt₁)

end NodeHit

/-! ### The opening-hiding splice

Root hiding's numerator came from two commitment-collision terms plus a distinguisher-hit term with a
nonce-guessing and a digest-guessing half.  Opening hiding's has **no digest-guessing half**: the
distinguisher may query every node input it likes, since both commitments present the same ones.  What
is left is one nonce-guessing term per differing leaf. -/

section OpeningSplice

variable {V : Type uView}

/-- The view the opening-hiding distinguisher receives, read off the tape: the root at slot `2n-2`,
frontier digest `v` at slot `2n-1-v`, and the opened nonces. -/
def openingViewOf (n : ℕ) (I : Finset (Fin n)) (nonce : Fin n → Salt) {T : ℕ}
    (answers : Fin T → D) (hT : 2 * n - 2 < T) : OpeningView n I Salt D :=
  ⟨answers ⟨2 * n - 2, hT⟩,
    { nonce := fun i => nonce i.val
      frontierValue := fun v => answers ⟨2 * n - 1 - v.val, by
        have := Heap.mem_frontier_iff.mp v.property
        rw [Heap.mem_nodes] at this
        omega⟩ }⟩

/-- The distinguisher's view in the opening-hiding experiment.  The message may be chosen as a
function of the tape — i.e. adaptively, using earlier oracle answers. -/
noncomputable def openingHidingView [DecidableEq Enc] (C : Codec Salt M D Enc) (n : ℕ)
    (I : Finset (Fin n)) {T f : ℕ} (m : (Fin T → D) → Fin n → M)
    (dist : (Fin T → D) → OpeningView n I Salt D → RandomOracle.Tree Enc D V f)
    (ω : HidingSample n T Salt D) : V :=
  (RandomOracle.lazyRun ω.2 default (openingHidingRun C n I ω.1 (m ω.2) (dist ω.2)) []).1

/-- The bad set: either commitment's inputs collide, or the distinguisher queries an input on which the
two commitments **differ**.  Queries of shared inputs — every node input, and every opened leaf's — are
deliberately allowed.

`E` is a *fixed* set containing every coordinate where the two messages can differ.  Fixing it, rather
than reading it off the messages, is what lets the messages themselves depend on the tape. -/
noncomputable def openingHidingBad [DecidableEq Enc] [Fintype Salt] [DecidableEq Salt] [Fintype D]
    [DecidableEq D] (C : Codec Salt M D Enc) (n : ℕ) (I : Finset (Fin n)) {T f : ℕ}
    (m₀ m₁ : (Fin T → D) → Fin n → M) (E : Finset (Fin n))
    (dist : (Fin T → D) → OpeningView n I Salt D → RandomOracle.Tree Enc D V f)
    (hT : 2 * n - 2 < T) : Finset (HidingSample n T Salt D) := by
  classical
  exact Finset.univ.filter fun ω =>
    ¬ commitInputsInjective C n ω.1 (m₀ ω.2) (commitOracle C n ω.1 (m₀ ω.2) ω.2) ∨
      ¬ commitInputsInjective C n ω.1 (m₁ ω.2) (commitOracle C n ω.1 (m₁ ω.2) ω.2) ∨
      ∃ qa ∈ (RandomOracle.lazyRun ω.2 default (dist ω.2 (openingViewOf n I ω.1 ω.2 hT))
          (commitSeen C n ω.1 (m₀ ω.2) ω.2)).2.2,
        ∃ i ∈ E,
          qa.1 = C.leafEnc (ω.1 i, m₀ ω.2 i) ∨ qa.1 = C.leafEnc (ω.1 i, m₁ ω.2 i)

/-- Off the bad set the two opening views are equal. -/
theorem openingHidingView_eq_off_bad [DecidableEq Enc] [Fintype Salt] [DecidableEq Salt] [Fintype D]
    [DecidableEq D] (C : Codec Salt M D Enc) (n : ℕ) (hn : 0 < n) (I : Finset (Fin n)) {T f : ℕ}
    (m₀ m₁ : (Fin T → D) → Fin n → M) (E : Finset (Fin n))
    (dist : (Fin T → D) → OpeningView n I Salt D → RandomOracle.Tree Enc D V f)
    (hT : 2 * n - 2 < T) (hTn : 2 * n - 1 ≤ T)
    (hE : ∀ (tape : Fin T → D) (i : Fin n), i ∉ E → m₀ tape i = m₁ tape i)
    (ω : HidingSample n T Salt D) (hω : ω ∉ openingHidingBad C n I m₀ m₁ E dist hT) :
    openingHidingView C n I m₀ dist ω = openingHidingView C n I m₁ dist ω := by
  classical
  rw [openingHidingBad] at hω
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hω
  obtain ⟨h₀, h₁, hhit⟩ := hω
  refine openingHiding_lazyView_eq_off_diff C n hn I ω.1 (m₀ ω.2) (m₁ ω.2) ω.2 (dist ω.2) hT hTn
    (not_not.mp h₀) (not_not.mp h₁) E (hE ω.2) ?_
  intro qa hqa i hi
  refine ⟨fun hc => hhit ⟨qa, hqa, i, hi, Or.inl hc⟩, fun hc => hhit ⟨qa, hqa, i, hi, Or.inr hc⟩⟩

/-- **Opening hiding as a closeness statement.** -/
theorem openingHiding_countingClose [DecidableEq Enc] [Fintype Salt] [DecidableEq Salt] [Fintype D]
    [DecidableEq D] [DecidableEq V] (C : Codec Salt M D Enc) (n : ℕ) (hn : 0 < n)
    (I : Finset (Fin n)) (T : ℕ) {f : ℕ} (m₀ m₁ : (Fin T → D) → Fin n → M) (E : Finset (Fin n))
    (dist : (Fin T → D) → OpeningView n I Salt D → RandomOracle.Tree Enc D V f)
    (hT : 2 * n - 2 < T) (hTn : 2 * n - 1 ≤ T)
    (hE : ∀ (tape : Fin T → D) (i : Fin n), i ∉ E → m₀ tape i = m₁ tape i) :
    RandomOracle.CountingClose (openingHidingBad C n I m₀ m₁ E dist hT).card
      (openingHidingView (T := T) C n I m₀ dist) (openingHidingView (T := T) C n I m₁ dist) :=
  RandomOracle.CountingClose.of_certificate
    { bad := openingHidingBad C n I m₀ m₁ E dist hT
      bad_card := le_refl _
      agrees := fun ω hω =>
        openingHidingView_eq_off_bad C n hn I m₀ m₁ E dist hT hTn hE ω hω }

/-- The closed opening-hiding numerator: two commitment-collision terms and one nonce-guessing term per
possibly-differing leaf.  No digest-guessing term — that is the structural difference from root
hiding. -/
def openingHidingNumerator (saltCard digestCard n f T d : ℕ) : ℕ :=
  2 * (2 * (digestCard ^ T * (n ^ 2 * saltCard ^ (n - 1))) +
      saltCard ^ n * ((2 * n - 1) * (2 * n - 2) / 2 * digestCard ^ (T - 1))) +
    d * (saltCard ^ (n - 1) * digestCard ^ T * (2 * f))

/-- **The opening-hiding bad set is bounded by a closed expression.**

The hit term is `leafCatch_prod_card_le` summed over `E`.  Its hypothesis — that the distinguisher's
execution is a function of (all other nonces, tape) — is exactly where `E ∩ I = ∅` is spent: the view
reveals the *opened* nonces, so only an unopened coordinate's nonce is absent from it. -/
theorem openingHidingBad_card_le [DecidableEq Enc] [Fintype Salt] [DecidableEq Salt] [Fintype D]
    [DecidableEq D] (C : Codec Salt M D Enc) (n : ℕ) (hn : 0 < n) (I : Finset (Fin n)) {T f : ℕ}
    (m₀ m₁ : (Fin T → D) → Fin n → M) (E : Finset (Fin n))
    (dist : (Fin T → D) → OpeningView n I Salt D → RandomOracle.Tree Enc D V f)
    (hT : 2 * n - 2 < T) (hinjC : C.Inj)
    (hEI : ∀ i ∈ E, i ∉ I)
    (hsalt₀ : ∀ (tape : Fin T → D) (i : Fin n),
      Function.Injective fun s : Salt => C.leafEnc (s, m₀ tape i))
    (hsalt₁ : ∀ (tape : Fin T → D) (i : Fin n),
      Function.Injective fun s : Salt => C.leafEnc (s, m₁ tape i)) :
    (openingHidingBad C n I m₀ m₁ E dist hT).card ≤
      openingHidingNumerator (Fintype.card Salt) (Fintype.card D) n f T E.card := by
  classical
  have hcover : openingHidingBad C n I m₀ m₁ E dist hT ⊆
      ((Finset.univ.filter fun ω : HidingSample n T Salt D =>
          ¬ commitInputsInjective C n ω.1 (m₀ ω.2) (commitOracle C n ω.1 (m₀ ω.2) ω.2)) ∪
        (Finset.univ.filter fun ω : HidingSample n T Salt D =>
          ¬ commitInputsInjective C n ω.1 (m₁ ω.2) (commitOracle C n ω.1 (m₁ ω.2) ω.2))) ∪
      E.biUnion fun i =>
        Finset.univ.filter fun ω : HidingSample n T Salt D =>
          commitInputsInjective C n ω.1 (m₀ ω.2) (commitOracle C n ω.1 (m₀ ω.2) ω.2) ∧
          (C.leafEnc (ω.1 i, m₀ ω.2 i) ∈ (RandomOracle.lazyRun ω.2 default
              (dist ω.2 (openingViewOf n I ω.1 ω.2 hT))
              (commitSeen C n ω.1 (m₀ ω.2) ω.2)).2.2.map Prod.fst ∨
            C.leafEnc (ω.1 i, m₁ ω.2 i) ∈ (RandomOracle.lazyRun ω.2 default
              (dist ω.2 (openingViewOf n I ω.1 ω.2 hT))
              (commitSeen C n ω.1 (m₀ ω.2) ω.2)).2.2.map Prod.fst) := by
    rw [openingHidingBad]
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
    by_cases h0 : commitInputsInjective C n ω.1 (m₀ ω.2) (commitOracle C n ω.1 (m₀ ω.2) ω.2)
    · rcases hω with h | h | ⟨qa, hqa, i, hi, hqi⟩
      · exact absurd h0 h
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
      · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, hi,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0, ?_⟩⟩)
        rcases hqi with hqi | hqi
        · exact Or.inl (List.mem_map.mpr ⟨qa, hqa, hqi⟩)
        · exact Or.inr (List.mem_map.mpr ⟨qa, hqa, hqi⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩))
  have hcol : ∀ m : (Fin T → D) → Fin n → M,
      (∀ (tape : Fin T → D) (i : Fin n),
        Function.Injective fun s : Salt => C.leafEnc (s, m tape i)) →
      (Finset.univ.filter fun ω : HidingSample n T Salt D =>
        ¬ commitInputsInjective C n ω.1 (m ω.2) (commitOracle C n ω.1 (m ω.2) ω.2)).card ≤
        2 * ((Fintype.card D) ^ T * (n ^ 2 * (Fintype.card Salt) ^ (n - 1))) +
          (Fintype.card Salt) ^ n *
            ((2 * n - 1) * (2 * n - 2) / 2 * (Fintype.card D) ^ (T - 1)) := by
    intro m hs
    refine le_trans (Finset.card_le_card ?_)
      (commitInjective_failure_card_le C n hn T m (by omega) hinjC hs)
    intro ω hω
    rw [commitInjectiveFailure]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (Finset.mem_filter.mp hω).2
  have hhitpart : ∀ i ∈ E,
      (Finset.univ.filter fun ω : HidingSample n T Salt D =>
        commitInputsInjective C n ω.1 (m₀ ω.2) (commitOracle C n ω.1 (m₀ ω.2) ω.2) ∧
        (C.leafEnc (ω.1 i, m₀ ω.2 i) ∈ (RandomOracle.lazyRun ω.2 default
            (dist ω.2 (openingViewOf n I ω.1 ω.2 hT))
            (commitSeen C n ω.1 (m₀ ω.2) ω.2)).2.2.map Prod.fst ∨
          C.leafEnc (ω.1 i, m₁ ω.2 i) ∈ (RandomOracle.lazyRun ω.2 default
            (dist ω.2 (openingViewOf n I ω.1 ω.2 hT))
            (commitSeen C n ω.1 (m₀ ω.2) ω.2)).2.2.map Prod.fst)).card ≤
      (Fintype.card Salt) ^ (n - 1) * (Fintype.card D) ^ T * (2 * f) := by
    intro i hi
    have hiI : i ∉ I := hEI i hi
    refine leafCatch_prod_card_le C n hn m₀ m₁ hT i
      (fun r tp => dist tp ⟨tp ⟨2 * n - 2, hT⟩,
        { nonce := fun i' => r ⟨i'.val, fun hc => hiI (hc ▸ i'.property)⟩
          frontierValue := fun v => tp ⟨2 * n - 1 - v.val, by
            have := Heap.mem_frontier_iff.mp v.property
            rw [Heap.mem_nodes] at this
            omega⟩ }⟩)
      (fun tape => hsalt₀ tape i) (fun tape => hsalt₁ tape i) _
      (fun ω hω => (Finset.mem_filter.mp hω).2.1) ?_
    intro ω hω
    exact (Finset.mem_filter.mp hω).2.2
  refine le_trans (Finset.card_le_card hcover) ?_
  refine le_trans (le_trans (Finset.card_union_le _ _)
    (Nat.add_le_add_right (Finset.card_union_le _ _) _)) ?_
  rw [openingHidingNumerator]
  refine Nat.add_le_add ?_ ?_
  · have hc0 := hcol m₀ hsalt₀
    have hc1 := hcol m₁ hsalt₁
    omega
  · refine le_trans Finset.card_biUnion_le ?_
    refine le_trans (Finset.sum_le_sum hhitpart) ?_
    rw [Finset.sum_const, smul_eq_mul]

/-- **Opening hiding, with a number, for adaptively chosen messages.**
`openingHiding_countingClose` with `openingHidingBad.card` discharged.  The fraction, over the
`|Salt|^n · |D|^T` sample points, is

    (4n² + 2·|E|·f)/|Salt|  +  (2n-1)(2n-2)/|D|

with a nonce-guessing term for each coordinate where the messages may differ, and **no**
digest-guessing term.  The messages may be chosen as functions of the tape — the counts are fibred
over it — provided the *set* `E` where they can differ is fixed and disjoint from the opened set. -/
theorem openingHiding_countingClose_closed [DecidableEq Enc] [Fintype Salt] [DecidableEq Salt]
    [Fintype D] [DecidableEq D] [DecidableEq V] (C : Codec Salt M D Enc) (n : ℕ) (hn : 0 < n)
    (I : Finset (Fin n)) (T : ℕ) {f : ℕ} (m₀ m₁ : (Fin T → D) → Fin n → M) (E : Finset (Fin n))
    (dist : (Fin T → D) → OpeningView n I Salt D → RandomOracle.Tree Enc D V f)
    (hT : 2 * n - 2 < T) (hTn : 2 * n - 1 ≤ T) (hinjC : C.Inj)
    (hEI : ∀ i ∈ E, i ∉ I)
    (hE : ∀ (tape : Fin T → D) (i : Fin n), i ∉ E → m₀ tape i = m₁ tape i)
    (hsalt₀ : ∀ (tape : Fin T → D) (i : Fin n),
      Function.Injective fun s : Salt => C.leafEnc (s, m₀ tape i))
    (hsalt₁ : ∀ (tape : Fin T → D) (i : Fin n),
      Function.Injective fun s : Salt => C.leafEnc (s, m₁ tape i)) :
    RandomOracle.CountingClose
      (openingHidingNumerator (Fintype.card Salt) (Fintype.card D) n f T E.card)
      (openingHidingView (T := T) C n I m₀ dist) (openingHidingView (T := T) C n I m₁ dist) :=
  le_trans (openingHiding_countingClose C n hn I T m₀ m₁ E dist hT hTn hE)
    (openingHidingBad_card_le C n hn I m₀ m₁ E dist hT hinjC hEI hsalt₀ hsalt₁)

end OpeningSplice

end MH

end Merkle
