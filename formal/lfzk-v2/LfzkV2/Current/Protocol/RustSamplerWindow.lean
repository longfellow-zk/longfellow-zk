import LfzkV2.Current.Protocol.RustSampler
import LfzkV2.Current.OracleWindow
import TranscriptV2.StrandVerifier

/-! How often the Rust reader aborts anywhere in a run.

A boundary reads its PRF stream `counter ↦ SHA (prf id parent counter)`. The
key `(id, parent)` of a reached boundary depends on earlier answers, so a
union over the boundaries a run reaches would be adaptive. The bound here is
not: it holds for every key at once. Over a uniform table of SHA answers at
every PRF input (`prfWindow`), the fraction of tables on which some role's
draws abort on some key's stream is at most the number of keys times one
stream's abort fraction (`allRead_abort_le`), and the answers outside the
window are arbitrary. For the deployed reader this is at most `2^-128`
(`sampled_abort_le`): then every boundary of every run samples. -/
noncomputable section
namespace LfzkV2.Current.Protocol.RustSampler
open Merkle.RandomOracle TranscriptV2
open scoped Classical

/-- The byte input of a PRF block, `Input.prf id parent counter`. -/
def prfKey : Word × Digest × Word ↪ Framing.Bytes where
  toFun key := (Strand.Input.prf key.1 key.2.1 key.2.2).encode
  inj' a b h := by
    have e := Strand.Input.encode_injective (a := .prf a.1 a.2.1 a.2.2) (b := .prf b.1 b.2.1 b.2.2)
      trivial trivial h
    simp only [Strand.Input.prf.injEq] at e
    exact Prod.ext e.1 (Prod.ext e.2.1 e.2.2)

/-- The keys, enumerated. -/
def keyIndex : Fin (2 ^ 64 * (256 ^ 32 * 2 ^ 64)) ≃ Word × Digest × Word :=
  finProdFinEquiv.symm.trans ((Equiv.refl _).prodCongr
    (finProdFinEquiv.symm.trans (finFunctionFinEquiv.symm.prodCongr (Equiv.refl _))))

/-- Every PRF block input. It is irreducible: unfolding the enumeration of
all `2^384` keys would only exhaust the elaborator. -/
@[irreducible] def prfWindow : Finset Framing.Bytes :=
  Finset.univ.map (keyIndex.toEmbedding.trans prfKey)

theorem prf_mem (id : Word) (parent : Digest) (counter : Word) :
    (Strand.Input.prf id parent counter).encode ∈ prfWindow := by
  unfold prfWindow
  have := Finset.mem_map_of_mem (keyIndex.toEmbedding.trans prfKey)
    (Finset.mem_univ (keyIndex.symm (id, parent, counter)))
  simpa [prfKey] using this

abbrev Table := {raw // raw ∈ prfWindow} → Digest

/-- The PRF stream of a key in a window table. -/
def prfStream (T : Table) (id : Word) (parent : Digest) : Word → Digest :=
  fun counter => T ⟨(Strand.Input.prf id parent counter).encode, prf_mem id parent counter⟩

theorem extend_stream (T : Table) (outside : Strand.Oracle) (id : Word) (parent : Digest) :
    (fun counter => OracleWindow.extend prfWindow T outside (Strand.Input.prf id parent counter).encode) =
      prfStream T id parent := by
  funext counter
  exact OracleWindow.extend_mem _ _ _ _ (prf_mem id parent counter)

theorem prfStream_injective (id : Word) (parent : Digest) :
    Function.Injective fun counter => (⟨(Strand.Input.prf id parent counter).encode, prf_mem id parent counter⟩ : {raw // raw ∈ prfWindow}) := by
  intro a b h
  have e := Strand.Input.encode_injective (a := .prf id parent a) (b := .prf id parent b) trivial trivial
    (congrArg Subtype.val h)
  cases e
  rfl

/-- A uniform table induces a uniform stream at every key. -/
theorem card_stream (id : Word) (parent : Digest) (P : (Word → Digest) → Prop) :
    Nat.card {T : Table // P (prfStream T id parent)} * Nat.card (Word → Digest) =
      Nat.card {H : Word → Digest // P H} * Nat.card Table := by
  let f := fun counter => (⟨(Strand.Input.prf id parent counter).encode, prf_mem id parent counter⟩ : {raw // raw ∈ prfWindow})
  let inside := Equiv.ofInjective f (prfStream_injective id parent)
  let p : {raw // raw ∈ prfWindow} → Prop := fun x => x ∈ Set.range f
  have restrict := card_restrict p (fun pre : {x // p x} → Digest => P fun counter => pre (inside counter))
  have total := card_restrict p (fun _ : {x // p x} → Digest => True)
  have same : Nat.card {pre : {x // p x} → Digest // P fun counter => pre (inside counter)} =
      Nat.card {H : Word → Digest // P H} :=
    Nat.card_congr ((inside.arrowCongr (Equiv.refl Digest)).symm.subtypeEquiv fun _ => Iff.rfl)
  have whole : Nat.card ({x // p x} → Digest) = Nat.card (Word → Digest) :=
    Nat.card_congr (inside.symm.arrowCongr (Equiv.refl Digest))
  simp only [Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial))] at total
  have lhs : Nat.card {T : Table // P (prfStream T id parent)} =
      Nat.card {T : Table // P fun counter => (fun x => T x) (inside counter)} := rfl
  rw [lhs, restrict, same, total, whole]
  ring

/-! ## Every key -/

variable {c : CertifiedProfile} {g : Geometry} {fields : Fields} {Advice B : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable {shared maskBits adviceBits : ℕ}
variable (S : Setup c g fields Advice B (shared := shared) (maskBits := maskBits) (adviceBits := adviceBits))
variable (degree : S.binary.degree = 128)

/-- Every role's draws read a value from every key's stream. -/
def AllRead (T : Table) : Prop :=
  ∀ (index : Fin g.roles.length) (id : Word) (parent : Digest),
    ((lazySampler (roleProg S degree index) rustBlocks rustBlocks_fits).run (prfStream T id parent)).1.isSome

/-- The union over keys: at most the number of keys times the worst stream. -/
theorem allRead_abort_le (ε : ℚ)
    (each : ∀ index : Fin g.roles.length,
      (Nat.card {H : Word → Digest //
        ((lazySampler (roleProg S degree index) rustBlocks rustBlocks_fits).run H).1 = none} : ℚ) /
        Nat.card (Word → Digest) ≤ ε) :
    (Nat.card {T : Table // ¬ AllRead S degree T} : ℚ) / Nat.card Table ≤
      g.roles.length * 2 ^ 64 * 2 ^ 256 * ε := by
  let Key := Fin g.roles.length × Word × Digest
  let bad : Key → Table → Prop := fun k T =>
    ((lazySampler (roleProg S degree k.1) rustBlocks rustBlocks_fits).run (prfStream T k.2.1 k.2.2)).1 = none
  have split : ∀ T, ¬ AllRead S degree T ↔ ∃ k, bad k T := by
    intro T
    simp only [AllRead, not_forall, Option.not_isSome_iff_eq_none, bad]
    exact ⟨fun ⟨i, d, p, h⟩ => ⟨(i, d, p), h⟩, fun ⟨k, h⟩ => ⟨k.1, k.2.1, k.2.2, h⟩⟩
  have union : Nat.card {T : Table // ¬ AllRead S degree T} ≤ ∑ k : Key, Nat.card {T : Table // bad k T} := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight split)]
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [show (Finset.univ.filter fun T => ∃ k, bad k T) =
        Finset.univ.biUnion fun k => Finset.univ.filter (bad k) by
      ext T; simp]
    exact Finset.card_biUnion_le
  have hpos : (0 : ℚ) < Nat.card Table := by exact_mod_cast Nat.card_pos
  have hpos' : (0 : ℚ) < Nat.card (Word → Digest) := by exact_mod_cast Nat.card_pos
  have term : ∀ k : Key, (Nat.card {T : Table // bad k T} : ℚ) / Nat.card Table ≤ ε := by
    intro k
    have e := card_stream k.2.1 k.2.2
      (fun H => ((lazySampler (roleProg S degree k.1) rustBlocks rustBlocks_fits).run H).1 = none)
    have e' : (Nat.card {T : Table // bad k T} : ℚ) / Nat.card Table =
        (Nat.card {H : Word → Digest //
          ((lazySampler (roleProg S degree k.1) rustBlocks rustBlocks_fits).run H).1 = none} : ℚ) /
          Nat.card (Word → Digest) := by
      rw [div_eq_div_iff hpos.ne' hpos'.ne']
      exact_mod_cast e
    rw [e']
    exact each k.1
  have keys : (Fintype.card Key : ℚ) = g.roles.length * 2 ^ 64 * 2 ^ 256 := by
    simp only [Key, Fintype.card_prod, Fintype.card_fin, Fintype.card_fun]
    push_cast
    ring
  calc (Nat.card {T : Table // ¬ AllRead S degree T} : ℚ) / Nat.card Table
      ≤ (∑ k : Key, (Nat.card {T : Table // bad k T} : ℚ)) / Nat.card Table := by
        apply div_le_div_of_nonneg_right _ hpos.le
        exact_mod_cast union
    _ = ∑ k : Key, (Nat.card {T : Table // bad k T} : ℚ) / Nat.card Table := by
        rw [Finset.sum_div]
    _ ≤ ∑ _k : Key, ε := Finset.sum_le_sum fun k _ => term k
    _ = g.roles.length * 2 ^ 64 * 2 ^ 256 * ε := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, keys]

/-- When every key's stream is read, every boundary of every run samples,
whatever the history assigns to its node and whatever SHA answers outside
the PRF window. -/
theorem sampled_of_allRead (T : Table) (all : AllRead S degree T) (outside : Strand.Oracle)
    (history : S.Point → Strand.History) (index : Fin g.roles.length) (past block) :
    StrandVerifier.sampled history (sampler S degree).data.execution.sample
      (OracleWindow.extend prfWindow T outside) (.round index past block) := by
  unfold StrandVerifier.sampled
  simp only [Sampling.sampler, StrandSampling.read, Tree.run_map, Option.isSome_map]
  rw [extend_stream]
  exact all index _ _

/-- The deployed bound: when every boundary's reject-free width is at most
`2^40` bytes and there are fewer than `2^64` boundaries, the reader samples
at every boundary of every run except on at most `2^-128` of all tables of
PRF answers, for every assignment of the other SHA answers. -/
theorem sampled_abort_le (queries : c.t ≤ c.n) (small : setupWidth S ≤ 2 ^ 40)
    (fits : g.roles.length < 2 ^ 64) (outside : Strand.Oracle) (history : S.Point → Strand.History) :
    (Nat.card {T : Table // ¬ ∀ (index : Fin g.roles.length) past block,
        StrandVerifier.sampled history (sampler S degree).data.execution.sample
          (OracleWindow.extend prfWindow T outside) (.round index past block)} : ℚ) / Nat.card Table ≤
      1 / 2 ^ 128 := by
  have sub : Nat.card {T : Table // ¬ ∀ (index : Fin g.roles.length) past block,
        StrandVerifier.sampled history (sampler S degree).data.execution.sample
          (OracleWindow.extend prfWindow T outside) (.round index past block)} ≤
      Nat.card {T : Table // ¬ AllRead S degree T} :=
    Nat.card_mono (Set.toFinite _) fun T bad all => bad (sampled_of_allRead S degree T all outside history)
  have each : ∀ index : Fin g.roles.length,
      (Nat.card {H : Word → Digest //
        ((lazySampler (roleProg S degree index) rustBlocks rustBlocks_fits).run H).1 = none} : ℚ) /
        Nat.card (Word → Digest) ≤ 2 ^ 40 * (1 / 2) ^ (2 ^ 20) := by
    intro index
    have hw := (roleProg_width_le S degree queries index).trans small
    have bound := roleProg_abort_le S degree queries index (2 ^ 20) (by
        unfold rustBlocks
        calc 2 ^ 20 * _ ≤ 2 ^ 20 * 2 ^ 40 := Nat.mul_le_mul_left _ hw
          _ ≤ (2 ^ 64 - 1) * 32 := by norm_num)
    refine bound.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    exact_mod_cast hw
  have total := allRead_abort_le S degree _ each
  have hpos : (0 : ℚ) < Nat.card Table := by exact_mod_cast Nat.card_pos
  have hL : (g.roles.length : ℚ) ≤ 2 ^ 64 := by exact_mod_cast fits.le
  have hp : (1 / 2 : ℚ) ^ (2 ^ 20) ≤ (1 / 2) ^ 552 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by norm_num)
  calc (Nat.card {T : Table // ¬ ∀ (index : Fin g.roles.length) past block,
        StrandVerifier.sampled history (sampler S degree).data.execution.sample
          (OracleWindow.extend prfWindow T outside) (.round index past block)} : ℚ) / Nat.card Table
      ≤ (Nat.card {T : Table // ¬ AllRead S degree T} : ℚ) / Nat.card Table := by
        apply div_le_div_of_nonneg_right _ hpos.le
        exact_mod_cast sub
    _ ≤ g.roles.length * 2 ^ 64 * 2 ^ 256 * (2 ^ 40 * (1 / 2) ^ (2 ^ 20)) := total
    _ ≤ 2 ^ 64 * 2 ^ 64 * 2 ^ 256 * (2 ^ 40 * (1 / 2) ^ 552) := by gcongr
    _ = 1 / 2 ^ 128 := by
        have e : (2 : ℚ) ^ 64 * 2 ^ 64 * 2 ^ 256 * 2 ^ 40 = 2 ^ 424 := by
          rw [← pow_add, ← pow_add, ← pow_add]
        rw [← mul_assoc, e, show (552 : ℕ) = 424 + 128 from rfl, pow_add, ← mul_assoc, ← mul_pow]
        norm_num

end LfzkV2.Current.Protocol.RustSampler
