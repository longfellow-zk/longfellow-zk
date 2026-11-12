import LfzkV2.Current.RuntimeCover

/-! The public schedule fixes the role and charge at each actual replay
boundary. Fragment count and proof values cannot add protocol roles. -/
noncomputable section
namespace LfzkV2.Current.RuntimeRoles
open Application ApplicationSetup ApplicationViews ApplicationOracle RecursivePolygero SumcheckV2
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice Base Key C B Salt : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B] [Fintype C]
variable {shared maskBits adviceBits k s n t : ℕ}
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable {binary : BinaryPublic B shared maskBits adviceBits}
variable {prime : PrimePublic N shared}
variable {P : FieldBackend B k s n t} {R : FieldBackend N k s n t}
variable {cfg : RuntimeVerifier.Public (g := g) binary prime P R (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key) (C := C) (Salt := Salt)}
variable {Oracle : Type}
variable {S : RuntimeCover.Source (g := g) (fields := fields) (Advice := Advice) (Base := Base)
  (Key := Key) (C := C) binary prime (Oracle := Oracle)} {LB LN : ℕ}
variable (q : RuntimeCover.QuerySetup binary prime P R cfg S LB LN)
local notation "Pair" => Selection.Pair B N binary.Original prime.Original
local notation "Point" => RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key)
local notation "Output" => RuntimeVerifier.Output (g := g) (fields := fields) (Advice := Advice)
local notation "e" => RuntimeVerifier.encoding binary prime P R cfg
local notation "Generator" => cfg.generator^Adapter.Mdoc.generatorExponent

omit [Fintype C] in
theorem point_role (proof : Output) (H : Point → Digest × C) (i : Fin g.roles.length) :
    (((e).chain cfg.initialLink).point proof H i.val).role = some (g.roles.get i) :=
  Input.role_eq_of_rank _ i (((e).chain cfg.initialLink).point_rank proof H i.isLt.le)

omit [Fintype C] in
theorem point_role_of_get (proof : Output) (H : Point → Digest × C)
    (i : ℕ) (hi : i < g.roles.length) (role : Role)
    (hget : g.roles[i]? = some role) :
    (((e).chain cfg.initialLink).point proof H i).role = some role := by
  have hrole : g.roles.get ⟨i,hi⟩ = role :=
    Option.some.inj ((List.getElem?_eq_getElem (l := g.roles) hi).symm.trans hget)
  simpa only [hrole] using point_role (cfg := cfg) proof H ⟨i,hi⟩

theorem adapter_get (g : Geometry) (i : Fin 3) :
    g.roles[ApplicationPrefix.rowBatchingIndex g+i.val]? =
      some (([Role.rowBatching,.rescaling,.conversion]).get i) := by
  let leading := [.fingerprint] ++ g.prime.roles .prime
  have hlength : leading.length = ApplicationPrefix.rowBatchingIndex g := by
    simp only [leading,List.length_append,List.length_singleton,ApplicationPrefix.rowBatchingIndex,
      Geometry.primeStart]
  have hroles : g.roles = leading ++
      ([.rowBatching,.rescaling,.conversion] ++ g.binary.roles .binary ++
        (if g.packingDegree = 1 then [] else [.packing]) ++ [.batching,.opening]) := by
    rw [g.roles_eq]
    simp only [leading,List.append_assoc]
  rw [hroles,List.getElem?_append_right (by rw [hlength]; omega),hlength,Nat.add_sub_cancel_left]
  simp only [List.append_assoc]
  rw [List.getElem?_append_left (show i.val < ([Role.rowBatching,.rescaling,.conversion]).length from i.isLt)]
  exact List.getElem?_eq_getElem i.isLt

theorem packing_get (g : Geometry) (nontrivial : g.packingDegree ≠ 1) :
    g.roles[ApplicationPrefix.packingIndex g]? = some .packing := by
  let leading := [.fingerprint] ++ g.prime.roles .prime ++ [.rowBatching,.rescaling,.conversion] ++
    g.binary.roles .binary
  have hlength : leading.length = ApplicationPrefix.packingIndex g := by
    simp only [leading,List.length_append,List.length_cons,List.length_nil,
      ApplicationPrefix.packingIndex,Geometry.binaryStart]
    omega
  have hroles : g.roles = leading ++ [.packing,.batching,.opening] := by
    rw [g.roles_eq]
    simp only [leading,if_neg nontrivial,List.append_assoc]
    rfl
  rw [hroles,List.getElem?_append_right (by rw [hlength]),hlength,Nat.sub_self]
  rfl

theorem stage_side (side : Side) (index : ℕ) (stage : Stage) (entries : List Entry)
    (role : Role) (h : role ∈ stage.roles side index entries) : frontendSide role = some side := by
  simp only [Stage.roles,List.mem_append,List.mem_cons,List.not_mem_nil,
    or_false,List.mem_map] at h
  rcases h with (rfl | ⟨i,_,rfl⟩) | rfl | rfl <;> rfl

theorem frontend_side (side : Side) (frontend : Frontend) (role : Role)
    (h : role ∈ frontend.roles side) : frontendSide role = some side := by
  by_cases empty : frontend.stages.isEmpty
  · simp only [Frontend.roles,empty,↓reduceIte,List.mem_singleton] at h
    subst role
    rfl
  · simp only [Frontend.roles,empty,Bool.false_eq_true,↓reduceIte,List.mem_flatMap] at h
    obtain ⟨i,_,h⟩ := h
    exact stage_side side i.val (frontend.stages.get i) _ role h

theorem roleCharge_frontend (role : Role) (side : Side) (point : Point)
    (H : Point → Digest × C) (answer : Digest × C) (h : frontendSide role = some side) :
    q.roleCharge role point H answer =
      match side with
      | .binary => frontendCharge S q.binaryRead point H answer
      | .prime => frontendCharge S q.primeRead point H answer := by
  cases role with
  | inputAssertions participant entries => cases participant <;> cases h <;> rfl
  | assertions participant stage entries fragments => cases participant <;> cases h <;> rfl
  | sumcheck participant stage round => cases participant <;> cases h <;> rfl
  | terminal participant stage => cases participant <;> cases h <;> rfl
  | combine participant stage entries => cases participant <;> cases h <;> rfl
  | fingerprint | rowBatching | rescaling | conversion | packing | batching | opening => cases h

theorem prime_single (proof : Output) (H : Point → Digest × C) (query : ℕ)
    (hquery : query < FrontendReplay.slots prime.circuit) (answer : Digest × C) :
    q.single (((e).chain cfg.initialLink).point proof H (g.primeStart+query)) H answer =
      frontendCharge S q.primeRead
        (((e).chain cfg.initialLink).point proof H (g.primeStart+query)) H answer := by
  have hslots : FrontendReplay.slots prime.circuit = (g.prime.roles .prime).length := by
    rw [q.primeShape.slots_eq_roles_length .prime,q.primeGeometry]
  let i : Fin (g.prime.roles .prime).length := ⟨query,by omega⟩
  have hr := point_role (cfg := cfg) proof H (g.primeIndex i)
  change (((e).chain cfg.initialLink).point proof H (g.primeStart+query)).role =
    some (g.roles.get (g.primeIndex i)) at hr
  rw [g.prime_role_get i] at hr
  have hs := frontend_side .prime g.prime _ (List.get_mem _ i)
  unfold RuntimeCover.QuerySetup.single
  rw [hr]
  exact roleCharge_frontend q _ .prime _ H answer hs

theorem binary_single (proof : Output) (H : Point → Digest × C)
    (packet : AdapterPacket binary prime C) (query : ℕ)
    (hquery : query < FrontendReplay.slots (packet.setup Generator).circuit) (answer : Digest × C) :
    q.single (((e).chain cfg.initialLink).point proof H (g.binaryStart+query)) H answer =
      frontendCharge S q.binaryRead
        (((e).chain cfg.initialLink).point proof H (g.binaryStart+query)) H answer := by
  have hslots : FrontendReplay.slots (packet.setup Generator).circuit = (g.binary.roles .binary).length := by
    rw [(q.binaryShape packet).slots_eq_roles_length .binary,q.binaryGeometry packet]
  let i : Fin (g.binary.roles .binary).length := ⟨query,by omega⟩
  have hr := point_role (cfg := cfg) proof H (g.binaryIndex i)
  change (((e).chain cfg.initialLink).point proof H (g.binaryStart+query)).role =
    some (g.roles.get (g.binaryIndex i)) at hr
  rw [g.binary_role_get i] at hr
  have hs := frontend_side .binary g.binary _ (List.get_mem _ i)
  unfold RuntimeCover.QuerySetup.single
  rw [hr]
  exact roleCharge_frontend q _ .binary _ H answer hs

theorem adapter_single (proof : Output) (H : Point → Digest × C) (i : Fin 3) (answer : Digest × C) :
    q.single (((e).chain cfg.initialLink).point proof H (ApplicationPrefix.rowBatchingIndex g+i.val)) H answer =
      q.roleCharge (([Role.rowBatching,.rescaling,.conversion]).get i)
        (((e).chain cfg.initialLink).point proof H (ApplicationPrefix.rowBatchingIndex g+i.val)) H answer := by
  have hindex : ApplicationPrefix.rowBatchingIndex g+i.val < g.roles.length := by
    have hlength := g.roles_length
    have hi := i.isLt
    simp only [ApplicationPrefix.rowBatchingIndex,Geometry.primeStart] at *
    omega
  have hr := point_role_of_get (cfg := cfg) proof H _ hindex _ (adapter_get g i)
  simp only [RuntimeCover.QuerySetup.single,hr]

theorem rowBatching_single (proof : Output) (H : Point → Digest × C) (answer : Digest × C) :
    q.single (((e).chain cfg.initialLink).point proof H (ApplicationPrefix.rowBatchingIndex g)) H answer =
      indicator (batchBad S q.batchRead
        (((e).chain cfg.initialLink).point proof H (ApplicationPrefix.rowBatchingIndex g)) H answer.2) := by
  simpa [RuntimeCover.QuerySetup.roleCharge] using adapter_single q proof H 0 answer

theorem rescaling_single (proof : Output) (H : Point → Digest × C) (answer : Digest × C) :
    q.single (((e).chain cfg.initialLink).point proof H (ApplicationPrefix.rescalingIndex g)) H answer =
      indicator (rescaleBad S q.rescaleRead q.rescaleDecoder
        (((e).chain cfg.initialLink).point proof H (ApplicationPrefix.rescalingIndex g)) H answer.2) := by
  simpa [ApplicationPrefix.rescalingIndex,RuntimeCover.QuerySetup.roleCharge] using adapter_single q proof H 1 answer

theorem conversion_single (proof : Output) (H : Point → Digest × C) (answer : Digest × C) :
    q.single (((e).chain cfg.initialLink).point proof H (ApplicationPrefix.conversionIndex g)) H answer =
      indicator (conversionBad S q.conversionRead q.conversionDecoder Adapter.Mdoc.groupOrder Adapter.Mdoc.quotientBound
        (((e).chain cfg.initialLink).point proof H (ApplicationPrefix.conversionIndex g)) H answer.2) := by
  simpa [ApplicationPrefix.conversionIndex,RuntimeCover.QuerySetup.roleCharge] using adapter_single q proof H 2 answer

theorem packing_single (proof : Output) (H : Point → Digest × C) (answer : Digest × C) :
    q.single (((e).chain cfg.initialLink).point proof H (ApplicationPrefix.packingIndex g)) H answer =
      indicator (packingBad S q.packingRead q.packingDecoder
        (((e).chain cfg.initialLink).point proof H (ApplicationPrefix.packingIndex g)) H answer.2) := by
  have nontrivial : g.packingDegree ≠ 1 := by
    rw [cfg.packingDegree]
    exact ne_of_gt binary.degree_gt
  have hindex : ApplicationPrefix.packingIndex g < g.roles.length := by
    have hlength := g.roles_length
    simp only [ApplicationPrefix.packingIndex,Geometry.binaryStart] at *
    omega
  have hr := point_role_of_get (cfg := cfg) proof H _ hindex .packing (packing_get g nontrivial)
  simp only [RuntimeCover.QuerySetup.single,hr,RuntimeCover.QuerySetup.roleCharge]

theorem fingerprint_single (proof : Output) (H : Point → Digest × C) (answer : Digest × C) :
    q.single (((e).chain cfg.initialLink).point proof H 0) H answer =
      indicator (S.binarySelection (((e).chain cfg.initialLink).point proof H 0) H answer.2) +
      indicator (S.primeSelection (((e).chain cfg.initialLink).point proof H 0) H answer.2) := by
  have hindex : 0 < g.roles.length := by rw [g.roles_length]; omega
  have hget : g.roles[0]? = some .fingerprint := by rw [g.roles_eq]; rfl
  have hr := point_role_of_get (cfg := cfg) proof H 0 hindex .fingerprint hget
  simp only [RuntimeCover.QuerySetup.single,hr,RuntimeCover.QuerySetup.roleCharge]

end LfzkV2.Current.RuntimeRoles
