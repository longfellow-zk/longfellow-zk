import LfzkV2.Current.WireBlocks

/-! Finite role packets give a public bound on complete block bytes. This
bound is an arbitrary natural number: u64 bounds apply to each framed
payload/count, not to the concatenation of every write in a boundary. -/
noncomputable section
namespace LfzkV2.Current.WireBlocks
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice : Type}
variable [∀ side, Fintype (fields side)] [Fintype Advice]
variable (shape : Shape g fields)

instance startDataFintype (start : Start) : Fintype (StartData (Advice := Advice) shape start) := by
  cases start <;> simp only [StartData,PrimeStart,BinaryStart,CircuitStatement,CircuitSchedule] <;> infer_instance

instance packingHeaderFintype : Fintype (PackingHeader shape) := by
  unfold PackingHeader
  split <;> infer_instance

instance packingTermsFintype {F : Type} [Fintype F] (bound : ℕ) : Fintype (PackingTerms F bound) :=
  inferInstance

instance packingSourceFintype : Fintype (PackingSource g fields shape) := inferInstance

instance packingAFintype : Fintype (PackingA g fields) := by
  unfold PackingA
  split <;> infer_instance

instance roleDataFintype (role : Role) : Fintype (RoleData shape role) := by
  cases role <;> simp only [RoleData,SourceStatement] <;> infer_instance

instance dataFintype (i : Fin g.roles.length) : Fintype (Data (Advice := Advice) shape i) := inferInstance

variable (repr : ProofBodyCodec.Representations fields Advice)

/-- A finite maximum over the actual public packet representation. Dynamic
RHS term counts, metadata bytes and both fields are included in this maximum;
no unused padding is appended to any encoded block. -/
def blockBound : ℕ :=
  Finset.univ.sup fun i : Fin g.roles.length =>
    Finset.univ.sup fun value : Data (Advice := Advice) shape i => ((codec repr shape i).encode value).length

theorem encode_length_le (i : Fin g.roles.length) (value : Data (Advice := Advice) shape i) :
    ((codec repr shape i).encode value).length ≤ blockBound shape repr := by
  unfold blockBound
  exact (Finset.le_sup (f := fun packet : Data (Advice := Advice) shape i =>
    ((codec repr shape i).encode packet).length) (Finset.mem_univ value)).trans
      (Finset.le_sup (f := fun index : Fin g.roles.length =>
        Finset.univ.sup fun packet : Data (Advice := Advice) shape index =>
          ((codec repr shape index).encode packet).length) (Finset.mem_univ i))

/-- The bounded base retains the complete encoded block. Its type is finite
without treating an unbounded byte list as an oracle-query coordinate. -/
def bounded (i : Fin g.roles.length) (value : Data (Advice := Advice) shape i) :
    BoundedBytes (blockBound shape repr) :=
  ⟨(codec repr shape i).encode value,encode_length_le shape repr i value⟩

@[simp] theorem bounded_bytes (i : Fin g.roles.length) (value : Data (Advice := Advice) shape i) :
    (bounded shape repr i value).bytes = (codec repr shape i).encode value := rfl

end LfzkV2.Current.WireBlocks
