import LfzkV2.Packed.CompiledFS
import LfzkV2.Packed.RuntimeCost

/-!
# Certified parameters for the actual packed and direct compilers

The candidate bound and cutoff are chosen before constructing each side, so
the proved packing count and transfer use precisely the certified list.
The terminal budgets are those of the profile's checked Polygero potential.
-/

namespace LfzkV2.Packed.Direct

open SumcheckV2 RecursivePolygero
open scoped Classical

variable {F C Context Pad Slot : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype C]
variable {out input nPublic nPrivate : ℕ}
variable (circuit : Native.Circuit F out input)
variable (inputIndex : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube input)
variable (privateCoordinate : Fin nPrivate → Slot) (coordinate : Pad → Slot)
variable (B : Instance F)
variable (plan : Native.Replay.PadPlan (Pad := Pad) (Slot := Slot) circuit)
variable (sampling : LfzkV2.Replay.Sampling F C circuit.shape) (dflt : C)
variable (publicOf : Context → Fin nPublic → F)
variable (primary : Slot → Fin B.nw × Fin B.q)
variable (product : (v : Native.Replay.Reconstruction circuit Pad Slot) →
  Fin v.constraints.layers.length → Fin B.nq × Fin B.q)
variable (eqns : ∀ ctx (v : Native.Replay.Reconstruction circuit Pad Slot), B.Equations ≃ Backend.Equation
  (rows circuit inputIndex (publicOf ctx) privateCoordinate coordinate v).length v.constraints.layers.length)
variable (p : LfzkV2.RuntimeProfiles.Profile) (geometry : LfzkV2.RuntimeProfiles.Geometry p B)
variable (decodeCoin : C → B.layer.Coin) (decodeQuery : C → B.layer.Query)
variable (backendSampling : LfzkV2.RuntimeProfiles.BackendSampling B decodeCoin decodeQuery)

noncomputable def profiledSide : Packed.CompiledSide F C Context circuit B :=
  side circuit inputIndex privateCoordinate coordinate B plan sampling dflt publicOf primary product eqns
    p.cutoff p.candidates (by simpa only [geometry.k] using p.cutoff_gt)
    (p.committedPacking_instance B geometry.n geometry.k) decodeCoin decodeQuery
    (p.potential B geometry.n geometry.k geometry.s geometry.t decodeCoin decodeQuery
      backendSampling.kCoin backendSampling.kQuery backendSampling.coin_bound backendSampling.query_bound)

noncomputable def profiledSide_profiled :
    (profiledSide circuit inputIndex privateCoordinate coordinate B plan sampling dflt publicOf primary product eqns
      p geometry decodeCoin decodeQuery backendSampling).Profiled p where
  geometry := geometry
  sampling := backendSampling
  cutoff_eq := rfl
  bound_eq := rfl
  challenge_eq := rfl
  query_eq := rfl

theorem profiledSide_direct :
    (profiledSide circuit inputIndex privateCoordinate coordinate B plan sampling dflt publicOf primary product eqns
      p geometry decodeCoin decodeQuery backendSampling).packed = false := rfl

theorem profiledSide_packingBudget :
    (profiledSide circuit inputIndex privateCoordinate coordinate B plan sampling dflt publicOf primary product eqns
      p geometry decodeCoin decodeQuery backendSampling).packingBudget = 0 := rfl

end LfzkV2.Packed.Direct

namespace LfzkV2.Packed.Compiled

open SumcheckV2 RecursivePolygero Finset
open scoped Classical

variable {K F Ix Words Pad Slot C Context : Type}
variable [Field K] [Fintype K] [Field F] [Fintype F] [DecidableEq F]
variable [Algebra K F] [Fintype Ix] [DecidableEq Ix] [Fintype Words] [Fintype C]
variable {out input nPublic nPrivate : ℕ}
variable (S : Packed.Statement K F Ix Words Slot) (circuit : Native.Circuit F out input)
variable (B : Instance F)
variable (plan : Native.Replay.PadPlan (Pad := Pad) (Slot := Slot) circuit)
variable (sampling : LfzkV2.Replay.Sampling F C circuit.shape) (dflt : C)
variable (inputIndex : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube input)
variable (packedIndex : Fin nPrivate ↪ Words × Ix)
variable (publicOf : Context → Fin nPublic → F) (coordinate : Pad → Slot)
variable (primary : Slot → Fin B.nw × Fin B.q)
variable (product : (v : Native.Replay.Reconstruction circuit Pad Slot) →
  Fin v.constraints.layers.length → Fin B.nq × Fin B.q)
variable (eqns : ∀ ctx (v : Native.Replay.Reconstruction circuit Pad Slot) (U delta : Ix → F) (A : F),
  B.Equations ≃ Backend.Equation
    (rows S circuit inputIndex packedIndex (publicOf ctx) coordinate v U delta A).length v.constraints.layers.length)
variable (decodePacking : C → Ix → F) (packingFiber : ℕ)
variable (hpackingFiber : ∀ delta, (univ.filter fun c => decodePacking c = delta).card ≤ packingFiber)
variable (hpackingBalanced : packingFiber * Fintype.card (Ix → F) = Fintype.card C)
variable (p : LfzkV2.RuntimeProfiles.Profile) (geometry : LfzkV2.RuntimeProfiles.Geometry p B)
variable (decodeCoin : C → B.layer.Coin) (decodeQuery : C → B.layer.Query)
variable (backendSampling : LfzkV2.RuntimeProfiles.BackendSampling B decodeCoin decodeQuery)

noncomputable def profiledSide : Packed.CompiledSide F C Context circuit B :=
  side S circuit B plan sampling dflt inputIndex packedIndex publicOf coordinate primary product eqns
    p.cutoff p.candidates (by simpa only [geometry.k] using p.cutoff_gt)
    (p.committedPacking_instance B geometry.n geometry.k)
    decodePacking packingFiber hpackingFiber hpackingBalanced decodeCoin decodeQuery
    (p.potential B geometry.n geometry.k geometry.s geometry.t decodeCoin decodeQuery
      backendSampling.kCoin backendSampling.kQuery backendSampling.coin_bound backendSampling.query_bound)

noncomputable def profiledSide_profiled :
    (profiledSide S circuit B plan sampling dflt inputIndex packedIndex publicOf coordinate primary product eqns
      decodePacking packingFiber hpackingFiber hpackingBalanced p geometry decodeCoin decodeQuery backendSampling).Profiled p where
  geometry := geometry
  sampling := backendSampling
  cutoff_eq := rfl
  bound_eq := rfl
  challenge_eq := rfl
  query_eq := rfl

theorem profiledSide_packed :
    (profiledSide S circuit B plan sampling dflt inputIndex packedIndex publicOf coordinate primary product eqns
      decodePacking packingFiber hpackingFiber hpackingBalanced p geometry decodeCoin decodeQuery backendSampling).packed = true := rfl

theorem profiledSide_packingBudget :
    let T := profiledSide S circuit B plan sampling dflt inputIndex packedIndex publicOf coordinate primary product eqns
      decodePacking packingFiber hpackingFiber hpackingBalanced p geometry decodeCoin decodeQuery backendSampling
    T.packingBudget = (T.sampling.unitFiber : ℚ) * T.bound := by
  exact Nat.cast_mul _ _

end LfzkV2.Packed.Compiled
