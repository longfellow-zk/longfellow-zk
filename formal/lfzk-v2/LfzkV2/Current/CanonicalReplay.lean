import LfzkV2.Current.PacketReplay
import LfzkV2.Current.QueryRuntime
import LfzkV2.Current.ProofBodyBounds

/-! Canonical replay at the deployed packets. -/
noncomputable section
namespace LfzkV2.Current.CanonicalReplay
open CanonicalPrefix QueryRuntime
open scoped Classical

namespace Runtime
variable {g : Geometry} {fields : Fields} {Advice : Type}
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (shape : WireBlocks.Shape g fields) (setup : FingerprintPrefix.Setup) (publicCount : ℕ)

local notation "packets" => QueryRuntime.Runtime.packets repr shape setup publicCount

def packetIndex (i : Fin g.roles.length) : Fin (packets).length :=
  Fin.cast (by simpa only [List.length_map] using
    (congrArg List.length (QueryRuntime.Runtime.roles_eq repr shape setup publicCount)).symm) i

def packetAt (i : Fin g.roles.length) := (packets).get (packetIndex repr shape setup publicCount i)

theorem packetAt_zero (i : Fin g.roles.length) (hi : i.val = 0) :
    packetAt repr shape setup publicCount i = QueryRuntime.Runtime.first repr shape setup publicCount := by
  cases i with
  | mk n hn =>
      change n = 0 at hi
      subst n
      rfl

theorem packetAt_pos (i : Fin g.roles.length) (hi : 0 < i.val) :
    packetAt repr shape setup publicCount i = QueryRuntime.Runtime.ordinary repr shape setup publicCount i := by
  rcases i with ⟨n,hn⟩
  change 0 < n at hi
  cases n with
  | zero => omega
  | succ n =>
      simp only [packetAt,packetIndex,QueryRuntime.Runtime.packets,List.get_eq_getElem,Fin.cast_mk,
        List.getElem_cons_succ,List.getElem_tail,List.getElem_ofFn]

private def castData {first second : Packet (QueryRuntime.Runtime.Fresh (g := g) (fields := fields) (Advice := Advice))
    (QueryRuntime.Runtime.capacity repr shape setup publicCount)} (h : first = second) (value : first.Data) : second.Data := h ▸ value

private theorem block_castData {first second : Packet (QueryRuntime.Runtime.Fresh (g := g) (fields := fields) (Advice := Advice))
    (QueryRuntime.Runtime.capacity repr shape setup publicCount)} (h : first = second) (value : first.Data) :
    second.block (castData repr shape setup publicCount h value) = first.block value := by cases h; rfl

/-- The first packet is the context itself. Ordinary packet data is supplied
by the body-and-request constructor at its actual counter. -/
def dataAt (context : FingerprintPrefix.Key publicCount)
    (i : Fin g.roles.length) (ordinary : WireBlocks.Data (Advice := Advice) shape i) : (packetAt repr shape setup publicCount i).Data :=
  if hi : i.val = 0 then castData repr shape setup publicCount
    (packetAt_zero repr shape setup publicCount i hi).symm context
  else castData repr shape setup publicCount
    (packetAt_pos repr shape setup publicCount i (by omega)).symm ordinary

theorem block_dataAt_zero (context : FingerprintPrefix.Key publicCount)
    (i : Fin g.roles.length) (ordinary : WireBlocks.Data (Advice := Advice) shape i) (hi : i.val = 0) :
    (packetAt repr shape setup publicCount i).block (dataAt repr shape setup publicCount context i ordinary) =
      (QueryRuntime.Runtime.first repr shape setup publicCount).block context := by
  simp only [dataAt,dif_pos hi]
  exact block_castData repr shape setup publicCount _ _

theorem block_dataAt_pos (context : FingerprintPrefix.Key publicCount)
    (i : Fin g.roles.length) (ordinary : WireBlocks.Data (Advice := Advice) shape i) (hi : 0 < i.val) :
    (packetAt repr shape setup publicCount i).block (dataAt repr shape setup publicCount context i ordinary) =
      (QueryRuntime.Runtime.ordinary repr shape setup publicCount i).block ordinary := by
  simp only [dataAt,dif_neg (by omega : i.val ≠ 0)]
  exact block_castData repr shape setup publicCount _ _


-- The frontend role lists are irrelevant here; unfolding them only slows unification.
attribute [local irreducible] LfzkV2.Current.Frontend.roles in
/-- A packet factory makes every verifier replay input canonical, including
the complete-proof final seal. Only a static public size bound is required
for framing that last body. The two block identities are constructor
identities, not a semantic acceptance or canonicality certificate. -/
theorem canonical_of_blocks {C : Type}
    (e : Replay.Encoding g fields Advice (OpeningBody.Authentication g)
      (FingerprintPrefix.Key publicCount)
      (Block (QueryRuntime.Runtime.capacity repr shape setup publicCount)
        (QueryRuntime.Runtime.Fresh (g := g) (fields := fields) (Advice := Advice))) C)
    (ordinary : Replay.Output g fields Advice (OpeningBody.Authentication g) →
      (i : Fin g.roles.length) → (Fin i.val → C) → WireBlocks.Data (Advice := Advice) shape i)
    (hzero : ∀ proof i past, i.val = 0 → e.block proof i past =
      (QueryRuntime.Runtime.first repr shape setup publicCount).block (e.context proof))
    (hpos : ∀ proof i past, 0 < i.val → e.block proof i past =
      (QueryRuntime.Runtime.ordinary repr shape setup publicCount i).block (ordinary proof i past))
    (hfits : ProofBodyBounds.bodyBound repr g ≤ maxLength)
    (initialLink : Digest) (proof : Replay.Output g fields Advice (OpeningBody.Authentication g))
    (H : QueryRuntime.Runtime.Point repr shape setup publicCount → Digest × C)
    (n : ℕ) (hn : n ≤ g.roles.length) :
    QueryRuntime.Runtime.Canonical repr shape setup publicCount ((e.chain initialLink).point proof H n) := by
  let roles := QueryRuntime.Runtime.roles_eq repr shape setup publicCount
  let producer := fun (proof : Replay.Output g fields Advice (OpeningBody.Authentication g))
      (ip : Fin (packets).length) (past : Fin ip.val → C) =>
    dataAt repr shape setup publicCount (e.context proof) (index (packets) roles ip)
      (ordinary proof (index (packets) roles ip) past)
  have hblocks : ∀ proof ip past,
      e.block proof (index (packets) roles ip) past =
        ((packets).get ip).block (producer proof ip past) := by
    intro proof ip past
    let i := index (packets) roles ip
    change e.block proof i past =
      (packetAt repr shape setup publicCount i).block
        (dataAt repr shape setup publicCount (e.context proof) i (ordinary proof i past))
    by_cases hi : i.val = 0
    · rw [block_dataAt_zero repr shape setup publicCount _ _ _ hi]
      exact hzero proof i past hi
    · rw [block_dataAt_pos repr shape setup publicCount _ _ _ (by omega : 0 < i.val)]
      exact hpos proof i past (by omega)
  have hlen : (packets).length = g.roles.length := by
    simpa only [List.length_map] using congrArg List.length roles
  have hn' : n ≤ (packets).length := by omega
  have hbody := ProofBodyBounds.final_fits repr g hfits proof.body
  let values := replayValues e (packets) producer initialLink proof H
  let value := valueAt (ProofBodyCodec.codec repr g) (packets) values
    (fun i => (H ((e.chain initialLink).point proof H i.val)).1) ⟨proof.body,hbody⟩ n hn'
  have hkey : QueryRuntime.Runtime.key repr shape setup publicCount value = e.context proof := by
    cases n <;> rfl
  refine ⟨value,?_⟩
  change reindex roles (embed (ProofBodyCodec.codec repr g).whole
    (QueryRuntime.Runtime.key repr shape setup publicCount value) (packets) value) = _
  rw [hkey]
  exact point_eq_replay e (ProofBodyCodec.codec repr g) (packets) roles producer hblocks
    initialLink proof hbody H n hn'

end Runtime

end LfzkV2.Current.CanonicalReplay
