import LfzkV2.Current.ZeroKnowledge.SHAOracle
import LfzkV2.Current.MdocIdentifiers

/-! Public setup hashes and Merkle hashes use distinct literal tags.
Their answers therefore come from the complementary coordinates of the
same SHA oracle, even when the observer queries these public setup bytes. -/
namespace LfzkV2.Current.ZeroKnowledge.SHAOracle

theorem context_not_domain (domain : Bytes) (witnessCells : ℕ) :
    ¬merkleDomain (MdocIdentifiers.contextBytes domain witnessCells) := by
  rintro (⟨tail,equal⟩ | ⟨tail,equal⟩)
  all_goals
    have byte := congrArg (fun bytes : Bytes => bytes[9]?) equal
    change some (106 : TranscriptV2.Framing.Byte) = some 114 at byte
    exact (by decide : (106 : TranscriptV2.Framing.Byte) ≠ 114) (Option.some.inj byte)

theorem joint_context_not_domain (binary prime : Digest) :
    ¬merkleDomain (MdocIdentifiers.jointContextBytes binary prime) := by
  rintro (⟨tail,equal⟩ | ⟨tail,equal⟩)
  · have byte := congrArg (fun bytes : Bytes => bytes[15]?) equal
    change some (108 : TranscriptV2.Framing.Byte) = some 99 at byte
    exact (by decide : (108 : TranscriptV2.Framing.Byte) ≠ 99) (Option.some.inj byte)
  · have byte := congrArg (fun bytes : Bytes => bytes[15]?) equal
    change some (110 : TranscriptV2.Framing.Byte) = some 99 at byte
    exact (by decide : (110 : TranscriptV2.Framing.Byte) ≠ 99) (Option.some.inj byte)

theorem context_hash (outside inside : Bytes → Digest) (domain : Bytes) (witnessCells : ℕ) :
    merge merkleDomain outside inside (MdocIdentifiers.contextBytes domain witnessCells) =
      outside (MdocIdentifiers.contextBytes domain witnessCells) :=
  merge_outside merkleDomain outside inside _ (context_not_domain domain witnessCells)

theorem joint_context_hash (outside inside : Bytes → Digest) (binary prime : Digest) :
    merge merkleDomain outside inside (MdocIdentifiers.jointContextBytes binary prime) =
      outside (MdocIdentifiers.jointContextBytes binary prime) :=
  merge_outside merkleDomain outside inside _ (joint_context_not_domain binary prime)

end LfzkV2.Current.ZeroKnowledge.SHAOracle
