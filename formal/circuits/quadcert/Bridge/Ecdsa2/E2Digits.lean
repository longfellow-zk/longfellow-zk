-- Generated. Do not edit.
import quadcert.Bridge.Ecdsa2.E2Sound
import quadcert.Gen.Ecdsa2.Ecdsa2Meaning

set_option maxRecDepth 4000000
set_option maxHeartbeats 4000000

/-!
# `hdig`: every digit wire is in range

The first of the bridges `soundness_of_v2` needs. Two forms are exported: the `∀ u ∈ …` one
that `soundness_of_v2` takes, and `digits_tuple`, the same 256 facts as an iterated
conjunction. The loop bridge needs them one at a time, and pulling 256 memberships out of a
256-element list costs O(n²) where one `obtain` on the tuple costs O(n). `assertions_zero` is destructured **once** per
chunk rather than searched per assertion (see `assert_at'` for why the per-assertion accessors
are the wrong shape), which names all 458 assertions in
the two chunks that carry digits; the generated meaning lemmas then turn each into `IsDigit`.
-/

namespace Ecdsa2.Assembly
open Quadcert Quadcert.Gen.Ecdsa2 Ecdsa2.Meaning
variable {F : Type} [Field F] [CharP F 115792089210356248762697446949407573530086143415290314195533631308867097853951]

/-- The 256 digit wires, in circuit order. -/
def digitWires (inputs : Nat → F) : List F := [inputs 6, inputs 7, inputs 8, inputs 9, inputs 10, inputs 11, inputs 12, inputs 13, inputs 14, inputs 15, inputs 16, inputs 17, inputs 18, inputs 19, inputs 20, inputs 21, inputs 22, inputs 23, inputs 24, inputs 25, inputs 26, inputs 27, inputs 28, inputs 29, inputs 30, inputs 31, inputs 32, inputs 33, inputs 34, inputs 35, inputs 36, inputs 37, inputs 38, inputs 39, inputs 40, inputs 41, inputs 42, inputs 43, inputs 44, inputs 45, inputs 46, inputs 47, inputs 48, inputs 49, inputs 50, inputs 51, inputs 52, inputs 53, inputs 54, inputs 55, inputs 56, inputs 57, inputs 58, inputs 59, inputs 60, inputs 61, inputs 62, inputs 63, inputs 64, inputs 65, inputs 66, inputs 67, inputs 68, inputs 69, inputs 70, inputs 71, inputs 72, inputs 73, inputs 74, inputs 75, inputs 76, inputs 77, inputs 78, inputs 79, inputs 80, inputs 81, inputs 82, inputs 83, inputs 84, inputs 85, inputs 86, inputs 87, inputs 88, inputs 89, inputs 90, inputs 91, inputs 92, inputs 93, inputs 94, inputs 95, inputs 96, inputs 97, inputs 98, inputs 99, inputs 100, inputs 101, inputs 102, inputs 103, inputs 104, inputs 105, inputs 106, inputs 107, inputs 108, inputs 109, inputs 110, inputs 111, inputs 112, inputs 113, inputs 114, inputs 115, inputs 116, inputs 117, inputs 118, inputs 119, inputs 120, inputs 121, inputs 122, inputs 123, inputs 124, inputs 125, inputs 126, inputs 127, inputs 128, inputs 129, inputs 130, inputs 131, inputs 132, inputs 133, inputs 134, inputs 135, inputs 136, inputs 137, inputs 138, inputs 139, inputs 140, inputs 141, inputs 142, inputs 143, inputs 144, inputs 145, inputs 146, inputs 147, inputs 148, inputs 149, inputs 150, inputs 151, inputs 152, inputs 153, inputs 154, inputs 155, inputs 156, inputs 157, inputs 158, inputs 159, inputs 160, inputs 161, inputs 162, inputs 163, inputs 164, inputs 165, inputs 166, inputs 167, inputs 168, inputs 169, inputs 170, inputs 171, inputs 172, inputs 173, inputs 174, inputs 175, inputs 176, inputs 177, inputs 178, inputs 179, inputs 180, inputs 181, inputs 182, inputs 183, inputs 184, inputs 185, inputs 186, inputs 187, inputs 188, inputs 189, inputs 190, inputs 191, inputs 192, inputs 193, inputs 194, inputs 195, inputs 196, inputs 197, inputs 198, inputs 199, inputs 200, inputs 201, inputs 202, inputs 203, inputs 204, inputs 205, inputs 206, inputs 207, inputs 208, inputs 209, inputs 210, inputs 211, inputs 212, inputs 213, inputs 214, inputs 215, inputs 216, inputs 217, inputs 218, inputs 219, inputs 220, inputs 221, inputs 222, inputs 223, inputs 224, inputs 225, inputs 226, inputs 227, inputs 228, inputs 229, inputs 230, inputs 231, inputs 232, inputs 233, inputs 234, inputs 235, inputs 236, inputs 237, inputs 238, inputs 239, inputs 240, inputs 241, inputs 242, inputs 243, inputs 244, inputs 245, inputs 246, inputs 247, inputs 248, inputs 249, inputs 250, inputs 251, inputs 252, inputs 253, inputs 254, inputs 255, inputs 256, inputs 257, inputs 258, inputs 259, inputs 260, inputs 261]

theorem digits_tuple (inputs : Nat → F) (hone : inputs 0 = 1)
    (hacc : Accepts (Ecdsa2.circuit F) inputs) :
    ECDSA2.IsDigit (inputs 6) ∧
      ECDSA2.IsDigit (inputs 7) ∧
      ECDSA2.IsDigit (inputs 8) ∧
      ECDSA2.IsDigit (inputs 9) ∧
      ECDSA2.IsDigit (inputs 10) ∧
      ECDSA2.IsDigit (inputs 11) ∧
      ECDSA2.IsDigit (inputs 12) ∧
      ECDSA2.IsDigit (inputs 13) ∧
      ECDSA2.IsDigit (inputs 14) ∧
      ECDSA2.IsDigit (inputs 15) ∧
      ECDSA2.IsDigit (inputs 16) ∧
      ECDSA2.IsDigit (inputs 17) ∧
      ECDSA2.IsDigit (inputs 18) ∧
      ECDSA2.IsDigit (inputs 19) ∧
      ECDSA2.IsDigit (inputs 20) ∧
      ECDSA2.IsDigit (inputs 21) ∧
      ECDSA2.IsDigit (inputs 22) ∧
      ECDSA2.IsDigit (inputs 23) ∧
      ECDSA2.IsDigit (inputs 24) ∧
      ECDSA2.IsDigit (inputs 25) ∧
      ECDSA2.IsDigit (inputs 26) ∧
      ECDSA2.IsDigit (inputs 27) ∧
      ECDSA2.IsDigit (inputs 28) ∧
      ECDSA2.IsDigit (inputs 29) ∧
      ECDSA2.IsDigit (inputs 30) ∧
      ECDSA2.IsDigit (inputs 31) ∧
      ECDSA2.IsDigit (inputs 32) ∧
      ECDSA2.IsDigit (inputs 33) ∧
      ECDSA2.IsDigit (inputs 34) ∧
      ECDSA2.IsDigit (inputs 35) ∧
      ECDSA2.IsDigit (inputs 36) ∧
      ECDSA2.IsDigit (inputs 37) ∧
      ECDSA2.IsDigit (inputs 38) ∧
      ECDSA2.IsDigit (inputs 39) ∧
      ECDSA2.IsDigit (inputs 40) ∧
      ECDSA2.IsDigit (inputs 41) ∧
      ECDSA2.IsDigit (inputs 42) ∧
      ECDSA2.IsDigit (inputs 43) ∧
      ECDSA2.IsDigit (inputs 44) ∧
      ECDSA2.IsDigit (inputs 45) ∧
      ECDSA2.IsDigit (inputs 46) ∧
      ECDSA2.IsDigit (inputs 47) ∧
      ECDSA2.IsDigit (inputs 48) ∧
      ECDSA2.IsDigit (inputs 49) ∧
      ECDSA2.IsDigit (inputs 50) ∧
      ECDSA2.IsDigit (inputs 51) ∧
      ECDSA2.IsDigit (inputs 52) ∧
      ECDSA2.IsDigit (inputs 53) ∧
      ECDSA2.IsDigit (inputs 54) ∧
      ECDSA2.IsDigit (inputs 55) ∧
      ECDSA2.IsDigit (inputs 56) ∧
      ECDSA2.IsDigit (inputs 57) ∧
      ECDSA2.IsDigit (inputs 58) ∧
      ECDSA2.IsDigit (inputs 59) ∧
      ECDSA2.IsDigit (inputs 60) ∧
      ECDSA2.IsDigit (inputs 61) ∧
      ECDSA2.IsDigit (inputs 62) ∧
      ECDSA2.IsDigit (inputs 63) ∧
      ECDSA2.IsDigit (inputs 64) ∧
      ECDSA2.IsDigit (inputs 65) ∧
      ECDSA2.IsDigit (inputs 66) ∧
      ECDSA2.IsDigit (inputs 67) ∧
      ECDSA2.IsDigit (inputs 68) ∧
      ECDSA2.IsDigit (inputs 69) ∧
      ECDSA2.IsDigit (inputs 70) ∧
      ECDSA2.IsDigit (inputs 71) ∧
      ECDSA2.IsDigit (inputs 72) ∧
      ECDSA2.IsDigit (inputs 73) ∧
      ECDSA2.IsDigit (inputs 74) ∧
      ECDSA2.IsDigit (inputs 75) ∧
      ECDSA2.IsDigit (inputs 76) ∧
      ECDSA2.IsDigit (inputs 77) ∧
      ECDSA2.IsDigit (inputs 78) ∧
      ECDSA2.IsDigit (inputs 79) ∧
      ECDSA2.IsDigit (inputs 80) ∧
      ECDSA2.IsDigit (inputs 81) ∧
      ECDSA2.IsDigit (inputs 82) ∧
      ECDSA2.IsDigit (inputs 83) ∧
      ECDSA2.IsDigit (inputs 84) ∧
      ECDSA2.IsDigit (inputs 85) ∧
      ECDSA2.IsDigit (inputs 86) ∧
      ECDSA2.IsDigit (inputs 87) ∧
      ECDSA2.IsDigit (inputs 88) ∧
      ECDSA2.IsDigit (inputs 89) ∧
      ECDSA2.IsDigit (inputs 90) ∧
      ECDSA2.IsDigit (inputs 91) ∧
      ECDSA2.IsDigit (inputs 92) ∧
      ECDSA2.IsDigit (inputs 93) ∧
      ECDSA2.IsDigit (inputs 94) ∧
      ECDSA2.IsDigit (inputs 95) ∧
      ECDSA2.IsDigit (inputs 96) ∧
      ECDSA2.IsDigit (inputs 97) ∧
      ECDSA2.IsDigit (inputs 98) ∧
      ECDSA2.IsDigit (inputs 99) ∧
      ECDSA2.IsDigit (inputs 100) ∧
      ECDSA2.IsDigit (inputs 101) ∧
      ECDSA2.IsDigit (inputs 102) ∧
      ECDSA2.IsDigit (inputs 103) ∧
      ECDSA2.IsDigit (inputs 104) ∧
      ECDSA2.IsDigit (inputs 105) ∧
      ECDSA2.IsDigit (inputs 106) ∧
      ECDSA2.IsDigit (inputs 107) ∧
      ECDSA2.IsDigit (inputs 108) ∧
      ECDSA2.IsDigit (inputs 109) ∧
      ECDSA2.IsDigit (inputs 110) ∧
      ECDSA2.IsDigit (inputs 111) ∧
      ECDSA2.IsDigit (inputs 112) ∧
      ECDSA2.IsDigit (inputs 113) ∧
      ECDSA2.IsDigit (inputs 114) ∧
      ECDSA2.IsDigit (inputs 115) ∧
      ECDSA2.IsDigit (inputs 116) ∧
      ECDSA2.IsDigit (inputs 117) ∧
      ECDSA2.IsDigit (inputs 118) ∧
      ECDSA2.IsDigit (inputs 119) ∧
      ECDSA2.IsDigit (inputs 120) ∧
      ECDSA2.IsDigit (inputs 121) ∧
      ECDSA2.IsDigit (inputs 122) ∧
      ECDSA2.IsDigit (inputs 123) ∧
      ECDSA2.IsDigit (inputs 124) ∧
      ECDSA2.IsDigit (inputs 125) ∧
      ECDSA2.IsDigit (inputs 126) ∧
      ECDSA2.IsDigit (inputs 127) ∧
      ECDSA2.IsDigit (inputs 128) ∧
      ECDSA2.IsDigit (inputs 129) ∧
      ECDSA2.IsDigit (inputs 130) ∧
      ECDSA2.IsDigit (inputs 131) ∧
      ECDSA2.IsDigit (inputs 132) ∧
      ECDSA2.IsDigit (inputs 133) ∧
      ECDSA2.IsDigit (inputs 134) ∧
      ECDSA2.IsDigit (inputs 135) ∧
      ECDSA2.IsDigit (inputs 136) ∧
      ECDSA2.IsDigit (inputs 137) ∧
      ECDSA2.IsDigit (inputs 138) ∧
      ECDSA2.IsDigit (inputs 139) ∧
      ECDSA2.IsDigit (inputs 140) ∧
      ECDSA2.IsDigit (inputs 141) ∧
      ECDSA2.IsDigit (inputs 142) ∧
      ECDSA2.IsDigit (inputs 143) ∧
      ECDSA2.IsDigit (inputs 144) ∧
      ECDSA2.IsDigit (inputs 145) ∧
      ECDSA2.IsDigit (inputs 146) ∧
      ECDSA2.IsDigit (inputs 147) ∧
      ECDSA2.IsDigit (inputs 148) ∧
      ECDSA2.IsDigit (inputs 149) ∧
      ECDSA2.IsDigit (inputs 150) ∧
      ECDSA2.IsDigit (inputs 151) ∧
      ECDSA2.IsDigit (inputs 152) ∧
      ECDSA2.IsDigit (inputs 153) ∧
      ECDSA2.IsDigit (inputs 154) ∧
      ECDSA2.IsDigit (inputs 155) ∧
      ECDSA2.IsDigit (inputs 156) ∧
      ECDSA2.IsDigit (inputs 157) ∧
      ECDSA2.IsDigit (inputs 158) ∧
      ECDSA2.IsDigit (inputs 159) ∧
      ECDSA2.IsDigit (inputs 160) ∧
      ECDSA2.IsDigit (inputs 161) ∧
      ECDSA2.IsDigit (inputs 162) ∧
      ECDSA2.IsDigit (inputs 163) ∧
      ECDSA2.IsDigit (inputs 164) ∧
      ECDSA2.IsDigit (inputs 165) ∧
      ECDSA2.IsDigit (inputs 166) ∧
      ECDSA2.IsDigit (inputs 167) ∧
      ECDSA2.IsDigit (inputs 168) ∧
      ECDSA2.IsDigit (inputs 169) ∧
      ECDSA2.IsDigit (inputs 170) ∧
      ECDSA2.IsDigit (inputs 171) ∧
      ECDSA2.IsDigit (inputs 172) ∧
      ECDSA2.IsDigit (inputs 173) ∧
      ECDSA2.IsDigit (inputs 174) ∧
      ECDSA2.IsDigit (inputs 175) ∧
      ECDSA2.IsDigit (inputs 176) ∧
      ECDSA2.IsDigit (inputs 177) ∧
      ECDSA2.IsDigit (inputs 178) ∧
      ECDSA2.IsDigit (inputs 179) ∧
      ECDSA2.IsDigit (inputs 180) ∧
      ECDSA2.IsDigit (inputs 181) ∧
      ECDSA2.IsDigit (inputs 182) ∧
      ECDSA2.IsDigit (inputs 183) ∧
      ECDSA2.IsDigit (inputs 184) ∧
      ECDSA2.IsDigit (inputs 185) ∧
      ECDSA2.IsDigit (inputs 186) ∧
      ECDSA2.IsDigit (inputs 187) ∧
      ECDSA2.IsDigit (inputs 188) ∧
      ECDSA2.IsDigit (inputs 189) ∧
      ECDSA2.IsDigit (inputs 190) ∧
      ECDSA2.IsDigit (inputs 191) ∧
      ECDSA2.IsDigit (inputs 192) ∧
      ECDSA2.IsDigit (inputs 193) ∧
      ECDSA2.IsDigit (inputs 194) ∧
      ECDSA2.IsDigit (inputs 195) ∧
      ECDSA2.IsDigit (inputs 196) ∧
      ECDSA2.IsDigit (inputs 197) ∧
      ECDSA2.IsDigit (inputs 198) ∧
      ECDSA2.IsDigit (inputs 199) ∧
      ECDSA2.IsDigit (inputs 200) ∧
      ECDSA2.IsDigit (inputs 201) ∧
      ECDSA2.IsDigit (inputs 202) ∧
      ECDSA2.IsDigit (inputs 203) ∧
      ECDSA2.IsDigit (inputs 204) ∧
      ECDSA2.IsDigit (inputs 205) ∧
      ECDSA2.IsDigit (inputs 206) ∧
      ECDSA2.IsDigit (inputs 207) ∧
      ECDSA2.IsDigit (inputs 208) ∧
      ECDSA2.IsDigit (inputs 209) ∧
      ECDSA2.IsDigit (inputs 210) ∧
      ECDSA2.IsDigit (inputs 211) ∧
      ECDSA2.IsDigit (inputs 212) ∧
      ECDSA2.IsDigit (inputs 213) ∧
      ECDSA2.IsDigit (inputs 214) ∧
      ECDSA2.IsDigit (inputs 215) ∧
      ECDSA2.IsDigit (inputs 216) ∧
      ECDSA2.IsDigit (inputs 217) ∧
      ECDSA2.IsDigit (inputs 218) ∧
      ECDSA2.IsDigit (inputs 219) ∧
      ECDSA2.IsDigit (inputs 220) ∧
      ECDSA2.IsDigit (inputs 221) ∧
      ECDSA2.IsDigit (inputs 222) ∧
      ECDSA2.IsDigit (inputs 223) ∧
      ECDSA2.IsDigit (inputs 224) ∧
      ECDSA2.IsDigit (inputs 225) ∧
      ECDSA2.IsDigit (inputs 226) ∧
      ECDSA2.IsDigit (inputs 227) ∧
      ECDSA2.IsDigit (inputs 228) ∧
      ECDSA2.IsDigit (inputs 229) ∧
      ECDSA2.IsDigit (inputs 230) ∧
      ECDSA2.IsDigit (inputs 231) ∧
      ECDSA2.IsDigit (inputs 232) ∧
      ECDSA2.IsDigit (inputs 233) ∧
      ECDSA2.IsDigit (inputs 234) ∧
      ECDSA2.IsDigit (inputs 235) ∧
      ECDSA2.IsDigit (inputs 236) ∧
      ECDSA2.IsDigit (inputs 237) ∧
      ECDSA2.IsDigit (inputs 238) ∧
      ECDSA2.IsDigit (inputs 239) ∧
      ECDSA2.IsDigit (inputs 240) ∧
      ECDSA2.IsDigit (inputs 241) ∧
      ECDSA2.IsDigit (inputs 242) ∧
      ECDSA2.IsDigit (inputs 243) ∧
      ECDSA2.IsDigit (inputs 244) ∧
      ECDSA2.IsDigit (inputs 245) ∧
      ECDSA2.IsDigit (inputs 246) ∧
      ECDSA2.IsDigit (inputs 247) ∧
      ECDSA2.IsDigit (inputs 248) ∧
      ECDSA2.IsDigit (inputs 249) ∧
      ECDSA2.IsDigit (inputs 250) ∧
      ECDSA2.IsDigit (inputs 251) ∧
      ECDSA2.IsDigit (inputs 252) ∧
      ECDSA2.IsDigit (inputs 253) ∧
      ECDSA2.IsDigit (inputs 254) ∧
      ECDSA2.IsDigit (inputs 255) ∧
      ECDSA2.IsDigit (inputs 256) ∧
      ECDSA2.IsDigit (inputs 257) ∧
      ECDSA2.IsDigit (inputs 258) ∧
      ECDSA2.IsDigit (inputs 259) ∧
      ECDSA2.IsDigit (inputs 260) ∧
      ECDSA2.IsDigit (inputs 261) := by
  have H := Ecdsa2.assertions_zero inputs hacc
  simp only [RawCircuit.toRecs, List.forall_mem_map,
    show (raw.asserts) = asserts_0 ++ asserts_1 ++ asserts_2 ++ asserts_3 ++ asserts_4 from rfl,
    List.forall_mem_append] at H
  obtain ⟨⟨⟨⟨H0, H1⟩, H2⟩, H3⟩, H4⟩ := H
  simp only [asserts_3, List.forall_mem_cons, List.forall_mem_nil] at H3
  obtain ⟨c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13, c3_14, c3_15, c3_16, c3_17, c3_18, c3_19, c3_20, c3_21, c3_22, c3_23, c3_24, c3_25, c3_26, c3_27, c3_28, c3_29, c3_30, c3_31, c3_32, c3_33, c3_34, c3_35, c3_36, c3_37, c3_38, c3_39, c3_40, c3_41, c3_42, c3_43, c3_44, c3_45, c3_46, c3_47, c3_48, c3_49, c3_50, c3_51, c3_52, c3_53, c3_54, c3_55, c3_56, c3_57, c3_58, c3_59, c3_60, c3_61, c3_62, c3_63, c3_64, c3_65, c3_66, c3_67, c3_68, c3_69, c3_70, c3_71, c3_72, c3_73, c3_74, c3_75, c3_76, c3_77, c3_78, c3_79, c3_80, c3_81, c3_82, c3_83, c3_84, c3_85, c3_86, c3_87, c3_88, c3_89, c3_90, c3_91, c3_92, c3_93, c3_94, c3_95, c3_96, c3_97, c3_98, c3_99, c3_100, c3_101, c3_102, c3_103, c3_104, c3_105, c3_106, c3_107, c3_108, c3_109, c3_110, c3_111, c3_112, c3_113, c3_114, c3_115, c3_116, c3_117, c3_118, c3_119, c3_120, c3_121, c3_122, c3_123, c3_124, c3_125, c3_126, c3_127, c3_128, c3_129, c3_130, c3_131, c3_132, c3_133, c3_134, c3_135, c3_136, c3_137, c3_138, c3_139, c3_140, c3_141, c3_142, c3_143, c3_144, c3_145, c3_146, c3_147, c3_148, c3_149, c3_150, c3_151, c3_152, c3_153, c3_154, c3_155, c3_156, c3_157, c3_158, c3_159, c3_160, c3_161, c3_162, c3_163, c3_164, c3_165, c3_166, c3_167, c3_168, c3_169, c3_170, c3_171, c3_172, c3_173, c3_174, c3_175, c3_176, c3_177, c3_178, c3_179, c3_180, c3_181, c3_182, c3_183, c3_184, c3_185, c3_186, c3_187, c3_188, c3_189, c3_190, c3_191, c3_192, c3_193, c3_194, c3_195, c3_196, c3_197, c3_198, c3_199, c3_200, c3_201, c3_202, c3_203, c3_204, c3_205, c3_206, c3_207, c3_208, c3_209, c3_210, c3_211, c3_212, c3_213, c3_214, c3_215, c3_216, c3_217, c3_218, c3_219, c3_220, c3_221, c3_222, c3_223, c3_224, c3_225, c3_226, c3_227, c3_228, c3_229, c3_230, c3_231, c3_232, c3_233, c3_234, c3_235, c3_236, c3_237, c3_238, c3_239, -⟩ := H3
  simp only [asserts_4, List.forall_mem_cons, List.forall_mem_nil] at H4
  obtain ⟨c4_0, c4_1, c4_2, c4_3, c4_4, c4_5, c4_6, c4_7, c4_8, c4_9, c4_10, c4_11, c4_12, c4_13, c4_14, c4_15, c4_16, c4_17, c4_18, c4_19, c4_20, c4_21, c4_22, c4_23, c4_24, c4_25, c4_26, c4_27, c4_28, c4_29, c4_30, c4_31, c4_32, c4_33, c4_34, c4_35, c4_36, c4_37, c4_38, c4_39, c4_40, c4_41, c4_42, c4_43, c4_44, c4_45, c4_46, c4_47, c4_48, c4_49, c4_50, c4_51, c4_52, c4_53, c4_54, c4_55, c4_56, c4_57, c4_58, c4_59, c4_60, c4_61, c4_62, c4_63, c4_64, c4_65, c4_66, c4_67, c4_68, c4_69, c4_70, c4_71, c4_72, c4_73, c4_74, c4_75, c4_76, c4_77, c4_78, c4_79, c4_80, c4_81, c4_82, c4_83, c4_84, c4_85, c4_86, c4_87, c4_88, c4_89, c4_90, c4_91, c4_92, c4_93, c4_94, c4_95, c4_96, c4_97, c4_98, c4_99, c4_100, c4_101, c4_102, c4_103, c4_104, c4_105, c4_106, c4_107, c4_108, c4_109, c4_110, c4_111, c4_112, c4_113, c4_114, c4_115, c4_116, c4_117, c4_118, c4_119, c4_120, c4_121, c4_122, c4_123, c4_124, c4_125, c4_126, c4_127, c4_128, c4_129, c4_130, c4_131, c4_132, c4_133, c4_134, c4_135, c4_136, c4_137, c4_138, c4_139, c4_140, c4_141, c4_142, c4_143, c4_144, c4_145, c4_146, c4_147, c4_148, c4_149, c4_150, c4_151, c4_152, c4_153, c4_154, c4_155, c4_156, c4_157, c4_158, c4_159, c4_160, c4_161, c4_162, c4_163, c4_164, c4_165, c4_166, c4_167, c4_168, c4_169, c4_170, c4_171, c4_172, c4_173, c4_174, c4_175, c4_176, c4_177, c4_178, c4_179, c4_180, c4_181, c4_182, c4_183, c4_184, c4_185, c4_186, c4_187, c4_188, c4_189, c4_190, c4_191, c4_192, c4_193, c4_194, c4_195, c4_196, c4_197, c4_198, c4_199, c4_200, c4_201, c4_202, c4_203, c4_204, c4_205, c4_206, c4_207, c4_208, c4_209, c4_210, c4_211, c4_212, c4_213, c4_214, c4_215, c4_216, c4_217, -⟩ := H4
  have d0 : ECDSA2.IsDigit (inputs 6) := m21681 inputs hone c3_185
  have d1 : ECDSA2.IsDigit (inputs 7) := m23408 inputs hone c3_186
  have d2 : ECDSA2.IsDigit (inputs 8) := m18773 inputs hone c3_187
  have d3 : ECDSA2.IsDigit (inputs 9) := m16150 inputs hone c3_188
  have d4 : ECDSA2.IsDigit (inputs 10) := m22221 inputs hone c3_189
  have d5 : ECDSA2.IsDigit (inputs 11) := m7422 inputs hone c3_190
  have d6 : ECDSA2.IsDigit (inputs 12) := m15356 inputs hone c3_191
  have d7 : ECDSA2.IsDigit (inputs 13) := m26100 inputs hone c3_192
  have d8 : ECDSA2.IsDigit (inputs 14) := m2952 inputs hone c3_193
  have d9 : ECDSA2.IsDigit (inputs 15) := m21948 inputs hone c3_194
  have d10 : ECDSA2.IsDigit (inputs 16) := m22600 inputs hone c3_195
  have d11 : ECDSA2.IsDigit (inputs 17) := m11158 inputs hone c3_196
  have d12 : ECDSA2.IsDigit (inputs 18) := m24047 inputs hone c3_197
  have d13 : ECDSA2.IsDigit (inputs 19) := m7528 inputs hone c3_198
  have d14 : ECDSA2.IsDigit (inputs 20) := m21574 inputs hone c3_199
  have d15 : ECDSA2.IsDigit (inputs 21) := m15396 inputs hone c3_200
  have d16 : ECDSA2.IsDigit (inputs 22) := m3830 inputs hone c3_201
  have d17 : ECDSA2.IsDigit (inputs 23) := m17370 inputs hone c3_202
  have d18 : ECDSA2.IsDigit (inputs 24) := m21713 inputs hone c3_203
  have d19 : ECDSA2.IsDigit (inputs 25) := m17313 inputs hone c3_204
  have d20 : ECDSA2.IsDigit (inputs 26) := m979 inputs hone c3_205
  have d21 : ECDSA2.IsDigit (inputs 27) := m16403 inputs hone c3_206
  have d22 : ECDSA2.IsDigit (inputs 28) := m12890 inputs hone c3_207
  have d23 : ECDSA2.IsDigit (inputs 29) := m20053 inputs hone c3_208
  have d24 : ECDSA2.IsDigit (inputs 30) := m339 inputs hone c3_209
  have d25 : ECDSA2.IsDigit (inputs 31) := m1686 inputs hone c3_210
  have d26 : ECDSA2.IsDigit (inputs 32) := m26794 inputs hone c3_211
  have d27 : ECDSA2.IsDigit (inputs 33) := m10887 inputs hone c3_212
  have d28 : ECDSA2.IsDigit (inputs 34) := m24692 inputs hone c3_213
  have d29 : ECDSA2.IsDigit (inputs 35) := m19659 inputs hone c3_214
  have d30 : ECDSA2.IsDigit (inputs 36) := m15209 inputs hone c3_215
  have d31 : ECDSA2.IsDigit (inputs 37) := m16332 inputs hone c3_216
  have d32 : ECDSA2.IsDigit (inputs 38) := m21737 inputs hone c3_217
  have d33 : ECDSA2.IsDigit (inputs 39) := m16306 inputs hone c3_218
  have d34 : ECDSA2.IsDigit (inputs 40) := m16336 inputs hone c3_219
  have d35 : ECDSA2.IsDigit (inputs 41) := m18357 inputs hone c3_220
  have d36 : ECDSA2.IsDigit (inputs 42) := m1916 inputs hone c3_221
  have d37 : ECDSA2.IsDigit (inputs 43) := m22644 inputs hone c3_222
  have d38 : ECDSA2.IsDigit (inputs 44) := m21460 inputs hone c3_223
  have d39 : ECDSA2.IsDigit (inputs 45) := m24544 inputs hone c3_224
  have d40 : ECDSA2.IsDigit (inputs 46) := m23483 inputs hone c3_225
  have d41 : ECDSA2.IsDigit (inputs 47) := m25850 inputs hone c3_226
  have d42 : ECDSA2.IsDigit (inputs 48) := m24506 inputs hone c3_227
  have d43 : ECDSA2.IsDigit (inputs 49) := m23816 inputs hone c3_228
  have d44 : ECDSA2.IsDigit (inputs 50) := m12862 inputs hone c3_229
  have d45 : ECDSA2.IsDigit (inputs 51) := m26860 inputs hone c3_230
  have d46 : ECDSA2.IsDigit (inputs 52) := m19118 inputs hone c3_231
  have d47 : ECDSA2.IsDigit (inputs 53) := m24688 inputs hone c3_232
  have d48 : ECDSA2.IsDigit (inputs 54) := m25046 inputs hone c3_233
  have d49 : ECDSA2.IsDigit (inputs 55) := m25010 inputs hone c3_234
  have d50 : ECDSA2.IsDigit (inputs 56) := m24239 inputs hone c3_235
  have d51 : ECDSA2.IsDigit (inputs 57) := m11477 inputs hone c3_236
  have d52 : ECDSA2.IsDigit (inputs 58) := m18006 inputs hone c3_237
  have d53 : ECDSA2.IsDigit (inputs 59) := m24259 inputs hone c3_238
  have d54 : ECDSA2.IsDigit (inputs 60) := m5272 inputs hone c3_239
  have d55 : ECDSA2.IsDigit (inputs 61) := m10879 inputs hone c4_0
  have d56 : ECDSA2.IsDigit (inputs 62) := m22636 inputs hone c4_1
  have d57 : ECDSA2.IsDigit (inputs 63) := m6538 inputs hone c4_2
  have d58 : ECDSA2.IsDigit (inputs 64) := m23870 inputs hone c4_3
  have d59 : ECDSA2.IsDigit (inputs 65) := m12858 inputs hone c4_4
  have d60 : ECDSA2.IsDigit (inputs 66) := m18010 inputs hone c4_5
  have d61 : ECDSA2.IsDigit (inputs 67) := m22233 inputs hone c4_6
  have d62 : ECDSA2.IsDigit (inputs 68) := m25562 inputs hone c4_7
  have d63 : ECDSA2.IsDigit (inputs 69) := m20499 inputs hone c4_8
  have d64 : ECDSA2.IsDigit (inputs 70) := m25924 inputs hone c4_9
  have d65 : ECDSA2.IsDigit (inputs 71) := m24884 inputs hone c4_10
  have d66 : ECDSA2.IsDigit (inputs 72) := m7761 inputs hone c4_11
  have d67 : ECDSA2.IsDigit (inputs 73) := m19881 inputs hone c4_12
  have d68 : ECDSA2.IsDigit (inputs 74) := m5884 inputs hone c4_13
  have d69 : ECDSA2.IsDigit (inputs 75) := m23318 inputs hone c4_14
  have d70 : ECDSA2.IsDigit (inputs 76) := m17653 inputs hone c4_15
  have d71 : ECDSA2.IsDigit (inputs 77) := m26440 inputs hone c4_16
  have d72 : ECDSA2.IsDigit (inputs 78) := m25002 inputs hone c4_17
  have d73 : ECDSA2.IsDigit (inputs 79) := m22739 inputs hone c4_18
  have d74 : ECDSA2.IsDigit (inputs 80) := m23883 inputs hone c4_19
  have d75 : ECDSA2.IsDigit (inputs 81) := m18002 inputs hone c4_20
  have d76 : ECDSA2.IsDigit (inputs 82) := m24494 inputs hone c4_21
  have d77 : ECDSA2.IsDigit (inputs 83) := m2962 inputs hone c4_22
  have d78 : ECDSA2.IsDigit (inputs 84) := m15205 inputs hone c4_23
  have d79 : ECDSA2.IsDigit (inputs 85) := m20295 inputs hone c4_24
  have d80 : ECDSA2.IsDigit (inputs 86) := m25488 inputs hone c4_25
  have d81 : ECDSA2.IsDigit (inputs 87) := m15683 inputs hone c4_26
  have d82 : ECDSA2.IsDigit (inputs 88) := m25811 inputs hone c4_27
  have d83 : ECDSA2.IsDigit (inputs 89) := m20495 inputs hone c4_28
  have d84 : ECDSA2.IsDigit (inputs 90) := m26476 inputs hone c4_29
  have d85 : ECDSA2.IsDigit (inputs 91) := m20551 inputs hone c4_30
  have d86 : ECDSA2.IsDigit (inputs 92) := m22755 inputs hone c4_31
  have d87 : ECDSA2.IsDigit (inputs 93) := m26262 inputs hone c4_32
  have d88 : ECDSA2.IsDigit (inputs 94) := m1193 inputs hone c4_33
  have d89 : ECDSA2.IsDigit (inputs 95) := m25838 inputs hone c4_34
  have d90 : ECDSA2.IsDigit (inputs 96) := m26694 inputs hone c4_35
  have d91 : ECDSA2.IsDigit (inputs 97) := m26856 inputs hone c4_36
  have d92 : ECDSA2.IsDigit (inputs 98) := m24133 inputs hone c4_37
  have d93 : ECDSA2.IsDigit (inputs 99) := m489 inputs hone c4_38
  have d94 : ECDSA2.IsDigit (inputs 100) := m17972 inputs hone c4_39
  have d95 : ECDSA2.IsDigit (inputs 101) := m26634 inputs hone c4_40
  have d96 : ECDSA2.IsDigit (inputs 102) := m25900 inputs hone c4_41
  have d97 : ECDSA2.IsDigit (inputs 103) := m5341 inputs hone c4_42
  have d98 : ECDSA2.IsDigit (inputs 104) := m15771 inputs hone c4_43
  have d99 : ECDSA2.IsDigit (inputs 105) := m26754 inputs hone c4_44
  have d100 : ECDSA2.IsDigit (inputs 106) := m19554 inputs hone c4_45
  have d101 : ECDSA2.IsDigit (inputs 107) := m2524 inputs hone c4_46
  have d102 : ECDSA2.IsDigit (inputs 108) := m26670 inputs hone c4_47
  have d103 : ECDSA2.IsDigit (inputs 109) := m23700 inputs hone c4_48
  have d104 : ECDSA2.IsDigit (inputs 110) := m25606 inputs hone c4_49
  have d105 : ECDSA2.IsDigit (inputs 111) := m7518 inputs hone c4_50
  have d106 : ECDSA2.IsDigit (inputs 112) := m15340 inputs hone c4_51
  have d107 : ECDSA2.IsDigit (inputs 113) := m23128 inputs hone c4_52
  have d108 : ECDSA2.IsDigit (inputs 114) := m26798 inputs hone c4_53
  have d109 : ECDSA2.IsDigit (inputs 115) := m25414 inputs hone c4_54
  have d110 : ECDSA2.IsDigit (inputs 116) := m26298 inputs hone c4_55
  have d111 : ECDSA2.IsDigit (inputs 117) := m18546 inputs hone c4_56
  have d112 : ECDSA2.IsDigit (inputs 118) := m22723 inputs hone c4_57
  have d113 : ECDSA2.IsDigit (inputs 119) := m24081 inputs hone c4_58
  have d114 : ECDSA2.IsDigit (inputs 120) := m5730 inputs hone c4_59
  have d115 : ECDSA2.IsDigit (inputs 121) := m25944 inputs hone c4_60
  have d116 : ECDSA2.IsDigit (inputs 122) := m3893 inputs hone c4_61
  have d117 : ECDSA2.IsDigit (inputs 123) := m15977 inputs hone c4_62
  have d118 : ECDSA2.IsDigit (inputs 124) := m23479 inputs hone c4_63
  have d119 : ECDSA2.IsDigit (inputs 125) := m20559 inputs hone c4_64
  have d120 : ECDSA2.IsDigit (inputs 126) := m21981 inputs hone c4_65
  have d121 : ECDSA2.IsDigit (inputs 127) := m12886 inputs hone c4_66
  have d122 : ECDSA2.IsDigit (inputs 128) := m21977 inputs hone c4_67
  have d123 : ECDSA2.IsDigit (inputs 129) := m4846 inputs hone c4_68
  have d124 : ECDSA2.IsDigit (inputs 130) := m20605 inputs hone c4_69
  have d125 : ECDSA2.IsDigit (inputs 131) := m18542 inputs hone c4_70
  have d126 : ECDSA2.IsDigit (inputs 132) := m4836 inputs hone c4_71
  have d127 : ECDSA2.IsDigit (inputs 133) := m22099 inputs hone c4_72
  have d128 : ECDSA2.IsDigit (inputs 134) := m25787 inputs hone c4_73
  have d129 : ECDSA2.IsDigit (inputs 135) := m26913 inputs hone c4_74
  have d130 : ECDSA2.IsDigit (inputs 136) := m12444 inputs hone c4_75
  have d131 : ECDSA2.IsDigit (inputs 137) := m14602 inputs hone c4_76
  have d132 : ECDSA2.IsDigit (inputs 138) := m26590 inputs hone c4_77
  have d133 : ECDSA2.IsDigit (inputs 139) := m22640 inputs hone c4_78
  have d134 : ECDSA2.IsDigit (inputs 140) := m26156 inputs hone c4_79
  have d135 : ECDSA2.IsDigit (inputs 141) := m25834 inputs hone c4_80
  have d136 : ECDSA2.IsDigit (inputs 142) := m16134 inputs hone c4_81
  have d137 : ECDSA2.IsDigit (inputs 143) := m26124 inputs hone c4_82
  have d138 : ECDSA2.IsDigit (inputs 144) := m22095 inputs hone c4_83
  have d139 : ECDSA2.IsDigit (inputs 145) := m20139 inputs hone c4_84
  have d140 : ECDSA2.IsDigit (inputs 146) := m1323 inputs hone c4_85
  have d141 : ECDSA2.IsDigit (inputs 147) := m21677 inputs hone c4_86
  have d142 : ECDSA2.IsDigit (inputs 148) := m19579 inputs hone c4_87
  have d143 : ECDSA2.IsDigit (inputs 149) := m21741 inputs hone c4_88
  have d144 : ECDSA2.IsDigit (inputs 150) := m2514 inputs hone c4_89
  have d145 : ECDSA2.IsDigit (inputs 151) := m26666 inputs hone c4_90
  have d146 : ECDSA2.IsDigit (inputs 152) := m22500 inputs hone c4_91
  have d147 : ECDSA2.IsDigit (inputs 153) := m23240 inputs hone c4_92
  have d148 : ECDSA2.IsDigit (inputs 154) := m11162 inputs hone c4_93
  have d149 : ECDSA2.IsDigit (inputs 155) := m20143 inputs hone c4_94
  have d150 : ECDSA2.IsDigit (inputs 156) := m26064 inputs hone c4_95
  have d151 : ECDSA2.IsDigit (inputs 157) := m17051 inputs hone c4_96
  have d152 : ECDSA2.IsDigit (inputs 158) := m21973 inputs hone c4_97
  have d153 : ECDSA2.IsDigit (inputs 159) := m24880 inputs hone c4_98
  have d154 : ECDSA2.IsDigit (inputs 160) := m24085 inputs hone c4_99
  have d155 : ECDSA2.IsDigit (inputs 161) := m16154 inputs hone c4_100
  have d156 : ECDSA2.IsDigit (inputs 162) := m22751 inputs hone c4_101
  have d157 : ECDSA2.IsDigit (inputs 163) := m5815 inputs hone c4_102
  have d158 : ECDSA2.IsDigit (inputs 164) := m15775 inputs hone c4_103
  have d159 : ECDSA2.IsDigit (inputs 165) := m3026 inputs hone c4_104
  have d160 : ECDSA2.IsDigit (inputs 166) := m1836 inputs hone c4_105
  have d161 : ECDSA2.IsDigit (inputs 167) := m16130 inputs hone c4_106
  have d162 : ECDSA2.IsDigit (inputs 168) := m25114 inputs hone c4_107
  have d163 : ECDSA2.IsDigit (inputs 169) := m23404 inputs hone c4_108
  have d164 : ECDSA2.IsDigit (inputs 170) := m25707 inputs hone c4_109
  have d165 : ECDSA2.IsDigit (inputs 171) := m22401 inputs hone c4_110
  have d166 : ECDSA2.IsDigit (inputs 172) := m23286 inputs hone c4_111
  have d167 : ECDSA2.IsDigit (inputs 173) := m20384 inputs hone c4_112
  have d168 : ECDSA2.IsDigit (inputs 174) := m2723 inputs hone c4_113
  have d169 : ECDSA2.IsDigit (inputs 175) := m24490 inputs hone c4_114
  have d170 : ECDSA2.IsDigit (inputs 176) := m26889 inputs hone c4_115
  have d171 : ECDSA2.IsDigit (inputs 177) := m25006 inputs hone c4_116
  have d172 : ECDSA2.IsDigit (inputs 178) := m24974 inputs hone c4_117
  have d173 : ECDSA2.IsDigit (inputs 179) := m26674 inputs hone c4_118
  have d174 : ECDSA2.IsDigit (inputs 180) := m25830 inputs hone c4_119
  have d175 : ECDSA2.IsDigit (inputs 181) := m10883 inputs hone c4_120
  have d176 : ECDSA2.IsDigit (inputs 182) := m24387 inputs hone c4_121
  have d177 : ECDSA2.IsDigit (inputs 183) := m23487 inputs hone c4_122
  have d178 : ECDSA2.IsDigit (inputs 184) := m26456 inputs hone c4_123
  have d179 : ECDSA2.IsDigit (inputs 185) := m26893 inputs hone c4_124
  have d180 : ECDSA2.IsDigit (inputs 186) := m25298 inputs hone c4_125
  have d181 : ECDSA2.IsDigit (inputs 187) := m4014 inputs hone c4_126
  have d182 : ECDSA2.IsDigit (inputs 188) := m11524 inputs hone c4_127
  have d183 : ECDSA2.IsDigit (inputs 189) := m5374 inputs hone c4_128
  have d184 : ECDSA2.IsDigit (inputs 190) := m2942 inputs hone c4_129
  have d185 : ECDSA2.IsDigit (inputs 191) := m14986 inputs hone c4_130
  have d186 : ECDSA2.IsDigit (inputs 192) := m13111 inputs hone c4_131
  have d187 : ECDSA2.IsDigit (inputs 193) := m25246 inputs hone c4_132
  have d188 : ECDSA2.IsDigit (inputs 194) := m25578 inputs hone c4_133
  have d189 : ECDSA2.IsDigit (inputs 195) := m21383 inputs hone c4_134
  have d190 : ECDSA2.IsDigit (inputs 196) := m4028 inputs hone c4_135
  have d191 : ECDSA2.IsDigit (inputs 197) := m12294 inputs hone c4_136
  have d192 : ECDSA2.IsDigit (inputs 198) := m19378 inputs hone c4_137
  have d193 : ECDSA2.IsDigit (inputs 199) := m25649 inputs hone c4_138
  have d194 : ECDSA2.IsDigit (inputs 200) := m16809 inputs hone c4_139
  have d195 : ECDSA2.IsDigit (inputs 201) := m25294 inputs hone c4_140
  have d196 : ECDSA2.IsDigit (inputs 202) := m11166 inputs hone c4_141
  have d197 : ECDSA2.IsDigit (inputs 203) := m26338 inputs hone c4_142
  have d198 : ECDSA2.IsDigit (inputs 204) := m24404 inputs hone c4_143
  have d199 : ECDSA2.IsDigit (inputs 205) := m2365 inputs hone c4_144
  have d200 : ECDSA2.IsDigit (inputs 206) := m11541 inputs hone c4_145
  have d201 : ECDSA2.IsDigit (inputs 207) := m2348 inputs hone c4_146
  have d202 : ECDSA2.IsDigit (inputs 208) := m22759 inputs hone c4_147
  have d203 : ECDSA2.IsDigit (inputs 209) := m479 inputs hone c4_148
  have d204 : ECDSA2.IsDigit (inputs 210) := m26214 inputs hone c4_149
  have d205 : ECDSA2.IsDigit (inputs 211) := m5650 inputs hone c4_150
  have d206 : ECDSA2.IsDigit (inputs 212) := m16062 inputs hone c4_151
  have d207 : ECDSA2.IsDigit (inputs 213) := m23622 inputs hone c4_152
  have d208 : ECDSA2.IsDigit (inputs 214) := m22823 inputs hone c4_153
  have d209 : ECDSA2.IsDigit (inputs 215) := m25602 inputs hone c4_154
  have d210 : ECDSA2.IsDigit (inputs 216) := m17309 inputs hone c4_155
  have d211 : ECDSA2.IsDigit (inputs 217) := m25034 inputs hone c4_156
  have d212 : ECDSA2.IsDigit (inputs 218) := m26646 inputs hone c4_157
  have d213 : ECDSA2.IsDigit (inputs 219) := m23987 inputs hone c4_158
  have d214 : ECDSA2.IsDigit (inputs 220) := m11726 inputs hone c4_159
  have d215 : ECDSA2.IsDigit (inputs 221) := m23322 inputs hone c4_160
  have d216 : ECDSA2.IsDigit (inputs 222) := m329 inputs hone c4_161
  have d217 : ECDSA2.IsDigit (inputs 223) := m4018 inputs hone c4_162
  have d218 : ECDSA2.IsDigit (inputs 224) := m21578 inputs hone c4_163
  have d219 : ECDSA2.IsDigit (inputs 225) := m15003 inputs hone c4_164
  have d220 : ECDSA2.IsDigit (inputs 226) := m18487 inputs hone c4_165
  have d221 : ECDSA2.IsDigit (inputs 227) := m16660 inputs hone c4_166
  have d222 : ECDSA2.IsDigit (inputs 228) := m16113 inputs hone c4_167
  have d223 : ECDSA2.IsDigit (inputs 229) := m11537 inputs hone c4_168
  have d224 : ECDSA2.IsDigit (inputs 230) := m17998 inputs hone c4_169
  have d225 : ECDSA2.IsDigit (inputs 231) := m21944 inputs hone c4_170
  have d226 : ECDSA2.IsDigit (inputs 232) := m25912 inputs hone c4_171
  have d227 : ECDSA2.IsDigit (inputs 233) := m23004 inputs hone c4_172
  have d228 : ECDSA2.IsDigit (inputs 234) := m5565 inputs hone c4_173
  have d229 : ECDSA2.IsDigit (inputs 235) := m22656 inputs hone c4_174
  have d230 : ECDSA2.IsDigit (inputs 236) := m19416 inputs hone c4_175
  have d231 : ECDSA2.IsDigit (inputs 237) := m18518 inputs hone c4_176
  have d232 : ECDSA2.IsDigit (inputs 238) := m22181 inputs hone c4_177
  have d233 : ECDSA2.IsDigit (inputs 239) := m25826 inputs hone c4_178
  have d234 : ECDSA2.IsDigit (inputs 240) := m11922 inputs hone c4_179
  have d235 : ECDSA2.IsDigit (inputs 241) := m17386 inputs hone c4_180
  have d236 : ECDSA2.IsDigit (inputs 242) := m13014 inputs hone c4_181
  have d237 : ECDSA2.IsDigit (inputs 243) := m25582 inputs hone c4_182
  have d238 : ECDSA2.IsDigit (inputs 244) := m14999 inputs hone c4_183
  have d239 : ECDSA2.IsDigit (inputs 245) := m24676 inputs hone c4_184
  have d240 : ECDSA2.IsDigit (inputs 246) := m16603 inputs hone c4_185
  have d241 : ECDSA2.IsDigit (inputs 247) := m3160 inputs hone c4_186
  have d242 : ECDSA2.IsDigit (inputs 248) := m1113 inputs hone c4_187
  have d243 : ECDSA2.IsDigit (inputs 249) := m13115 inputs hone c4_188
  have d244 : ECDSA2.IsDigit (inputs 250) := m20447 inputs hone c4_189
  have d245 : ECDSA2.IsDigit (inputs 251) := m8534 inputs hone c4_190
  have d246 : ECDSA2.IsDigit (inputs 252) := m21590 inputs hone c4_191
  have d247 : ECDSA2.IsDigit (inputs 253) := m17710 inputs hone c4_192
  have d248 : ECDSA2.IsDigit (inputs 254) := m25354 inputs hone c4_193
  have d249 : ECDSA2.IsDigit (inputs 255) := m7024 inputs hone c4_194
  have d250 : ECDSA2.IsDigit (inputs 256) := m24532 inputs hone c4_195
  have d251 : ECDSA2.IsDigit (inputs 257) := m16058 inputs hone c4_196
  have d252 : ECDSA2.IsDigit (inputs 258) := m2872 inputs hone c4_197
  have d253 : ECDSA2.IsDigit (inputs 259) := m22193 inputs hone c4_198
  have d254 : ECDSA2.IsDigit (inputs 260) := m19205 inputs hone c4_199
  have d255 : ECDSA2.IsDigit (inputs 261) := m26766 inputs hone c4_200
  exact ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31, d32, d33, d34, d35, d36, d37, d38, d39, d40, d41, d42, d43, d44, d45, d46, d47, d48, d49, d50, d51, d52, d53, d54, d55, d56, d57, d58, d59, d60, d61, d62, d63, d64, d65, d66, d67, d68, d69, d70, d71, d72, d73, d74, d75, d76, d77, d78, d79, d80, d81, d82, d83, d84, d85, d86, d87, d88, d89, d90, d91, d92, d93, d94, d95, d96, d97, d98, d99, d100, d101, d102, d103, d104, d105, d106, d107, d108, d109, d110, d111, d112, d113, d114, d115, d116, d117, d118, d119, d120, d121, d122, d123, d124, d125, d126, d127, d128, d129, d130, d131, d132, d133, d134, d135, d136, d137, d138, d139, d140, d141, d142, d143, d144, d145, d146, d147, d148, d149, d150, d151, d152, d153, d154, d155, d156, d157, d158, d159, d160, d161, d162, d163, d164, d165, d166, d167, d168, d169, d170, d171, d172, d173, d174, d175, d176, d177, d178, d179, d180, d181, d182, d183, d184, d185, d186, d187, d188, d189, d190, d191, d192, d193, d194, d195, d196, d197, d198, d199, d200, d201, d202, d203, d204, d205, d206, d207, d208, d209, d210, d211, d212, d213, d214, d215, d216, d217, d218, d219, d220, d221, d222, d223, d224, d225, d226, d227, d228, d229, d230, d231, d232, d233, d234, d235, d236, d237, d238, d239, d240, d241, d242, d243, d244, d245, d246, d247, d248, d249, d250, d251, d252, d253, d254, d255⟩

/-- The `∀ u ∈ …` form `soundness_of_v2` consumes, from the tuple. -/
theorem digits_ok (inputs : Nat → F) (hone : inputs 0 = 1)
    (hacc : Accepts (Ecdsa2.circuit F) inputs) :
    ∀ u ∈ digitWires inputs, ECDSA2.IsDigit u := by
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31, d32, d33, d34, d35, d36, d37, d38, d39, d40, d41, d42, d43, d44, d45, d46, d47, d48, d49, d50, d51, d52, d53, d54, d55, d56, d57, d58, d59, d60, d61, d62, d63, d64, d65, d66, d67, d68, d69, d70, d71, d72, d73, d74, d75, d76, d77, d78, d79, d80, d81, d82, d83, d84, d85, d86, d87, d88, d89, d90, d91, d92, d93, d94, d95, d96, d97, d98, d99, d100, d101, d102, d103, d104, d105, d106, d107, d108, d109, d110, d111, d112, d113, d114, d115, d116, d117, d118, d119, d120, d121, d122, d123, d124, d125, d126, d127, d128, d129, d130, d131, d132, d133, d134, d135, d136, d137, d138, d139, d140, d141, d142, d143, d144, d145, d146, d147, d148, d149, d150, d151, d152, d153, d154, d155, d156, d157, d158, d159, d160, d161, d162, d163, d164, d165, d166, d167, d168, d169, d170, d171, d172, d173, d174, d175, d176, d177, d178, d179, d180, d181, d182, d183, d184, d185, d186, d187, d188, d189, d190, d191, d192, d193, d194, d195, d196, d197, d198, d199, d200, d201, d202, d203, d204, d205, d206, d207, d208, d209, d210, d211, d212, d213, d214, d215, d216, d217, d218, d219, d220, d221, d222, d223, d224, d225, d226, d227, d228, d229, d230, d231, d232, d233, d234, d235, d236, d237, d238, d239, d240, d241, d242, d243, d244, d245, d246, d247, d248, d249, d250, d251, d252, d253, d254, d255⟩ := digits_tuple inputs hone hacc
  intro u hu
  simp only [digitWires, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

end Ecdsa2.Assembly
