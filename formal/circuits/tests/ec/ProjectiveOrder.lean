/-
# Copyright 2026 Google LLC.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
-/

import ECDSA.EcdsaSpec
import ECDSA.Pratt

/-! Regression for the public-key order check in `StandardEcdsaVerify`.

The P-256 generator has order n, but the complete projective formulas return
an unnormalized representative of infinity. Coordinate equality incorrectly
rejects this public key; equality up to a nonzero scale accepts it.
-/
namespace ProjectiveOrder
abbrev p := 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF
theorem pPrime : Nat.Prime p := ECDSA.prime_115792089210356248762697446949407573530086143415290314195533631308867097853951
instance : Fact (Nat.Prime p) := ⟨pPrime⟩
abbrev K := ZMod p
def params : CurveParameters K := {
  a := -3
  b := 0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B
  gx := 0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296
  gy := 0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5
  kBits := 256 }
def n := 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551
def nG := bsmul (padBits (natToBits n) 256)
  ({ X := params.gx, Y := params.gy } : AffinePoint K).toProjective params

#guard nG.X = 0
#guard nG.Z = 0
#guard nG.Y ≠ 0
#guard nG.Y ≠ 1
#guard nG.Y.val = 18221937977142805162813603447807087164633376901873964114704461939180691492884
#guard nG ≠ infinityPoint
#guard nG = nG.Y • (infinityPoint : ProjectivePoint K)

-- The specification exposes projective equivalence, just like the generator
-- and reconstructed-point order hypotheses in the soundness theorem.
example (pk : AffinePoint K) (e r s : Nat)
    (h : StandardEcdsaVerify pk e r s n params) :
    ProjectiveEquiv (bsmul (padBits (natToBits n) params.kBits)
      pk.toProjective params) infinityPoint := h.2.1
end ProjectiveOrder
