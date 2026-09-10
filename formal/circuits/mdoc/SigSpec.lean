/-
# What the mDOC signature circuit is supposed to prove

The companion to `mdoc/Spec.lean`. That file covers `mdoc_hash`, compiled over GF(2^128); this
one covers `mdoc_signature`, compiled over the P-256 base field. The two are separate circuits
with separate proofs, joined only by a triple of GF(2^128) MAC tags that are public inputs of
both.

## The statement, in English

Fix an issuer public key `pk_i`, a device-authentication digest `deviceSigE`, a MAC key `α` and
tags `(macE, macDpkX, macDpkY)`. Then `ValidSignatures` says: **there exist**

* a 32-byte value `e`, and a device public key `(dpkX, dpkY)`, each 32 bytes;
* MAC pads under which those three carry the given tags;
* ECDSA signatures `(r_i, s_i)` and `(r_d, s_d)`;

such that `(r_i, s_i)` is a valid P-256 signature by `pk_i` over `e`, and `(r_d, s_d)` is a valid
P-256 signature by `(dpkX, dpkY)` over `deviceSigE`.

Nothing here says what `e` is a hash *of* — that is the hash circuit's clause `MessageHash`, and
`e` is witness in both circuits. The MAC tags are what force the two `e`'s to be the same value;
see `## The seam` at the end and `MDoc.Spec`'s closing section.

## What is *not* in this circuit

`deviceSigE` is a public input, computed by the verifier outside the circuit as
`compute_transcript_hash(transcript, docType)` — SHA-256 of the COSE `Sign1` structure wrapping
`["DeviceAuthentication", SessionTranscript, docType, deviceNameSpaces]`
(`circuits/src/cbor/mdoc.rs`). The circuit checks a signature over it and nothing about how it
was formed. A verifier that computes this digest wrongly gets a meaningless proof, and no clause
below will notice.

## Provenance

The clauses are `mdoc_zk/circuits/src/signature/circuit.rs::assert_signatures_and_macs`. Its
`assert_signature` calls are `circuits/ecdsa2/src/circuit.rs`, whose relation is already modelled
in `ECDSA/Ecdsa.lean` as `ValidEcdsaWitness` and carried to `StandardEcdsaVerify` by
`ECDSA/EcdsaSound.lean::ecdsa_circuit_soundness`. So this file states the *specification* side —
`StandardEcdsaVerify` — and records, under `## Residual trust`, exactly which hypotheses of that
soundness theorem are not discharged by the circuit.

The MAC equation is `circuits/mac/src/circuit.rs`. It is the same equation as the hash circuit's
`circuits/mac_gf128`, but evaluated on 128-bit bitvectors with an emulated GF(2^128) multiply,
because this circuit's native field is `Fp256`. `MDoc.MacOk` therefore applies verbatim.
-/

import mdoc.Spec
import ECDSA.EcdsaSpec

namespace MDoc

section Sig

variable {F : Type} [Field F]

/-! ## Statement and witness

The split is `compile/src/allocate_sig.rs`. Public: `issuer_pk`, `device_sig_e`, the three MAC
tags and the MAC key. Witness: `issuer_sig_e`, `device_pk`, both ECDSA witnesses, the MAC pads.

Note that `issuer_pk` is allocated as two *field elements* — the affine coordinates directly —
while `device_sig_e`, `issuer_sig_e` and `device_pk` are allocated as 256 individually
booleanity-asserted bit wires. That asymmetry is why the device key crosses the seam and the
issuer key does not. -/

/-- The public inputs of the signature circuit. -/
structure SigStatement (F : Type) where
  /-- `issuer_pk`, as affine coordinates in the P-256 base field. -/
  issuerPk : AffinePoint F
  /-- `device_sig_e`: the DeviceAuthentication transcript digest, 32 big-endian bytes. Computed
      by the verifier, not by the circuit. -/
  deviceSigE : List Nat
  /-- `mac_av`, the GF(2^128) MAC key α — the same public value the hash circuit gets. -/
  macKey : Nat
  /-- `mac_e`, as (low half, high half). -/
  macE : Nat × Nat
  /-- `mac_device_pkx`. -/
  macDpkX : Nat × Nat
  /-- `mac_device_pky`. -/
  macDpkY : Nat × Nat

/-- The private inputs of the signature circuit. `r`/`s` are not wires — the circuit witnesses
    them as 256 base-8 digits packing the bits of `e`, `r` and `n - s` — but they are what the
    digits *mean*, and `ecdsa_circuit_soundness` is the theorem that says so. -/
structure SigWitness where
  /-- `issuer_sig_e`: the digest the issuer signed. 32 big-endian bytes. Witness here and in the
      hash circuit; only its MAC tag is public. -/
  e : List Nat
  /-- The device public key's 32-byte x-coordinate. -/
  dpkX : List Nat
  /-- ... and y-coordinate. -/
  dpkY : List Nat
  /-- The issuer signature. -/
  issuerR : Nat
  issuerS : Nat
  /-- The device signature. -/
  deviceR : Nat
  deviceS : Nat
  /-- `mac_ap`: the three one-time pads, each a pair. -/
  macPad : List (Nat × Nat)

/-! ## The clauses -/

/-- The bit-level linkage the circuit actually asserts, at the one point where it is *not* an
    equality of integers.

    `as_eltw_unsafe` reads a 256-bit wire vector as `Σ bᵢ · 2ⁱ` **in `F`**, and the circuit then
    asserts that field element equals the ECDSA scalar. So the MAC'd byte string and the scalar
    fed to the elliptic-curve arithmetic agree modulo `p`, not as integers: since both are below
    `2²⁵⁶` and `p > 2²⁵⁵`, they can differ by exactly `p`.

    This is stated rather than swept up because it is the difference between "the issuer signed
    the digest the hash circuit computed" and "the issuer signed something congruent to it mod
    `p`". Exploiting it would require a signature under the issuer's key on a *different* digest,
    so it is not a break; it is a place where the composed statement is weaker than it reads. -/
def AgreesModP (bytes : List Nat) (n : Nat) : Prop :=
  n < 2 ^ 256 ∧ ((n : F) = ((beVal bytes : Nat) : F))

/-- `assert_signature` for the issuer, plus the three `assert_eq`s that wire `issuer_pk` and
    `issuer_sig_e` into it. -/
def IssuerSignature (s : SigStatement F) (w : SigWitness) (order : Nat)
    (params : CurveParameters F) : Prop :=
  ∃ eSig : Nat, AgreesModP (F := F) w.e eSig ∧
    StandardEcdsaVerify s.issuerPk eSig w.issuerR w.issuerS order params

/-- `assert_signature` for the device. The signed message is the *public* transcript digest; the
    verifying key is the *witness* device key, which is what makes this a proof of possession
    without revealing which device. -/
def DeviceSignature (s : SigStatement F) (w : SigWitness) (order : Nat)
    (params : CurveParameters F) : Prop :=
  ∃ eSig dx dy : Nat,
    AgreesModP (F := F) s.deviceSigE eSig ∧
    AgreesModP (F := F) w.dpkX dx ∧ AgreesModP (F := F) w.dpkY dy ∧
    StandardEcdsaVerify { X := (dx : F), Y := (dy : F) } eSig w.deviceR w.deviceS order params

/-- The same three `assert_mac` calls as the hash circuit, on the same three messages under the
    same key. `MacOk` is reused verbatim from `MDoc.Spec`: this is the whole interface between
    the two circuits, so it must be one definition, not two that happen to agree. -/
def SigMacTags (s : SigStatement F) (w : SigWitness) : Prop :=
  MacOk s.macKey s.macE (w.macPad.getD 0 (0, 0)) w.e ∧
  MacOk s.macKey s.macDpkX (w.macPad.getD 1 (0, 0)) w.dpkX ∧
  MacOk s.macKey s.macDpkY (w.macPad.getD 2 (0, 0)) w.dpkY

/-! ## The top-level statement -/

/-- **Valid mDOC signatures.** Existential in the witness: the verifier learns that *some* device
    key signed the transcript and that the issuer signed *some* digest, and learns which ones
    only up to the MAC tags. -/
def ValidSignatures (s : SigStatement F) (order : Nat) (params : CurveParameters F) : Prop :=
  ∃ w : SigWitness,
    IssuerSignature s w order params ∧ DeviceSignature s w order params ∧ SigMacTags s w

/-! ## The composed presentation

The two circuits are proved separately and verified separately. What ties them is that
`macKey` and the three tags are public inputs of both, and the MAC is one-time: for a fixed
witness commitment, at most one value of `α` in `2¹²⁸` lets a prover carry different messages
through the two halves. That step is probabilistic, so it cannot be a Lean implication — it is a
hypothesis, and `MacsAgree` is where it is named. -/

/-- The two circuits' public MAC data coincide. Checked by the verifier, byte for byte. -/
def SharedMacs (h : Statement) (s : SigStatement F) : Prop :=
  h.macKey = s.macKey ∧ h.macE = s.macE ∧ h.macDpkX = s.macDpkX ∧ h.macDpkY = s.macDpkY

/-- **The soundness step this file cannot prove.** Given the same public tags, the witnesses the
    two circuits used agree. This is not an implication: a prover who could choose `mac_ap` after
    seeing `α` would break it trivially. It holds because `ZkProver::commit` commits `mac_ap` in
    both circuits *before* `av_val = tp.u128()` is drawn from the Fiat-Shamir transcript, so the
    bound is `2⁻¹²⁸` per proof over the choice of `α`. Recorded as a named hypothesis so that
    every theorem depending on it says so. -/
def MacsAgree (wh : Witness) (ws : SigWitness) : Prop :=
  wh.e = ws.e ∧ wh.dpkX = ws.dpkX ∧ wh.dpkY = ws.dpkY

/-- **A valid mDOC presentation, both halves.** The full statement a verifier is entitled to
    believe: the issuer signed a digest of a well-formed, in-date MSO that commits to the
    disclosed attributes and to a device key, and the holder of that device key signed this
    session's transcript.

    `MacsAgree` appears as a hypothesis on the shared witness rather than as a conclusion, for
    the reason given above. -/
def ValidPresentationFull (h : Statement) (s : SigStatement F) (order : Nat)
    (params : CurveParameters F) : Prop :=
  ∃ (wh : Witness) (ws : SigWitness),
    SharedMacs h s ∧ MacsAgree wh ws ∧
    -- the hash half
    MessageHash wh ∧ MsoDocType h wh ∧ MsoValidity h wh ∧ MsoDeviceKey wh ∧
      MsoValueDigests wh ∧ Attributes h wh ∧ MacTags h wh ∧
    -- the signature half
    IssuerSignature s ws order params ∧ DeviceSignature s ws order params ∧ SigMacTags s ws

/-! ## Consequences -/

/-- The composed statement really does give the headline claim: the issuer signed a digest, and
    that digest is the SHA-256 of a byte string of at most 2551 bytes that contains the disclosed
    attributes' commitments. Both halves are needed — `MessageHash` from one, `IssuerSignature`
    from the other, `MacsAgree` to identify their `e`. -/
theorem full_gives_signed_hash (h : Statement) (s : SigStatement F) (order : Nat)
    (params : CurveParameters F) (hv : ValidPresentationFull h s order params) :
    ∃ (wh : Witness) (eSig : Nat),
      wh.msgLen ≤ 2551 ∧
      sha256 wh.preimage wh.nblocks = wh.e ∧
      AgreesModP (F := F) wh.e eSig ∧
      ∃ r sg : Nat, StandardEcdsaVerify s.issuerPk eSig r sg order params := by
  obtain ⟨wh, ws, _, ⟨hme, _, _⟩, hmsg, _, _, _, _, _, _, ⟨eSig, hagree, hstd⟩, _, _⟩ := hv
  refine ⟨wh, eSig, msgLen_le wh hmsg, hmsg.2, ?_, ws.issuerR, ws.issuerS, hstd⟩
  rw [hme]; exact hagree

/-- And the device half: the key the transcript was signed under is the key the MSO binds. The
    MSO side is `MsoDeviceKey`, the signature side is `DeviceSignature`, and `MacsAgree` is the
    only thing joining them. -/
theorem full_binds_device_key (h : Statement) (s : SigStatement F) (order : Nat)
    (params : CurveParameters F) (hv : ValidPresentationFull h s order params) :
    ∃ (wh : Witness) (dx dy eSig r sg : Nat),
      window wh.preimage (wh.devKeyInfoOff + deviceKeyInfoKey.length) 32 = wh.dpkX ∧
      window wh.preimage (wh.devKeyInfoOff + deviceKeyInfoKey.length + 35) 32 = wh.dpkY ∧
      AgreesModP (F := F) wh.dpkX dx ∧ AgreesModP (F := F) wh.dpkY dy ∧
      AgreesModP (F := F) s.deviceSigE eSig ∧
      StandardEcdsaVerify { X := (dx : F), Y := (dy : F) } eSig r sg order params := by
  obtain ⟨wh, ws, _, ⟨_, hx, hy⟩, _, _, _, ⟨_, _, hkx, _, hky⟩, _, _, _, _,
    ⟨eSig, dx, dy, he, hdx, hdy, hstd⟩, _⟩ := hv
  refine ⟨wh, dx, dy, eSig, ws.deviceR, ws.deviceS, hkx, hky, ?_, ?_, he, hstd⟩
  · rw [hx]; exact hdx
  · rw [hy]; exact hdy

end Sig

/-! ## Residual trust

Everything `mdoc/Spec.lean`'s closing section lists still applies to the hash half. These are the
signature half's own.

* **The four hypotheses of `ecdsa_circuit_soundness` that the circuit does not assert.**
  `ECDSA/EcdsaSound.lean` carries `h_pk_order`, `h_G_order`, `h_R_order` — that `n · P = O` for
  the public key, the generator and the reconstructed point. The circuit asserts only
  `is_on_curve`. For P-256 these are free, because the curve group has prime order `n` and
  cofactor 1, so Lagrange gives `n · P = O` for *every* curve point; but `#E(F_p) = n` is not
  proved anywhere in this tree, so the discharge is an arithmetic fact taken on trust rather than
  a theorem. This is the cheapest remaining gap to close and the one worth closing first.

* **The exceptional-addition hypotheses.** `h_GPK_Z`, `h_GR_Z`, `h_RPK_Z`, `h_GRPK_Z` say the
  four precomputed sums are not the point at infinity. The circuit does not assert them, but
  neither does it assume them: `ec::slicing2` asserts `X = Z·wx` and `Y = Z·wy`, so a `Z = 0`
  witness would need `X = Y = 0`, which the RCB addition formula never outputs. Closing this
  properly means proving that, not adding a check.

* **`r < n` is asserted, `r = R.x mod n` is not.** The circuit asserts `rx_lt_order`, so it
  accepts only signatures whose `R.x` is already below the group order. Standard ECDSA reduces
  `R.x` mod `n`. Since `p - n < 2¹²⁸`, an honest signer produces such a signature except with
  probability about `2⁻¹²⁸`, so this costs completeness, not soundness — but a spec that claimed
  plain `StandardEcdsaVerify` completeness would be wrong.

* **`e` is not reduced mod `n` in the circuit.** The scalar multiplication consumes the full
  256-bit `e`, and `e · G = (e mod n) · G`, so this is only a restatement, not a gap. It is
  listed because `StandardEcdsaVerify` writes `z := e % order` and the correspondence is worth
  seeing rather than assuming.

* **`AgreesModP`, twice over.** See its docstring. It applies to `e`, to `deviceSigE`, and to
  both device-key coordinates.

* **Who `issuer_pk` is.** The circuit proves a signature under whatever key is supplied. That
  the key belongs to a trusted issuer is PKI, outside every circuit and every file here.

* **What the device signed.** `deviceSigE` is the verifier's own SHA-256 of the
  DeviceAuthentication structure. Nothing in the circuit relates it to the session, the docType,
  or the `docType` the hash circuit checks. A verifier that builds the transcript incorrectly
  gets a valid proof of a useless statement.

## The seam

`compile/src/allocate_hash.rs` and `compile/src/allocate_sig.rs` both allocate `mac_e`,
`mac_device_pkx`, `mac_device_pky` and `mac_av` among their public inputs, and both allocate
`mac_ap` after their subfield boundary, as witness. `SharedMacs` is the verifier-side check that
the public halves match; `MacsAgree` is the probabilistic consequence.

The asymmetry worth noticing: `e`, `dpkX` and `dpkY` cross the seam, and `docType` does not. The
hash circuit checks `docType` against its own public input; the signature circuit's
`deviceSigE` incorporates a `docType` chosen by the verifier. Nothing in-circuit forces those two
to be the same string. They are the same only because the same verifier supplies both.
-/

end MDoc
