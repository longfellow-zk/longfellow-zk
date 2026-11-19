Every input of `run_mdoc_verifier` and where the transcript absorbs it
(transcript I1 to I4):

- `zk_spec`: the combined hash, the version and the attribute count, in
  `MdocStatement`; the Polygero profile, in `JointGeometry`.
- `circuits_compressed`: checked against the spec's combined hash; each
  circuit by its ID in a `Circuit` message (the ID hashes the whole
  circuit), the adapter fragment's too, which the verifier generates from
  the layout `AdapterLayout` holds.
- `pkx`, `pky`: the signature circuit's first two public inputs, in its
  `PublicInputs`.
- `transcript`: the session transcript, in `MdocStatement`; with
  `doc_type`, the digest `e2` of the device authentication, the signature
  circuit's other public inputs.
- `attrs`, `now`, `doc_type`: the hash circuit's public inputs, in its
  `PublicInputs`.
- `proof_bytes`: parsed against the geometry the statement wrote; each
  interactive field is absorbed as its prover message where it is sent,
  and the seal covers every byte before the seal block.

Both commitment layouts and the adapter layout are written from the
composition the verifier builds from these inputs. The fields and their
evaluation domains are the verifier's own; the domains are not absorbed.

The verifier takes no geometry, circuit or public inputs except through
those inputs, which its statement absorbs. The call that verifies:

```
use longfellow_zk::{
    mdoc::v2::{run_mdoc_verifier, MdocVerifierErrorCode, RequestedAttribute, ZkSpecStruct},
    runtime::v2::transcript::VerifiedProof,
};
fn verify(
    spec: &ZkSpecStruct,
    circuits: &[u8],
    attrs: &[RequestedAttribute],
    proof: &[u8],
) -> Result<VerifiedProof, MdocVerifierErrorCode> {
    run_mdoc_verifier(spec, circuits, "0x1", "0x2", b"session", attrs, "now", "doc", proof)
}
```

There is no argument for a geometry,

```compile_fail,E0061
use longfellow_zk::mdoc::v2::{run_mdoc_verifier, MdocProofGeometry, RequestedAttribute, ZkSpecStruct};
fn verify(
    spec: &ZkSpecStruct,
    circuits: &[u8],
    attrs: &[RequestedAttribute],
    proof: &[u8],
    geometry: &MdocProofGeometry,
) {
    let _ = run_mdoc_verifier(spec, circuits, "0x1", "0x2", b"session", attrs, "now", "doc", proof, geometry);
}
```

the circuits are the archive the spec names, not decoded circuits,

```compile_fail,E0308
use longfellow_zk::{
    core::proto::v2::Circuit,
    mdoc::v2::{run_mdoc_verifier, RequestedAttribute, ZkSpecStruct},
    runtime::algebra::gf2_128::Gf2_128Field,
};
fn verify(
    spec: &ZkSpecStruct,
    circuit: &Circuit<Gf2_128Field>,
    attrs: &[RequestedAttribute],
    proof: &[u8],
) {
    let _ = run_mdoc_verifier(spec, circuit, "0x1", "0x2", b"session", attrs, "now", "doc", proof);
}
```

and there is no argument for public inputs, which the verifier derives
from the request:

```compile_fail,E0061
use longfellow_zk::{
    mdoc::v2::{run_mdoc_verifier, RequestedAttribute, ZkSpecStruct},
    runtime::algebra::p256::P256Element,
};
fn verify(
    spec: &ZkSpecStruct,
    circuits: &[u8],
    attrs: &[RequestedAttribute],
    proof: &[u8],
    public: &[P256Element],
) {
    let _ = run_mdoc_verifier(spec, circuits, "0x1", "0x2", b"session", attrs, "now", "doc", proof, public);
}
```
