
Every input of `reduce_and_authenticate` and where the transcript absorbs
it (transcript I1 to I4):

- `session`: the composed statement it opened with, absorbed first: the
  application's identity message; a `Circuit` message per circuit (host
  circuit, adapter fragment, split circuit), whose ID hashes the whole
  circuit; both fields' `CommitmentLayout` (packing, cell counts, the split
  participant's storage runs and R's bits); the mode's `AdapterLayout`
  (mode ID, Q, tree shape, pads); `JointGeometry` (the profile); both
  fields' `PublicInputs`. The parsing geometry, the input layouts and the
  mode's claim widths are derived from these.
- `proof`: the body, parsed against the geometry the statement wrote; each
  interactive field is absorbed as its prover message where it is sent.
  The application's complete reader checks the seal over every byte.

The evaluation domains are the composition's own; the transcript does not
absorb them, and each participant rejects a domain other than the one it
was built with. There is no argument for a geometry, a circuit or public
inputs.

It is not complete verification, so it is crate-private, like the
composed statement it takes: only an application's complete verifier
(`run_mdoc_verifier`), which checks the seal, calls it.
