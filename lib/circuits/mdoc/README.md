Procedure for updating a circuit to ensure backwards compatibility.

## If the inputs and witnesses are the same, but the gates have changed

* Produce a new set of hashes and add them to zk_spec.
* Generate the files in `circuits/mdoc/circuits` using `circuit_maker`.
```
$ cmake -S lib -B build
$ cmake --build build --target circuit_maker
$ build/circuits/mdoc/circuit_maker --output_dir lib/circuits/mdoc/circuits --num_attributes 1
```
Run these commands from the repository root. The `circuit_maker` target is
available when CMake finds Abseil.

* Ensure that unit tests pass.

## If the inputs/witnesses have changed

* In addition to the above, the code that produces the witness and fills it
into the Dense object must branch on the version to properly create the prover
and verifier parameters.
