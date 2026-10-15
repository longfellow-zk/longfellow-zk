#!/usr/bin/env python3
"""Serial correctness checks, not a performance benchmark."""
import os
from pathlib import Path
import subprocess

PROVER = "target/release/deps/template_proofs-1eba8861353003c4"
FOLDS = "target/release/deps/morton_folds-270188b5b090fa0a"
OUT = Path("target/scheduling-segmentation-v1/validation")
PROFILES = [
    ("target/scheduling-segmentation-refine", "whole", "shape_classes", p)
    for p in ("reuse_window_64", "reuse_window_128", "reuse_cdc_128", "reuse_cdcstored_64")
] + [("target/scheduling-segmentation-v1", "role", t, s)
     for t, s in (("shape_classes", "reuse"), ("morton", "cdc_128"))]


def run(binary, test, env, log):
    clean = {k: v for k, v in os.environ.items() if not k.startswith(("ORDER_", "MLDSA_", "SWEEP_"))}
    clean.update(env)
    with log.open("w") as out:
        subprocess.run([binary, test, "--exact", "--ignored", "--nocapture"],
                       env=clean, stdout=out, stderr=subprocess.STDOUT, check=True)
    assert "test result: ok." in log.read_text(), log
    print("VERIFIED", log.name, flush=True)


if __name__ == "__main__":
    OUT.mkdir(exist_ok=True)
    for root, wire, traversal, segment in PROFILES:
        label = f"{wire}-{traversal}-{segment}"
        for name in ("mldsa44", "mldsa65"):
            path = Path(root) / name / f"{wire}-{traversal}" / (segment + ".lfc2")
            env = dict(ORDER_PROOF_CIRCUIT=str(path), ORDER_SUMCHECK="round" if traversal == "morton" else "hand",
                       ORDER_REPEATS="1", MLDSA_SLICE_PERIOD="4", MLDSA_FIRST_ROUND="1", MLDSA_PLUCKER_BITS="0")
            if wire == "whole":
                env["ORDER_EXPECT_PROOF"] = f"target/plucker-grid-sf18/p4-b0-r1/{name}/proof.bin"
            run(PROVER, name + "_template_proof", env, OUT / f"{name}-{label}.log")
        archive = Path(root) / "archives" / ("--".join((wire, traversal, segment)) + ".archive")
        env = dict(ORDER_MDOC_ARCHIVE=str(archive), ORDER_REPEATS="1", ORDER_ATTRS="2")
        if wire == "whole":
            env["ORDER_EXPECT_PROOF"] = "target/template-core-mdoc.proof"
        run(PROVER, "mdoc_template_proof", env, OUT / f"mdoc-{label}.log")
        if traversal == "morton":
            for name in ("mdoc_sig", "mdoc_hash2", "mldsa44", "mldsa65"):
                path = Path(root) / name / f"{wire}-{traversal}" / (segment + ".lfc2")
                run(FOLDS, "stored_morton_folds", dict(ORDER_DATASET=name, ORDER_PROOF_CIRCUIT=str(path)),
                    OUT / f"{name}-{label}-folds.log")
