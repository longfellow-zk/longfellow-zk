#!/usr/bin/env python3
"""Prove with ordinary hand-major runtime; require byte-identical baseline proofs.

These are serial correctness flows, not a controlled timing benchmark.
"""
from pathlib import Path
from validate_scheduling_sweep import run, PROVER

PROFILES = [("refine", p) for p in ("dictsuffix@reuse_cdc_128", "pair_cdc_repair_8192_prune",
                                  "pair_delta_repair_512_prune")]
PROFILES += [("factor", p) for p in ("dictbucketsuffix@extractprefix32@reuse_cdc_128",
                                    "dictbucketsuffix@extractprefix128@reuse_cdc_128",
                                    "dictbucketsuffix@extractboth8@reuse_cdc_128")]
OUT = Path("target/pair-segmentation-validation")

if __name__ == "__main__":
    OUT.mkdir(exist_ok=True)
    for suite, policy in PROFILES:
        root = Path("target/pair-segmentation-" + suite)
        for name in ("mldsa44", "mldsa65"):
            env = dict(ORDER_PROOF_CIRCUIT=str(root / name / "whole-shape_classes" / (policy + ".lfc2")),
                       ORDER_SUMCHECK="hand", ORDER_REPEATS="1", MLDSA_SLICE_PERIOD="4",
                       MLDSA_FIRST_ROUND="1", MLDSA_PLUCKER_BITS="0",
                       ORDER_EXPECT_PROOF=f"target/plucker-grid-sf18/p4-b0-r1/{name}/proof.bin")
            run(PROVER, name + "_template_proof", env, OUT / f"{name}-{policy}.log")
        env = dict(ORDER_MDOC_ARCHIVE=str(root / "archives" / f"whole--shape_classes--{policy}.archive"),
                   ORDER_REPEATS="1", ORDER_ATTRS="2", ORDER_EXPECT_PROOF="target/template-core-mdoc.proof")
        run(PROVER, "mdoc_template_proof", env, OUT / f"mdoc-{policy}.log")
