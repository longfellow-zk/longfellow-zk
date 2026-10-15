#!/usr/bin/env python3
"""Validate three-level outputs through their exact flattened LFC2 adapter.

This does not claim that the production prover reads L3E1 directly.
"""
from pathlib import Path
from validate_scheduling_sweep import run, PROVER

ROOT = Path("target/three-level-v1")
OUT = ROOT / "validation"
PROFILES = [("cdc", "factor_128_prune"), ("cdc", "top_64_suffix"), ("reuse", "two_32_128_prune")]

if __name__ == "__main__":
    OUT.mkdir(exist_ok=True)
    for seed, policy in PROFILES:
        for name in ("mldsa44", "mldsa65"):
            path = ROOT / name / seed / (policy + ".lfc2")
            env = dict(ORDER_PROOF_CIRCUIT=str(path), ORDER_SUMCHECK="hand", ORDER_REPEATS="1",
                       MLDSA_SLICE_PERIOD="4", MLDSA_FIRST_ROUND="1", MLDSA_PLUCKER_BITS="0",
                       ORDER_EXPECT_PROOF=f"target/plucker-grid-sf18/p4-b0-r1/{name}/proof.bin")
            run(PROVER, name + "_template_proof", env, OUT / f"{name}-{seed}-{policy}.log")
        archive = OUT / f"{seed}-{policy}.archive"
        env = dict(ORDER_SIG=str(ROOT / "mdoc_sig" / seed / (policy + ".lfc2")),
                   ORDER_HASH=str(ROOT / "mdoc_hash2" / seed / (policy + ".lfc2")),
                   ORDER_ATTRS="2", ORDER_SAVE_ARCHIVE=str(archive))
        run(PROVER, "mdoc_template_proof", env, OUT / f"archive-{seed}-{policy}.log")
        run(PROVER, "mdoc_template_proof", dict(ORDER_MDOC_ARCHIVE=str(archive), ORDER_REPEATS="1",
                                               ORDER_ATTRS="2", ORDER_EXPECT_PROOF="target/template-core-mdoc.proof"),
            OUT / f"mdoc-{seed}-{policy}.log")
