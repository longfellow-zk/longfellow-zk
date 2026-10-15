#!/usr/bin/env python3
"""Run deterministic offline order sweeps; no production policy selection.

Usage: python3 run_traversal_sweep.py TEST_BINARY PHASE DATASET...
Phases: core, groups, components, shapes, roles, hybrid, component_shapes,
global_components, component_numeric, dictionary, final. Up to four independent
processes are used; these are size measurements, not runtime benchmarks.
"""
import concurrent.futures
import itertools
import os
from pathlib import Path
import subprocess
import sys


def configuration(phase):
    axes = list(itertools.permutations(range(3)))
    if phase == "dictionary":
        return "global", "abs", []
    if phase == "final":
        return "kind", "abs", ["lex0213_r5", "lex0213_r1"]
    if phase == "core":
        orders = [f"lex{a}{b}{c}3_r{r}" for a, b, c in axes for r in range(8)]
        for a, b, c in axes:
            orders += [f"gap{a}{b}{c}", f"relative{a}{b}{c}", f"hilbert{a}{b}{c}",
                       f"m{a}{b}_b1_k0_r0", f"m{a}{b}{c}_b1_k0_r0"]
        return "global,kind", "abs", orders
    if phase == "groups":
        orders = [f"lex{a}{b}{c}3_r{r}" for a, b, c in axes for r in (0, 5)]
        return "slot,kind_slot,coefficient,kind_coefficient", "abs", orders
    if phase == "components":
        orders = ["lex0213_r5", "lex0123_r0", "lex1203_r0", "lex2103_r0",
                  "m12_b1_k0_r0", "m012_b1_k0_r0", "hilbert120", "relative120"]
        return "bip0,bip1,whole", "abs,offset,rank", orders
    if phase == "shapes":
        orders = [f"lex{a}{b}{c}3_r{r}" for a, b, c in axes for r in (0, 5)]
        return "stencil,kind_stencil,kind_wiring,kind_arity", "abs", orders
    if phase == "roles":
        orders = [f"lex{a}{b}{c}3_r{r}" for a, b, c in axes for r in (0, 5)]
        return "role,kind_coeffclass,role_coeffclass,kind_assert", "abs", orders
    if phase == "hybrid":
        orders = [f"lex{a}{b}{c}3_r{r}" for a, b, c in axes for r in (0, 5)]
        return "hybrid,hybrid_arity,hybrid_coeffclass,hybrid_coefficient", "abs", orders
    if phase == "component_shapes":
        return ("kind_whole,whole_kind,kind_bip0,bip0_kind,kind_bip1,bip1_kind,kind_bipshape0,kind_bipshape1",
                "abs,offset,rank",
                ["lex0213_r5", "lex2013_r0", "m12_b1_k0_r0", "m012_b1_k0_r0"])
    if phase == "global_components":
        return ("kind_whole_one,whole_one_kind,kind_whole_nonzero,whole_nonzero_kind,kind_whole_one_nonzero,whole_one_nonzero_kind",
                "abs,offset", ["lex0213_r5", "lex2013_r0", "m12_b1_k0_r0"])
    if phase == "component_numeric":
        return ("kind_bip0,bip0_kind,kind_bip1,bip1_kind,kind_bipshape0,kind_bipshape1",
                "abs,offset", ["lex0213_r5", "lex2013_r0", "m12_b1_k0_r0"])
    raise ValueError(phase)


def main():
    binary, phase, *datasets = sys.argv[1:]
    contexts, norms, orders = configuration(phase)
    directory = Path(__file__).resolve().parent / "results"
    def run(dataset):
        env = {k: v for k, v in os.environ.items()
               if not k.startswith(("SWEEP_", "MORTON_", "MLDSA_"))}
        env.update(MORTON_ORDER_SWEEP="1", SWEEP_DATASET=dataset,
                   SWEEP_CONTEXTS=contexts, SWEEP_NORMS=norms,
                   SWEEP_EXTENDED="1", SWEEP_ORDERS=",".join(orders))
        if phase == "final":
            env.update(SWEEP_FINAL="1", SWEEP_LAYER_STATS="1",
                       SWEEP_SAVE_DIR=str(Path("target/traversal-circuits").resolve()))
        if phase == "dictionary":
            env["MORTON_DICTIONARY_SWEEP"] = "1"
        if phase == "component_numeric":
            env["SWEEP_COMPONENT_NUMERIC_MIN"] = "1"
        path = directory / f"traversal-{dataset}-{phase}.log"
        with path.open("w") as output:
            subprocess.run([str(Path(binary).resolve()), "--exact",
                            "all::mldsa_verifier::analyze_traversal_sweep",
                            "--ignored", "--nocapture", "--test-threads=1"],
                           env=env, stdout=output, stderr=subprocess.STDOUT, check=True)
        print(f"FINISHED {dataset} {phase}: {path}", flush=True)
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        list(pool.map(run, datasets))


if __name__ == "__main__":
    main()
