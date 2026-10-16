#!/usr/bin/env python3
"""Axiom audit for the separate graded and 116-bit v7 extraction targets."""

from __future__ import annotations

import re
import subprocess
import tempfile
from pathlib import Path

from audit_axioms import FOUNDATIONAL, NATIVE, NATIVE_AUX, keyword_hits


FORMAL = Path(__file__).resolve().parents[2]
LIGERO_NATIVE_AUX = re.compile(
    r"^Ligero\.[\w.']+\._native\.native_decide\.ax_\d+_\d+$"
)
GRADED_PRIVATE_NATIVE_AUX = re.compile(
    r"^Lfzk\.GradedV7Hash\.weight_(?:nonneg|total)\._native\.native_decide\.ax_\d+_\d+✝$"
)
V1_STRONG_NATIVE_AUX = re.compile(
    r"^Lfzk\.V1Strong[\w.']+\._native\.native_decide\.ax_\d+(?:_\d+)?$"
)
THEOREMS = [
    "Bcs.TotalOracle.CtxGrinding.potential_ratio_le_rat",
    "Lfzk.CompiledZkDeployedHash.compiled_twoFieldPotential_fs_extraction_budgeted",
    "Lfzk.CompiledZkProfileRows.v7_circuit_potential_extraction_115",
    "Lfzk.CompiledZkProfileRows.v7_circuit_potential_extraction_116_of_pos_queries",
    "Lfzk.CompiledZkProfileRows.v8_circuit_potential_extraction_115",
    "Lfzk.V1StrongV7Interactive.v7_v1_payload_iop_uniform_failure_le",
    "Lfzk.V1StrongV7Interactive.v7_v1_payload_iop_uniform_acceptance_of_noDecoded_le",
    "Lfzk.V1StrongV7Hash1HybridFS.flatEvent_hybrid_fs_ratio_le_116_circuit_typed",
    "Lfzk.V1StrongV7Hash1HybridFS.falseStatement_hybrid_fs_ratio_le_116_circuit_typed",
] + [
    f"Lfzk.CompiledZk.{module}.v7Hash{i}_{suffix}"
    for i, module in (
        (1, "FlatV7Headline"),
        (2, "FlatV7Hash2Headline"),
        (3, "FlatV7Hash3Headline"),
        (4, "FlatV7Hash4Headline"),
    )
    for suffix in (
        "deployed_fs_extraction_116_circuit",
        "deployed_fs_false_statement_116",
    )
]


def main() -> int:
    with tempfile.TemporaryDirectory() as directory:
        source = Path(directory) / "AuditFlatV7.lean"
        source.write_text(
            "import Lfzk.FlatV7All\nimport Lfzk.GradedCircuitGrid\n"
            "import Lfzk.V1StrongV7Interactive\n"
            "import Lfzk.V1StrongV7Hash1HybridCircuitHeadline\n"
            + "".join(f"#print axioms {name}\n" for name in THEOREMS)
        )
        result = subprocess.run(
            ["lake", "env", "lean", str(source)],
            cwd=FORMAL, text=True, capture_output=True,
        )
    if result.returncode:
        print(result.stdout[-4000:], result.stderr[-4000:])
        return 1

    seen = set()
    failed = False
    for record in re.split(r"\n(?=')", result.stdout.strip()):
        record = " ".join(record.split())
        match = re.fullmatch(r"'([^']+)' depends on axioms: \[(.*)\]", record)
        if match:
            name = match.group(1)
            axioms = {a.strip() for a in match.group(2).split(",") if a.strip()}
            allowed = FOUNDATIONAL | NATIVE | {
                a for a in axioms if NATIVE_AUX.match(a) or LIGERO_NATIVE_AUX.match(a)
                or GRADED_PRIVATE_NATIVE_AUX.match(a)
                or V1_STRONG_NATIVE_AUX.match(a)
            }
            extra = axioms - allowed
        else:
            match = re.fullmatch(r"'([^']+)' does not depend on any axioms", record)
            name = match.group(1) if match else "<unparsed>"
            extra = set() if match else {record}
        seen.add(name)
        failed |= bool(extra)
        print(f"{'FAIL' if extra else 'ok  '} {name}" + (f": {sorted(extra)}" if extra else ""))

    missing = set(THEOREMS) - seen
    if missing:
        failed = True
        print("FAIL missing declarations:", sorted(missing))
    hits = keyword_hits()
    if hits:
        failed = True
        print("FAIL sorry/axiom/admit in code:", *hits, sep="\n")
    else:
        print("ok   no sorry/axiom/admit in lfzk, bcs, merkle, sumcheck")
    return int(failed)


if __name__ == "__main__":
    raise SystemExit(main())
