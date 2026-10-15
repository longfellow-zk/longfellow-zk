#!/usr/bin/env python3
"""Axiom audit for the Longfellow NIZK development.

Runs `#print axioms` on every headline theorem and checks that each depends only on Lean's
foundational axioms (`propext`, `Classical.choice`, `Quot.sound`), plus — for the theorems stated
at a certified row — the `native_decide` auxiliaries that the row's own `native_decide` checks
own (`Lean.ofReduceBool`, and in Lean 4.31 the per-call `<decl>._native.native_decide.ax_i_j`).
Long axiom lists are wrapped over several lines by `#print axioms`; records are re-joined before
parsing, and any record that does not parse, or any headline that is not printed, fails the audit.
Also scans the four libraries' code (comments and docstrings excluded) for `sorry`, `admit` and
`axiom` declarations.

    python3 lfzk/scripts/audit_axioms.py          # from formal/
"""
from __future__ import annotations

import re
import subprocess
import sys
import tempfile
from pathlib import Path

FORMAL = Path(__file__).resolve().parents[2]

FOUNDATIONAL = {"propext", "Classical.choice", "Quot.sound"}
NATIVE = {"Lean.ofReduceBool"}

# theorem -> native_decide allowed?
HEADLINES = {
    # Ligero V1, round by round
    "Ligero.V1.ligerov1_roundByRound_profiled": False,
    "Lfzk.LigeroV1Rows.Row.rbr_soundness": False,
    "Lfzk.LigeroV1Rows.v8Hash_valid": True,
    "Lfzk.LigeroV1Rows.v8Sig_valid": True,
    # the sequential composed theorem
    "Lfzk.CertifiedV1.Row.nizk_ratio_le": False,
    "Lfzk.CertifiedV1.Row.nizk_ratio_le_family": False,
    "Lfzk.CertifiedV1.v8Hash_nizk_ratio_le": True,
    # grinding, re-committing, compiled
    "Lfzk.CertifiedV1.Row.fs_ratio_le_bound": False,
    "Lfzk.CertifiedV1.v8Hash_fs_ratio_le": True,
    "Lfzk.CertifiedV1.Row.adaptive_ratio_le": False,
    "Lfzk.CertifiedV1.v8Hash_adaptive_ratio_le": True,
    "Lfzk.CompiledLongfellow.hright_v1": False,
    "Lfzk.CompiledLongfellow.v8Hash_compiled_fs_ratio_le": True,
    # two-field
    "Lfzk.TwoField.twofield_soundness": False,
    "Lfzk.TwoFieldV1Rows.TwoFieldRowV1.nizk_ratio_le": False,
    "Lfzk.TwoFieldV1Rows.p256sha_nizk_ratio_le_keyFirst": True,
    "Lfzk.NizkGrindingTwoField.p256sha_fs_ratio_le_keyFirst": True,
    "Lfzk.NizkAdaptiveTwoField.p256sha_adaptive_ratio_le": True,
    "Lfzk.CompiledLongfellowTwoField.p256sha_compiled_fs_ratio_le_keyFirst": True,
    # the compiled verifier against a re-committing prover, `hlig` and `hright` discharged
    "Lfzk.CompiledLongfellowAdaptive.exists_msgLigeroData": False,
    "Lfzk.CompiledLongfellowAdaptive.hright_v1": False,
    "Lfzk.CompiledLongfellowAdaptive.CompiledSide.hright": False,
    "Lfzk.CompiledLongfellowAdaptive.row_adaptive_ratio_le_v1": False,
    "Lfzk.CompiledLongfellowAdaptive.v8Hash_adaptive_compiled_ratio_le": True,
    "Lfzk.CompiledLongfellowAdaptive.twofield_adaptive_compiled_ratio_le": False,
    "Lfzk.CompiledLongfellowAdaptive.p256sha_adaptive_compiled_ratio_le": True,
    # zero knowledge: Ligero V1, the composed compiled argument, two-field, v7 numerals
    "Lfzk.FromLigeroZK.V1.isLigeroZeroKnowledge_v1": False,
    "Lfzk.CompiledLigeroZk.v1_compiled_zk_bits256_q115": False,
    "Lfzk.ZkAdaptiveV1.statClose_adaptive": False,
    "Lfzk.ZkAdaptiveV1.toSim_response": False,
    "Lfzk.ZkAdaptiveV1.linCorr_unique": False,
    "Lfzk.CompiledLongfellowZk.compiled_longfellow_zk": False,
    "Lfzk.CompiledLongfellowZk.compiled_longfellow_zk_bits256": False,
    "Lfzk.CompiledLongfellowZk.compiled_longfellow_zk_bits256_q115": False,
    "Lfzk.CompiledLongfellowZk.compiled_longfellow_wi": False,
    "Lfzk.CompiledLongfellowZkTwoField.twofield_wi": False,
    "Lfzk.ZkFrontendOfSetup.compiled_longfellow_zk_of_setup": False,
    "Lfzk.CompiledLongfellowZkTwoField.twofield_zk": False,
    "Lfzk.CompiledLongfellowZkV7.row_compiled_zk": False,
    "Lfzk.CompiledLongfellowZkV7.v7Sig_compiled_zk": False,
    "Lfzk.CompiledLongfellowZkV7.v7Hash4_compiled_zk": False,
    "Lfzk.CompiledLongfellowZkV7.twofield_zk_bits256": False,
    "Lfzk.CompiledLongfellowZkV7.v7_twofield_zk_q115": False,
    "Lfzk.ZkMerkleStat.leaf_statClose": False,
    "Lfzk.ZkMerkleStat.digests_statClose": False,
    "Lfzk.ZkMerkleStat.view_statClose": False,
    "Lfzk.CompiledLongfellowZkStat.compiled_longfellow_zk_stat": False,
    "Lfzk.CompiledLongfellowZkStat.twofield_zk_stat": False,
    "Lfzk.CompiledLongfellowZkStat.v7_twofield_zk_stat542": False,
    # Fiat–Shamir at deployed hash inputs (message prefixes, total random oracle)
    "Bcs.TotalOracle.card_coord_le_const": False,
    "Bcs.TotalOracle.CtxGrinding.ratio_le": False,
    "Bcs.TotalOracle.Grinding.ratio_le": False,
    "Bcs.TotalOracleCommit.Setup.ratio_le": False,
    "Bcs.TotalOracleCommit.Setup.ratio_le_two": False,
    "Lfzk.NizkDeployedHash.row_fs_ratio_le_bound": False,
    "Lfzk.NizkDeployedHash.v8Hash_fs_ratio_le": True,
    "Lfzk.NizkDeployedHashAdaptive.row_adaptive_ratio_le": False,
    "Lfzk.NizkDeployedHashAdaptive.row_adaptive_ratio_le_v1": False,
    "Lfzk.NizkDeployedHashAdaptive.v8Hash_adaptive_compiled_ratio_le": True,
    "Lfzk.NizkDeployedHashTwoField.twofield_adaptive_compiled_ratio_le": False,
    "Lfzk.NizkDeployedHashTwoField.p256sha_adaptive_compiled_ratio_le": True,
    "Lfzk.NizkDeployedHashV7.v7Sig_fs_ratio_le": True,
    "Lfzk.NizkDeployedHashV7.v7Hash1_fs_ratio_le": True,
    "Lfzk.NizkDeployedHashV7.v7Hash2_fs_ratio_le": True,
    "Lfzk.NizkDeployedHashV7.v7Hash3_fs_ratio_le": True,
    "Lfzk.NizkDeployedHashV7.v7Hash4_fs_ratio_le": True,
    "Lfzk.NizkDeployedHashV7.v7Sig_adaptive_ratio_le": True,
    "Lfzk.NizkDeployedHashV7.v7Hash1_adaptive_ratio_le": True,
    "Lfzk.NizkDeployedHashV7.v7Hash2_adaptive_ratio_le": True,
    "Lfzk.NizkDeployedHashV7.v7Hash3_adaptive_ratio_le": True,
    "Lfzk.NizkDeployedHashV7.v7Hash4_adaptive_ratio_le": True,
    "Lfzk.NizkDeployedHashV7.v7Sig_adaptive_compiled_ratio_le": True,
    "Lfzk.NizkDeployedHashV7.v7Hash1_adaptive_compiled_ratio_le": True,
    "Lfzk.NizkDeployedHashV7.v7Hash2_adaptive_compiled_ratio_le": True,
    "Lfzk.NizkDeployedHashV7.v7Hash3_adaptive_compiled_ratio_le": True,
    "Lfzk.NizkDeployedHashV7.v7Hash4_adaptive_compiled_ratio_le": True,
    "Lfzk.NizkDeployedHashV7.v7P256Sha1_adaptive_compiled_ratio_le": True,
    "Lfzk.NizkDeployedHashV7.v7P256Sha2_adaptive_compiled_ratio_le": True,
    "Lfzk.NizkDeployedHashV7.v7P256Sha3_adaptive_compiled_ratio_le": True,
    "Lfzk.NizkDeployedHashV7.v7P256Sha4_adaptive_compiled_ratio_le": True,
    # soundness against the deployed ZK verifier, the list factor at field slots only, and the
    # concrete arithmetization
    "Lfzk.RbrLayerStepS.layerStep_ratio_le_mixed": False,
    "Lfzk.RbrSplitS.FieldData.ratio_leS": False,
    "Lfzk.CertifiedV1.Row.adaptive_ratio_leS": False,
    "Lfzk.NizkAdaptiveTwoField.twofield_adaptive_ratio_leS": False,
    "Lfzk.CompiledLongfellowAdaptive.row_adaptive_ratio_le_v1S": False,
    "Lfzk.CompiledLongfellowAdaptive.twofield_adaptive_compiled_ratio_leS": False,
    "Lfzk.RbrZkSplit.ZkFieldData.ratio_le": False,
    "Lfzk.RbrZkSplit.hinit_of_output": False,
    "Lfzk.CertifiedV1.Row.zk_adaptive_ratio_le": False,
    "Lfzk.CompiledZk.hright_zk": False,
    "Lfzk.CompiledZk.row_zk_compiled_ratio_le": False,
    "Lfzk.NizkZkTwoField.twofield_zk_adaptive_ratio_le": False,
    "Lfzk.CompiledZk.CompiledZkSide.hright": False,
    "Lfzk.CompiledZk.twofield_zk_compiled_ratio_le": False,
    "Lfzk.ZkArithInit.outExt_ne": False,
    "Lfzk.ZkArithInit.zk_hinit": False,
    "Lfzk.ZkArithInit.zkBoundaryOf": False,
    "Lfzk.ZkArithInit.zkFieldDataOf": False,
    "Lfzk.Arith.QuadCircuit.toLayered": False,
    "Lfzk.Arith.QuadCircuit.toLayered_input_wMle": False,
    "Lfzk.Arith.QuadCircuit.unsat_iff": False,
    "Lfzk.Arith.QuadCircuit.toLayered_unsat_iff": False,
    "Lfzk.Arith.QuadCircuit.toLayered_eqqAgree": False,
    "Lfzk.Arith.QuadCircuit.top_harith": False,
    "Lfzk.Arith.Cex.output_only_false": False,
    "Lfzk.Arith.fieldData_harith_false": False,
    "Lfzk.CompiledLongfellowAdaptive.v8Hash_adaptive_compiled_ratio_leS": True,
    "Lfzk.CompiledLongfellowAdaptive.v8Sig_adaptive_compiled_ratio_leS": True,
    "Lfzk.CompiledLongfellowAdaptive.p256sha_adaptive_compiled_ratio_leS": True,
    "Lfzk.CompiledLongfellowAdaptive.v7Sig_adaptive_compiled_ratio_leS": True,
    "Lfzk.CompiledLongfellowAdaptive.v7Hash1_adaptive_compiled_ratio_leS": True,
    "Lfzk.CompiledLongfellowAdaptive.v7Hash2_adaptive_compiled_ratio_leS": True,
    "Lfzk.CompiledLongfellowAdaptive.v7Hash3_adaptive_compiled_ratio_leS": True,
    "Lfzk.CompiledLongfellowAdaptive.v7Hash4_adaptive_compiled_ratio_leS": True,
    "Lfzk.CompiledLongfellowAdaptive.v7P256Sha1_adaptive_compiled_ratio_leS": True,
    "Lfzk.CompiledLongfellowAdaptive.v7P256Sha2_adaptive_compiled_ratio_leS": True,
    "Lfzk.CompiledLongfellowAdaptive.v7P256Sha3_adaptive_compiled_ratio_leS": True,
    "Lfzk.CompiledLongfellowAdaptive.v7P256Sha4_adaptive_compiled_ratio_leS": True,
    "Lfzk.CompiledZk.v7Hash1_zk_compiled_ratio_le": True,
    "Lfzk.CompiledZk.v7Hash2_zk_compiled_ratio_le": True,
    "Lfzk.CompiledZk.v7Hash3_zk_compiled_ratio_le": True,
    "Lfzk.CompiledZk.v7Hash4_zk_compiled_ratio_le": True,
    "Lfzk.CompiledZk.v7Sig_zk_compiled_ratio_le": True,
    "Lfzk.CompiledZk.v8Hash_zk_compiled_ratio_le": True,
    "Lfzk.CompiledZk.v8Sig_zk_compiled_ratio_le": True,
    "Lfzk.CompiledZk.v7P256Sha1_zk_compiled_ratio_le": True,
    "Lfzk.CompiledZk.v7P256Sha2_zk_compiled_ratio_le": True,
    "Lfzk.CompiledZk.v7P256Sha3_zk_compiled_ratio_le": True,
    "Lfzk.CompiledZk.v7P256Sha4_zk_compiled_ratio_le": True,
    "Lfzk.CompiledZk.p256sha_zk_compiled_ratio_le": True,
    # the deployed zero-knowledge verifier at deployed hash inputs
    "Lfzk.NizkZkDeployedHash.zkChain_doomed_congr": False,
    "Lfzk.NizkZkDeployedHash.row_zk_deployed_adaptive_ratio_le": False,
    "Lfzk.NizkZkDeployedHash.twofield_zk_deployed_adaptive_ratio_le": False,
    "Lfzk.CompiledZkDeployedHash.zkBuilt_congr": False,
    "Lfzk.CompiledZkDeployedHash.hright_zkDH": False,
    "Lfzk.CompiledZkDeployedHash.row_zk_deployed_ratio_le": False,
    "Lfzk.CompiledZk.CompiledZkSide.hrightDH": False,
    "Lfzk.CompiledZkDeployedHash.twofield_zk_deployed_ratio_le": False,
    "Lfzk.CompiledZkDeployedHash.v7Hash1_zk_deployed_ratio_le": True,
    "Lfzk.CompiledZkDeployedHash.v7Hash2_zk_deployed_ratio_le": True,
    "Lfzk.CompiledZkDeployedHash.v7Hash3_zk_deployed_ratio_le": True,
    "Lfzk.CompiledZkDeployedHash.v7Hash4_zk_deployed_ratio_le": True,
    "Lfzk.CompiledZkDeployedHash.v7Sig_zk_deployed_ratio_le": True,
    "Lfzk.CompiledZkDeployedHash.v7P256Sha1_zk_deployed_ratio_le": True,
    "Lfzk.CompiledZkDeployedHash.v7P256Sha2_zk_deployed_ratio_le": True,
    "Lfzk.CompiledZkDeployedHash.v7P256Sha3_zk_deployed_ratio_le": True,
    "Lfzk.CompiledZkDeployedHash.v7P256Sha4_zk_deployed_ratio_le": True,
    # the arithmetization at the deployed width profile, and the end-to-end v7 headlines
    "Lfzk.ZkArithProfile.cube_sum_hands": False,
    "Lfzk.ZkArithProfile.lpoly_rel": False,
    "Lfzk.ZkArithProfile.lpoly_quadratic": False,
    "Lfzk.ZkArithProfile.cPendP_round": False,
    "Lfzk.ZkArithProfile.zk_hinitP": False,
    "Lfzk.ZkArithProfile.zkBoundaryP": False,
    "Lfzk.ZkArithProfile.zkFieldDataP": False,
    "Lfzk.ZkArithProfile.zkFieldDataP_exactAt": False,
    "Lfzk.CompiledZkProfileRows.row_zk_deployed_circuit_ratio_le": False,
    "Lfzk.CompiledZk.CircuitSide.toSide": False,
    "Lfzk.CompiledZkProfileRows.v7Hash1_zk_circuit_ratio_le": True,
    "Lfzk.CompiledZkProfileRows.v7Hash2_zk_circuit_ratio_le": True,
    "Lfzk.CompiledZkProfileRows.v7Hash3_zk_circuit_ratio_le": True,
    "Lfzk.CompiledZkProfileRows.v7Hash4_zk_circuit_ratio_le": True,
    "Lfzk.CompiledZkProfileRows.v7Sig_zk_circuit_ratio_le": True,
    "Lfzk.CompiledZkProfileRows.v7P256Sha1_zk_circuit_ratio_le": True,
    "Lfzk.CompiledZkProfileRows.v7P256Sha2_zk_circuit_ratio_le": True,
    "Lfzk.CompiledZkProfileRows.v7P256Sha3_zk_circuit_ratio_le": True,
    "Lfzk.CompiledZkProfileRows.v7P256Sha4_zk_circuit_ratio_le": True,
    # no Merkle-query budget: the uncapped chain and T-security
    "Lfzk.NizkZkDeployedHash.row_zk_deployed_adaptive_ratio_leT": False,
    "Lfzk.NizkZkDeployedHash.twofield_zk_deployed_adaptive_ratio_leT": False,
    "Lfzk.CompiledZkDeployedHash.row_zk_deployed_ratio_leT": False,
    "Lfzk.CompiledZkDeployedHash.twofield_zk_deployed_ratio_leT": False,
    "Lfzk.CompiledZkProfileRows.row_zk_deployed_circuit_ratio_leT": False,
    "Lfzk.TSec.tsec_real": False,
    "Lfzk.TSec.tsec_of_uncapped": False,
    "Lfzk.TSec.row_tsec": False,
    "Lfzk.TSec.twofield_tsec": False,
    "Lfzk.CompiledZkProfileRows.v7Hash1_zk_circuit_tsec": True,
    "Lfzk.CompiledZkProfileRows.v7Hash2_zk_circuit_tsec": True,
    "Lfzk.CompiledZkProfileRows.v7Hash3_zk_circuit_tsec": True,
    "Lfzk.CompiledZkProfileRows.v7Hash4_zk_circuit_tsec": True,
    "Lfzk.CompiledZkProfileRows.v7Sig_zk_circuit_tsec": True,
    "Lfzk.CompiledZkProfileRows.v7P256Sha1_zk_circuit_tsec": True,
    "Lfzk.CompiledZkProfileRows.v7P256Sha2_zk_circuit_tsec": True,
    "Lfzk.CompiledZkProfileRows.v7P256Sha3_zk_circuit_tsec": True,
    "Lfzk.CompiledZkProfileRows.v7P256Sha4_zk_circuit_tsec": True,
}


# the deployed-v7 rows and the v8 headlines restated at them (`LigeroV1RowsV7`, `CertifiedV7`,
# `TwoFieldV7Rows`, `CompiledV7`)
V7_SIDES = ["v7Sig", "v7Hash1", "v7Hash2", "v7Hash3", "v7Hash4"]
V7_PAIRS = ["v7P256Sha1", "v7P256Sha2", "v7P256Sha3", "v7P256Sha4"]

HEADLINES.update({
    "Lfzk.CertifiedV1.Row.fs_rhs_le_of": False,
    "Lfzk.CertifiedV1.Row.adaptive_rhs_le_of_slack": False,
    "Lfzk.TwoFieldV1Rows.TwoFieldRowV1.adaptive_rhs_le_of_slack": False,
})
for s in V7_SIDES:
    HEADLINES.update({
        f"Lfzk.LigeroV1Rows.{s}_valid": True,
        f"Lfzk.LigeroV1Rows.{s}_sharp": True,
        f"Lfzk.CertifiedV1.{s}_valid": True,
        f"Lfzk.CertifiedV1.{s}_sharp": True,
        f"Lfzk.CertifiedV1.{s}_adaptive_rhs_le": True,
        f"Lfzk.CertifiedV1.{s}_fs_rhs_le": True,
        f"Lfzk.CertifiedV1.{s}_nizk_ratio_le": True,
        f"Lfzk.CertifiedV1.{s}_fs_ratio_le": True,
        f"Lfzk.CertifiedV1.{s}_adaptive_ratio_le": True,
        f"Lfzk.CompiledLongfellow.{s}_compiled_fs_ratio_le": True,
        f"Lfzk.CompiledLongfellowAdaptive.{s}_adaptive_compiled_ratio_le": True,
    })
for p in V7_PAIRS:
    HEADLINES.update({
        f"Lfzk.TwoFieldV1Rows.{p}_valid": True,
        f"Lfzk.TwoFieldV1Rows.{p}_sharp": True,
        f"Lfzk.TwoFieldV1Rows.{p}_premises_satisfiable": True,
        f"Lfzk.TwoFieldV1Rows.{p}_adaptive_rhs_le": True,
        f"Lfzk.TwoFieldV1Rows.{p}_nizk_ratio_le_keyFirst": True,
        f"Lfzk.NizkAdaptiveTwoField.{p}_adaptive_ratio_le": True,
        f"Lfzk.CompiledLongfellowAdaptive.{p}_adaptive_compiled_ratio_le": True,
    })


# Lean 4.31's `native_decide` owns one auxiliary axiom per call, `<decl>._native.native_decide.ax_i_j`
NATIVE_AUX = re.compile(r"^Lfzk\.[\w.']+\._native\.native_decide\.ax_\d+_\d+$")


def strip_comments(text: str) -> str:
    """Drop `--` line comments, nested `/- … -/` block comments (docstrings included) and string
    literals, so that the keyword scan below only sees code."""
    out, i, depth, n = [], 0, 0, len(text)
    while i < n:
        if depth:
            if text.startswith("/-", i):
                depth, i = depth + 1, i + 2
            elif text.startswith("-/", i):
                depth, i = depth - 1, i + 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("/-", i):
            depth, i = 1, i + 2
        elif text.startswith("--", i):
            while i < n and text[i] != "\n":
                i += 1
        elif text[i] == '"':
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def keyword_hits() -> list[str]:
    hits = []
    for lib in ("lfzk", "bcs", "merkle", "sumcheck"):
        for f in sorted((FORMAL / lib).rglob("*.lean")):
            code = strip_comments(f.read_text())
            for k, line in enumerate(code.splitlines(), 1):
                if re.search(r"\b(sorry|admit)\b", line) or re.match(r"\s*(private\s+)?axiom\b", line):
                    hits.append(f"{f.relative_to(FORMAL)}:{k}: {line.strip()}")
    return hits


def main() -> int:
    bad = 0
    with tempfile.TemporaryDirectory() as d:
        src = Path(d) / "Audit.lean"
        src.write_text("import Lfzk\n" + "".join(f"#print axioms {t}\n" for t in HEADLINES))
        out = subprocess.run(["lake", "env", "lean", str(src)], cwd=FORMAL, text=True,
                             capture_output=True)
        if out.returncode != 0:
            print(out.stdout[-4000:], out.stderr[-4000:])
            return 1
    seen = set()
    # `#print axioms` wraps long lists over several lines: one record per line starting with `'`
    for rec in re.split(r"\n(?=')", out.stdout.strip()):
        rec = " ".join(rec.split())
        m = re.match(r"^'([^']+)' depends on axioms: \[(.*)\]$", rec)
        if not m:
            m2 = re.match(r"^'([^']+)' does not depend on any axioms$", rec)
            if m2:
                seen.add(m2.group(1))
                print(f"ok     {m2.group(1)}: no axioms")
                continue
            bad += 1
            print("FAIL  unparsed output:", rec)
            continue
        name, axioms = m.group(1), {a.strip() for a in m.group(2).split(",") if a.strip()}
        seen.add(name)
        native = ({a for a in axioms if NATIVE_AUX.match(a)} | (axioms & NATIVE)
                  if HEADLINES.get(name) else set())
        extra = axioms - FOUNDATIONAL - native
        if extra:
            bad += 1
        status = "ok    " if not extra else "FAIL  "
        shown = sorted(axioms & FOUNDATIONAL) + ([f"+{len(native)} native_decide row facts"]
                                                 if native else [])
        print(f"{status} {name}: {shown}" + (f" EXTRA {sorted(extra)}" if extra else ""))
    missing = set(HEADLINES) - seen
    if missing:
        bad += 1
        print("FAIL  not printed:", sorted(missing))
    hits = keyword_hits()
    if hits:
        bad += 1
        print("FAIL  sorry/axiom/admit in code:")
        print("\n".join(hits))
    else:
        print("ok     no sorry/axiom/admit in lfzk, bcs, merkle, sumcheck (comments excluded)")
    print(f"audit of {len(HEADLINES)} declarations", "FAILED" if bad else "passed")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
