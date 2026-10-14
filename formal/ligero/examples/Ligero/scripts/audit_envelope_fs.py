#!/usr/bin/env python3
"""Build and audit every certified v7/v8 Ligero FS endpoint.

Run from any directory. Catalog geometry and coefficient exponents are checked
against Lean records, and transitive dependencies are checked against a narrow
allowlist of foundational axioms and the certificates' native arithmetic checks.
"""

import json
from pathlib import Path
import re
import subprocess
import tempfile


FORMAL = Path(__file__).resolve().parents[4]
CATALOG = FORMAL / "ligero/examples/Ligero/Longfellow"
OPTIMIZED = "Ligero.Examples.Grid.LongfellowProfiledExtraction.Optimized."
FOUNDATIONS = {"propext", "Classical.choice", "Quot.sound"}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def run_lean_tool(*args):
    result = subprocess.run(
        ["lake", *args], cwd=FORMAL, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False,
    )
    if result.returncode:
        raise RuntimeError(result.stdout)
    return result.stdout


def main():
    catalog = json.loads((CATALOG / "envelope-fs-certified-results.json").read_text())
    iop = json.loads((CATALOG / "optimized-iop-certified-results.json").read_text())
    rows = catalog["certificates"]
    require(catalog["fs_bound"] == "bindingError + min(1, (Q+1)*2^(-target_bits))",
            "Unexpected FS bound in catalog")
    require(catalog["fs_coefficient_bound"] ==
            "bindingError + min(1, (Q+1)*2^(-linear_fs_coefficient_bits))",
            "Unexpected coefficient interpretation")
    require(catalog["fs_compiler_theorem"] ==
            "Bcs.EnvelopeFiatShamir.FixedKey.extraction_ratio_le_capped",
            "Catalog points to the wrong compiler")
    expected = {f"v{version}{component}_v{variant}"
                for version in (7, 8)
                for component in ("Sig", "Hash1", "Hash2", "Hash3", "Hash4")
                for variant in (1, 2, 3)}
    require(len(rows) == 30 and {row["name"] for row in rows} == expected,
            "Catalog must contain all 30 distinct instances")
    source_rows = {row["name"]: row for row in iop["certificates"]}
    require(len(source_rows) == 30 and set(source_rows) == expected,
            "IOP and FS instance sets differ")

    parameters = json.loads((CATALOG / "v8-extracted-parameters.json").read_text())
    require(len(parameters) == 8, "Incomplete current-circuit parameter snapshot")
    for row in rows:
        if row["version"] != 8:
            continue
        require(row["source_parameter_file"] == "v8-extracted-parameters.json",
                f"Wrong current-circuit parameter source: {row['name']}")
        matching = [p for p in parameters if p["component"] == row["component"]
                    and p["attributes"] in row["attributes"]]
        require(len(matching) == len(row["attributes"]), "Missing source geometry")
        for parameter in matching:
            require(parameter["version"] == 8, "Wrong CURRENT version")
            mapping = {"n": "n", "k": "k", "d": "d_base", "openings": "queries",
                       "payload_width": "w", "field_order": "field_size",
                       "source_circuit_id": "circuit_id", "source_tree_sha256": "source_tree_sha256",
                       "block_enc": "block_enc", "rateinv": "rateinv"}
            for key, source_key in mapping.items():
                require(row[key] == parameter[source_key],
                        f"Current parameter mismatch: {row['name']}.{key}")
            k = (parameter["block_enc"] + 1) // (parameter["rateinv"] + 2)
            require(parameter["k"] == k and
                    parameter["n"] == parameter["block_enc"] - (2 * k - 1) and
                    parameter["w"] == k - parameter["queries"] and
                    parameter["d_base"] == parameter["n"] - k + 1,
                    "Invalid tableau-to-code conversion")
        require(row["registry_combined_ids"] == [p["registered_combined_id"] for p in matching]
                and row["generated_combined_ids"] == [p["generated_combined_id"] for p in matching]
                and row["combined_ids_match_registry"] ==
                    all(p["combined_id_matches_registry"] for p in matching),
                f"Incorrect circuit ID provenance: {row['name']}")

    core = [
        "CodingTheory.HahnDelsarte.hahnKernel_gram_nonneg",
        "CodingTheory.HahnDelsarte.card_le_of_delsarte",
        "CodingTheory.HahnDelsarte.uniformFamilyBound_of_certificate",
        "CodingTheory.UniformFamilyBound.of_le_size",
        "CodingTheory.card_le_of_uniformFamilyBound",
        "CodingTheory.InterleavedJohnson.uniformFamilyBound_of_denominator_pos",
        "CodingTheory.InterleavedJohnson.card_le_listBound",
        "Bcs.EnvelopeFiatShamir.ResponseUniformBound.strategy_bound",
        "Bcs.EnvelopeFiatShamir.responseBeforeSubset_congr",
        "Bcs.EnvelopeFiatShamir.responseBeforeSubset_eq",
        "Bcs.EnvelopeFiatShamir.FixedKey.gated_subset_slot_le",
        "Bcs.EnvelopeFiatShamir.FixedKey.injectAlpha_slot",
        "Bcs.EnvelopeFiatShamir.FixedKey.injectAlpha_alpha",
        "Bcs.EnvelopeFiatShamir.FixedKey.responseAt_congr",
        "Bcs.EnvelopeFiatShamir.FixedKey.responseAt_eq",
        "Bcs.EnvelopeFiatShamir.Linear.alphaSlot_gate_congr",
        "Bcs.EnvelopeFiatShamir.FixedKey.presampled_at_slot_le",
        "Bcs.EnvelopeFiatShamir.FixedKey.presampled_density_le",
        "Bcs.EnvelopeFiatShamir.FixedKey.extraction_density_le",
        "Bcs.EnvelopeFiatShamir.FixedKey.extraction_ratio_le_capped",
        "Bcs.EnvelopeFiatShamir.FixedKey.errorBound_dyadic",
        "LigeroFamily.EnvelopeFS.Experiment.compiledBound_dyadic",
        "LigeroFamily.EnvelopeFS.localBound_of_mean",
        "LigeroFamily.EnvelopeFS.accepts_of_binding",
        "LigeroFamily.EnvelopeFS.extraction_ratio_le",
        "LigeroFamily.EnvelopeFS.soundness_ratio_le",
    ]
    endpoints = []
    numeric_owners = set()
    checks = [
        "import examples.Ligero.Longfellow.EnvelopeFSCertificates",
        "set_option maxHeartbeats 2000000",
        "example (Q s : ℕ) : Bcs.EnvelopeFiatShamir.FixedKey.errorBound Q "
        "((1 : ℚ) / 2 ^ s) = min 1 ((Q + 1 : ℚ) / 2 ^ s) := "
        "Bcs.EnvelopeFiatShamir.FixedKey.errorBound_dyadic Q s",
    ]
    for row in rows:
        name = row["name"]
        source = source_rows[name]
        for key, value in source.items():
            require(row.get(key) == value, f"IOP catalog mismatch: {name}.{key}")
        bits = row["target_bits"]
        require(bits > 0 and row["linear_fs_coefficient_bits"] == bits,
                f"Incorrect linear FS coefficient: {name}")
        record = OPTIMIZED + name
        cert = record + ".certificate"
        checks.append(f"example : {record}.variant = .v{row['variant']} := rfl")
        checks.append(f"example : {cert}.targetBits = "
                      f"{row['linear_fs_coefficient_bits']} := rfl")
        fields = ("n", "k", "d", "e", "g", "m", "openings", "targetBits", "fieldSize",
                  "maskThreshold")
        values = [row[key] for key in ("n", "k", "d", "e", "g", "m", "openings",
                                      "target_bits", "field_order", "mask_threshold")]
        checks.append("example : ([" + ", ".join(f"{cert}.{key}" for key in fields) +
                      "] : List ℕ) = [" + ", ".join(map(str, values)) + "] := by native_decide")
        require(row["payload_width"] == row["k"] - row["openings"],
                f"Witness layout mismatch: {name}")
        for key, suffix in (("fs_local_contract", "fs_localBound"),
                            ("fs_extractor_theorem", "fs_extraction"),
                            ("fs_soundness_theorem", "fs_soundness")):
            require(row[key] == f"{record}_{suffix}", f"Wrong endpoint for {name}: {key}")
            endpoints.append(row[key])
        numeric_owners.update(record + suffix for suffix in
                              ("_parameters", "_compressed_bound"))

    readme = (FORMAL / "ligero/README.md").read_text()
    display_groups = (
        ("v7 signature (all attribute counts)", ("v7Sig",)),
        ("v7 hash (1–4 attributes)", ("v7Hash1", "v7Hash2", "v7Hash3", "v7Hash4")),
        ("v8 signature (all attribute counts)", ("v8Sig",)),
        ("v8 hash (1–4 attributes)", ("v8Hash1", "v8Hash2", "v8Hash3", "v8Hash4")),
    )
    by_name = {row["name"]: row for row in rows}
    for label, group in display_groups:
        values = []
        for variant in (1, 2, 3):
            bits = {by_name[f"{name}_v{variant}"]["linear_fs_coefficient_bits"]
                    for name in group}
            require(len(bits) == 1, f"Display group has different bounds: {label}")
            values.append(str(bits.pop()))
        require(f"| {label} | {' | '.join(values)} |" in readme,
                f"Incorrect FS coefficient table row: {label}")

    declarations = core + endpoints
    checks.extend(f"#print axioms {name}" for name in declarations)
    print("Building verifier bridges, operational tests, and numerical certificates…", flush=True)
    run_lean_tool("build", "Bcs.EnvelopeFiatShamirTest", "Ligero.APITest",
                  "examples.Ligero.Longfellow.EnvelopeFSCertificates")
    with tempfile.TemporaryDirectory(prefix="ligero-fs-audit-") as directory:
        audit = Path(directory) / "Audit.lean"
        audit.write_text("\n".join(checks) + "\n")
        output = run_lean_tool("env", "lean", str(audit))
    dependencies = re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]", output, re.S)
    require(len(dependencies) == len(declarations) and
            {name for name, _ in dependencies} == set(declarations),
            "Incomplete theorem dependency audit")
    native_dependencies = set()
    for name, body in dependencies:
        for dependency in body.split(","):
            dependency = dependency.strip()
            if dependency in FOUNDATIONS:
                continue
            owner, separator, _ = dependency.partition("._native.native_decide.ax_")
            require(name not in core and separator and owner in numeric_owners,
                    f"Unexpected dependency: {name} uses {dependency}")
            native_dependencies.add(dependency)
    print(f"Passed: {len(core)} core theorems, 90 FS endpoints,")
    print("30 catalog geometries and their linear coefficient exponents.")
    print(f"Core uses only foundational axioms; numerical endpoints use "
          f"{len(native_dependencies)} generated native arithmetic checks.")
    print("FS coefficient bits s: error <= bindingError + min(1, (Q+1)*2^(-s))")
    for version in (7, 8):
        for component in ("Sig", "Hash1", "Hash2", "Hash3", "Hash4"):
            values = [next(row["linear_fs_coefficient_bits"] for row in rows
                           if row["name"] == f"v{version}{component}_v{variant}")
                      for variant in (1, 2, 3)]
            print(f"v{version} {component}: V1={values[0]}, V2={values[1]}, V3={values[2]}")


if __name__ == "__main__":
    main()
