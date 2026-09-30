#!/usr/bin/env python3
"""Compare regenerated numerical quantities with the recorded focused baseline.

This is a numerical regression comparison, not a proof of the infinite-
dimensional spectral gap or a certified quadrature-error estimate.
"""
from pathlib import Path
import argparse
import csv
import hashlib
import json
import sys
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
BASELINE = ROOT / "numerics/results"
CSV_FILES = ["ritz_spectra.csv", "trial_quotients.csv", "linear_response_times.csv",
             "linear_response_spectral_weights.csv"]
FIGURES = ["collision_memory_picture", "resonance_geometry_3d", "preparation_memory_3d",
           "weak_time_response", "weak_physical_memory"]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_csv(path):
    with path.open() as stream:
        reader = csv.DictReader(stream)
        return reader.fieldnames, list(reader)


def compare_csv(name, actual_dir, rtol, atol):
    columns, expected = read_csv(BASELINE / name)
    new_columns, actual = read_csv(actual_dir / name)
    if columns != new_columns or len(expected) != len(actual):
        raise AssertionError(f"{name}: column or row-count mismatch")
    numeric_columns = []
    for column in columns:
        try:
            left = np.array([float(row[column]) for row in expected])
            right = np.array([float(row[column]) for row in actual])
        except ValueError:
            if [row[column] for row in expected] != [row[column] for row in actual]:
                raise AssertionError(f"{name}: categorical mismatch in {column}")
            continue
        if not np.all(np.isfinite(right)) or not np.allclose(left, right, rtol=rtol, atol=atol):
            idx = int(np.argmax(np.abs(left-right)))
            raise AssertionError(f"{name}: numeric mismatch in {column}, row {idx+1}: {left[idx]} vs {right[idx]}")
        numeric_columns.append(dict(column=column, maximum_absolute_difference=float(np.max(np.abs(left-right)))))
    return dict(file=name, rows=len(actual), columns=columns, comparisons=numeric_columns)


def compare_nested(expected, actual, rtol, atol, path):
    if isinstance(expected, dict):
        if set(expected) != set(actual):
            raise AssertionError(f"{path}: dictionary keys differ")
        for key in expected:
            compare_nested(expected[key], actual[key], rtol, atol, f"{path}.{key}")
    elif isinstance(expected, list):
        if len(expected) != len(actual):
            raise AssertionError(f"{path}: list lengths differ")
        for j, (left, right) in enumerate(zip(expected, actual)):
            compare_nested(left, right, rtol, atol, f"{path}[{j}]")
    elif isinstance(expected, (float, int)) and not isinstance(expected, bool):
        if not np.isclose(expected, actual, rtol=rtol, atol=atol):
            raise AssertionError(f"{path}: {expected} vs {actual}")
    elif expected != actual:
        raise AssertionError(f"{path}: values differ")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=ROOT / "generated/results")
    parser.add_argument("--figures-dir", type=Path, help="also require the five regenerated PDF/PNG pairs")
    parser.add_argument("--rtol", type=float, default=5e-8)
    parser.add_argument("--atol", type=float, default=5e-11)
    parser.add_argument("--report", type=Path, help="save a JSON report outside the recorded baseline")
    args = parser.parse_args()
    out = args.output_dir.resolve()
    if out == BASELINE.resolve():
        parser.error("Select regenerated results, not the recorded baseline itself.")
    provenance = json.loads((ROOT / "numerics/source-provenance.json").read_text())
    for entry in provenance["files"]:
        if sha(ROOT / entry["path"]) != entry["sha256"]:
            raise AssertionError(f"Recorded source/baseline hash changed: {entry['path']}")
    report = dict(status="passed", rtol=args.rtol, atol=args.atol, output_dir=str(out),
                  qualification="Numerical regression only; no certified continuum error or gap lower bound.",
                  csv=[compare_csv(name, out, args.rtol, args.atol) for name in CSV_FILES])

    # Generalized eigenvectors have arbitrary signs. Compare the reconstructed
    # physical spectrum and sign-invariant quantities rather than raw vectors.
    skipped = {"eigenvectors", "spectral_amplitudes"}
    npz_checks = []
    with np.load(BASELINE / "preparation_memory_galerkin.npz", allow_pickle=False) as old, \
         np.load(out / "preparation_memory_galerkin.npz", allow_pickle=False) as new:
        if set(old.files) != set(new.files):
            raise AssertionError("Reconstruction NPZ keys differ")
        for name in old.files:
            if name in skipped:
                continue
            left, right = old[name], new[name]
            if left.shape != right.shape or not np.all(np.isfinite(right)) or not np.allclose(left, right, rtol=args.rtol, atol=args.atol):
                raise AssertionError(f"Reconstruction mismatch in {name}")
            npz_checks.append(dict(array=name, maximum_absolute_difference=float(np.max(np.abs(left-right)))))
    report["reconstruction"] = npz_checks
    report["eigenvector_sign_dependent_arrays_excluded"] = sorted(skipped)

    old = json.loads((BASELINE / "linear_response_metadata.json").read_text())
    new = json.loads((out / "linear_response_metadata.json").read_text())
    compare_nested(old["plan"], new["plan"], args.rtol, args.atol, "response.plan")
    compare_nested(old["convergence"], new["convergence"], args.rtol, args.atol, "response.convergence")
    for j, (left, right) in enumerate(zip(old["runs"], new["runs"])):
        for field in ["d", "M", "n", "prepared_sin2", "checks", "C2_integrated_time"]:
            compare_nested(left[field], right[field], args.rtol, args.atol, f"response.runs[{j}].{field}")
    old = json.loads((BASELINE / "preparation_memory_metadata.json").read_text())
    new = json.loads((out / "preparation_memory_metadata.json").read_text())
    for field in ["configuration", "densities", "checks"]:
        compare_nested(old[field], new[field], args.rtol, args.atol, f"reconstruction.{field}")
    if args.figures_dir:
        figure_paths = [args.figures_dir / f"{name}.{suffix}" for name in FIGURES for suffix in ["pdf", "png"]]
        for path in figure_paths:
            if not path.is_file() or path.stat().st_size < 1000:
                raise AssertionError(f"Missing or empty regenerated figure: {path}")
        report["regenerated_figures"] = [str(path) for path in figure_paths]
    if args.report:
        destination = args.report.resolve()
        if destination == BASELINE.resolve() or BASELINE.resolve() in destination.parents:
            parser.error("The comparison report cannot overwrite the recorded baseline.")
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, OSError, ValueError) as error:
        print(f"Numerical comparison failed: {error}", file=sys.stderr)
        sys.exit(1)
