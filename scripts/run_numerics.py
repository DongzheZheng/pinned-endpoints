#!/usr/bin/env python3
"""Recompute the focused numerical experiments and five manuscript figures."""
from pathlib import Path
import argparse
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=ROOT / "generated" / "results")
    parser.add_argument("--figures-dir", type=Path, default=ROOT / "generated" / "figures")
    args = parser.parse_args()
    out, figs = args.output_dir.resolve(), args.figures_dir.resolve()
    for output, baseline in [(out, ROOT / "numerics/results"), (figs, ROOT / "figures")]:
        baseline = baseline.resolve()
        if output == baseline or baseline in output.parents:
            parser.error("Choose an output directory outside the tracked recorded baselines.")
    env = os.environ.copy()
    env.update(PINNED_RESULTS_DIR=str(out), PINNED_PLOT_RESULTS_DIR=str(out),
               PINNED_FIGURES_DIR=str(figs), PINNED_CHECKS_DIR=str(out.parent / "checks"),
               PYTHONDONTWRITEBYTECODE="1")
    for name in ["OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "MKL_NUM_THREADS"]:
        env.setdefault(name, "1")
    programs = ["numerics/endpoint_spectrum.py", "numerics/linear_response.py",
                "scripts/preparation_memory.py", "scripts/manuscript_figures.py",
                "scripts/three_d_resonance.py"]
    for program in programs:
        print(f"Running {program}", flush=True)
        subprocess.run([sys.executable, str(ROOT / program)], cwd=ROOT, env=env, check=True)
    print(f"Results: {out}\nFigures: {figs}")
    print("Compare against recorded results with:")
    print(f'{sys.executable} scripts/check_numerics.py --output-dir "{out}"')


if __name__ == "__main__":
    main()
