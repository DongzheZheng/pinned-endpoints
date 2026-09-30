"""Output paths shared by focused numerical experiments and plotting scripts."""
from pathlib import Path
import os

ROOT = Path(__file__).resolve().parents[1]
BASELINE = ROOT / "numerics" / "results"


def results_dir():
    out = Path(os.environ.get("PINNED_RESULTS_DIR", ROOT / "generated" / "results")).resolve()
    if out == BASELINE.resolve() or BASELINE.resolve() in out.parents:
        raise ValueError("Recomputed outputs cannot overwrite the recorded numerics/results baseline.")
    out.mkdir(parents=True, exist_ok=True)
    return out


def plot_results_dir():
    return Path(os.environ.get("PINNED_PLOT_RESULTS_DIR",
                os.environ.get("PINNED_RESULTS_DIR", BASELINE))).resolve()


def figures_dir():
    out = Path(os.environ.get("PINNED_FIGURES_DIR", ROOT / "generated" / "figures")).resolve()
    baseline_figures = (ROOT / "figures").resolve()
    if out == baseline_figures or baseline_figures in out.parents:
        raise ValueError("Regenerated figures cannot overwrite the recorded figures baseline.")
    out.mkdir(parents=True, exist_ok=True)
    return out


def checks_dir():
    out = Path(os.environ.get("PINNED_CHECKS_DIR", ROOT / "generated" / "checks")).resolve()
    out.mkdir(parents=True, exist_ok=True)
    return out
