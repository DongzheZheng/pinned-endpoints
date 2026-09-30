# Reproducing narrow-band spectral memory

The experiments study linear spectral memory in the one-dimensional pinned four-wave collision system. The collision integrals are evaluated on the exact nontrivial resonance branch. The entropy mass matrix is used, and the two exact collision-invariant directions, the constant and the frequency, are projected out. The Python calculations produce decay rates, spectral-moment responses and occupation-spectrum reconstructions in finite Galerkin spaces. The complete invariant classification is proved separately by the Lean development.

## Environment and complete run

The recorded environment uses Python 3.14.2. Dependency versions are pinned in `numerics/requirements.txt`; installing these Python packages does not require or invoke Lean.

```bash
python -m venv .venv
.venv/bin/python -m pip install -r numerics/requirements.txt
OPENBLAS_NUM_THREADS=1 .venv/bin/python scripts/run_numerics.py
.venv/bin/python scripts/check_numerics.py \
  --output-dir generated/results --figures-dir generated/figures
```

`run_numerics.py` constructs the collision matrices, computes spectral-moment responses, reconstructs the occupation spectrum and draws all five figures. Its default outputs are `generated/results`, `generated/figures` and `generated/checks`. It does not overwrite the tracked baselines in `numerics/results` and `figures`. Alternative output directories can be specified:

```bash
OPENBLAS_NUM_THREADS=1 python scripts/run_numerics.py \
  --output-dir /tmp/pinned-results --figures-dir /tmp/pinned-figures
python scripts/check_numerics.py \
  --output-dir /tmp/pinned-results --figures-dir /tmp/pinned-figures \
  --report /tmp/pinned-comparison.json
```

`check_numerics.py` validates baseline hashes and compares CSV columns, rows and values, the reconstructed physical spectra, the quadratic entropy response and the independent resolution comparisons. The default relative and absolute tolerances are `5e-8` and `5e-11`. Generalized eigenvectors can change overall sign; their raw entries and signed overlaps are therefore not compared directly. The resulting physical spectra, spectral weights and correlations must still agree.

## Configurations and stored data

- **Decay rates:** `d=0.004,0.008,0.016,0.032,0.064,0.1`, with `M=14,n=768`. Only the physical entropy-norm convention `ALS_q_entropy` is retained. The CSV files contain 162 Ritz rates and 18 trial quotients.
- **Spectral moments:** four main bandwidths `d=0.004,0.008,0.016,0.032`, with `M=14,n=768`. At `d=0.008`, independent runs use `(M,n)=(8,768),(20,768),(14,384),(14,1536)`. The eight configurations contain 4184 sampled times and 216 finite-mode spectral weights.
- **Preparation spectra:** `d=0.008,M=14,n=768,eta=0.1`, with initial occupations `W_±=N±eta*N²*sin(2x)`. The full Galerkin coefficients and physical spectra are stored, without fitting a single exponential.

The physical relative occupation perturbation is `g=N*phi`, where `N=1/omega`. Thus `phi=sin(2x)` corresponds to `g=N*sin(2x)`. The dissipation and mass matrices satisfy `B U=G U diag(rates)` and `U.T G U=I`. Correlations sum the spectral weights of all retained modes. The normalized quadratic entropy-deficit response is `C2(2t)`; this quadratic quantity does not represent the full entropy of a finite-amplitude nonlinear evolution.

Baseline data were copied after selecting the relevant rows and columns from the original project. Every retained numerical cell string is unchanged. `numerics/source-provenance.json` records original and packaged file hashes, CSV selection rules and retained columns. The full preparation NPZ and all five PDF/PNG figures were copied without modification. The `original_source_sha256` fields in reconstruction metadata refer to the original run; current packaged-file hashes are recorded in the provenance manifest.

## Individual programs and plotting

```bash
OPENBLAS_NUM_THREADS=1 python numerics/endpoint_spectrum.py
OPENBLAS_NUM_THREADS=1 python numerics/linear_response.py
PINNED_RESULTS_DIR=generated/results python scripts/preparation_memory.py
PINNED_PLOT_RESULTS_DIR=generated/results python scripts/manuscript_figures.py
python scripts/three_d_resonance.py
```

Standalone plotting reads the tracked `numerics/results` by default and writes to `generated/figures`. Set `PINNED_PLOT_RESULTS_DIR` and `PINNED_FIGURES_DIR` to use other paths. `PINNED_RESULTS_DIR` controls numerical output. The `endpoint_spectrum.py --quick` option runs only a small `d=0.008,M=6,n=128` matrix check and writes files prefixed by `quick_`; it does not replace the complete run.

The five figures show dispersion and mirror pairing, three-dimensional exact resonance geometry, the initial preparations and relaxing spectrum, spectral-moment and quadratic entropy responses, and narrow-band Ritz rates and trial quotients. Energy and symmetry checks for the resonance geometry are written to `generated/checks/three-d-resonance-check.json`.

Quadrature uses midpoint grids without a certified error bound. With exact integration, rates obtained by restriction to a finite trial space are variational upper bounds. The present computations provide neither a lower bound for the full collision spectral gap nor a proof of infinite-dimensional semigroup convergence.

## Recorded reproduction

A complete run on 2026-09-30 UTC recomputed all six rate configurations, all eight spectral-moment configurations and the full preparation spectrum using the locked numerical environment, then regenerated the five figures. The maximum differences in the four CSV files and compared physical spectrum arrays were zero. All five PNG figures were byte-identical and visually inspected. The record is in `numerics/verification/regression.json` and the resonance-geometry check file. These checks establish reproducibility of the finite calculations; they do not certify continuum spectral gaps or quadrature errors.
