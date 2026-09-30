# Recorded narrow-band spectral memory

The physical perturbation is `g=N*phi`, `N=1/omega`, with `phi=sin(2x)`.
The generalized matrix problem is `B U = G U diag(rates)`, `U.T G U=I`.
The normalized spectral moment uses all finite-dimensional spectral weights,
without fitting a single exponential.

Main response data: `d=0.004,0.008,0.016,0.032`, `M=14,n=768`.
At `d=0.008`, independent changes are `(M,n)=(8,768),(20,768),
(14,384),(14,1536)`. Relative changes in the slow-window C2 curve
are `9.20e-6,5.50e-7,2.01e-5,5.04e-6`, respectively.
These are observed comparisons, not rigorous error bounds.

The CSVs preserve the original C2 values exactly and remove unrelated columns.
The numerical collision quadrature is not a certification of the full operator.
Finite-space Ritz values cannot supply a lower bound on the infinite-dimensional
spectral gap. All filter details and file hashes are in `numerics/source-provenance.json`.

Recompute and compare using `python scripts/run_numerics.py` and
`python scripts/check_numerics.py --output-dir generated/results`.
