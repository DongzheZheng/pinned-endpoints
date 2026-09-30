#!/usr/bin/env python3
"""Entropy-Galerkin response of the prepared spectral moment phi=sin(2x).

The physical perturbation is g=N*phi, with N=1/omega. Exact invariants are
projected out by the mass Schur complement. This program retains only the
spectral-memory experiment and its cutoff/quadrature comparisons.
"""
from pathlib import Path
import csv
import json
import platform
import time
import numpy as np
import scipy
from scipy.linalg import eigh
from endpoint_spectrum import collision_matrices, projected_mass
from output_paths import results_dir

PLAN = [(d, 14, 768) for d in (.004, .008, .016, .032)] + [
    (.008, 8, 768), (.008, 20, 768), (.008, 14, 384), (.008, 14, 1536)]


def write_csv(path, rows):
    with path.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def time_grids(d):
    """The slow scale is tau=d*t; the fast scale is u=t/d."""
    return {
        "slow": np.linspace(0., 4., 201) / d,
        "fast": d * np.linspace(0., 4., 201),
        "long_tail": np.geomspace(4.02, 40., 121) / d,
    }


def observable(U, rates, G, a):
    norm = float(a @ G @ a)
    amplitudes = U.T @ G @ a
    raw_weights = amplitudes**2
    weights = raw_weights / norm
    return dict(
        norm=norm, weights=weights, raw_weights=raw_weights,
        weight_sum=float(weights.sum()), initial_rate=float(weights @ rates),
        integrated_normalized=float(weights @ (1. / rates)),
        integrated_raw=float(raw_weights @ (1. / rates)),
        initial_rate_direct=None,
    )


def correlations(rates, weights, times):
    return np.exp(-np.outer(times, rates)) @ weights


def solve(d, M, n):
    start = time.perf_counter()
    B, energy_residual = collision_matrices(d, M, n)
    G = projected_mass(d, M, True)
    rates, U = eigh(B, G)
    if rates[0] <= 0 or not np.all(np.isfinite(rates)):
        raise ValueError(f"Nonpositive or nonfinite rates for {(d, M, n)}")
    a2 = np.zeros(2*M-1)
    a2[M] = 1.                 # phi=sin(2x), so g=N*sin(2x)
    obs2 = observable(U, rates, G, a2)
    obs2["initial_rate_direct"] = float(a2 @ B @ a2) / obs2["norm"]

    rows = []
    curves = {}
    for tag, times in time_grids(d).items():
        c2 = correlations(rates, obs2["weights"], times)
        curves[tag] = dict(times=times, c2=c2)
        for t, v2 in zip(times, c2):
            rows.append(dict(d=d, M=M, n=n, time_grid=tag, t=float(t),
                             tau=float(d*t), u=float(t/d), C2_normalized=float(v2)))

    times_all = np.unique(np.concatenate([c["times"] for c in curves.values()]))
    c2_all = correlations(rates, obs2["weights"], times_all)
    checks = dict(
        minimum_rate=float(rates[0]), maximum_rate=float(rates[-1]),
        minimum_mass_eigenvalue=float(np.linalg.eigvalsh(G)[0]),
        eigenvector_G_orthogonality_max=float(np.max(np.abs(U.T @ G @ U-np.eye(len(rates))))),
        generalized_eigen_residual_relative=float(
            np.linalg.norm(B @ U - (G @ U)*rates[None, :]) /
            max(np.linalg.norm(B @ U), np.finfo(float).tiny)),
        energy_resonance_residual=float(energy_residual),
        C2_weight_sum=obs2["weight_sum"],
        C2_max_monotonicity_violation=float(max(0., np.max(np.diff(c2_all)))),
        C2_initial_rate_identity_relative=abs(obs2["initial_rate"]-obs2["initial_rate_direct"])/obs2["initial_rate_direct"],
    )
    if abs(checks["C2_weight_sum"]-1) > 1e-10:
        raise ValueError(f"Spectral weights fail completeness: {checks}")
    if checks["C2_max_monotonicity_violation"] > 1e-13:
        raise ValueError(f"Semigroup correlations fail monotonicity: {checks}")

    slow_indices = [h-2 for h in range(3, M+1, 2)] + [M-2+h for h in range(2, M+1, 2)]
    slow_mass = np.zeros_like(G)
    slow_mass[np.ix_(slow_indices, slow_indices)] = G[np.ix_(slow_indices, slow_indices)]
    spectral = [dict(
        d=d, M=M, n=n, eigen_index=j+1, rate=float(rate), rate_over_d=float(rate/d),
        C2_normalized_weight=float(obs2["weights"][j]),
        C2_raw_weight=float(obs2["raw_weights"][j]),
        mirror_antisymmetric_G_norm=float(U[:, j] @ slow_mass @ U[:, j]))
        for j, rate in enumerate(rates)]
    prepared_summary = {k: v for k, v in obs2.items() if k not in ("weights", "raw_weights")}
    summary = dict(
        d=d, M=M, n=n, runtime_seconds=time.perf_counter()-start,
        prepared_sin2=prepared_summary, checks=checks,
        C2_integrated_time=obs2["integrated_normalized"],
    )
    return rows, spectral, summary, curves


def relative_error(value, reference):
    return abs(value-reference) / max(abs(reference), np.finfo(float).tiny)


def curve_errors(curve, reference):
    diff = np.abs(curve-reference)
    mask = reference >= 1e-8
    return dict(
        absolute_max=float(diff.max()),
        relative_max_with_floor_1e_minus_12=float(np.max(diff/np.maximum(reference, 1e-12))),
        relative_max_where_reference_ge_1e_minus_8=float(np.max(diff[mask]/reference[mask])) if np.any(mask) else None,
    )


def main():
    out = results_dir()
    start = time.perf_counter()
    times, spectra, summaries = [], [], []
    solutions = {}
    for d, M, n in PLAN:
        rr, ss, summary, curves = solve(d, M, n)
        times.extend(rr)
        spectra.extend(ss)
        summaries.append(summary)
        solutions[(d, M, n)] = (summary, curves)
        print(f"d={d:g} M={M} n={n}: {summary['runtime_seconds']:.2f}s; "
              f"first Ritz/d={summary['checks']['minimum_rate']/d:.8g}; "
              f"C2 initial rate/d={summary['prepared_sin2']['initial_rate']/d:.8g}", flush=True)

    reference, ref_curves = solutions[(.008, 14, 768)]
    convergence = []
    for key in PLAN[4:]:
        summary, curves = solutions[key]
        check = dict(
            d=key[0], M=key[1], n=key[2], reference_M=14, reference_n=768,
            changed_parameter="Fourier_cutoff" if key[1] != 14 else "quadrature_grid",
            C2_integral_relative_error=relative_error(summary["C2_integrated_time"], reference["C2_integrated_time"]),
            minimum_rate_relative_error=relative_error(summary["checks"]["minimum_rate"], reference["checks"]["minimum_rate"]),
            curves={grid: {"c2": curve_errors(curves[grid]["c2"], ref_curves[grid]["c2"])}
                    for grid in curves},
        )
        convergence.append(check)

    metadata = dict(
        created_utc=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        calculation="exact-resonance ALS collision form with entropy Galerkin semigroup",
        variable="g=N*phi, N=1/omega; G=projected integral N^2 H_i H_j dm",
        eigenproblem="B U = G U diag(rates), U.T G U = identity",
        observables={"prepared_sin2": "phi=sin(2x), coefficient index M"},
        weights="(U.T G a)^2/(a.T G a); raw correlation=(a.T G a)*normalized correlation",
        time_grids="slow: tau=d*t in [0,4]; fast: u=t/d in [0,4]; long_tail: tau in [4.02,40]",
        projection="exact invariant span{1,(omega-1)/d} removed using projected_mass physical=True; the observable is odd",
        error_metrics="pointwise relative maximum uses denominator floor 1e-12; separately report only reference values >=1e-8",
        warning="Galerkin approximation with unvalidated quadrature error; not a microscopic simulation, certified infinite-dimensional semigroup, or gap lower bound",
        plan=PLAN, runs=summaries, convergence=convergence,
        runtime_seconds=time.perf_counter()-start, python_version=platform.python_version(),
        numpy_version=np.__version__, scipy_version=scipy.__version__,
    )
    write_csv(out / "linear_response_times.csv", times)
    write_csv(out / "linear_response_spectral_weights.csv", spectra)
    (out / "linear_response_metadata.json").write_text(json.dumps(metadata, indent=2)+"\n")
    print(f"Saved {len(times)} time rows and {len(spectra)} spectral rows.", flush=True)


if __name__ == "__main__":
    main()
