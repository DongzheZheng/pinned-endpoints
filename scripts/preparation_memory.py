#!/usr/bin/env python3
"""Reconstruct one entropy-Galerkin spectrum for the prepared sin(2x) moment.

Reconstruction reads C2 data from PINNED_RESULTS_DIR, or the recorded baseline.
Run with: OPENBLAS_NUM_THREADS=1 python scripts/preparation_memory.py
The figure generator reads the saved NPZ; it never reruns collision quadrature.
"""
from pathlib import Path
import csv
import hashlib
import json
import platform
import sys
import time

import numpy as np
import scipy
from scipy.linalg import eigh

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "numerics"))
from endpoint_spectrum import (collision_matrices, energy_basis, harmonic_basis,
                               omega, projected_mass)
from output_paths import plot_results_dir, results_dir

OUT = results_dir()
SOURCE_RESULTS = plot_results_dir()


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    start = time.perf_counter()
    d, M, n, eta = 0.008, 14, 768, 0.1
    mass_count = 65536
    tau = np.linspace(0.0, 3.0, 121)
    x = np.linspace(-np.pi, np.pi, 401)
    dissipation, energy_residual = collision_matrices(d, M, n)
    mass = projected_mass(d, M, True, count=mass_count)
    rates, U = eigh(dissipation, mass)
    if not np.all(np.isfinite(rates)) or rates[0] <= 0:
        raise ValueError("The finite Galerkin rates must be finite and positive.")
    c0 = np.zeros(2 * M - 1)
    c0[M] = 1.0                  # phi(x,0)=sin(2x), g/eta=N_d*sin(2x)
    amplitudes = U.T @ mass @ c0
    norm0 = float(c0 @ mass @ c0)
    weights = amplitudes**2 / norm0
    coefficients = (np.exp(-tau[:, None] * rates[None, :] / d)
                    * amplitudes[None, :]) @ U.T

    # Reconstruct the same weighted orthogonal projection used by the mass.
    xm = 2 * np.pi * (np.arange(mass_count) + 0.5) / mass_count
    Nm = 1 / omega(xm, d)
    raw = harmonic_basis(xm, M)
    kernel = np.stack([np.ones_like(xm), energy_basis(xm, d)], axis=-1)
    kk = kernel.T @ (Nm[:, None]**2 * kernel) / mass_count
    kh = kernel.T @ (Nm[:, None]**2 * raw) / mass_count
    projection_coefficients = np.linalg.solve(kk, kh)
    Hm = raw - kernel @ projection_coefficients
    reconstructed_mass = Hm.T @ (Nm[:, None]**2 * Hm) / mass_count
    H = (harmonic_basis(x, M)
         - np.stack([np.ones_like(x), energy_basis(x, d)], axis=-1)
         @ projection_coefficients)
    N = 1 / omega(x, d)
    phi = coefficients @ H.T
    relative_distortion = phi * N[None, :]   # g_+(x,t)/eta, not a fitted exponential
    W_plus = N + eta * N**2 * np.sin(2*x)
    W_minus = N - eta * N**2 * np.sin(2*x)
    W_plus_linear = N[None, :] * (1 + eta * relative_distortion)
    W_minus_linear = N[None, :] * (1 - eta * relative_distortion)
    C2 = np.exp(-tau[:, None] * rates[None, :] / d) @ weights
    entropy_ratio = np.exp(-2*tau[:, None] * rates[None, :] / d) @ weights
    entropy_direct = np.einsum("ti,ij,tj->t", coefficients, mass, coefficients) / norm0
    action_basis_moment = np.mean(Nm[:, None]**2 * Hm, axis=0)
    energy_basis_moment = np.mean(omega(xm,d)[:, None] * Nm[:, None]**2 * Hm, axis=0)

    source_weights = SOURCE_RESULTS / "linear_response_spectral_weights.csv"
    with source_weights.open() as stream:
        old = [r for r in csv.DictReader(stream)
               if float(r["d"]) == d and int(r["M"]) == M and int(r["n"]) == n]
    old_rates = np.array([float(r["rate"]) for r in old])
    old_weights = np.array([float(r["C2_normalized_weight"]) for r in old])
    source_times = SOURCE_RESULTS / "linear_response_times.csv"
    with source_times.open() as stream:
        old_curves = [r for r in csv.DictReader(stream)
                      if float(r["d"]) == d and int(r["M"]) == M
                      and int(r["n"]) == n and r["time_grid"] == "slow"]
    old_t = np.array([float(r["t"]) for r in old_curves])
    old_C = np.array([float(r["C2_normalized"]) for r in old_curves])
    new_C = np.exp(-old_t[:, None] * rates[None, :]) @ weights
    initial_plus = Nm + eta * Nm**2 * np.sin(2*xm)
    initial_minus = Nm - eta * Nm**2 * np.sin(2*xm)
    rho0 = float(np.mean(Nm))
    rho1 = float(np.mean(omega(xm,d)*Nm))
    checks = {
        "energy_resonance_residual": float(energy_residual),
        "mass_from_projected_basis_max_error": float(np.max(np.abs(reconstructed_mass-mass))),
        "eigenvector_mass_orthogonality_max": float(np.max(np.abs(U.T @ mass @ U-np.eye(len(rates))))),
        "generalized_eigen_residual_relative": float(np.linalg.norm(dissipation @ U-(mass @ U)*rates[None,:]) / np.linalg.norm(dissipation @ U)),
        "weight_sum_error": float(abs(weights.sum()-1)),
        "initial_shape_max_error": float(np.max(np.abs(relative_distortion[0]-N*np.sin(2*x)))),
        "odd_parity_max_error": float(np.max(np.abs(relative_distortion+relative_distortion[:,::-1]))),
        "quadratic_entropy_semigroup_identity_max_error": float(np.max(np.abs(entropy_direct-entropy_ratio))),
        "initial_action_plus_error": float(abs(np.mean(initial_plus)-rho0)),
        "initial_action_minus_error": float(abs(np.mean(initial_minus)-rho0)),
        "initial_energy_plus_error": float(abs(np.mean(omega(xm,d)*initial_plus)-rho1)),
        "initial_energy_minus_error": float(abs(np.mean(omega(xm,d)*initial_minus)-rho1)),
        "linear_action_change_max": float(eta*np.max(np.abs(coefficients @ action_basis_moment))),
        "linear_energy_change_max": float(eta*np.max(np.abs(coefficients @ energy_basis_moment))),
        "positive_linear_occupation_min": float(min(W_plus_linear.min(),W_minus_linear.min())),
        "existing_rates_relative_max_difference": float(np.max(np.abs(rates-old_rates)/old_rates)),
        "existing_C2_weights_absolute_max_difference": float(np.max(np.abs(weights-old_weights))),
        "existing_slow_C2_absolute_max_difference": float(np.max(np.abs(new_C-old_C))),
    }
    for name in ["mass_from_projected_basis_max_error", "eigenvector_mass_orthogonality_max",
                 "generalized_eigen_residual_relative", "weight_sum_error", "initial_shape_max_error",
                 "odd_parity_max_error", "quadratic_entropy_semigroup_identity_max_error",
                 "linear_action_change_max", "linear_energy_change_max"]:
        if checks[name] > 1e-10:
            raise ValueError(f"Reconstruction failed {name}: {checks[name]}")
    if checks["existing_slow_C2_absolute_max_difference"] > 1e-9:
        raise ValueError("New shape reconstruction disagrees with original moment data.")
    if checks["positive_linear_occupation_min"] <= 0:
        raise ValueError("The displayed prepared spectra are not positive.")

    destination = OUT / "preparation_memory_galerkin.npz"
    np.savez_compressed(destination, d=d, M=M, n=n, eta=eta, mass_count=mass_count,
                        x=x, tau=tau, equilibrium=N, W_plus=W_plus, W_minus=W_minus,
                        relative_distortion=relative_distortion, coefficients=coefficients,
                        mass=mass, dissipation=dissipation, eigenvectors=U, rates=rates,
                        initial_coefficients=c0, spectral_amplitudes=amplitudes,
                        normalized_weights=weights, projection_coefficients=projection_coefficients,
                        C2=C2, quadratic_entropy_ratio=entropy_ratio)
    metadata = {
        "created_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "configuration": {"d":d,"M":M,"n":n,"eta":eta,"mass_count":mass_count,
                          "wave_grid_points":len(x),"tau_interval":[float(tau[0]),float(tau[-1])],
                          "tau_points":len(tau)},
        "preparation": "W_plus/minus=N_d +/- eta*N_d^2*sin(2x); both exactly share rho0 and rho1",
        "densities": {"rho0_equilibrium":rho0,"rho1_equilibrium":rho1},
        "reconstruction": "c(t)=U exp(-Lambda*t) U.T M c0; g_plus/eta=N_d H c(t), H is the exact-invariant projected basis",
        "entropy": "quadratic entropy deficit ratio ||g(t)||^2/||g(0)||^2 = C2(2t), not the finite-amplitude nonlinear entropy",
        "warning": "one finite Galerkin reconstruction with unvalidated resonance quadrature; not nonlinear chain dynamics or a certified infinite-dimensional semigroup",
        "checks": checks,
        "source_sha256": {p.name:digest(p) for p in [Path(__file__),ROOT/"numerics/endpoint_spectrum.py",source_weights,source_times]},
        "data_sha256":digest(destination),
        "runtime_seconds":time.perf_counter()-start,
        "python_version":platform.python_version(),"numpy_version":np.__version__,"scipy_version":scipy.__version__,
    }
    (OUT / "preparation_memory_metadata.json").write_text(json.dumps(metadata,indent=2)+"\n")
    print(json.dumps({"runtime_seconds":metadata["runtime_seconds"],"checks":checks,
                      "output":str(destination)},indent=2))


if __name__ == "__main__":
    main()
