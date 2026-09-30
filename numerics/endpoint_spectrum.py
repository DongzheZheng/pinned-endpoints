#!/usr/bin/env python3
"""Exact-resonance narrow-band entropy-Galerkin collision matrices.

Recomputations go to generated/results, preserving numerics/results as the
recorded baseline. Set PINNED_RESULTS_DIR to select another output directory.
Only the physical entropy form is exposed by this focused extraction.
"""
from pathlib import Path
import argparse
import csv
import json
import platform
import time
import numpy as np
import scipy
from scipy.linalg import eigh
from output_paths import results_dir

PLAN = [(d, 14, 768) for d in (.004, .008, .016, .032, .064, .1)]


def omega(x, d):
    # Stable evaluation of the pinned dispersion.
    return np.sqrt((1 - 2*d) + 4*d*np.sin(x/2)**2)


def energy_basis(x, d):
    # (omega_d - 1)/d, evaluated without small-d cancellation.
    return -2*np.cos(x)/(omega(x, d)+1)


def harmonic_basis(x, M):
    # cos(x) is replaced by the exact invariant energy_basis and projected out.
    return np.concatenate([np.cos(x[..., None]*np.arange(2,M+1)),
                           np.sin(x[..., None]*np.arange(1,M+1))], axis=-1)


def projected_mass(d, M, physical, count=65536):
    x = 2*np.pi*(np.arange(count)+.5)/count
    H = harmonic_basis(x, M)
    K = np.stack([np.ones_like(x),energy_basis(x,d)],axis=-1)
    wt = 1/omega(x,d)**2 if physical else np.ones_like(x)
    kk = K.T @ (wt[:,None]*K)/count
    kh = K.T @ (wt[:,None]*H)/count
    hh = H.T @ (wt[:,None]*H)/count
    return hh-kh.T @ np.linalg.solve(kk,kh)


def collision_matrices(d, M, n):
    """Full-square, exact-resonance coarea midpoint quadrature.

    x,y,z,w = s+u,s-u,s+v,s-v; u,v in (0,pi), s in (0,pi).
    Reflection multiplicity four gives dXi=du dv/(pi^3 |F_s|).
    The two trivial branches u=+/-v have identically zero collision difference.
    On our square only u=v occurs, with continuous zero extension of the integrand.
    """
    u = np.pi*(np.arange(n)+.5)/n
    als = np.zeros((2*M-1,2*M-1))
    max_energy_error = 0.
    ns_c=np.arange(2,M+1); ns_s=np.arange(1,M+1)
    for start in range(0,n,48):
        U = u[start:start+48,None]; V = u[None,:]
        t=np.cos(U); r=np.cos(V)
        c=d*(t+r)/(1+np.sqrt(1-d*d*(4-(t-r)**2)))
        S=np.arccos(c)
        legs=np.stack(np.broadcast_arrays(S+U,S-U,S+V,S-V),axis=-1)
        om=omega(legs,d)
        max_energy_error=max(max_energy_error,float(np.max(np.abs(
            om[...,0]+om[...,1]-om[...,2]-om[...,3]))))
        vel=d*np.sin(legs)/om
        fs=vel[...,0]+vel[...,1]-vel[...,2]-vel[...,3]
        diagonal=(np.arange(start,min(start+48,n))[:,None]==np.arange(n)[None,:])
        fs[diagonal]=1.
        coarea=1/(np.pi*n*n*np.abs(fs))
        coarea[diagonal]=0.
        # Analytic full collision differences, including all four legs.
        def cdiff(ns):
            return -2*np.sin((U+V)[...,None]*ns/2)*np.sin((U-V)[...,None]*ns/2)
        delta=np.concatenate([2*np.cos(S[...,None]*ns_c)*cdiff(ns_c),
                              2*np.sin(S[...,None]*ns_s)*cdiff(ns_s)],axis=-1)
        delta=delta.reshape(-1,2*M-1)
        cw=coarea.ravel()
        aw=cw/np.prod(om**2,axis=-1).ravel()
        als+=delta.T@(aw[:,None]*delta)
    return (9*np.pi/16)*als,max_energy_error


def solve(d, M, n):
    if not 0 < d <= .1:
        raise ValueError("The numerical experiment is restricted to 0 < d <= 0.1.")
    B, error = collision_matrices(d, M, n)
    G = projected_mass(d, M, True)
    rates = eigh(B, G, eigvals_only=True)
    rows = [dict(d=d, epsilon=1-2*d, M=M, n=n,
                 convention="ALS_q_entropy", eigen_index=j+1,
                 ritz=float(rate), energy_residual=error)
            for j, rate in enumerate(rates)]
    trials = [dict(d=d, epsilon=1-2*d, M=M, n=n, trial=name,
                   convention="ALS_q_entropy", quotient=float(B[idx,idx]/G[idx,idx]))
              for name, idx in [("sin2", M), ("cos3", 1), ("sin1", M-1)]]
    return rows, trials


def save_csv(path, rows):
    with path.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quick", action="store_true", help="one small matrix smoke check")
    args = parser.parse_args()
    out = results_dir()
    plan = [(.008, 6, 128)] if args.quick else PLAN
    rows, trials = [], []
    start = time.perf_counter()
    for d, M, n in plan:
        rr, tt = solve(d, M, n)
        rows.extend(rr)
        trials.extend(tt)
        print(f"d={d:g} M={M} n={n}: physical first Ritz/d={rr[0]['ritz']/d:.8g}", flush=True)
    prefix = "quick_" if args.quick else ""
    save_csv(out / (prefix+"ritz_spectra.csv"), rows)
    save_csv(out / (prefix+"trial_quotients.csv"), trials)
    metadata = dict(
        created_utc=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        normalization="ALS_q_entropy: (9pi/16) D_prod(omega^-2); mass integral phi^2/omega^2 dm",
        quadrature="exact nontrivial resonance s chart; midpoint u,v in (0,pi); diagonal zero extension",
        projection="exact invariant span{1,(omega-1)/d} removed by mass Schur complement; invariants annihilated analytically in form",
        warning="finite-dimensional Ritz values are variational upper bounds after exact integration, not lower bounds or certified gaps; numerical quadrature has unvalidated error",
        plan=plan, runtime_seconds=time.perf_counter()-start,
        python_version=platform.python_version(), numpy_version=np.__version__,
        scipy_version=scipy.__version__)
    (out / (prefix+"metadata.json")).write_text(json.dumps(metadata, indent=2)+"\n")


if __name__ == "__main__":
    main()
