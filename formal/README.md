# Formal proof of collision-invariant classification in one dimension

This directory contains a standalone Lean proof of the complete collision-invariant classification for the one-dimensional pinned four-wave system. For every `0 < d < 1/2`, the dispersion is `ω_d(x) = sqrt(1 - 2 d cos x)`. A finite-valued, Haar-almost-everywhere measurable function satisfying the four-leg collision identity almost everywhere with respect to the original Euclidean-normalized regular coarea measure is almost everywhere uniquely of the form `A + B ω_d`. The proof also gives the real-valued classification, the unique smooth periodic representative, and the converse identity on every resonant quadruple.

The classification is proved end to end from these original hypotheses. Smoothness, integrability, and the intermediate differential relations are established within the proof rather than assumed. The complete proof and its dependencies contain no `sorry`, `admit`, or custom axioms; the only foundational axioms used are the standard Lean/Mathlib axioms `propext`, `Classical.choice`, and `Quot.sound`.

The source is extracted from [veridiscoverLab/resonance-kinetic-lean](https://github.com/veridiscoverLab/resonance-kinetic-lean), frozen at commit `7afa3fa2d2c3c46023cd863ab26ac32352995578`. The upstream repository has 690 modules; this extraction contains 21 project modules and 232 explicit theorems. The 20 `Pinned*.lean` files are preserved byte for byte. The shared `Collision.lean` module retains only the original `pinnedDispersion` definition. Three-dimensional momentum and energy algebra, unused collision-entropy algebra, spectral gaps, operator theory, Onsager relations, and hydrodynamic-limit theorems are outside this package.

The three coordinates in `PinnedMeasure` are three independent wave numbers of a collision quadruple on a one-dimensional chain. They are part of the one-dimensional resonance geometry.

## Theorem entry points

The aggregate entry point is `Resonance.lean`. All five main theorems are in `Resonance.PinnedClassificationFinal`:

- `euclidean_coarea_classification_unique`
- `euclidean_coarea_unique_smooth_representative`
- `euclidean_coarea_classification_real`
- `affine_representative_all_resonances`
- `affine_representative_euclidean_invariant`

The dependencies are pinned to Lean 4.29.0 and Mathlib commit `8a178386ffc0f5fef0b77738bb5449d50efeea95`. Dependency source trees and compilation caches are not distributed with the source package.

## Local source checks

The local workflow runs Python only; it does not execute Lean, Lake, or the Lean checker:

```sh
python3 scripts/verify.py --source-only
python3 -m unittest discover -s scripts -p 'test_verify.py' -v
python3 scripts/reextract.py --upstream /path/to/frozen-upstream --check
```

`reextract.py` checks the frozen upstream commit and file hashes, reconstructs the import closure, trims the shared module, and compares the extracted source byte for byte with the current source and manifest. It also supports `--output /path/to/new-directory`, which writes the same mathematical sources, Lake configuration, and manifest for independent comparison. This output mode does not copy documentation, verification scripts, or recorded server evidence.

## Server verification

Both the shell script and the Python verifier require Linux and the explicit environment variable `PINNED_LEAN_SERVER=1` before executing Lean. On an authorized server with elan/Lake installed, run:

```sh
PINNED_LEAN_SERVER=1 sh scripts/server-verify.sh
```

By default, the verifier builds all project modules in a new directory, checks the types of all 232 explicit theorems, audits the actual proof dependencies and axioms of every imported project theorem, including private and generated declarations, and prints the axiom dependencies of each of the five main theorems. A fresh kernel replay is enabled only by explicitly running `server-verify.sh --fresh`.

This extraction changes the shared module, so the earlier 256-theorem package's server records were not copied and do not certify this snapshot. The extracted package completed a new project build on cab75 on 2026-09-30 UTC in 56.708 seconds, followed by the 232 explicit theorem-type checks, a dependency audit of 349 project theorem roots including private and generated declarations, and individual axiom checks for the five main theorems. The result is `PASS_FOR_FROZEN_DECLARATIONS_ONLY`. The only axioms are `propext`, `Classical.choice`, and `Quot.sound`; the unsafe and partial dependency counts are both zero.

The recorded manifest and source hashes match the current files. See `verification/server/result.json` and the accompanying manifest, source-sha256, and logs. No additional fresh replay was requested, and Lean was not executed locally. The verification covers the complete frozen classification declarations and their dependencies.

## Provenance and attribution

File hashes, extraction rules, and source provenance are recorded in `verification/provenance.json`; the verification procedure is described in `docs/VERIFICATION.md`. The upstream `NOTICE.md` and `CONTRIBUTORS.md` are retained. The original citation metadata is stored in `provenance/upstream-CITATION.cff` as a source record; its broader abstract does not describe the scope of this package. The upstream project has not selected an open-source license, and this extraction does not grant a new license. The classification proof is published independently in this repository; the related manuscript has not been released as a preprint or submitted to a journal.
