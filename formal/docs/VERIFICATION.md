# Verification procedure and scope

## Frozen proof sources

`verification/manifest.json` lists the exact 21 project modules, 232 explicit `theorem`/`lemma` declarations, five main theorems, and SHA-256 hashes of the mathematical sources and four Lake configuration or aggregate-entry files. The 20 `Pinned` modules are unchanged from the frozen upstream commit. `Collision` retains only the original dispersion definition needed for classification. Auxiliary theorems within the import closure are retained; the extraction does not claim to be minimal at the level of individual declarations.

The source scanner is adapted from the same upstream verifier, with the module count set to 21, server-execution guards, and axiom records for the five main roots. `verification/CheckAxioms.lean` and `verification/MainAxioms.lean` audit the same Lean environment; they are not a second, independent proof assistant.

The formalized result is the complete measurable classification, proved end to end from the original collision condition for `0 < d < 1/2`. It does not assume the regularity or differential identities needed by the proof. The proof and its dependencies contain no `sorry`, `admit`, or custom axioms, and use only the standard foundational axioms listed below. This claim concerns the classification theorem, not every result in the accompanying manuscript.

## Python checks

`--source-only` executes no Lean commands. It checks the frozen hashes, dependency order, complete list of explicit source theorems, and forbidden proof-bypass keywords. `reextract.py` reconstructs the same closure from the frozen upstream source and reproduces the trimming of `Collision`. Source scans and matching hashes cannot replace Lean kernel verification.

## A new server run

Both the Python verifier and shell entry point require Linux and `PINNED_LEAN_SERVER=1`. By default, the shell script performs the following checks without starting a fresh replay:

1. Check the Python source snapshot and test that the verifier rejects failing cases.
2. Check the pinned Lean version, the exact Mathlib commit, and the absence of changes to tracked Mathlib sources.
3. Create a new project directory from the frozen bytes, rebuild all 21 project modules, and compare every source file and lockfile again after the build.
4. Resolve private declaration names from the actual Lean environment, then print the types of all 232 explicit theorems and the complete parameters of the five main theorems.
5. Traverse the type and proof constants of every imported project theorem, including private and generated declarations, and reject unsafe declarations, partial declarations, and nonstandard axioms. The only allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`.
6. Print and check the axiom set of each of the five main theorems.

Running `PINNED_LEAN_SERVER=1 python3 scripts/verify.py --output /new/evidence/directory` directly performs the same default checks. Only an explicit `--fresh` adds `lake env leanchecker --fresh Resonance`, which replays all imported declarations in an empty Lean kernel environment. This replay still uses the same Lean kernel.

## Reading the evidence

Each run writes a new `.verification-runs/<UTC>/result.json`. A successful record must report `PASS_FOR_FROZEN_DECLARATIONS_ONLY`, and its manifest and source-sha256 must match the current snapshot. On a successful default run, `fresh_replay` is `not_requested`; that does not establish that a fresh replay passed. An explicit fresh run establishes this only when the corresponding field reports `PASS`. An interrupted or failed run cannot be certified by substituting evidence from an earlier snapshot.

The delivered evidence in `verification/server/` records a new run of this package on cab75 on 2026-09-30 UTC: 21 modules, 232 explicit theorems, 349 actual theorem roots, and 52659 dependency constants, with result `PASS_FOR_FROZEN_DECLARATIONS_ONLY`. All five main roots depend only on the three standard axioms; the unsafe and partial counts are both zero. The manifest and every source-file hash match the recorded evidence. In this run, `fresh_replay` is `not_requested`. Evidence from the earlier 256-theorem package was not copied.

This evidence verifies the complete frozen collision-invariant classification and its proof dependencies. Numerical experiments, narrow-band spectral-gap bounds, long-lived linear spectral-shape memory, and other manuscript results are outside the formalized theorem set.
