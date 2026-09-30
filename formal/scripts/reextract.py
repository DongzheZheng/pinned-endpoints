#!/usr/bin/env python3
"""Reproduce or check this exact proof extraction using only Python and Git."""
from __future__ import annotations
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
COMMIT = "7afa3fa2d2c3c46023cd863ab26ac32352995578"
ROOT_MODULE = "Resonance.PinnedClassificationFinal"
UPSTREAM_MANIFEST_SHA256 = "823f36d3fbab78f78272582cf5b411a419344f504b731835bbbb6523cba72c54"
UPSTREAM_HASHES = {'Resonance/PinnedGeometry.lean': '6e3471f62e8377b9ac391201e3b9432f476bcb89b22c5bd2b579a0213a2e7de4', 'Resonance/PinnedCharts.lean': 'a59ab8c4bb2b6c6a0cbd8ad2b1afefb189572d0455047dc0ebd3e473d10d9dc7', 'Resonance/PinnedMeasure.lean': 'f39f931d68e87380c5d95c22bb665504cec04c5aed6be7fdd53aaed7ff35569a', 'Resonance/PinnedJacobian.lean': 'cb46c6fc3b87a9c06041a98145787b38baa54b1e77faea84c88aa496ec8aa506', 'Resonance/PinnedPeriodicity.lean': '262a0a1c9b5e3de0e799a84a82ac4ffa058419ffec2d6a34ee24a0f8b557938b', 'Resonance/PinnedMeasurable.lean': '9b26f3ac182182a0194bb29c26d33d3ea7e8e60ae740a87830fb8cffc380bf4b', 'Resonance/PinnedElimination.lean': 'b5b9983e3a69f9070109869bbb7d9b66bacc86c24b62f063be036476dd218ea7', 'Resonance/PinnedODE.lean': 'ecdc4978a8203248775eaec3dc1c6350c0539b6db2b141f1548c55a79007adce', 'Resonance/PinnedClassification.lean': '8e8aae9456f8d20a48a19f24381b494230610baad4624f67dc1a481151706a6e', 'Resonance/PinnedSmoothing.lean': '208bd06c82d72a09350da19782be220cff1abe25d5799a047fc3d3314126229e', 'Resonance/PinnedAveraging.lean': 'ced6d1fcce74ada6b5f31955a70f6eb388f208f26957c6cfea26d32fc113f6e5', 'Resonance/PinnedLocalSmooth.lean': '9c38f4c880a43d6cb8218369cc865d373cb6753fe77dc50bee68263451be5a17', 'Resonance/PinnedRepresentatives.lean': '0a9551508fa3880b36db1ecf57fa36263a4a4822505243b050f9120f6fa848b5', 'Resonance/PinnedGlobalRegularity.lean': '3b2686484defe272817890d797b602d4fcabd5c054e773da2e323744aea2d24f', 'Resonance/PinnedInvariantTransfer.lean': '26b55402d5d3fd9df739ef6a817f2f1af8da294dd61e4108bbbde62e01db67bb', 'Resonance/PinnedCircleAE.lean': '8ff6157dc4244f51be8b1a5c9aa6dba0f2d7624b3ea0436720ae1b6070496395', 'Resonance/PinnedAERegularity.lean': '9b8d467351066f41d7638184d7f3f6bf2516609dabad842cdeb4c5fcebe1ff8c', 'Resonance/PinnedEndToEnd.lean': '889db49eed46181d80af2d4bc3bf32cf1d8833bea907969b07f266c8bcee20bc', 'Resonance/PinnedMeasureNormalization.lean': '23de1115243c76dbb095b20c667dff2036ab5ccd68a3c22f3559562ba1e5ac4f', 'Resonance/PinnedClassificationFinal.lean': '151a2d20e9d1758795b61f1362de00ab3223d9b0565a8865d809957f130e406a', 'lakefile.toml': 'c01c65c72f99b81c38d4b43539fc1bd5bc8e01156eb00a86e40e38f7a56cbcd0', 'lake-manifest.json': '14fa517a368f6f657556121f19a47963024756e72ffa0807fe9359e0521ede65', 'lean-toolchain': '651c8accb402b0c071cd336e9d3dc0a55516b1bfb434ddc4801f14936785b1d2', 'Resonance/Collision.lean': 'dd83fac398d22f137a3253641edc98bd958ccac6cb292162c4fa5ba86848f769'}
META = {'schema_version': 1, 'snapshot': 'pinned-classification-only-20260929', 'whole_paper_end_to_end_verified': False, 'main_roots': ['Resonance.PinnedClassificationFinal.euclidean_coarea_classification_unique', 'Resonance.PinnedClassificationFinal.euclidean_coarea_unique_smooth_representative', 'Resonance.PinnedClassificationFinal.euclidean_coarea_classification_real', 'Resonance.PinnedClassificationFinal.affine_representative_all_resonances', 'Resonance.PinnedClassificationFinal.affine_representative_euclidean_invariant'], 'allowed_axioms': ['propext', 'Classical.choice', 'Quot.sound'], 'toolchain': 'leanprover/lean4:v4.29.0', 'mathlib_revision': '8a178386ffc0f5fef0b77738bb5449d50efeea95', 'scope': 'One-dimensional measurable collision-invariant classification only; upstream shared Collision module reduced to the original dispersion definition. No spectral gap or transport theorems.'}
COLLISION = 'import Mathlib\n\n/-!\n# Pinned one-dimensional dispersion\n\nOnly the original dispersion definition needed by the collision-invariant\nclassification is retained from the upstream shared algebra module.\n-/\n\nnamespace Resonance.Collision\nnoncomputable section\n\n/-- The unmodified pinned dispersion on a real lift of the circle. -/\ndef pinnedDispersion (d x : ℝ) : ℝ := Real.sqrt (1 - 2 * d * Real.cos x)\n\nend\nend Resonance.Collision\n'


def sha(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def json_bytes(value: object) -> bytes:
    return (json.dumps(value, indent=2) + "\n").encode()


def reconstruct(upstream: Path) -> dict[str, bytes]:
    original_bytes = (upstream / "verification/manifest.json").read_bytes()
    if sha(original_bytes) != UPSTREAM_MANIFEST_SHA256:
        raise ValueError("Upstream manifest differs from the frozen source commit")
    if (upstream / ".git").exists():
        commit = subprocess.check_output(["git", "-C", str(upstream), "rev-parse", "HEAD"], text=True).strip()
        if commit != COMMIT:
            raise ValueError("Upstream Git commit differs from the frozen source commit")
    payloads = {}
    for name, digest in UPSTREAM_HASHES.items():
        payload = (upstream / name).read_bytes()
        if sha(payload) != digest:
            raise ValueError(f"Changed upstream source: {name}")
        payloads[name] = payload
    spec = importlib.util.spec_from_file_location("extract_verify", ROOT / "scripts/verify.py")
    verify = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(verify)
    seen = set()
    def visit(module: str):
        if module in seen:
            return
        seen.add(module)
        name = module.replace(".", "/") + ".lean"
        if name not in payloads:
            raise ValueError(f"Dependency outside the pinned proof closure: {module}")
        for line in verify.uncomment(payloads[name].decode()).splitlines():
            matched = re.fullmatch(r"\s*import\s+(.+?)\s*", line)
            if matched:
                for item in matched.group(1).split():
                    if item.startswith("Resonance."):
                        visit(item)
                    elif item == "Resonance":
                        raise ValueError("Unexpected whole-project umbrella import")
    visit(ROOT_MODULE)
    original = json.loads(original_bytes)
    ordered = [q if q.startswith("Resonance.") else "Resonance." + q for q in original["modules"]]
    modules = [q for q in ordered if q in seen]
    if len(modules) != 21 or seen != set(modules):
        raise ValueError("Pinned proof import closure has changed")
    # Retain the original definition exactly; omit every unused shared declaration.
    retained = "def pinnedDispersion (d x : ℝ) : ℝ := Real.sqrt (1 - 2 * d * Real.cos x)"
    if payloads["Resonance/Collision.lean"].decode().count(retained) != 1:
        raise ValueError("Missing or ambiguous original dispersion definition")
    payloads["Resonance/Collision.lean"] = COLLISION.encode()
    payloads["Resonance.lean"] = "".join(f"import {q}\n" for q in modules).encode()
    theorem_names = []
    for module in modules:
        theorem_names.extend(verify.declarations(verify.uncomment(payloads[module.replace(".", "/") + ".lean"].decode()), module))
    if len(theorem_names) != 232:
        raise ValueError("Expected exactly 232 explicit proof theorems")
    manifest = dict(META, modules=modules, theorems=theorem_names,
                    source_sha256={q: sha(payload) for q,payload in sorted(payloads.items())})
    # Match the canonical field order used by the frozen package.
    order = ["schema_version", "snapshot", "whole_paper_end_to_end_verified", "modules", "theorems", "main_roots", "source_sha256", "allowed_axioms", "toolchain", "mathlib_revision", "scope"]
    payloads["verification/manifest.json"] = json_bytes({q:manifest[q] for q in order})
    return payloads


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", required=True, type=Path, help="Frozen upstream checkout or exact source snapshot")
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--check", action="store_true", help="Compare extraction with this package without writing files")
    modes.add_argument("--output", type=Path, help="Write reconstructed Lean sources/configuration/manifest into a new directory")
    args = parser.parse_args()
    payloads = reconstruct(args.upstream.resolve())
    if args.check:
        mismatched = [q for q,b in payloads.items() if not (ROOT / q).is_file() or (ROOT / q).read_bytes() != b]
        if mismatched:
            raise ValueError("Extraction differs: " + ", ".join(mismatched))
        print("PASS: exact extraction; 21 modules; 232 explicit theorems; no Lean execution")
    else:
        out = args.output.resolve()
        if out.exists():
            parser.error("Output must be a new directory")
        for name, payload in payloads.items():
            target = out / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(payload)
        print(f"Wrote {len(payloads)} frozen source/configuration/manifest files to {out}; no Lean execution")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
