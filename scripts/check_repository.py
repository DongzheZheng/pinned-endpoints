#!/usr/bin/env python3
"""Check source hashes, recorded server evidence and focused data without Lean.

This is a Python/ Git integrity check, not a new proof-assistant verification.
It never imports numerical dependencies, executes Lean, or writes source caches.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import importlib.util
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import zipfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
SHA256 = re.compile(r"[0-9a-f]{64}\Z")
EXCLUDED_PARTS = {".git", ".lake", ".venv", "venv", "__pycache__", ".cache",
                  ".pytest_cache", "node_modules", "build", "dist", "generated",
                  ".verification-runs"}
EXCLUDED_SUFFIXES = {".pyc", ".pyo", ".olean", ".ilean"}
DATA_BRANCH = re.compile(r"(?:c11|k11|acoustic)", re.IGNORECASE)


class RepositoryError(RuntimeError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RepositoryError(message)


def digest(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def safe_path(name: str) -> PurePosixPath:
    require(isinstance(name, str) and bool(name), "Empty or non-string relative path")
    path = PurePosixPath(name)
    require(not path.is_absolute() and ".." not in path.parts and "\\" not in name
            and path.as_posix() == name, f"Unsafe relative path: {name!r}")
    return path


def read_json(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def git(*args: str, root: Path = ROOT) -> str:
    result = subprocess.run(["git", "-C", str(root), *args], capture_output=True,
                            text=True, check=False)
    require(result.returncode == 0, f"git {' '.join(args)} failed: {result.stderr.strip()}")
    return result.stdout


def source_verifier(root: Path):
    path = root / "formal/scripts/verify.py"
    spec = importlib.util.spec_from_file_location("pinned_source_verifier", path)
    require(spec is not None and spec.loader is not None, "Cannot load the source-only verifier")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def check_formal(root: Path) -> dict:
    formal = root / "formal"
    verifier = source_verifier(root)
    manifest, payloads, modules = verifier.source_snapshot(formal)
    require(len(modules) == 21 and len(manifest["theorems"]) == 232,
            "Expected exactly 21 proof modules and 232 explicit source theorems")
    collision = verifier.uncomment(payloads["Resonance/Collision.lean"].decode("utf-8"))
    require(re.findall(r"(?m)^\s*(?:noncomputable\s+)?def\s+(\w+)", collision)
            == ["pinnedDispersion"], "Collision must retain only pinnedDispersion")
    require(not re.search(r"\b(?:theorem|lemma|structure|class|instance|abbrev)\b", collision),
            "Collision contains an unrelated declaration")
    require("def pinnedDispersion (d x : ℝ) : ℝ := Real.sqrt (1 - 2 * d * Real.cos x)" in collision,
            "The retained dispersion definition has changed")
    provenance = read_json(formal / "verification/provenance.json")
    require(provenance["project_module_count"] == 21 and provenance["source_theorem_count"] == 232,
            "Formal provenance inventory disagrees with the source")
    pinned = {p for p in payloads if p.startswith("Resonance/Pinned")}
    unchanged = provenance["unchanged_upstream_files"]
    require(len(pinned) == 20 and pinned == {p for p in unchanged if p.startswith("Resonance/Pinned")},
            "Expected provenance for exactly 20 unchanged Pinned modules")
    for name in sorted(pinned):
        require(digest(payloads[name]) == unchanged[name], f"Upstream Pinned source changed: {name}")
    trimmed = provenance["modified_upstream_files"]["Resonance/Collision.lean"]
    require(trimmed["extracted_sha256"] == digest(payloads["Resonance/Collision.lean"])
            and trimmed["retained_definition"] == "Resonance.Collision.pinnedDispersion"
            and trimmed["retained_definition_verbatim"] is True,
            "Collision extraction provenance disagrees with the source")

    evidence = formal / "verification/server"
    result = read_json(evidence / "result.json")
    require(result.get("status") == "PASS_FOR_FROZEN_DECLARATIONS_ONLY"
            and result.get("source_equivalence") is True
            and result.get("whole_paper_end_to_end_verified") is False,
            "Server result does not establish this frozen classification snapshot")
    require(result.get("module_count") == 21 and result.get("listed_theorem_count") == 232,
            "Server result has the wrong source inventory")
    require((evidence / "manifest.json").read_bytes() == (formal / "verification/manifest.json").read_bytes(),
            "Recorded server manifest differs from the current manifest")
    require(read_json(evidence / "source-sha256.json") == manifest["source_sha256"],
            "Recorded server source hashes differ from the current source")
    hashes = {"manifest_sha256": formal / "verification/manifest.json",
              "verifier_sha256": formal / "scripts/verify.py",
              "checker_sha256": formal / "verification/CheckAxioms.lean"}
    for field, path in hashes.items():
        require(result.get(field) == digest(path.read_bytes()), f"Server {field} mismatch")
    require(result.get("mathlib_revision") == manifest["mathlib_revision"],
            "Recorded Mathlib revision disagrees with the lockfile")
    version = manifest["toolchain"].split(":v", 1)[1]
    require(re.search(r"\bLean \(version " + re.escape(version) + r"(?:,|\))",
                      result.get("lean_version", "")) is not None, "Recorded Lean version mismatch")
    commands = result.get("commands", [])
    require(isinstance(commands, list) and commands, "Missing server command records")
    recorded_logs = set()
    for command in commands:
        require(command.get("status") == "PASS" and command.get("exit_code") == 0,
                "A recorded server command did not pass")
        name = command.get("log", "")
        safe_path(name)
        require(name.startswith("logs/") and (evidence / name).is_file(), f"Missing server log: {name}")
        recorded_logs.add(name)
    required_logs = {"logs/toolchain.log", "logs/mathlib-revision.log", "logs/mathlib-status.log",
                     "logs/build.log", "logs/private-inventory.log", "logs/theorem-types.log",
                     "logs/actual-proof-cone.log"}
    require(required_logs <= recorded_logs, "Missing required server build/type/axiom command records")
    resolved = verifier.resolve_private(manifest["theorems"],
               (evidence / "logs/private-inventory.log").read_text(encoding="utf-8"))
    cone = verifier.parse_cone((evidence / "logs/actual-proof-cone.log").read_text(encoding="utf-8"),
                              resolved, STANDARD_AXIOMS)
    require(result.get("actual_proof_cone") == {k: v for k, v in cone.items() if k != "roots"},
            "Server proof-cone summary disagrees with its complete log")
    require(cone["unsafe_count"] == 0 and cone["partial_count"] == 0
            and set(cone["axioms"]) <= STANDARD_AXIOMS, "Nonstandard proof dependency")
    main_log_path = evidence / "logs/main-axioms.log"
    require(main_log_path.is_file(), "Missing five-main-root axiom log")
    main_log = main_log_path.read_text(encoding="utf-8")
    require("sorryAx" not in main_log, "Main-root axiom log contains sorryAx")
    printed = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", main_log)
    main_axioms = {name: [a.strip() for a in body.split(",") if a.strip()] for name, body in printed}
    require(len(printed) == len(manifest["main_roots"]) == 5
            and set(main_axioms) == set(manifest["main_roots"])
            and all(set(a) <= STANDARD_AXIOMS for a in main_axioms.values()),
            "Incomplete or nonstandard main-root axiom output")
    main_checker_hash = digest((formal / "verification/MainAxioms.lean").read_bytes())
    if "logs/main-axioms.log" in recorded_logs:
        require(result.get("main_axioms_checker_sha256") == main_checker_hash
                and result.get("main_root_axioms") == main_axioms,
                "Main-root result/hash does not agree with its checker and log")
    else:
        metadata = read_json(evidence / "run-metadata.json")
        require(metadata.get("main_axioms_exit_code") == 0
                and metadata.get("main_axioms_checker_sha256") == main_checker_hash,
                "Independent MainAxioms record does not certify this checker")
    return {"modules": 21, "explicit_theorems": 232, "main_roots": 5,
            "server_status": result["status"], "proof_cone_roots": cone["root_count"],
            "axioms": cone["axioms"], "local_lean_execution": False}


def check_data(root: Path) -> dict:
    provenance = read_json(root / "numerics/source-provenance.json")
    require(provenance.get("schema_version") == 1, "Unsupported numerical provenance schema")
    records = provenance.get("files", [])
    require(isinstance(records, list) and records, "Empty numerical source provenance")
    seen, total_bytes = set(), 0
    for record in records:
        name = record["path"]
        safe_path(name)
        require(name not in seen, f"Duplicate numerical provenance path: {name}")
        seen.add(name)
        payload = (root / name).read_bytes()
        require(record.get("sha256") == digest(payload), f"Numerical source/data hash mismatch: {name}")
        total_bytes += len(payload)
        if "source_path" in record:
            safe_path(record["source_path"])
            require(SHA256.fullmatch(record.get("source_sha256", "")) is not None,
                    f"Invalid original source hash: {name}")
        if name.endswith(".csv"):
            with (root / name).open(newline="", encoding="utf-8") as handle:
                reader = csv.DictReader(handle)
                columns = reader.fieldnames or []
                require(columns and not any(DATA_BRANCH.search(c) for c in columns),
                        f"Out-of-scope data columns: {name}")
                rows = list(reader)
            require(rows, f"Empty numerical table: {name}")
            require(record.get("rows", len(rows)) == len(rows), f"Provenance row-count mismatch: {name}")
            require(record.get("columns", columns) == columns, f"Provenance column mismatch: {name}")
            for row in rows:
                if "d" in row:
                    require(0 < float(row["d"]) <= 0.1, f"Non-narrow-band row in {name}")
                if "convention" in row:
                    require(row["convention"] == "ALS_q_entropy", f"Unselected collision convention in {name}")
        if name.startswith("numerics/results/") and name.endswith(".json"):
            def inspect(value):
                if isinstance(value, dict):
                    for key, child in value.items():
                        require(not DATA_BRANCH.search(key), f"Out-of-scope data key {key!r} in {name}")
                        if key == "d" and isinstance(child, (int, float)):
                            require(0 < child <= 0.1, f"Non-narrow-band configuration in {name}")
                        inspect(child)
                elif isinstance(value, list):
                    for child in value:
                        inspect(child)
            inspect(json.loads(payload))
        if name.endswith(".npz"):
            with zipfile.ZipFile(root / name) as archive:
                for entry in archive.namelist():
                    safe_path(entry)
                    require(entry.endswith(".npy") and not DATA_BRANCH.search(entry),
                            f"Out-of-scope NPZ field: {entry}")
    expected_data = {p.relative_to(root).as_posix() for p in (root / "numerics/results").rglob("*") if p.is_file()}
    expected_figures = {p.relative_to(root).as_posix() for p in (root / "figures").rglob("*") if p.is_file()}
    require(expected_data and expected_data | expected_figures <= seen,
            "A baseline data or figure file is missing from numerical provenance")
    require(not any(DATA_BRANCH.search(Path(name).name) for name in expected_data),
            "Out-of-scope baseline data file")
    return {"provenance_files": len(seen), "baseline_data_files": len(expected_data),
            "figure_files": len(expected_figures), "bytes": total_bytes}


def check_git(root: Path, allow_dirty: bool) -> dict:
    if not (root / ".git").is_dir():
        require(allow_dirty, "Initialize and commit the standalone repository first")
        return {"initialized": False, "clean": False, "allow_dirty": True}
    require(Path(git("rev-parse", "--show-toplevel", root=root).strip()).resolve() == root.resolve(),
            "Repository is not an independent Git worktree")
    status = git("status", "--porcelain", "--untracked-files=all", root=root)
    require(allow_dirty or not status, "Git worktree is dirty; commit all changes before packaging")
    commit = subprocess.run(["git", "-C", str(root), "rev-parse", "--verify", "HEAD"],
                            capture_output=True, text=True, check=False)
    require(allow_dirty or commit.returncode == 0, "The repository has no commit")
    tracked = git("ls-files", "-z", root=root).split("\0")
    for name in filter(None, tracked):
        path = safe_path(name)
        require(not (set(path.parts) & EXCLUDED_PARTS)
                and path.suffix not in EXCLUDED_SUFFIXES and path.name != ".DS_Store",
                f"Generated/cache file is tracked: {name}")
        require(not (root / name).is_symlink(), f"Tracked symlink is not allowed in this source bundle: {name}")
    return {"initialized": True, "clean": not bool(status),
            "commit": commit.stdout.strip() if commit.returncode == 0 else None,
            "allow_dirty": allow_dirty}


def check_repository(root: Path = ROOT, allow_dirty: bool = False) -> dict:
    return {"status": "PASS", "check_kind": "source_and_recorded_evidence_integrity_only",
            "formal": check_formal(root), "numerics": check_data(root),
            "git": check_git(root, allow_dirty), "local_lean_execution": False}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--allow-dirty", action="store_true",
                        help="Allow checks before the initial commit or while preparing source changes")
    args = parser.parse_args()
    try:
        result = check_repository(allow_dirty=args.allow_dirty)
    except (OSError, ValueError, KeyError, RuntimeError) as error:
        print(json.dumps({"status": "FAIL", "error": str(error), "local_lean_execution": False},
                         ensure_ascii=False))
        return 1
    print(json.dumps(result, ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
