#!/usr/bin/env python3
"""Package exactly the clean committed worktree and its standalone Git history.

The deterministic tarball restores the tracked files without caches or .git.
The separate verified Git bundle can be cloned to retain the commit and refs.
No Lean or numerical program is executed.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tarfile
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]


def load_checker():
    spec = importlib.util.spec_from_file_location("pinned_repository_checker", ROOT / "scripts/check_repository.py")
    if spec is None or spec.loader is None:
        raise RuntimeError("Cannot load repository integrity checks")
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    return checker


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path: Path, value: dict) -> None:
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def tracked_files(checker) -> dict:
    records = {}
    for entry in filter(None, checker.git("ls-files", "--stage", "-z").split("\0")):
        metadata, name = entry.split("\t", 1)
        mode, _, stage = metadata.split()
        checker.safe_path(name)
        checker.require(stage == "0" and mode in {"100644", "100755"}, f"Unsupported Git entry: {name}")
        checker.require(name not in records, f"Duplicate tracked Git entry: {name}")
        payload = (ROOT / name).read_bytes()
        records[name] = {"sha256": hashlib.sha256(payload).hexdigest(), "bytes": len(payload),
                         "mode": 0o755 if mode == "100755" else 0o644}
    checker.require(bool(records), "No tracked files to package")
    return dict(sorted(records.items()))


def tar_snapshot(path: Path, records: dict, prefix: str, epoch: int) -> None:
    with path.open("wb") as raw:
        with gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0, compresslevel=9) as compressed:
            with tarfile.open(fileobj=compressed, mode="w", format=tarfile.PAX_FORMAT) as archive:
                for name, record in records.items():
                    payload = (ROOT / name).read_bytes()
                    if hashlib.sha256(payload).hexdigest() != record["sha256"]:
                        raise RuntimeError(f"Tracked file changed while packaging: {name}")
                    entry = tarfile.TarInfo(prefix + "/" + name)
                    entry.size, entry.mode, entry.mtime = len(payload), record["mode"], epoch
                    entry.uid = entry.gid = 0
                    entry.uname = entry.gname = ""
                    archive.addfile(entry, io.BytesIO(payload))


def verify_archive(path: Path, records: dict, prefix: str, checker) -> None:
    found = set()
    with tarfile.open(path, "r:gz") as archive:
        for entry in archive.getmembers():
            checker.safe_path(entry.name)
            checker.require(entry.isfile() and entry.name.startswith(prefix + "/"),
                            f"Unsafe/non-file archive entry: {entry.name}")
            name = entry.name[len(prefix) + 1:]
            checker.require(name in records and name not in found, f"Unexpected archive entry: {name}")
            handle = archive.extractfile(entry)
            checker.require(handle is not None, f"Missing archive payload: {name}")
            payload = handle.read()
            checker.require(hashlib.sha256(payload).hexdigest() == records[name]["sha256"]
                            and len(payload) == records[name]["bytes"]
                            and entry.mode == records[name]["mode"], f"Archive mismatch: {name}")
            found.add(name)
    checker.require(found == set(records), "Archive does not restore every tracked file")


def package() -> dict:
    checker = load_checker()
    checked = checker.check_repository()
    commit = checked["git"]["commit"]
    records = tracked_files(checker)
    name = ROOT.name
    checker.safe_path(name)
    epoch = int(checker.git("show", "-s", "--format=%ct", "HEAD").strip())
    refs = checker.git("for-each-ref", "--format=%(refname) %(objectname)").splitlines()
    checker.require(bool(refs), "The repository has no named Git refs to bundle")
    dist = ROOT / "dist"
    dist.mkdir(exist_ok=True)
    checker.require(checker.git("check-ignore", str(dist.relative_to(ROOT))).strip(),
                    "dist/ must be Git-ignored before packaging")
    with tempfile.TemporaryDirectory(prefix=".pack-", dir=dist) as temporary:
        work = Path(temporary)
        tarball = work / (name + ".tar.gz")
        bundle = work / (name + ".bundle")
        tar_snapshot(tarball, records, name, epoch)
        verify_archive(tarball, records, name, checker)
        checker.git("bundle", "create", str(bundle), "--all")
        checker.git("bundle", "verify", str(bundle))
        manifest = {"schema_version": 1, "repository": name, "commit": commit,
                    "refs": refs, "file_count": len(records),
                    "worktree_bytes": sum(r["bytes"] for r in records.values()),
                    "tar_root": name, "stable_file_mtime": epoch,
                    "files": records,
                    "archive": {"file": tarball.name, "sha256": sha256(tarball),
                                "bytes": tarball.stat().st_size},
                    "git_bundle": {"file": bundle.name, "sha256": sha256(bundle),
                                   "bytes": bundle.stat().st_size}}
        manifest_path = work / "source-manifest.json"
        write_json(manifest_path, manifest)
        # Ensure the snapshot and refs still describe the committed worktree.
        checker.require(not checker.git("status", "--porcelain", "--untracked-files=all")
                        and checker.git("rev-parse", "HEAD").strip() == commit
                        and checker.git("for-each-ref", "--format=%(refname) %(objectname)").splitlines() == refs,
                        "Repository changed while packaging")
        for output in (tarball, bundle, manifest_path):
            (work / (output.name + ".sha256")).write_text(sha256(output) + "  " + output.name + "\n", encoding="utf-8")
        for output in sorted(work.iterdir()):
            os.replace(output, dist / output.name)
    return {"status": "PASS", "commit": commit, "files": len(records),
            "worktree_bytes": manifest["worktree_bytes"],
            "tarball": str(dist / tarball.name), "tarball_sha256": manifest["archive"]["sha256"],
            "git_bundle": str(dist / bundle.name), "git_bundle_sha256": manifest["git_bundle"]["sha256"],
            "manifest": str(dist / "source-manifest.json"), "local_lean_execution": False}


def main() -> int:
    argparse.ArgumentParser(description=__doc__).parse_args()
    try:
        result = package()
    except (OSError, ValueError, KeyError, RuntimeError, subprocess.SubprocessError) as error:
        print(json.dumps({"status": "FAIL", "error": str(error), "local_lean_execution": False}, ensure_ascii=False))
        return 1
    print(json.dumps(result, ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
