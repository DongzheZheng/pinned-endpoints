#!/usr/bin/env python3
"""Verify this repository's frozen source inventory and actual Lean proof cone.

Uses only the Python standard library and executables supplied by the user's
pinned Lean/Lake and Git installations. Historical evidence is never treated
as the outcome of this run. See docs/VERIFICATION.md for the exact scope.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
import platform
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import time

REPOSITORY = Path(__file__).resolve().parents[1]
EXPECTED_MODULES = 21
STANDARD_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
CONFIG_FILES = {"Resonance.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain"}
NAME = re.compile(r"[A-Za-z_][\w]*(?:\.[A-Za-z_][\w]*)*\Z")
SHA256 = re.compile(r"[0-9a-f]{64}\Z")
FORBIDDEN = re.compile(r"\b(sorry|admit|axiom|unsafe|partial|native_decide|implemented_by|run_tac)\b")


class VerificationError(RuntimeError):
    """A failed check, distinct from a successful narrower verification mode."""


def require_server_execution() -> None:
    """Guard every Lean command; source-only Python checks remain portable."""
    if platform.system() != "Linux" or os.environ.get("PINNED_LEAN_SERVER") != "1":
        raise VerificationError("Lean execution requires Linux and PINNED_LEAN_SERVER=1; local Lean execution is disabled.")


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def uncomment(text: str) -> str:
    """Remove nested Lean comments; preserve strings and line boundaries.

    This is the restricted source inventory lexer used by the frozen audit.
    It is not a Lean parser. Unsupported declaration syntax is rejected below.
    """
    out, i, depth, string = [], 0, 0, False
    while i < len(text):
        if depth:
            if text[i:i + 2] == "/-":
                depth += 1
                i += 2
            elif text[i:i + 2] == "-/":
                depth -= 1
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif string:
            out.append(text[i])
            if text[i] == "\\" and i + 1 < len(text):
                out.append(text[i + 1])
                i += 2
                continue
            if text[i] == '"':
                string = False
            i += 1
        elif text[i:i + 2] == "/-":
            depth = 1
            out.append(" ")
            i += 2
        elif text[i:i + 2] == "--":
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        else:
            out.append(text[i])
            string = text[i] == '"'
            i += 1
    if depth or string:
        raise VerificationError("Unterminated Lean comment or string")
    return "".join(out)


def declarations(code: str, module: str) -> list[str]:
    """Inventory all source theorem/lemma declarations, failing closed."""
    scope, result, short_names = [], [], []
    for line in code.splitlines():
        opener = re.fullmatch(r"(namespace|(?:noncomputable )?section)(?:\s+([\w.]+))?\s*", line)
        closer = re.fullmatch(r"end(?:\s+([\w.]+))?\s*", line)
        theorem = re.match(r"^(?:@\[[^\]\n]*\]\s*)*(private\s+)?(?:theorem|lemma)\s+(\w+(?:\.\w+)*)\b", line)
        if opener:
            kind, name = opener.groups()
            if kind == "namespace" and not name:
                raise VerificationError(f"Unnamed namespace in {module}")
            scope.append((kind, name))
        elif closer:
            if not scope:
                raise VerificationError(f"Unmatched scope end in {module}")
            _, name = scope.pop()
            if closer.group(1) is not None and closer.group(1) != name:
                raise VerificationError(f"Mismatched scope end in {module}")
        elif theorem:
            namespaces = [name for kind, name in scope if kind == "namespace"]
            if not namespaces or namespaces[0] != module:
                raise VerificationError(f"Declaration outside its module namespace in {module}")
            short_names.append(theorem.group(2))
            result.append(("PRIVATE:" if theorem.group(1) else "") +
                          ".".join(namespaces + [theorem.group(2)]))
    all_named = re.findall(r"\b(?:theorem|lemma)\s+(\w+(?:\.\w+)*)\b", code)
    if scope or short_names != all_named or len(result) != len(set(result)):
        raise VerificationError(f"Unsupported, missed, duplicate, or unclosed declaration syntax in {module}")
    return result


def normalized_source_name(name: str) -> str:
    """Normalize a manifest name only for source inventory comparison.

    Actual private kernel names are resolved again from Lean's environment.
    No numerical private-name index is guessed when generating Lean commands.
    """
    if name.startswith("PRIVATE:"):
        if not NAME.fullmatch(name[8:]) or not name[8:].startswith("Resonance."):
            raise VerificationError(f"Invalid private source name: {name}")
        return name
    if name.startswith("_private."):
        match = re.fullmatch(r"_private\.(?:[A-Za-z_]\w*\.)+\d+\.(Resonance\.[\w.]+)", name)
        if not match or not NAME.fullmatch(match.group(1)):
            raise VerificationError(f"Unsupported private kernel name: {name}")
        return "PRIVATE:" + match.group(1)
    if not NAME.fullmatch(name) or not name.startswith("Resonance."):
        raise VerificationError(f"Invalid theorem name: {name}")
    return name


def string_list(value: object, field: str) -> list[str]:
    if not isinstance(value, list) or not all(isinstance(x, str) for x in value):
        raise VerificationError(f"{field} must be an array of strings")
    if len(value) != len(set(value)):
        raise VerificationError(f"Duplicate entries in {field}")
    return value


def source_snapshot(root: Path) -> tuple[dict, dict[str, bytes], list[str]]:
    """Validate and retain the exact bytes that will later be built."""
    manifest = json.loads((root / "verification/manifest.json").read_text(encoding="utf-8"))
    if manifest.get("schema_version") != 1:
        raise VerificationError("Unsupported manifest schema_version")
    modules = [x if x.startswith("Resonance.") else "Resonance." + x
               for x in string_list(manifest.get("modules"), "modules")]
    if len(modules) != EXPECTED_MODULES or len(set(modules)) != EXPECTED_MODULES:
        raise VerificationError(f"The package must contain exactly {EXPECTED_MODULES} distinct modules")
    if any(not NAME.fullmatch(x) or not x.startswith("Resonance.") for x in modules):
        raise VerificationError("Invalid module name")
    allowed = string_list(manifest.get("allowed_axioms"), "allowed_axioms")
    if set(allowed) != STANDARD_AXIOMS:
        raise VerificationError("allowed_axioms must be exactly the three documented standard axioms")
    toolchain = manifest.get("toolchain")
    if not isinstance(toolchain, str) or not re.fullmatch(r"leanprover/lean4:v\d+\.\d+\.\d+", toolchain):
        raise VerificationError("Expected an exact released Lean toolchain")
    revision = manifest.get("mathlib_revision")
    if not isinstance(revision, str) or not re.fullmatch(r"[0-9a-f]{40}", revision):
        raise VerificationError("Expected a full Mathlib Git commit")
    if manifest.get("whole_paper_end_to_end_verified", False) is not False:
        raise VerificationError("This package does not establish whole-paper end-to-end verification")
    expected_paths = {x.replace(".", "/") + ".lean" for x in modules} | CONFIG_FILES
    hashes = manifest.get("source_sha256")
    if not isinstance(hashes, dict) or set(hashes) != expected_paths:
        raise VerificationError("source_sha256 must cover exactly the listed modules and four configuration files")
    actual_sources = {p.relative_to(root).as_posix() for p in (root / "Resonance").rglob("*.lean")}
    if actual_sources != expected_paths - CONFIG_FILES:
        raise VerificationError("Unlisted or missing .lean sources under Resonance/")
    payloads = {}
    for relative in sorted(expected_paths):
        path = PurePosixPath(relative)
        if path.is_absolute() or ".." in path.parts or "\\" in relative:
            raise VerificationError(f"Unsafe relative source path: {relative}")
        expected = hashes[relative]
        if not isinstance(expected, str) or not SHA256.fullmatch(expected):
            raise VerificationError(f"Invalid SHA-256 for {relative}")
        payload = (root / relative).read_bytes()
        if digest(payload) != expected:
            raise VerificationError(f"Source hash mismatch: {relative}")
        payloads[relative] = payload
    if payloads["lean-toolchain"].decode().strip() != toolchain:
        raise VerificationError("lean-toolchain disagrees with manifest")
    lock = json.loads(payloads["lake-manifest.json"])
    mathlib = [p for p in lock.get("packages", []) if p.get("name") == "mathlib"]
    if len(mathlib) != 1 or mathlib[0].get("rev") != revision:
        raise VerificationError("Lake lockfile disagrees with mathlib_revision")
    collected = []
    seen_modules = set()
    for module in modules:
        code = uncomment(payloads[module.replace(".", "/") + ".lean"].decode("utf-8"))
        forbidden = FORBIDDEN.search(code)
        if forbidden:
            raise VerificationError(f"Forbidden source token {forbidden.group()} in {module}")
        for line in code.splitlines():
            match = re.fullmatch(r"\s*import\s+(.+?)\s*", line)
            if match:
                for imported in match.group(1).split():
                    if imported == "Resonance" or (imported.startswith("Resonance.") and imported not in seen_modules):
                        raise VerificationError(f"Unlisted or out-of-order project import {imported} in {module}")
        collected.extend(declarations(code, module))
        seen_modules.add(module)
    if len(collected) != len(set(collected)):
        raise VerificationError("Duplicate source theorem names across modules")
    umbrella = uncomment(payloads["Resonance.lean"].decode("utf-8"))
    umbrella_imports = []
    for line in umbrella.splitlines():
        if not line.strip():
            continue
        match = re.fullmatch(r"\s*import\s+([\w.]+)\s*", line)
        if not match:
            raise VerificationError("Resonance.lean must contain only the listed imports")
        umbrella_imports.append(match.group(1))
    if umbrella_imports != modules:
        raise VerificationError("Resonance.lean differs from the exact ordered module inventory")
    theorems = string_list(manifest.get("theorems"), "theorems")
    normalized = [normalized_source_name(x) for x in theorems]
    if normalized != collected:
        raise VerificationError("Manifest theorem inventory differs from the complete ordered source inventory")
    roots = string_list(manifest.get("main_roots", []), "main_roots")
    if not set(roots) <= set(theorems):
        raise VerificationError("A main_roots entry is absent from the source theorem inventory")
    return manifest, payloads, modules


PRIVATE_INVENTORY = '''import Resonance
open Lean in
run_cmd do
  for (name, ci) in (← getEnv).constants.toList do
    match ci, privateToUserName? name with
    | .thmInfo _, some userName =>
      if userName.toString.startsWith "Resonance." then
        logInfo m!"PRIVATE_NAME {userName} {name}"
    | _, _ => pure ()
'''


def resolve_private(theorems: list[str], text: str) -> list[str]:
    by_user = {}
    for user, kernel in re.findall(r"PRIVATE_NAME (\S+) (\S+)", text):
        by_user.setdefault(user, []).append(kernel)
    resolved = []
    for requested in theorems:
        normalized = normalized_source_name(requested)
        if normalized.startswith("PRIVATE:"):
            matches = by_user.get(normalized[8:], [])
            if len(matches) != 1:
                raise VerificationError(f"Missing or ambiguous actual private theorem: {requested}")
            if requested.startswith("_private.") and requested != matches[0]:
                raise VerificationError(f"Private kernel name changed: {requested}")
            resolved.append(matches[0])
        else:
            resolved.append(requested)
    return resolved


def type_checker(theorems: list[str], main_roots: list[str]) -> str:
    lines = ["import Resonance", "set_option pp.explicit false", "set_option pp.universes true",
             "set_option pp.fullNames true", "set_option pp.proofs false"]
    for name in theorems:
        if name.startswith("_private."):
            # Numeric Name components cannot safely be printed as Lean source identifiers.
            lines += ["open Lean in", "run_cmd do", "  let mut found := false",
                      "  for (name, ci) in (← getEnv).constants.toList do",
                      "    if name.toString == " + json.dumps(name) + " then",
                      "      match ci with", "      | .thmInfo _ =>", "        found := true",
                      '        logInfo m!"PRIVATE_TYPE {name} : {ci.type}"',
                      '      | _ => throwError "Expected a theorem"',
                      '  unless found do throwError "Missing private theorem"']
        else:
            lines.append("#check " + name)
    for name in main_roots:
        if name.startswith("_private."):
            raise VerificationError("main_roots must name public theorem declarations")
        lines += ["set_option pp.explicit true in", "#check " + name]
    return "\n".join(lines) + "\n"


def parse_cone(text: str, theorems: list[str], allowed: set[str]) -> dict:
    counts = re.findall(r"CONE_COUNTS roots=(\d+) constants=(\d+) unsafe=(\d+) partial=(\d+)", text)
    if len(counts) != 1:
        raise VerificationError("Missing or duplicate proof-cone counts")
    root_count, constant_count, unsafe, partial = map(int, counts[0])
    roots = re.findall(r"CONE_ROOT ([^\s]+)", text)
    constants = re.findall(r"CONE_CONSTANT ([^\s]+)", text)
    axioms = sorted(set(re.findall(r"CONE_AXIOM ([^\s]+)", text)))
    if root_count != len(roots) or len(set(roots)) != len(roots) or not roots:
        raise VerificationError("Incomplete or duplicate theorem-root inventory")
    if constant_count != len(constants) or len(set(constants)) != len(constants):
        raise VerificationError("Incomplete or duplicate dependency-constant inventory")
    if not set(theorems) <= set(roots) or not set(roots) <= set(constants):
        raise VerificationError("The proof cone does not cover every listed and generated theorem root")
    if unsafe or partial or re.search(r"CONE_(?:UNSAFE|PARTIAL)\s", text) or set(axioms) - allowed:
        raise VerificationError("Unsafe/partial dependency or nonstandard axiom in the actual proof cone")
    return {"root_count": root_count, "constant_count": constant_count,
            "unsafe_count": unsafe, "partial_count": partial, "axioms": axioms,
            "roots": sorted(roots), "listed_theorem_count": len(theorems)}


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


class Runner:
    def __init__(self, cwd: Path, logs: Path, timeout: float | None):
        self.cwd, self.logs, self.timeout = cwd, logs, timeout
        self.commands = []

    def run(self, args: list[str], name: str, read: bool = True) -> str:
        if args and Path(args[0]).name in {"lake", "lean", "leanchecker"}:
            require_server_execution()
        started = time.monotonic()
        record = {"argv": args, "log": "logs/" + name, "status": "RUNNING"}
        self.commands.append(record)
        print(f"Running: {' '.join(args)}", flush=True)
        try:
            with (self.logs / name).open("w", encoding="utf-8") as out:
                proc = subprocess.run(args, cwd=self.cwd, stdout=out, stderr=subprocess.STDOUT,
                                      timeout=self.timeout, check=False)
            record["exit_code"] = proc.returncode
            if proc.returncode:
                raise VerificationError(f"Command exited {proc.returncode}; see logs/{name}")
            record["status"] = "PASS"
        except BaseException:
            record["status"] = "FAILED_OR_INTERRUPTED"
            raise
        finally:
            record["elapsed_seconds"] = round(time.monotonic() - started, 3)
        return (self.logs / name).read_text(encoding="utf-8") if read else ""


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-only", action="store_true", help="Check source equivalence and inventories only; do not run Lean")
    parser.add_argument("--fresh", action="store_true", help="Also run lake env leanchecker --fresh Resonance")
    parser.add_argument("--output", type=Path, help="New evidence directory (must not already exist)")
    parser.add_argument("--timeout", type=float, help="Optional positive timeout in seconds for each external command")
    args = parser.parse_args()
    if args.source_only and args.fresh:
        parser.error("--source-only and --fresh are mutually exclusive")
    if args.timeout is not None and args.timeout <= 0:
        parser.error("--timeout must be positive")
    if not args.source_only:
        try:
            require_server_execution()
        except VerificationError as error:
            print(str(error), file=sys.stderr)
            return 2
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    output = args.output.resolve() if args.output else REPOSITORY / ".verification-runs" / stamp
    output.mkdir(parents=True, exist_ok=False)
    logs = output / "logs"
    logs.mkdir()
    result = {"schema_version": 1, "utc": stamp, "status": "RUNNING",
              "verification_mode": "source-only" if args.source_only else ("fresh" if args.fresh else "default"),
              "whole_paper_end_to_end_verified": False,
              "source_equivalence": False, "historical_evidence_used_as_runtime_result": False,
              "fresh_replay": "not_requested", "commands": []}
    runner = None
    try:
        manifest_bytes = (REPOSITORY / "verification/manifest.json").read_bytes()
        manifest, payloads, modules = source_snapshot(REPOSITORY)
        result.update(source_equivalence=True, module_count=len(modules),
                      listed_theorem_count=len(manifest["theorems"]),
                      manifest_sha256=digest(manifest_bytes),
                      verifier_sha256=digest(Path(__file__).read_bytes()))
        (output / "manifest.json").write_bytes(manifest_bytes)
        write_json(output / "source-sha256.json", {p: digest(b) for p, b in payloads.items()})
        if args.source_only:
            result["status"] = "SOURCE_EQUIVALENCE_ONLY"
            return 0
        packages = REPOSITORY / ".lake/packages"
        mathlib = packages / "mathlib"
        if not mathlib.is_dir():
            raise VerificationError("Mathlib dependencies are not installed. Follow docs/VERIFICATION.md first.")
        clean = output / "clean"
        (clean / ".lake").mkdir(parents=True)
        for relative, payload in payloads.items():
            target = clean / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(payload)
        (clean / ".lake/packages").symlink_to(packages.resolve(), target_is_directory=True)
        checker = (REPOSITORY / "verification/CheckAxioms.lean").read_bytes()
        (clean / "CheckAxioms.lean").write_bytes(checker)
        (output / "CheckAxioms.lean").write_bytes(checker)
        (output / "verify.py").write_bytes(Path(__file__).read_bytes())
        result["checker_sha256"] = digest(checker)
        result["project_build"] = "fresh directory; dependency package build caches may be reused"
        runner = Runner(clean, logs, args.timeout)
        result["commands"] = runner.commands
        version = runner.run(["lake", "env", "lean", "--version"], "toolchain.log").strip()
        expected_version = manifest["toolchain"].split(":v", 1)[1]
        if not re.search(r"\bLean \(version " + re.escape(expected_version) + r"(?:,|\))", version):
            raise VerificationError("Runtime Lean version differs from the manifest toolchain")
        result["lean_version"] = version
        revision = runner.run(["git", "-C", str(mathlib.resolve()), "rev-parse", "HEAD"], "mathlib-revision.log").strip()
        if revision != manifest["mathlib_revision"]:
            raise VerificationError("Installed Mathlib commit differs from the manifest")
        status = runner.run(["git", "-C", str(mathlib.resolve()), "status", "--porcelain", "--untracked-files=no"], "mathlib-status.log")
        if status.strip():
            raise VerificationError("Installed Mathlib has modified tracked source files")
        result["mathlib_revision"] = revision
        runner.run(["lake", "build", "Resonance"], "build.log", read=False)
        # Lake must not silently move the lockfile or any source in the clean copy.
        for relative, payload in payloads.items():
            if (clean / relative).read_bytes() != payload:
                raise VerificationError(f"Build changed a frozen source/configuration file: {relative}")
        (clean / "PrivateInventory.lean").write_text(PRIVATE_INVENTORY, encoding="utf-8")
        private_text = runner.run(["lake", "env", "lean", "PrivateInventory.lean"], "private-inventory.log")
        resolved = resolve_private(manifest["theorems"], private_text)
        write_json(output / "resolved-theorems.json", dict(zip(manifest["theorems"], resolved)))
        audit = type_checker(resolved, manifest.get("main_roots", []))
        (clean / "CheckTypes.lean").write_text(audit, encoding="utf-8")
        (output / "CheckTypes.lean").write_text(audit, encoding="utf-8")
        runner.run(["lake", "env", "lean", "CheckTypes.lean"], "theorem-types.log", read=False)
        cone_text = runner.run(["lake", "env", "lean", "CheckAxioms.lean"], "actual-proof-cone.log")
        cone = parse_cone(cone_text, resolved, set(manifest["allowed_axioms"]))
        write_json(output / "actual-proof-cone.json", cone)
        result["actual_proof_cone"] = {k: v for k, v in cone.items() if k != "roots"}
        result["axiom_audit_method"] = "Union of transitive type/value dependencies of all imported Resonance theorem roots, including private and generated roots; not the exact per-theorem axiom set."
        main_axioms = (REPOSITORY / "verification/MainAxioms.lean").read_bytes()
        (clean / "MainAxioms.lean").write_bytes(main_axioms)
        (output / "MainAxioms.lean").write_bytes(main_axioms)
        result["main_axioms_checker_sha256"] = digest(main_axioms)
        main_log = runner.run(["lake", "env", "lean", "MainAxioms.lean"], "main-axioms.log")
        printed = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", main_log)
        root_axioms = {name: [a.strip() for a in body.split(",") if a.strip()] for name, body in printed}
        if set(root_axioms) != set(manifest["main_roots"]) or any(
            set(axioms) - STANDARD_AXIOMS for axioms in root_axioms.values()
        ):
            raise VerificationError("Missing main-root axiom output or nonstandard main-root axiom")
        result["main_root_axioms"] = root_axioms
        if args.fresh:
            result["fresh_replay"] = "RUNNING"
            runner.run(["lake", "env", "leanchecker", "--fresh", "Resonance"], "fresh-replay.log", read=False)
            result["fresh_replay"] = "PASS; same Lean kernel, not an independent proof assistant"
        result["status"] = "PASS_FOR_FROZEN_DECLARATIONS_ONLY"
        return 0
    except (Exception, KeyboardInterrupt) as error:
        result["status"] = "FAILED_OR_INTERRUPTED"
        result["error"] = str(error) or type(error).__name__
        print(f"Verification did not pass: {result['error']}", file=sys.stderr, flush=True)
        return 130 if isinstance(error, KeyboardInterrupt) else 1
    finally:
        write_json(output / "result.json", result)
        print(f"Result: {result['status']}; evidence: {output}", flush=True)


if __name__ == "__main__":
    sys.exit(main())
