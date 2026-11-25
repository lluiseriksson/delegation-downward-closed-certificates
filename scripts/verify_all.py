"""End-to-end deterministic verification harness for Paper 54 (DELEG-DC-CERT-1.0).

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path
from typing import Dict, List

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from src.delegation_certifier import verify_certificate_file

MANIFEST_PATH = ROOT / "SHA256_MANIFEST.json"
FORBIDDEN_LEAN_TOKENS = ["sorry", "axiom ", "Classical.choice", "Lean.ofReduceBool", "Lean.trustCompiler"]
FORBIDDEN_PY_TOKENS = ["float(", "math.", "numpy"]


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    h.update(path.read_bytes())
    return h.hexdigest()


def collect_tracked_files() -> List[Path]:
    patterns = [
        "LICENSE",
        "README.md",
        "pyproject.toml",
        "lean/lean-toolchain",
        "lean/lakefile.toml",
        "lean/DelegationBounds.lean",
        "lean/AuditAxioms.lean",
        "src/__init__.py",
        "src/delegation_exact.py",
        "src/delegation_certifier.py",
        "scripts/run_all_experiments.py",
        "scripts/make_figures.py",
        "scripts/verify_all.py",
        "tests/test_suite.py",
        "paper/main.tex",
        "paper/references.bib",
    ]
    files = [ROOT / p for p in patterns if (ROOT / p).exists()]
    files.extend(sorted((ROOT / "certificates").glob("*.cert.json")))
    files.extend(sorted((ROOT / "results").glob("*.json")))
    files.extend(sorted((ROOT / "paper" / "figures").glob("*.png")))
    return files


def audit_lean() -> None:
    lean_dir = ROOT / "lean"
    src_text = (lean_dir / "DelegationBounds.lean").read_text(encoding="utf-8")
    for tok in FORBIDDEN_LEAN_TOKENS:
        if tok in src_text:
            raise AssertionError(f"Forbidden token '{tok}' found in DelegationBounds.lean")
    r1 = subprocess.run(["lake", "build"], cwd=lean_dir, capture_output=True, text=True)
    if r1.returncode != 0 or "warning:" in (r1.stdout + r1.stderr).lower():
        raise AssertionError(f"lake build failed or warned:\n{r1.stdout}\n{r1.stderr}")
    r2 = subprocess.run(["lake", "env", "lean", "-j", "1", "AuditAxioms.lean"], cwd=lean_dir, capture_output=True, text=True)
    if r2.returncode != 0:
        raise AssertionError(f"AuditAxioms.lean failed:\n{r2.stdout}\n{r2.stderr}")
    out = r2.stdout + r2.stderr
    for forbidden in ("sorryAx", "Classical.choice", "Lean.ofReduceBool", "Lean.trustCompiler"):
        if forbidden in out:
            raise AssertionError(f"Forbidden axiom '{forbidden}' reported:\n{out}")
    lines = [ln for ln in out.splitlines() if "depends on axioms:" in ln or "does not depend on any axioms" in ln]
    if len(lines) != 18:
        raise AssertionError(f"Expected 18 axiom audit lines, got {len(lines)}")
    print("[PASS] Lean 4.35.0 build & 18/18 axiom audit (0 warnings, 0 sorry, 0 Classical.choice).")


def audit_python_sources() -> None:
    for py_file in sorted((ROOT / "src").glob("*.py")):
        txt = py_file.read_text(encoding="utf-8")
        for tok in FORBIDDEN_PY_TOKENS:
            if tok in txt:
                raise AssertionError(f"Forbidden token '{tok}' in {py_file.name}")
    print("[PASS] Zero-float static audit passed on src/*.py.")


def audit_certificates() -> None:
    certs = sorted((ROOT / "certificates").glob("*.cert.json"))
    if len(certs) != 16:
        raise AssertionError(f"Expected 16 certificates, found {len(certs)}")
    for c in certs:
        verify_certificate_file(c)
    print(f"[PASS] Replayed all {len(certs)}/16 canonical DELEG-DC-CERT-1.0 certificates.")


def run_pytest() -> None:
    r = subprocess.run([sys.executable, "-m", "pytest", "-q"], cwd=ROOT, capture_output=True, text=True)
    if r.returncode != 0:
        raise AssertionError(f"pytest failed:\n{r.stdout}\n{r.stderr}")
    print(f"[PASS] pytest passed: {r.stdout.strip()}")


def write_or_check_manifest(write_mode: bool) -> None:
    files = collect_tracked_files()
    current: Dict[str, str] = {f.relative_to(ROOT).as_posix(): sha256_file(f) for f in files}
    if write_mode:
        MANIFEST_PATH.write_text(json.dumps(current, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(f"[PASS] Wrote SHA256_MANIFEST.json ({len(current)} files).")
    else:
        saved = json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
        if saved != current:
            raise AssertionError("SHA-256 manifest mismatch!")
        print(f"[PASS] Verified SHA256_MANIFEST.json ({len(current)}/{len(current)} exact hashes).")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write-manifest", action="store_true")
    args = parser.parse_args()
    audit_lean()
    audit_python_sources()
    audit_certificates()
    run_pytest()
    write_or_check_manifest(args.write_manifest)


if __name__ == "__main__":
    main()
