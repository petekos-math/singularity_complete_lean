#!/usr/bin/env python3
"""Build the full Fuchsian singularity proof and audit its logical dependencies."""
from pathlib import Path
import re
import hashlib
import json
import subprocess

ROOT = Path(__file__).resolve().parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def run(*args):
    result = subprocess.run(args, cwd=ROOT, text=True, capture_output=True)
    output = result.stdout + result.stderr
    print(output, end="", flush=True)
    if result.returncode:
        raise SystemExit(result.returncode)
    return output


# All project-local imports must be present and reachable from the root.
modules = {"Singularity." + p.stem: p for p in (ROOT / "Singularity").glob("*.lean")}
modules["Singularity"] = ROOT / "Singularity.lean"
reachable = set()
def visit(module):
    if module in reachable:
        return
    if module not in modules:
        raise SystemExit(f"Missing local dependency: {module}")
    reachable.add(module)
    for line in re.findall(r"^import\s+(.+)$", modules[module].read_text(), re.M):
        for dep in line.split():
            if dep.startswith("Singularity."):
                visit(dep)
visit("Singularity")
if reachable != set(modules):
    raise SystemExit(f"Local modules missing from root: {set(modules) - reachable}")

expected = set()
declaration_sources = {}
for path in sorted((ROOT / "Singularity").glob("*.lean")):
    for name in re.findall(r"^(?:theorem|def) ([\w.]+)", path.read_text(), re.M):
        full_name = "Singularity." + name
        if full_name in declaration_sources:
            raise SystemExit(f"Duplicate declaration name: {full_name} in {declaration_sources[full_name]} and {path}")
        declaration_sources[full_name] = path
        expected.add(full_name)

audit_names = set(re.findall(r"^#print axioms (\S+)",
                            (ROOT / "Audit.lean").read_text(), re.M))
if audit_names != expected:
    raise SystemExit(f"Audit coverage mismatch: {audit_names ^ expected}")

build_output = run("lake", "build")
audit_output = run("lake", "env", "lean", "Audit.lean")
statement_output = run("lake", "env", "lean", "THEOREM.lean")
reported = set()
for name, dependencies in re.findall(
        r"'([^']+)' depends on axioms: \[([^\]]*)\]", audit_output):
    reported.add(name)
    axioms = {s.strip() for s in dependencies.split(",") if s.strip()}
    if axioms - ALLOWED:
        raise SystemExit(f"Unexpected axioms for {name}: {axioms - ALLOWED}")
reported.update(re.findall(r"'([^']+)' does not depend on any axioms", audit_output))
if reported != expected:
    raise SystemExit(f"Missing or unexpected audit reports: {reported ^ expected}")

report = (
    "FULL FUCHSIAN THEOREM: the actual hitting measure is singular to visual/Lebesgue measure for every discrete nonelementary subgroup of PSL(2,R), with finite positive semigroup-generating probability support. No symmetry or covolume assumption. The Dirichlet-end argument closes the noncompact full-limit-set case.\n"
    f"Audited {len(expected)} theorem/definition declarations.\n"
    "Allowed axioms: propext, Classical.choice, Quot.sound.\n\n"
    + build_output + "\n" + audit_output
)
(ROOT / "VERIFICATION.txt").write_text(report)
(ROOT / "THEOREM_STATEMENTS.txt").write_text(statement_output)
source_paths = sorted(modules.values()) + [ROOT / name for name in
    ["Audit.lean", "THEOREM.lean", "lean-toolchain", "lakefile.toml", "lake-manifest.json", "verify.py"]]
manifest = {
    "entry_theorem": "Singularity.fuchsian_hittingMeasure_singular",
    "module_count": len(modules) - 1,
    "audited_declaration_count": len(expected),
    "allowed_axioms": sorted(ALLOWED),
    "files": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
              for p in source_paths},
}
(ROOT / "SOURCE_MANIFEST.json").write_text(json.dumps(manifest, indent=2) + "\n")
print(f"Verified {len(expected)} declarations; no additional axioms detected.")
