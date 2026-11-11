#!/usr/bin/env python3
"""Check that crates/, lakefile.toml, claims.toml and the Cargo workspace agree.

Needs no Lean.

- Every modelled workspace crate has a crates/<crate>/crate.toml, and every crate.toml models one.
- Each library is in lakefile.toml, rooted in the directory its state selects, and a default target.
- A crate's Lean imports only its own library, its Cargo dependencies' libraries and the shared ones.
- Every statement module a crate.toml names exists.
- Every claims.toml entry is well formed.
"""

import re
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RUST = ROOT.parents[1]
STATEMENT = ROOT.parent / "Statement"

# Workspace crates with no model.
# The benchmark harness is never linked by the prover.
NOT_MODELLED = {"bench"}
# The keys a crate.toml may set.
KEYS = {"lean_lib", "state", "package", "features", "start_from", "charon_args", "rustflags",
        "watch", "spec", "oracle", "mirror"}
# The libraries every crate may import: the Rust models and their extensions.
SHARED = {"Aeneas", "CoreModels", "HaxExt"}
# One import line of a Lean module, with or without the module-system keywords.
IMPORT = re.compile(r"^(?:public )?(?:meta )?import (\S+)", re.M)

errors = []


def error(msg):
    """Record one failure; every check runs before the script exits."""
    errors.append(msg)


def cargo_deps(manifest):
    """The dependencies a crate links with no feature enabled, on every target."""
    m = tomllib.loads(manifest.read_text())
    # Platform-specific dependencies count: a model covers every target.
    tables = [m.get("dependencies", {})]
    tables += [t.get("dependencies", {}) for t in m.get("target", {}).values()]
    # An optional dependency is linked only through a feature, which extraction leaves off.
    return {name for t in tables for name, spec in t.items()
            if not (isinstance(spec, dict) and spec.get("optional"))}


def main():
    # Phase 1: the Lake libraries and the crates on both sides.
    lake = tomllib.loads((ROOT / "lakefile.toml").read_text())
    libs = {lib["name"]: lib for lib in lake.get("lean_lib", [])}
    defaults = set(lake.get("defaultTargets", []))

    workspace = {d.name for d in (RUST / "crates").iterdir() if (d / "Cargo.toml").is_file()}
    modelled = {d.name: d for d in (ROOT / "crates").iterdir()
                if d.is_dir() and not d.name.startswith("_")}

    # Every crate is modelled exactly once, and nothing else is.
    for name in sorted(workspace - NOT_MODELLED - modelled.keys()):
        error(f"crates/{name}: the workspace crate has no directory here (copy crates/_template)")
    for name in sorted(modelled.keys() - workspace):
        error(f"crates/{name}: no workspace crate of that name")

    # Phase 2: each crate.toml, against the lakefile and the file tree.
    crate_lib = {}
    configs = {}
    for name, d in sorted(modelled.items()):
        f = d / "crate.toml"
        if not f.is_file():
            error(f"crates/{name}: no crate.toml")
            continue
        c = tomllib.loads(f.read_text())
        configs[name] = c
        for k in sorted(c.keys() - KEYS):
            error(f"crates/{name}/crate.toml: unknown key `{k}`")
        if c.get("state") not in {"extracted", "scoped", "stub"}:
            error(f"crates/{name}/crate.toml: state must be extracted, scoped or stub")
            continue
        lib = c.get("lean_lib", "")
        crate_lib[name] = lib
        # The state selects the library root.
        # The other directory must not linger.
        src = "stub" if c["state"] == "stub" else "extraction"
        other = "extraction" if src == "stub" else "stub"
        if c["state"] != "scoped" and c.get("start_from"):
            error(f"crates/{name}/crate.toml: start_from is for state = \"scoped\" only")
        if lib not in libs:
            error(f"crates/{name}: lakefile.toml has no [[lean_lib]] named `{lib}`")
        elif libs[lib].get("srcDir") != f"crates/{name}/{src}":
            error(f"lakefile.toml: `{lib}` must have srcDir = \"crates/{name}/{src}\"")
        if lib not in defaults:
            error(f"lakefile.toml: `{lib}` is not a default target")
        if not (d / src / f"{lib}.lean").is_file():
            error(f"crates/{name}/{src}/{lib}.lean: missing, the library root")
        if (d / other).exists():
            error(f"crates/{name}/{other}/: present, but state = \"{c['state']}\"")
        # A spec module is a path under the statement package.
        for mod in c.get("spec", []):
            if not (STATEMENT.parent / (mod.replace(".", "/") + ".lean")).is_file():
                error(f"crates/{name}/crate.toml: spec names `{mod}`, which is no Statement module")

    # Phase 3: imports follow the Cargo graph.
    for name, c in sorted(configs.items()):
        lib = crate_lib.get(name)
        allowed = SHARED | {lib} | {crate_lib[dep] for dep in cargo_deps(RUST / "crates" / name / "Cargo.toml")
                                    if dep in crate_lib}
        for f in sorted((modelled[name]).rglob("*.lean")):
            # Templates sit beside the generated code and are never built.
            if f.name.endswith("_Template.lean"):
                continue
            for imp in IMPORT.findall(f.read_text()):
                if imp.split(".")[0] not in allowed:
                    error(f"{f.relative_to(ROOT)}: imports `{imp}`, which is no Cargo dependency of `{name}`")

    # Phase 4: claims.toml names only theorems of the claims namespace.
    claims = tomllib.loads((ROOT / "claims.toml").read_text()).get("claim", [])
    for c in claims:
        if set(c) != {"name", "axioms"} or not c["name"].startswith("Refinement.Claims."):
            error(f"claims.toml: malformed entry {c}")

    # Report every failure at once.
    for e in errors:
        print(f"error: {e}", file=sys.stderr)
    if errors:
        sys.exit(1)
    print(f"check-layout: {len(configs)} crate(s), {len(claims)} claim(s); crates/, lakefile.toml and Cargo agree")


if __name__ == "__main__":
    main()
