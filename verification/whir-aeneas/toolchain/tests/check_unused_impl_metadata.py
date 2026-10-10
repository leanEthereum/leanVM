"""Check the generator's missing-trait metadata guard on pinned Charon output."""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile


def value_id_max(value):
    if isinstance(value, dict):
        tagged = value.get("Value")
        own = tagged[0] if isinstance(tagged, list) and len(tagged) == 2 and isinstance(tagged[0], int) else -1
        return max([own] + [value_id_max(child) for child in value.values()])
    if isinstance(value, list):
        return max([-1] + [value_id_max(child) for child in value])
    return -1


def main():
    generator, llbc_path = sys.argv[1:]
    data = json.loads(Path(llbc_path).read_text())
    crate = data["translated"]
    declared = {decl["def_id"] for decl in crate["trait_decls"] if decl is not None}
    unused = next(impl for impl in crate["trait_impls"] if impl is not None and not impl["methods"] and impl["impl_trait"]["id"] not in declared)
    with tempfile.TemporaryDirectory(prefix="aeneas-metadata-") as directory:
        accepted = subprocess.run([generator, "-backend", "lean", "-all-computable", "-no-progress-bar", "-dest", directory, llbc_path], text=True, capture_output=True)
        assert accepted.returncode == 0, accepted.stdout + accepted.stderr
        # Add a semantic reference in another impl's signature metadata, not a declaration/name occurrence.
        negative = copy.deepcopy(data)
        target = next(impl for impl in negative["translated"]["trait_impls"] if impl is not None and impl["def_id"] != unused["def_id"])
        reference = {
            "kind": {"TraitImpl": {"id": unused["def_id"], "generics": {"regions": [], "types": [], "const_generics": [], "trait_refs": []}}},
            "trait_decl_ref": {"regions": [], "skip_binder": copy.deepcopy(unused["impl_trait"])},
        }
        target["implied_trait_refs"].append({"Value": [value_id_max(data) + 1, reference]})
        path = Path(directory) / "referenced.llbc"
        path.write_text(json.dumps(negative))
        rejected = subprocess.run([generator, "-backend", "lean", "-no-progress-bar", "-dest", directory, str(path)], text=True, capture_output=True)
        assert rejected.returncode != 0 and "Missing trait declaration for a referenced or nonempty impl" in rejected.stdout + rejected.stderr, rejected.stdout + rejected.stderr
        print("Unreferenced empty impl translated; referenced empty impl rejected by the guard.")


if __name__ == "__main__":
    main()
