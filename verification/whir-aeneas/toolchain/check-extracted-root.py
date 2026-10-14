"""Reject partial Charon IR and successful invocations missing the requested root."""
import json
from pathlib import Path
import sys

extraction = json.loads(Path(sys.argv[1]).read_text())
if extraction["has_errors"]:
    raise SystemExit("Charon reported extraction errors; refusing partial IR")
crate = extraction["translated"]


def function_references(value):
    if isinstance(value, dict):
        kind = value.get("kind")
        if isinstance(kind, dict) and isinstance(kind.get("Fun"), int):
            yield kind["Fun"]
        for nested in value.values():
            yield from function_references(nested)
    elif isinstance(value, list):
        for nested in value:
            yield from function_references(nested)


function_ids = {declaration["def_id"] for declaration in crate["fun_decls"] if declaration is not None}
for group in ("fun_decls", "global_decls", "trait_impls"):
    for declaration in crate[group]:
        if declaration is None:
            continue
        missing = sorted(set(function_references(declaration)) - function_ids)
        if missing:
            raise SystemExit(
                "Translated declaration references missing functions; refusing partial IR: "
                + group + "/" + str(declaration["def_id"]) + " -> " + str(missing)
            )

def receiver_types(value, index):
    """Collect only serialized Ty::Adt values, never unrelated deduplication tables."""
    if isinstance(value, dict):
        entry = value.get("Value")
        if isinstance(entry, list) and len(entry) == 2 and entry[0] == index:
            candidate = entry[1]
            if isinstance(candidate, dict) and set(candidate) == {"Adt"}:
                adt = candidate["Adt"]
                if isinstance(adt, dict) and isinstance(adt.get("id"), int) and "generics" in adt:
                    yield candidate
        for nested in value.values():
            yield from receiver_types(nested, index)
    elif isinstance(value, list):
        for nested in value:
            yield from receiver_types(nested, index)


def concrete_name(name):
    if all("Ident" in part for part in name):
        return [part["Ident"][0] for part in name]
    if len(name) < 2 or not all("Ident" in part for part in name[:-2] + name[-1:]):
        return None
    impl = name[-2].get("Impl", {}).get("Ty")
    if impl is None or impl.get("kind") != "InherentImplBlock":
        return None
    receiver = impl["skip_binder"]
    if "Deduplicated" in receiver:
        candidates = {
            json.dumps(candidate, sort_keys=True): candidate
            for candidate in receiver_types(extraction, receiver["Deduplicated"])
        }
        if len(candidates) != 1:
            raise SystemExit("Inherent receiver type is absent or ambiguous; refusing root validation")
        receiver = next(iter(candidates.values()))
    elif "Value" in receiver:
        receiver = receiver["Value"][1]
    if set(receiver) != {"Adt"} or not isinstance(receiver["Adt"].get("id"), int):
        return None
    declarations = [
        declaration for declaration in crate["type_decls"]
        if declaration is not None and declaration["def_id"] == receiver["Adt"]["id"]
    ]
    if len(declarations) != 1:
        raise SystemExit("Inherent receiver declaration is absent or ambiguous")
    type_name = declarations[0]["item_meta"]["name"]
    if not all("Ident" in part for part in type_name):
        return None
    return [part["Ident"][0] for part in type_name] + [name[-1]["Ident"][0]]


expected = sys.argv[2].split("::")
retained = []
for declaration in crate["fun_decls"]:
    if declaration is None:
        continue
    name = declaration["item_meta"]["name"]
    if not name or name[-1].get("Ident", [None])[0] != expected[-1]:
        continue
    if concrete_name(name) == expected:
        retained.append(declaration)
if len(retained) != 1 or not isinstance(retained[0]["body"], dict) or "Structured" not in retained[0]["body"]:
    raise SystemExit("Requested concrete extraction root is absent or has no translated body: " + sys.argv[2])
print("Retained concrete extraction root: " + sys.argv[2])
