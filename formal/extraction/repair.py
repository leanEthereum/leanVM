#!/usr/bin/env python3
"""Get the extraction clean again after the Rust moved under it.

    repair.py patches                 re-fit every pre/ patch to the source as it stands
    repair.py extract [crate dir]...  extract, and leave opaque what no longer translates (every crate
                                      with a scenario, when none is named)

Both say what they did, crate by crate; neither replaces
reading the result. The crates are taken in dependency order: a crate's extraction imports
those of the crates it uses.

**patches.** A hunk whose context is still in the source, exactly, is kept; any other is
dropped, and a patch left empty is deleted. Nothing is merged: a hunk that meets changed code
is not guessed at, and what it rewrote comes back as a rejection of `extract`, to be patched
again or left opaque. A patch whose paths name a crate directory that is gone is read against
the directory it sits in. Run `hax.sh test` after: a kept hunk can still be wrong for the new code.

**extract.** Runs `hax.sh extract -p <package>` and builds the package's `Extraction` in Lean,
until both pass or a round changes nothing. After each round, every definition Aeneas left a
`sorry` in, ignored the body of, or that Lean rejects goes on the scenario's `opaque` list, by
the Rust name in its doc comment, under a "Not yet triaged" heading, with what was reported. An
opaque item whose own signature Lean rejects goes on `exclude` instead.
"""

import argparse
import json
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(subprocess.check_output(["git", "rev-parse", "--show-toplevel"], text=True).strip())
WORKSPACE = ROOT / "formal" / "extraction"
ANSI = re.compile(r"\x1b\[[0-9;]*m")
HEADING = "  # Not yet triaged: left here by repair.py with what Aeneas or Lean reported. Each is to be\n  # patched, modelled, or reduced to a reportable case.\n"


def run(args, **kwargs):
    return subprocess.run(args, cwd=kwargs.pop("cwd", ROOT), capture_output=True, text=True, **kwargs)


def scenarios():
    """Each crate directory that declares a scenario, with the scenario's name."""
    found = {}
    for toml in [*ROOT.glob("crates/*/hax.toml"), *ROOT.glob("crates/*/*/hax.toml")]:
        match = re.search(r"^\[scenario\.([^\]]+)\]", toml.read_text(), re.M)
        if match:
            found[toml.parent] = match.group(1)
    return found


# ---------------------------------------------------------------------------------------------
# patches


def hunks_of(patch):
    """The patch as (file header, [hunk]) per file."""
    files = []
    for part in re.split(r"(?m)^(?=diff --git )", patch):
        if not part.startswith("diff --git "):
            continue
        pieces = re.split(r"(?m)^(?=@@ )", part)
        files.append((pieces[0], pieces[1:]))
    return files


def heading_of(patch):
    """What stands before the patch's first diff: its heading (README.md, "Patches")."""
    return re.split(r"(?m)^(?=diff --git )", patch, maxsplit=1)[0] if "diff --git " in patch else ""


def refit(crate, patch_path):
    """Keep the hunks of the patch that apply to the working tree, and leave them applied."""
    text = patch_path.read_text()
    here = str(crate.relative_to(ROOT))
    named = set(re.findall(r"^diff --git a/(crates/(?:stable_prover/)?[^/]+)/", text, re.M))
    for old in named:
        if not (ROOT / old).is_dir() or not (ROOT / old / "src").is_dir():
            text = text.replace(f"a/{old}/", f"a/{here}/").replace(f"b/{old}/", f"b/{here}/")
    kept = dropped = 0
    before = run(["git", "diff", "--", here]).stdout
    for header, hunks in hunks_of(text):
        for hunk in hunks:
            applied = subprocess.run(["git", "apply", "--recount", "-"], cwd=ROOT, input=header + hunk, text=True, capture_output=True)
            kept, dropped = (kept + 1, dropped) if applied.returncode == 0 else (kept, dropped + 1)
    after = run(["git", "diff", "--", here]).stdout
    return kept, dropped, before, after


def patches():
    strip = run([sys.executable, "formal/extraction/mechanical.py"]).stdout
    if strip:
        subprocess.run(["git", "apply", "-"], cwd=ROOT, input=strip, text=True, check=True)
    subprocess.run(["git", "add", "-A", "--", "crates"], cwd=ROOT, check=True)  # the strip is the base of every diff below
    try:
        for crate in sorted(scenarios()):
            here = str(crate.relative_to(ROOT))
            for patch in sorted(crate.glob("proofs/*/patches/pre/*.patch")):
                heading = heading_of(patch.read_text())
                kept, dropped, _, _ = refit(crate, patch)
                diff = run(["git", "diff", "--", f"{here}/src"]).stdout
                if not diff.strip():
                    patch.unlink()
                elif dropped:
                    patch.write_text(heading + diff)
                subprocess.run(["git", "add", "-A", "--", f"{here}/src"], cwd=ROOT, check=True)
                state = "deleted" if not diff.strip() else "as it was" if not dropped else "reduced"
                print(f"{patch.relative_to(ROOT)}: {kept} hunks kept, {dropped} dropped ({state})")
    finally:
        # Back to the committed source; the patch files stay.
        subprocess.run(["git", "reset", "-q", "--", "crates"], cwd=ROOT, check=True)
        sources = [str(p.relative_to(ROOT)) for p in [*ROOT.glob("crates/*/src"), *ROOT.glob("crates/*/*/src")]]
        subprocess.run(["git", "checkout", "-q", "--", *sources], cwd=ROOT, check=True)


# ---------------------------------------------------------------------------------------------
# extract


def split_path(name):
    """The `::`-separated segments of a Rust path, braces and angle brackets kept whole."""
    segments, depth, start, i = [], 0, 0, 0
    while i < len(name):
        c = name[i]
        if c in "{<(":
            depth += 1
        elif c in "}>)" and not (c == ">" and name[i - 1] == "-"):
            depth -= 1
        elif depth == 0 and name.startswith("::", i):
            segments.append(name[start:i])
            start = i + 2
            i += 1
        i += 1
    segments.append(name[start:])
    return segments


def without_generics(text):
    out, depth = [], 0
    for i, c in enumerate(text):
        if c == "<":
            depth += 1
        elif c == ">" and text[i - 1] != "-":
            depth -= 1
        elif depth == 0:
            out.append(c)
    return "".join(out)


def pattern(name, crate):
    """The Charon name pattern of the Rust item a doc comment names; closures go to their function."""
    for segment in split_path(name):
        if segment.startswith("{impl core::ops::function::Fn") and "{closure" in segment:
            depth = 0
            for i, c in enumerate(segment):
                if c in "{<(":
                    depth += 1
                elif c in "}>)" and segment[i - 1] != "-":
                    depth -= 1
                elif depth == 1 and segment.startswith(" for ", i):
                    name = segment[i + 5 : -1]
                    break
            break
    cut = [i for i, seg in enumerate(split_path(name)) if seg.startswith("{closure")]
    if cut:
        name = "::".join(split_path(name)[: cut[0]])
    own = re.compile(rf"(?<![\w:]){re.escape(crate)}::")
    segments = []
    for segment in split_path(name):
        if segment.startswith("{impl "):
            trait, _, ty = segment[6:-1].partition(" for ")
            segment = "{impl " + own.sub("crate::", without_generics(trait)) + " for " + own.sub("crate::", without_generics(ty)) + "}"
        elif segment.startswith("{"):
            segment = "_"
        else:
            segment = without_generics(segment)
        segments.append(segment)
    if segments[0] == crate:
        segments[0] = "crate"
    for i, segment in enumerate(segments):
        if segment.startswith("{impl "):  # a trait impl is named without the module it is written in
            return "::".join(segments[i:])
    return "::".join(segments)


ITEM = re.compile(r"^\s*(?:pub(?:\([^)]*\))?\s+)?(?:const\s+|unsafe\s+|async\s+)*(fn|const|static)\s+([A-Za-z_0-9]+)")


def item_at(crate, patched, file, line):
    """The pattern of the function or constant of the patched source at `file:line`."""
    if file not in patched:
        patched[file] = run(["formal/extraction/hax.sh", "patched", "cat", file]).stdout.split("\n")
    lines = patched[file]
    start = line - 1
    if start >= len(lines):
        return None
    at_item = ITEM.match(lines[start]) or lines[start].lstrip().startswith(("#[", "///"))
    while 0 <= start < len(lines) and not ITEM.match(lines[start]):
        start += 1 if at_item else -1  # an error inside a body: the function it is in
    if not 0 <= start < len(lines):
        return None
    name = ITEM.match(lines[start]).group(2)
    indent = len(lines[start]) - len(lines[start].lstrip())
    owner = None
    for back in range(start - 1, -1, -1):
        text = lines[back]
        if text.strip() and len(text) - len(text.lstrip()) < indent and not text.lstrip().startswith(("//", "#[", ")", "}")):
            owner = text.strip()
            break
    module = pathlib.Path(file).relative_to(crate.relative_to(ROOT) / "src").with_suffix("").parts
    module = [m for m in module if m not in ("lib", "mod", "main")]
    path = ["crate", *module]
    if owner and owner.startswith(("impl", "unsafe impl")):
        path.append("_")
    elif owner and re.match(r"(?:pub(?:\([^)]*\))?\s+)?mod\s+(\w+)", owner):
        path.append(re.match(r"(?:pub(?:\([^)]*\))?\s+)?mod\s+(\w+)", owner).group(1))
    elif owner and re.match(r"(?:pub(?:\([^)]*\))?\s+)?(?:const\s+|unsafe\s+)*fn\s+(\w+)", owner):
        return "::".join(path + [re.match(r"(?:pub(?:\([^)]*\))?\s+)?(?:const\s+|unsafe\s+)*fn\s+(\w+)", owner).group(1)])
    return "::".join(path + [name])


DOC = re.compile(r"/-- (?:Trait implementation: )?\[([^\n]*?)\](?::[^\n]*)?\n(?:\s+Source: '([^']*)', lines (\d+):)?")


def definitions(path):
    """The line each documented definition starts at, with the Rust name in its doc comment."""
    text = path.read_text()
    starts = []
    for match in DOC.finditer(text):
        starts.append((text.count("\n", 0, match.start()) + 1, match.group(1)))
    return text, starts


def definition_at(starts, line):
    name = None
    for start, rust in starts:
        if start > line:
            break
        name = rust
    return name


def with_sorry(path):
    text, starts = definitions(path)
    found = set()
    for number, line in enumerate(text.split("\n"), 1):
        if re.search(r"\bsorry\b", line) and not line.lstrip().startswith(("--", "/-")):
            name = definition_at(starts, number)
            if name:
                found.add(name)
    return found


def add_entries(toml, key, entries):
    """Append `entries` (pattern -> reason) to the scenario's `key` list, under the "Not yet triaged" heading."""
    text = toml.read_text()
    if key == "exclude":  # an opaque item whose signature does not translate moves here
        block = re.search(r"(?ms)^exclude = \[\n(.*?)^\]\n", text)
        already = set(re.findall(r'^\s*"([^"]+)",', block.group(1), re.M)) if block else set()
        entries = {p: why for p, why in entries.items() if p not in already}
        moved = "".join(l for l in text.splitlines(True) if not any(re.match(rf'\s*"{re.escape(p)}",', l) for p in entries))
        if moved != text:
            text = moved
            toml.write_text(text)
    present = set(re.findall(r'^\s*"([^"]+)",', text, re.M))
    entries = {p: why for p, why in entries.items() if p not in present}
    if not entries:
        return {}
    lines = "".join(f'  "{p}",  # {why}\n' for p, why in sorted(entries.items()))
    match = re.search(rf"(?ms)^{key} = \[\n(.*?)^\]\n", text)
    if not match:
        scenario = re.search(r"(?m)^\[scenario\.[^\]]+\]\n(?:backend = [^\n]*\n)?", text)
        block = f"{key} = [\n" + (HEADING if key == "opaque" else "") + lines + "]\n"
        text = text[: scenario.end()] + block + text[scenario.end() :]
    else:
        heading = HEADING
        body = match.group(1)
        if key == "opaque" and heading not in body:
            body = body.rstrip("\n") + "\n\n" + heading if body.strip() else heading
        text = text[: match.start(1)] + body + lines + text[match.end(1) :]
    toml.write_text(text)
    return entries


def lean_errors(log, package):
    """Each error of the build log in one of the package's files: (file, line, message)."""
    return [(m.group(1), int(m.group(2)), m.group(3)) for m in re.finditer(rf"(?m)^error: ({package}/[^:]+):(\d+):\d+: (.*)$", log)]


def extract(crate, rounds):
    crate = (ROOT / crate).resolve()
    scenario = scenarios()[crate]
    toml = crate / "hax.toml"
    package = json.loads(run(["cargo", "metadata", "--format-version", "1", "--no-deps"]).stdout)
    name = next(p["name"] for p in package["packages"] if pathlib.Path(p["manifest_path"]).parent == crate)
    lean = crate / "proofs" / scenario / "lean"
    print(f"== {crate.relative_to(ROOT)} (package {name}, scenario {scenario})")
    added = {"opaque": {}, "exclude": {}}
    patched = {}
    for round_ in range(1, rounds + 1):
        result = run(["formal/extraction/hax.sh", "extract", "-p", name])
        log = ANSI.sub("", result.stdout + result.stderr)
        gone = set(re.findall(r"failed to resolve item path `([^`]+)`", log))
        if gone:
            text = toml.read_text()
            kept = "".join(l for l in text.splitlines(True) if not any(re.match(rf'\s*"{re.escape(g)}",', l) for g in gone))
            if kept != text:
                toml.write_text(kept)
                for g in sorted(gone):
                    print(f"   - {g}: no longer in the source, taken off the scenario")
                continue
        if "no longer applies" in log:
            print(log.strip().splitlines()[-1])
            return False
        if not (lean / "lakefile.toml").exists():
            print("   no package was scaffolded:\n   " + "\n   ".join(l[:220] for l in log.splitlines() if re.search(r"error|panicked|not found", l))[:3000])
            return False
        lean_name = re.search(r'^name = "([^"]+)"', (lean / "lakefile.toml").read_text(), re.M).group(1)
        funs = lean / lean_name / "Extraction" / "Funs.lean"
        opaque, exclude = {}, {}
        error_log = lean / "aeneas-error.log"
        reasons = {}
        if error_log.exists():
            errors = ANSI.sub("", error_log.read_text())
            last = "rejected by Aeneas"
            for line in errors.splitlines():
                ignored = re.match(r"\[Error\] Ignoring the body of '(.*)' because", line) or re.match(
                    r"\[Warn ?\] Could not translate the body of function '(.*?)'? because", line
                )
                if ignored:
                    reasons[pattern(ignored.group(1), name)] = last
                elif line.startswith("[Error] "):
                    last = "Aeneas: " + line[8:].strip()[:70].rstrip(".").lower()
        opaque.update(reasons)
        iterator_crash = False
        if error_log.exists():
            located = []
            for block in re.split(r"(?m)^(?=\[Error\] )", ANSI.sub("", error_log.read_text())):
                head = re.match(r"\[Error\] (?!Ignoring)([^\n]*)", block)
                inside = re.search(rf"Source: '({re.escape(str(crate.relative_to(ROOT)))}/[^']*)', lines (\d+):", block)
                if head and inside:
                    located.append((head.group(1), inside.group(1), inside.group(2)))
                elif head and "iter/traits/iterator.rs" in block:
                    iterator_crash = True
            block = re.search(r"(?ms)^opaque = \[\n(.*?)^\]\n", toml.read_text())
            already_opaque = set(re.findall(r'^\s*"([^"]+)",', block.group(1), re.M)) if block else set()
            for message, file, line in located:
                found = item_at(crate, patched, file, int(line))
                why = "Aeneas: " + message.strip()[:70].rstrip(".").lower()
                if found in already_opaque:
                    # Rejected with no body to blame: its signature does not translate (a `dyn Fn`, a
                    # function pointer), and an opaque item still needs one.
                    exclude.setdefault(found, why + " (in its signature)")
                elif found:
                    opaque.setdefault(found, why)
        if funs.exists():
            for rust in with_sorry(funs):
                opaque.setdefault(pattern(rust, name), "Aeneas left its body out")
        aeneas_failed = result.returncode != 0 and "aeneas exited" in log
        charon_failed = result.returncode != 0 and not aeneas_failed and "wrote file" not in log
        if charon_failed:
            print("\n".join(l for l in log.splitlines() if re.search(r"error|panicked", l))[:3000])
            return False
        build_log = ""
        if not opaque and not aeneas_failed:
            run([sys.executable, "formal/extraction/wire.py"])
            build = run(["lake", "build", f"{lean_name}.Extraction"], cwd=WORKSPACE)
            build_log = build.stdout + build.stderr
            cache = {}
            for file, line, message in lean_errors(build_log, lean_name):
                path = lean / file
                if path not in cache:
                    cache[path] = definitions(path)[1]
                rust = definition_at(cache[path], line)
                if not rust:
                    continue
                why = "Lean: " + re.sub(r"`CoreModels\.", "`", message)[:70].rstrip(":").lower()
                found = pattern(rust, name)
                # An opaque item's signature, or a whole trait impl: nothing of it can stay.
                (exclude if "/Assumptions/" in file or found.endswith("}") else opaque).setdefault(found, why)
            if build.returncode == 0:
                warnings = len(re.findall(r"(?m)^warning: " + lean_name, build_log))
                print(f"   clean after {round_} round(s): {len(added['opaque'])} opaque and {len(added['exclude'])} excluded added, {warnings} warnings in the package")
                for key in ("opaque", "exclude"):
                    for p, why in sorted(added[key].items()):
                        print(f"   + {key}: {p}  ({why})")
                return True
        if iterator_crash:
            # Their signatures crash Aeneas while it translates the `Iterator` trait (LIMITATIONS.md);
            # without them, what uses them is rejected by Lean, and goes opaque in the next rounds.
            why = "its signature crashes Aeneas on the `Iterator` trait"
            exclude.update({f"core::iter::traits::iterator::Iterator::{m}": why for m in ("filter", "copied", "cloned", "find", "unzip")})
            exclude["core::slice::iter::_::find"] = why
            # `Sum` and `Product` take `I: Iterator`, which brings the whole trait in.
            exclude["{impl core::iter::traits::accum::Sum<_> for _}"] = why
            exclude["{impl core::iter::traits::accum::Product<_> for _}"] = why
        new = add_entries(toml, "opaque", {p: w for p, w in opaque.items() if p not in exclude})
        new_excluded = add_entries(toml, "exclude", exclude)
        added["opaque"].update(new)
        added["exclude"].update(new_excluded)
        print(f"   round {round_}: {len(new)} opaque, {len(new_excluded)} excluded")
        if not new and not new_excluded:
            print("   no progress; what is left:")
            if error_log.exists():
                lines = ANSI.sub("", error_log.read_text()).splitlines()
                print("   " + "\n   ".join([l for l in lines if l.startswith(("[Error]", "Source"))] or [l[:200] for l in lines[:4]])[:2500])
            print("   " + "\n   ".join(l[:230] for l in build_log.splitlines() if l.startswith("error"))[:4000])
            return False
    print("   out of rounds")
    return False


def in_dependency_order(crates):
    """The named crate directories (every scenario's, when none is named), a crate after those it uses."""
    known = scenarios()
    chosen = [(ROOT / crate).resolve() for crate in crates] or list(known)
    missing = [str(crate.relative_to(ROOT)) for crate in chosen if crate not in known]
    if missing:
        sys.exit(f"error: no scenario in {', '.join(missing)} (a crate takes part by a [scenario.<name>] in its hax.toml)")
    metadata = json.loads(run(["cargo", "metadata", "--format-version", "1", "--no-deps"]).stdout)
    at = {p["name"]: pathlib.Path(p["manifest_path"]).parent for p in metadata["packages"]}
    uses = {at[p["name"]]: {at[d["name"]] for d in p["dependencies"] if d["kind"] is None and d["name"] in at} for p in metadata["packages"]}
    ordered = []

    def visit(crate):
        if crate in ordered:
            return
        for used in sorted(uses.get(crate, ())):
            if used in known and used != crate:
                visit(used)
        if crate in chosen:
            ordered.append(crate)

    for crate in sorted(chosen):
        visit(crate)
    return ordered


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("patches")
    one = commands.add_parser("extract")
    one.add_argument("crates", nargs="*")
    one.add_argument("--rounds", type=int, default=12)
    args = parser.parse_args()
    if args.command == "patches":
        patches()
    else:
        ok = [extract(crate, args.rounds) for crate in in_dependency_order(args.crates)]
        sys.exit(0 if all(ok) else 1)


if __name__ == "__main__":
    main()
