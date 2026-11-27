#!/usr/bin/env python3
"""Print, as one patch for `git apply`, the mechanical rewrites the extraction needs.

`hax.sh` applies this patch before the hand-written ones in `patches/pre/`. These rewrites
recur all over the crates and change nothing a function computes; generating them, rather than
keeping them in hand-written patches, means code that moves under them never stales a patch.

    mechanical.py             the crates' sources in the working tree
    mechanical.py --rev REV   those of commit REV, read from git, nothing checked out

**Anonymous constants** (`const _: () = assert!(..)`, which Aeneas names `__N`, a name Lean
rejects) are named `_ASSERT_<hash of the item>`, a name that stays put as code moves around it.

**Tracing spans**, which the toolchain cannot translate, are removed, the arguments of each macro
balanced over parentheses and string literals:

- `#[tracing::instrument(...)]` attributes;
- `let x = tracing::<span>!(...).entered();` and `let x = tracing::<span>!(...);` statements,
  and the `drop(x);` that ends one;
- `tracing::<span>!(...).in_scope(|| body)`, which becomes `body` (`in_scope(f)`, `(f)()`),
  and likewise `x.in_scope(...)` for a span `x` bound by name;
- `use` lines and one-line `let`s whose names only the spans' fields used (`pretty_integer`).
"""

import argparse
import difflib
import glob
import hashlib
import re
import subprocess
import sys

SPAN = r"tracing::(?:info|debug|trace|warn|error)_span!"


def skip_string(src: str, i: int) -> int:
    """The index just past the string literal opening at `src[i]` (a `"` or an `r#"`)."""
    raw = re.match(r'r(#*)"', src[i:])
    if raw:
        end = src.index('"' + raw.group(1), i + len(raw.group(0)))
        return end + 1 + len(raw.group(1))
    i += 1
    while src[i] != '"':
        i += 2 if src[i] == "\\" else 1
    return i + 1


def close(src: str, i: int) -> int:
    """The index just past the bracket matching the opening one at `src[i]`."""
    pairs = {"(": ")", "[": "]", "{": "}"}
    stack = [pairs[src[i]]]
    i += 1
    while stack:
        c = src[i]
        if c == '"' or (c == "r" and re.match(r'r#*"', src[i:]) and not src[i - 1].isalnum()):
            i = skip_string(src, i)
            continue
        if src.startswith("//", i):
            i = src.index("\n", i)
            continue
        if c in pairs:
            stack.append(pairs[c])
        elif c in ")]}":
            if c != stack.pop():
                raise ValueError(f"unbalanced {c!r} at {i}")
        i += 1
    return i


def line_bounds(src: str, start: int, end: int) -> tuple[int, int]:
    """Widen `[start, end)` to whole lines when nothing else shares them."""
    ls = src.rfind("\n", 0, start) + 1
    le = src.find("\n", end)
    le = len(src) if le < 0 else le + 1
    if src[ls:start].strip() == "" and src[end:le].strip() == "":
        return ls, le
    return start, end


def name_constants(src: str) -> str:
    """Name each `const _: T = ...;` after a hash of its item, and make it `pub`: a name with a
    leading underscore is not a root of the dead-code lint, as `_` is, so a private constant only
    an assertion reads would otherwise be dead."""
    names = set()
    while m := re.search(r"\b(?:pub(?:\([\w:]+\))?\s+)?const\s+_\s*:", src):
        end = m.end()
        while src[end] != ";":
            end = close(src, end) if src[end] in "([{" else end + 1
        digest = hashlib.sha1(re.sub(r"\s+", " ", src[m.end():end]).encode()).hexdigest()[:8].upper()
        name, n = f"_ASSERT_{digest}", 1
        while name in names:
            n += 1
            name = f"_ASSERT_{digest}_{n}"
        names.add(name)
        src = src[:m.start()] + f"pub const {name}:" + src[m.end():]
    return src


def strip_tracing(src: str) -> str:
    # `#[tracing::instrument(...)]`.
    while m := re.search(r"#\[tracing::instrument\b", src):
        end = close(src, m.start() + 1)
        s, e = line_bounds(src, m.start(), end)
        src = src[:s] + src[e:]

    # `let x = span!(...).entered();` (a guard) or `let x = span!(...);` (a span used by name
    # below), and the `drop(x);` that ends either.
    named = set()
    at = 0
    while m := re.compile(r"let\s+(mut\s+)?(\w+)\s*=\s*" + SPAN + r"\s*\(").search(src, at):
        end = close(src, m.end() - 1)
        rest = re.match(r"\s*(\.entered\(\))?\s*;", src[end:])
        if not rest:  # `let x = span!(...).in_scope(...)`: the pass below
            at = end
            continue
        if not rest.group(1):
            named.add(m.group(2))
        s, e = line_bounds(src, m.start(), end + rest.end())
        src = src[:s] + src[e:]
        fn_end = re.compile(r"\n\s*(pub(\([\w:]+\))?\s+)?fn\s").search(src, s)
        drop = re.compile(r"drop\(\s*" + re.escape(m.group(2)) + r"\s*\)\s*;").search(
            src, s, fn_end.start() if fn_end else len(src)
        )
        if drop:
            ds, de = line_bounds(src, drop.start(), drop.end())
            src = src[:ds] + src[de:]
        at = s

    # `span!(...).in_scope(|| body)`, or `x.in_scope(|| body)` for a span `x` named above,
    # becomes `body`; `in_scope(f)` becomes `(f)()`.
    span_or_name = SPAN + r"\s*\("
    if named:
        span_or_name += r"|\b(?:" + "|".join(map(re.escape, sorted(named))) + r")\b(?=\s*\.in_scope\()"
    while m := re.search(span_or_name, src):
        end = close(src, m.end() - 1) if m.group(0).endswith("(") else m.end()
        scope = re.match(r"\s*\.in_scope\(", src[end:])
        if not scope:
            raise ValueError(f"a span neither entered nor in_scope: {src[m.start():end + 40]!r}")
        arg_start = end + scope.end()
        arg_end = close(src, arg_start - 1) - 1
        arg = src[arg_start:arg_end]
        closure = re.match(r"\s*(move\s*)?\|\|\s*", arg)
        body = arg[closure.end():].rstrip() if closure else f"({arg.strip()})()"
        src = src[:m.start()] + body + src[arg_end + 1:]

    return src


def unused_bindings(before: str, after: str) -> str:
    """Drop `use a::b;` lines, and one-line `let b = ...;` statements, whose name the stripped
    spans were the only users of (a span's fields)."""
    out = after
    for m in re.finditer(r"^use [\w:]+::(\w+);\n|^[ \t]*let (?:mut )?(\w+)\s*=[^;\n]*;\n", after, re.M):
        name = m.group(1) or m.group(2)
        uses = lambda s: len(re.findall(r"\b" + name + r"\b", s))
        if uses(after) == 1 and uses(before) > 1:
            out = out.replace(m.group(0), "", 1)
    return out


# What marks a file one of the rewrites applies to.
APPLIES = re.compile(r"tracing::|\bconst\s+_\s*:")


def sources(rev: str | None) -> list[tuple[str, str]]:
    """Each crate source file a rewrite applies to, with its text."""
    if rev is None:
        paths = sorted(glob.glob("crates/*/src/**/*.rs", recursive=True) + glob.glob("crates/stable_prover/*/src/**/*.rs", recursive=True))
        texts = [open(path).read() for path in paths]
    else:
        listed = subprocess.run(
            ["git", "grep", "-l", "-E", "-e", r"tracing::|const +_ *:", rev, "--", "crates"],
            capture_output=True,
            text=True,
        ).stdout.split()
        paths = [p.split(":", 1)[1] for p in listed]
        paths = [p for p in paths if re.fullmatch(r"crates/(?:stable_prover/)?[^/]+/src/.*\.rs", p)]
        texts = [subprocess.run(["git", "show", f"{rev}:{p}"], capture_output=True, text=True, check=True).stdout for p in paths]
    return [(p, t) for p, t in zip(paths, texts) if APPLIES.search(t)]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--rev", help="read the sources of this commit instead of the working tree")
    for path, src in sources(parser.parse_args().rev):
        try:
            new = name_constants(unused_bindings(src, strip_tracing(src)) if "tracing::" in src else src)
        except ValueError as e:
            sys.exit(f"mechanical.py: {path}: {e}")
        if new != src:
            sys.stdout.writelines(
                difflib.unified_diff(
                    src.splitlines(keepends=True),
                    new.splitlines(keepends=True),
                    f"a/{path}",
                    f"b/{path}",
                )
            )


if __name__ == "__main__":
    main()
