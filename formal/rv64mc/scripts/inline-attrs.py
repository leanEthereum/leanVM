#!/usr/bin/env python3
"""Gives every function with a body in the Rust files of DIR `#[inline(always)]` if BOUNDARIES lists it and
`#[inline(never)]` otherwise, replacing the `#[inline]` attributes the source has: `inline-attrs.py BOUNDARIES DIR`.

A function is keyed by its file and `name`, `Type::name` or `Trait for Type::name`, the impl's header as written after
`impl<..>` (see boundaries.txt). Fails if an entry names no function, so that the list follows the source.
"""

import os
import re
import sys

FN = re.compile(r"^(\s*)(pub(\([a-z]+\))? )?(const )?(unsafe )?fn (\w+)")
IMPL = re.compile(r"^impl(<.*?>)?\s+(.*?)\s*(where.*)?\{?\s*$")
INLINE = re.compile(r"^\s*#\[inline(\(\w+\))?\]\s*$")


def has_body(lines, i):
    """Whether the signature starting at line i ends in `{` (a body) rather than `;`."""
    for line in lines[i:]:
        code = line.split("//")[0].rstrip()
        if code.endswith("{") or code.endswith("}"):
            return True
        if code.endswith(";"):
            return False
    return False


def main():
    boundaries, root = sys.argv[1], sys.argv[2]
    always = set()
    for line in open(boundaries):
        line = line.strip()
        if line and not line.startswith("#"):
            file, key = line.split(None, 1)
            always.add((file, key))
    seen = set()
    for file in sorted(os.listdir(root)):
        if not file.endswith(".rs"):
            continue
        path = os.path.join(root, file)
        lines = open(path).read().split("\n")
        out, impl = [], None
        for i, line in enumerate(lines):
            if INLINE.match(line):
                continue
            m = IMPL.match(line)
            if m:
                impl = m.group(2).strip()
            elif re.match(r"^\S", line) and not line.startswith(("#", "//", "}")):
                impl = None  # a top-level item that is not an impl ends the previous impl
            m = FN.match(line)
            if m and has_body(lines, i):
                indent, name = m.group(1), m.group(6)
                key = f"{impl}::{name}" if indent and impl else name
                attr = "always" if (file, key) in always else "never"
                seen.add((file, key))
                # Above the function's outer attributes and doc comments, so that a `const fn` keeps them adjacent.
                j = len(out)
                while j > 0 and re.match(r"^\s*(#\[|///)", out[j - 1]) and not INLINE.match(out[j - 1]):
                    j -= 1
                out.insert(j, f"{indent}#[inline({attr})]")
            out.append(line)
        open(path, "w").write("\n".join(out))
    missing = always - seen
    if missing:
        sys.exit("boundaries.txt names no function: " + ", ".join(f"{f} {k}" for f, k in sorted(missing)))


main()
