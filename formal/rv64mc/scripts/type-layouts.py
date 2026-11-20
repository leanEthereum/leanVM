#!/usr/bin/env python3
"""The layouts of the types `layouts.txt` names, as Lean constants (`Rv64mc/Gen/Layouts.lean`).

  type-layouts.py probe SPEC SRC MAIN WHICH   add to the verifier's no_std copy SRC (WHICH = lib) or to the guest's
                                              MAIN (WHICH = main) one `#[rustc_dump_layout(debug)]` alias per `dump`
                                              line of SPEC, in a child module of the line's module
  type-layouts.py gen SPEC SRC MAIN PTS DUMP OUT [--check]
                                              read `-Zprint-type-sizes`'s output PTS and the dumps' DUMP (rustc's
                                              stderr) and write OUT; with --check, write nothing and exit 1 if OUT
                                              would change

Field and variant names come from the source's declarations (rustc numbers them in declaration order), except for
`pts` types, whose fields `-Zprint-type-sizes` names in memory order. The generator fails on a type it cannot find,
a dump it cannot read, two printings of one type that disagree, and a `family` member whose fields differ.
"""

import os
import subprocess
import re
import sys

KEYWORDS = {"at", "by", "do", "else", "end", "fun", "from", "have", "if", "in", "let", "match", "open", "show",
            "then", "where", "with", "for", "return", "instance", "structure", "deriving", "namespace", "section",
            "variable", "universe", "import", "def", "theorem", "abbrev", "example", "local", "private",
            "protected", "mut", "unless", "try", "catch", "finally", "break", "continue", "calc", "Type", "Prop"}
CORE_ENUMS = {"Option": [("None", []), ("Some", ["f0"])], "Result": [("Ok", ["f0"]), ("Err", ["f0"])]}


def die(msg):
    sys.exit(f"type-layouts: {msg}")


def spec(path):
    out = []
    for n, line in enumerate(open(path), 1):
        line = line.split("#", 1)[0].strip()
        if not line:
            continue
        w = line.split()
        if w[0] == "dump" and len(w) >= 4:
            out.append(("dump", w[1], w[2], " ".join(w[3:])))
        elif w[0] in ("pts", "family") and len(w) >= 3:
            out.append((w[0], w[1], " ".join(w[2:])))
        elif w[0] == "path" and len(w) >= 3:
            out.append(("path", w[1], w[2:]))
        else:
            die(f"{path}:{n}: cannot read {line!r}")
    return out


def module_file(src, main, module):
    return main if module == "main" else os.path.join(src, f"{module}.rs")


def alias(name):
    return f"__Layout_{name}"


def probe(spec_path, src, main, which):
    by_file = {}
    for e in spec(spec_path):
        if e[0] == "dump" and (e[2] == "main") == (which == "main"):
            by_file.setdefault(module_file(src, main, e[2]), []).append(e)
    feature = "#![feature(rustc_attrs)]\n#![allow(internal_features)]\n"
    root = main if which == "main" else os.path.join(src, "lib.rs")
    text = open(root).read()
    # after the crate's first inner attribute
    i = text.index("#![")
    j = text.index("\n", i) + 1
    open(root, "w").write(text[:j] + feature + text[j:])
    for path, es in by_file.items():
        body = "".join(f"    #[rustc_dump_layout(debug)]\n    type {alias(e[1])} = {e[3]};\n" for e in es)
        with open(path, "a") as f:
            f.write(f"\n#[allow(dead_code, unused_imports)]\nmod __layouts {{\n    use super::*;\n{body}}}\n")


# ---- Rust declarations: field and variant names in declaration order ----

def strip_comments(s):
    s = re.sub(r"//[^\n]*", "", s)
    return re.sub(r"/\*.*?\*/", "", s, flags=re.S)


def split_top(s):
    """`s` split at commas outside brackets."""
    parts, depth, cur = [], 0, ""
    for ch in s:
        if ch in "([{<":
            depth += 1
        elif ch in ")]}>":
            depth -= 1
        if ch == "," and depth == 0:
            parts.append(cur)
            cur = ""
        else:
            cur += ch
    parts.append(cur)
    return [p.strip() for p in parts if p.strip()]


def strip_attrs(s):
    return re.sub(r"#\[[^\]]*\]", "", s).strip()


def block(text, start, open_ch, close_ch):
    """The text between the bracket at `start` and its match."""
    depth = 0
    for k in range(start, len(text)):
        if text[k] == open_ch:
            depth += 1
        elif text[k] == close_ch:
            depth -= 1
            if depth == 0:
                return text[start + 1:k]
    die("unbalanced declaration")


def field_names(body, tuple_like):
    if tuple_like:
        return [f"f{k}" for k, _ in enumerate(split_top(body))]
    names = []
    for f in split_top(body):
        f = strip_attrs(f)
        f = re.sub(r"^pub(\([^)]*\))?\s+", "", f)
        names.append(f.split(":", 1)[0].strip())
    return names


def library_file(ty, kind, name):
    """The file of rustc's library sources (`rust-src`) under `ty`'s module path that declares `kind name`."""
    sysroot = subprocess.run(["rustc", "--print", "sysroot"], capture_output=True, text=True, check=True,
                             cwd=os.path.dirname(os.path.abspath(__file__)) + "/../guest").stdout.strip()
    parts = re.match(r"((?:\w+::)*)\w+", ty.strip()).group(1).strip(":").split("::")
    root = os.path.join(sysroot, "lib/rustlib/src/rust/library", parts[0], "src", *parts[1:])
    hits = []
    for d, _, fs in os.walk(root if os.path.isdir(root) else os.path.dirname(root)):
        for f in fs:
            p = os.path.join(d, f)
            if f.endswith(".rs") and re.search(rf"\b{kind}\s+{re.escape(name)}\b", strip_comments(open(p).read())):
                hits.append(p)
    if len(hits) != 1:
        die(f"`{kind} {name}` declared in {len(hits)} files under {root}")
    return hits[0]


def declaration(path, kind, name, ty=None):
    text = strip_comments(open(path).read())
    m = re.search(rf"\b{kind}\s+{re.escape(name)}\b(<[^>]*>)?\s*([({{;])", text)
    if not m and ty and "::" in ty:
        path = library_file(ty, kind, name)
        text = strip_comments(open(path).read())
        m = re.search(rf"\b{kind}\s+{re.escape(name)}\b(<[^>]*>)?\s*([({{;])", text)
    if not m:
        die(f"no `{kind} {name}` in {path}")
    ch = m.group(2)
    if ch == ";":
        return []
    body = block(text, m.end() - 1, ch, ")" if ch == "(" else "}")
    if kind == "struct":
        return field_names(body, ch == "(")
    variants = []
    for v in split_top(body):
        v = strip_attrs(v)
        vm = re.match(r"(\w+)\s*(=\s*(\S+))?\s*([({])?", v)
        if vm.group(3):
            die(f"explicit discriminant in {name}::{vm.group(1)}")
        fs = []
        if vm.group(4):
            k = v.index(vm.group(4))
            fs = field_names(block(v, k, vm.group(4), ")" if vm.group(4) == "(" else "}"), vm.group(4) == "(")
        variants.append((vm.group(1), fs))
    return variants


def head_name(ty):
    """The type's own name: `Result<(), E>` is `Result`, `&'static [E]` is a slice, `field::E` is `E`."""
    ty = ty.strip()
    if ty.startswith("&"):
        return "&"
    return re.match(r"(?:\w+::)*(\w+)", ty).group(1)


# ---- `#[rustc_dump_layout(debug)]` output ----

def parse_debug(lines):
    """Rust's pretty `Debug` output, one item per line, as nested dicts (`{_: kind, key: value}`), lists and strings."""
    def value(i, text):
        text = text.rstrip(",")
        if text == "[]":
            return i + 1, []
        m = re.match(r"^(\w*)\s*([{(\[])$", text)
        if m:
            close = {"{": "}", "(": ")", "[": "]"}[m.group(2)]
            node = {"_": m.group(1)} if m.group(2) != "[" else []
            i += 1
            while True:
                t = lines[i].strip()
                if t.rstrip(",") == close:
                    return i + 1, node
                if m.group(2) == "{":
                    key, rest = t.split(":", 1)
                    i, v = value(i, rest.strip())
                    node[key.strip()] = v
                else:
                    i, v = value(i, t)
                    if isinstance(node, list):
                        node.append(v)
                    else:
                        node.setdefault("args", []).append(v)
        return i + 1, text
    return value(0, lines[0].strip())[1]


def size_of(s):
    m = re.fullmatch(r"(?:Size|Align)\((\d+) bytes\)", s)
    if not m:
        die(f"not a size: {s!r}")
    return int(m.group(1))


def dumps(path):
    """Each dumped alias's layout, by alias name."""
    text = open(path).read()
    out = {}
    for m in re.finditer(r"^error: layout_of\((.*?)\) = Layout \{\n(.*?)^\s*\}\n\s*--> [^\n]*\n[^\n]*\n"
                         r"[^\n]*type (\w+) =", text, flags=re.S | re.M):
        lines = ["Layout {"] + m.group(2).splitlines() + ["}"]
        out[m.group(3)] = (m.group(1), parse_debug(lines))
    return out


def offsets_of(fields):
    if fields.get("_") == "Arbitrary":
        return [size_of(o) for o in fields["offsets"]]
    if fields.get("_") == "" or fields == "Primitive":
        return []
    die(f"unexpected fields {fields}")


def tag_bytes(tag):
    m = re.match(r"[ui](8|16|32|64|128)\b", tag)
    if not m:
        die(f"unexpected tag {tag!r}")
    return int(m.group(1)) // 8


# ---- `-Zprint-type-sizes` output ----

def pts(path):
    """Each printed type's size, alignment and fields (name, offset) in memory order; a type printed twice must
    agree."""
    seen = {}
    cur = None
    for line in open(path):
        m = re.match(r"print-type-size type: `(.*)`: (\d+) bytes, alignment: (\d+) bytes$", line.rstrip())
        if m:
            cur = (int(m.group(2)), int(m.group(3)), [])
            seen.setdefault(m.group(1), []).append(cur)
            off = 0
            continue
        # a struct's own lines; a variant's fields are indented further
        if cur is None or not line.startswith("print-type-size     ") or line.startswith("print-type-size      "):
            continue
        body = line[len("print-type-size     "):].strip()
        fm = re.match(r"field `\.(\w+)`: (\d+) bytes", body)
        pm = re.match(r"(?:end )?padding: (\d+) bytes", body)
        if fm:
            cur[2].append((fm.group(1), off))
            off += int(fm.group(2))
        elif pm:
            off += int(pm.group(1))
    out = {}
    for ty, ps in seen.items():
        if any(q != ps[0] for q in ps):
            die(f"`{ty}` printed more than once, with different layouts")
        out[ty] = ps[0]
    return out


# ---- Lean ----

def lean_name(n):
    return f"«{n}»" if n in KEYWORDS else n


def gen(spec_path, src, main, pts_path, dump_path, out_path, check):
    entries = spec(spec_path)
    printed = pts(pts_path)
    dumped = dumps(dump_path)
    consts = {}  # NAME -> {field: offset}
    blocks = []
    for e in entries:
        if e[0] == "pts":
            _, name, ty = e
            if ty not in printed:
                die(f"`-Zprint-type-sizes` printed no `{ty}`")
            size, align, fields = printed[ty]
            consts[name] = dict(fields)
            lines = [f"abbrev byteSize : Nat := {size}", f"abbrev byteAlign : Nat := {align}"]
            lines += [f"/-- `.{f}` -/\nabbrev {lean_name(f)} : Nat := {o}" for f, o in fields]
            blocks.append((name, f"`{ty}`, as `-Zprint-type-sizes` prints it: {size} bytes, aligned to {align}.",
                           lines))
        elif e[0] == "family":
            _, name, prefix = e
            n = 0
            for ty, (size, align, fields) in printed.items():
                if ty.startswith(prefix):
                    n += 1
                    if dict(fields) != consts[name]:
                        die(f"`{ty}` has fields {fields}, not {name}'s {consts[name]}")
            blocks.append((name, None, [f"-- every `{prefix}..>` printed ({n}) has these fields at these offsets"]))
        elif e[0] == "path":
            _, dotted, steps = e
            total = 0
            for s in steps:
                t, f = s.split(".", 1)
                if f not in consts.get(t, {}):
                    die(f"path {dotted}: no field {s}")
                total += consts[t][f]
            t, f = dotted.split(".", 1)
            consts[t][f] = total
            blocks.append((t, None, [f"/-- `{' + '.join(steps)}` -/\nabbrev {lean_name(f)} : Nat := {total}"]))
        else:
            _, name, module, ty = e
            key = alias(name)
            if key not in dumped:
                die(f"no layout dumped for {name} ({ty})")
            rty, lay = dumped[key]
            size = size_of(lay["size"])
            align = size_of(lay["align"]["abi"])
            offs = offsets_of(lay["fields"])
            lines = [f"abbrev byteSize : Nat := {size}", f"abbrev byteAlign : Nat := {align}"]
            head = head_name(ty)
            variants = lay["variants"]
            doc = f"`{rty}` (`{ty}` in `{module}`): {size} bytes, aligned to {align}."
            if variants["_"] == "Single":
                if head == "&":
                    names = ["ptr", "len"] if len(offs) == 2 else ["ptr"]
                elif len(offs) == 0:
                    names = []
                else:
                    names = declaration(module_file(src, main, module), "struct", head, ty)
                if len(names) != len(offs):
                    die(f"{name}: {len(offs)} fields laid out, {len(names)} declared")
                consts[name] = dict(zip(names, offs))
                lines += [f"abbrev {lean_name(f)} : Nat := {o}" for f, o in zip(names, offs)]
            else:
                vs = CORE_ENUMS.get(head) or declaration(module_file(src, main, module), "enum", head, ty)
                vls = variants["variants"]
                if len(vs) != len(vls):
                    die(f"{name}: {len(vls)} variants laid out, {len(vs)} declared")
                tag_field = int(variants["tag_field"])
                toff = offs[tag_field]
                tb = tag_bytes(variants["tag"])
                lines += [f"abbrev tagOffset : Nat := {toff}", f"abbrev tagBytes : Nat := {tb}"]
                enc = variants["tag_encoding"]
                tags = {}
                if enc == "Direct":
                    doc += " Tagged: each variant's tag is its index."
                    tags = {k: k for k in range(len(vs))}
                elif isinstance(enc, dict) and enc["_"] == "Niche":
                    a, b = (int(x) for x in enc["niche_variants"].split("..="))
                    start = int(enc["niche_start"])
                    unt = int(enc["untagged_variant"])
                    tags = {v: (v - a + start) % (1 << (8 * tb)) for v in range(a, b + 1)}
                    doc += (f" Niche-encoded: a tag value `t` with `t - nicheStart < nicheVariants` (modulo"
                            f" 2^{8 * tb}) names variant `nicheFirst + (t - nicheStart)`, any other the untagged"
                            f" `{vs[unt][0]}`.")
                    lines += [f"abbrev nicheStart : Nat := {start}", f"abbrev nicheFirst : Nat := {a}",
                              f"abbrev nicheVariants : Nat := {b - a + 1}"]
                else:
                    die(f"{name}: tag encoding {enc}")
                for k, ((vname, fnames), vl) in enumerate(zip(vs, vls)):
                    vo = [size_of(o) for o in vl["field_offsets"]]
                    if len(vo) != len(fnames):
                        die(f"{name}::{vname}: {len(vo)} fields laid out, {len(fnames)} declared")
                    vlines = [f"abbrev index : Nat := {k}"]
                    if k in tags:
                        vlines.append(f"abbrev tag : Nat := {tags[k]}")
                    vlines += [f"abbrev {lean_name(f)} : Nat := {o}" for f, o in zip(fnames, vo)]
                    lines.append(f"namespace {lean_name(vname)}\n" + "\n".join(vlines) + f"\nend {lean_name(vname)}")
            blocks.append((name, doc, lines))
    out = ["/-",
           "  Rv64mc.Gen.Layouts",
           "",
           "  Written by `scripts/type-layouts.sh` from `layouts.txt`; do not edit. The layouts rustc gives the guest's",
           "  types, in bytes: each type's size and alignment, each field's offset, and for an enum its tag's offset and",
           "  size and each variant's tag and field offsets. Proofs name these, never a literal offset.",
           "-/",
           "",
           "namespace Rv64mc.Layouts",
           ""]
    for name, doc, lines in blocks:
        if doc:
            out.append(f"/-! ## `{name}`: {doc} -/")
        out.append(f"namespace {name}")
        out += lines
        out.append(f"end {name}")
        out.append("")
    out.append("end Rv64mc.Layouts")
    text = "\n".join(out) + "\n"
    old = open(out_path).read() if os.path.exists(out_path) else None
    if check:
        if old != text:
            print(f"{out_path} would change")
            sys.exit(1)
        return
    if old != text:
        os.makedirs(os.path.dirname(out_path), exist_ok=True)
        open(out_path, "w").write(text)
        print(f"wrote {out_path}")
    else:
        print(f"{out_path} unchanged")


if __name__ == "__main__":
    a = sys.argv[1:]
    if len(a) == 5 and a[0] == "probe":
        probe(*a[1:])
    elif len(a) in (7, 8) and a[0] == "gen":
        gen(*a[1:7], check=len(a) == 8 and a[7] == "--check")
    else:
        die(__doc__)
