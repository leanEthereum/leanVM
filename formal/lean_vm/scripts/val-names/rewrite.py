#!/usr/bin/env python3
"""Rewrite the value numbers and statement positions a hand proof spells to their names.

    python3 -I scripts/val-names/rewrite.py [--write] [--fn F] [--fn-map TSV] [--suggest] [--dump FILE]
        [--report TSV] FILE...

For each file it finds the one core function whose body the file reads (`fn% «f»`, `core% «f» …`,
`Fn.«f».core`, `idx% «f»`, `find? "name"`, and the templates tied to a body anywhere; `--fn F` or the
map (`--fn-map`, by default `scripts/val-names/fnmap.tsv`) names it when the source does not, a
person's decision: `FILE F`, `FILE@decl F`, or
`tie T F` for a template the source ties by a check the tool cannot read, `F` a function or a family
`f__L` (every specialization of `f`) or `f__L_loop0` (their loops); `--suggest` lists the candidates
and their evidence) and
classifies
every integer literal outside comments:

* `value`: the argument of `.n`/`V.n`, a numeral or a sum of numerals: written
  `val% «f» "name"`, the value's source name (`acc`; `g.acc` through the inlined callee `g`; `acc@2`
  the second value named `acc`) or, without one, its expansion path (`guest-core --names`); `value (family)`: in a
  template tied to up to six specializations of one source function (`f__L…`) that all name the
  value alike, `val% «f__L0» «f__L1» "name"`;
* `stride`: a numeral next to `*` in a parametric index `.n (17 + 7 * j)`, left as it is (the
  template's tie checks it); its additive numeral is flagged (`strided base`): it is the index at
  zero only when zero is in the template's range, which the text does not say;
* `argument value`: a value's number in an argument place that holds one (`Completes C rd lo hi`,
  `Completes.append (m := k)`, `AgreeBelow k`, `NBv k`, `∀ k < n, σ (.n k)`), named the same way; a
  named argument elsewhere (`(b := 88)`, `(m := 8)`) is a bare literal, flagged;
* `value (family)` over every specialization of one source function `f__L…` a template is tied to:
  `valf% «f» "name"` (their common number);
* `position`: `drop`/`take` of a body (`(fn% «f»).body.drop k`, `Fn.body … |>.drop`): written
  `pos% «f» "name"`, by the first value the statement at `k` names;
* `flagged`: a value or position the tool cannot name for certain (no single function, a
  parametric index `.n (b + 6)`, a position relative to another, a statement naming no new value, a
  number past the function's values), and every other literal of 3 digits or more outside a word, a
  power or a doc comment, which might be an index spelled bare (`(b := 62094)`, `Completes … 66
  119742`, `∀ k < 62094`);
* `other`: smaller literals and literals in words (`word 32768 0`), exponents and doc comments.

Nothing is guessed: a literal is rewritten only in the two forms above and only when the function is
unique. Without `--write` it only reports. With `--write` it rewrites, adds the imports
(`LeanVM.Guest.ValRef`, `LeanVM.Guest.Data.ValNames.«f»`, private), and leaves the flagged literals
as they are. `--report` appends one row per literal: file, line, class, literal, reason or name.
Run from `lean_vm`; then `scripts/val-names/gen.py` writes the names' data.
"""
import os, re, subprocess, sys

DUMP = None


def load_names(dump):
    text = open(dump, encoding="utf-8").read() if dump else subprocess.run(
        [os.path.join(".lake", "build", "bin", "guest-core"), "--names"], check=True,
        capture_output=True, text=True).stdout
    vals, src, stmts = {}, {}, {}
    for line in text.splitlines():
        f, kind, i, n = line.split("\t")
        {"v": vals, "n": src, "s": stmts}[kind].setdefault(f, {})[int(i)] = n
    # a value's source name where it has one, else its expansion path
    for f, t in src.items():
        for i, n in t.items():
            vals[f][i] = n
    return vals, stmts


def compiled_names():
    """Compiled name -> stable name, from `Data/NameStrings.lean`."""
    t = {}
    p = os.path.join("LeanVM", "Guest", "Data", "NameStrings.lean")
    for m in re.finditer(r'abbrev «([^»]+)» : String := "([^"]+)"', open(p, encoding="utf-8").read()):
        t[m.group(2)] = m.group(1)
    return t


def mask_comments(src):
    """The source with comments and strings blanked (same length), and a mask of doc positions."""
    out, doc, i, n, depth = list(src), [False] * len(src), 0, len(src), 0
    while i < n:
        if src.startswith("/-", i):
            j, depth = i + 2, 1
            while j < n and depth:
                if src.startswith("/-", j):
                    depth += 1; j += 2
                elif src.startswith("-/", j):
                    depth -= 1; j += 2
                else:
                    j += 1
            for k in range(i, j):
                doc[k] = True
                if out[k] != "\n": out[k] = " "
            i = j
        elif src.startswith("--", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            for k in range(i, j):
                doc[k] = True; out[k] = " "
            i = j
        elif src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            for k in range(i + 1, min(j, n)):
                if out[k] != "\n": out[k] = " "
            i = j + 1
        else:
            i += 1
    return "".join(out), doc


BODY_FN = [r'fn%\s+«?([A-Za-z0-9_]+)»?', r'core%\s+«?([A-Za-z0-9_]+)»?', r'core_eq%\s+«?([A-Za-z0-9_]+)»?',
           r'Fn\.«([A-Za-z0-9_]+)»\.core', r'idx%\s+«?([A-Za-z0-9_]+)»?', r'fn_idx%\s+«?([A-Za-z0-9_]+)»?']


def functions(code, cnames):
    fs = set()
    for pat in BODY_FN:
        fs.update(re.findall(pat, code))
    for n in re.findall(r'find\?\s+"([^"]+)"', code):
        if n in cnames: fs.add(cnames[n])
    return fs


FAMILY = 6

DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|nonrec)\s+)*'
                  r'(?:theorem|lemma|def|abbrev|instance|structure|inductive|example)\b\s*([^\s:({\[]*)', re.M)
TIE = re.compile(r'(?:Fn\.body\s+fn%\s+«([A-Za-z0-9_]+)»|\(fn%\s+«([A-Za-z0-9_]+)»\)\.body|'
                 r'\(Fn\.«([A-Za-z0-9_]+)»\.core\)\.body|Fn\.body\s+\(fn%\s+«([A-Za-z0-9_]+)»\))\s*=\s*(.*?)(?::=|\bby\b)', re.S)
IDENT = re.compile(r'(?<![\w.])([a-z][A-Za-z0-9_\']*)')


def decls(code):
    """(start, end, name) of each top-level declaration."""
    ms = list(DECL.finditer(code))
    return [(m.start(), ms[i + 1].start() if i + 1 < len(ms) else len(code), m.group(1)) for i, m in enumerate(ms)]


BODIES = {}


def global_ties(roots=("LeanVM",)):
    """Template definition (a `def` or `abbrev` whose type names `Stmt`, its name defined in one file
    only) -> the functions whose bodies it is tied to, closed down the templates a tied one names; and
    the file that defines each."""
    raw, bodies, where, eqs, renaming, renamers, mapped = {}, {}, {}, [], set(), set(), {}
    for top in roots:
        for d, _, fs in os.walk(top):
            if d.startswith((os.path.join("LeanVM", "Guest", "Data"), os.path.join("LeanVM", "Guest", "Pack"))):
                continue
            for f in fs:
                if not f.endswith(".lean"): continue
                path = os.path.join(d, f)
                code, _ = mask_comments(open(path, encoding="utf-8").read())
                for m in TIE.finditer(code):
                    fn = next(g for g in m.groups()[:4] if g)
                    for x in IDENT.findall(m.group(5)):
                        raw.setdefault(x, set()).add(fn)
                for m in TIE_EQ.finditer(code):
                    eqs.append((m.group(1), IDENT.findall(m.group(2))))
                for a, b, n in decls(code):
                    if not n: continue
                    where.setdefault(n.split(".")[-1], set()).add(path)
                    text = code[a:b]
                    if re.search(r"rename(?!_i)", text): renamers.add(n.split(".")[-1])
                    head = text.split(":=", 1)[0]
                    # a template's result is statements and no parameter is one: a function of
                    # statements (`fixNe`, `flatIte`) is a transformer, generic, never a template
                    transformer = len(re.findall(r'\bStmt\b', head)) > 1 or re.search(r'Stmt\s*→', head)
                    if re.match(r'(?:@\[[^\]]*\]\s*)?(?:\w+\s+)*(?:def|abbrev)\b', text) and "Stmt" in head and not transformer:
                        # a template that renames or maps statements (`renameList`, `.map f`) holds
                        # them in another numbering: nothing it names inherits its tie
                        body = text.split(":=", 1)[1] if ":=" in text else ""
                        mapped[n.split(".")[-1]] = (body, set(IDENT.findall(body)))
    # a template that renames statements (`renameList`), or maps them by a function that renames
    # (`.map glcMap`), holds them in another numbering: it is tied to nothing, nothing it names
    # inherits a tie through it
    for x, (body, names) in mapped.items():
        maps = re.findall(r'\.map\s+([a-z][\w\']*)', body)
        if re.search(r"rename(?!_i)", body) or any(g in renamers for g in maps):
            renaming.add(x); bodies.setdefault(x, set())
        else:
            bodies.setdefault(x, set()).update(names)
    # a name two files define is no one template's: dropped
    bodies = {x: ys for x, ys in bodies.items() if len(where.get(x, ())) == 1}
    BODIES.update(bodies)
    ties = {x: fs for x, fs in raw.items() if x in bodies and x not in renaming}
    direct = set(ties)
    changed = True
    while changed:
        changed = False
        work = list(ties)
        while work:
            x = work.pop()
            for y in bodies.get(x, ()):
                if y in bodies and y != x and y not in renaming and not ties.get(y, set()) >= ties[x]:
                    ties.setdefault(y, set()).update(ties[x]); work.append(y)
        # an untied template that is a piece of exactly one directly tied template (`vkPre :=
        # vkT.dropLast`, `secA1 := (layerT 0).take k`) holds its statements; a template of several
        # pieces (`glTail`, canonically numbered) inherits nothing
        for x, names in bodies.items():
            if x in ties or x in renaming: continue
            src = [y for y in names if y in direct and y != x]
            if len(src) == 1 and not [y for y in names if y in bodies and y not in direct and y != x]:
                ties[x] = set(ties[src[0]]); changed = True
        # a kernel-checked equation `T = A ++ B` of a tied template ties `A`, `B`
        for lhs, rhs in eqs:
            if lhs in ties and lhs not in renaming:
                for y in rhs:
                    if y in bodies and y != lhs and y not in renaming and not ties.get(y, set()) >= ties[lhs]:
                        ties.setdefault(y, set()).update(ties[lhs]); changed = True
    return ties, {x: next(iter(ps)) for x, ps in where.items() if len(ps) == 1}


_CLOSURE = {}


def closure(path):
    """The hand-written files `path` imports, transitively, and itself."""
    if path in _CLOSURE: return _CLOSURE[path]
    _CLOSURE[path] = {path}
    out = {path}
    try:
        text = open(path, encoding="utf-8").read()
    except OSError:
        return out
    for mod in re.findall(r'^(?:public\s+|meta\s+)*import\s+(?:all\s+)?(\S+)', text, re.M):
        q = mod.replace("«", "").replace("»", "").replace(".", "/") + ".lean"
        if q.startswith("LeanVM/") and os.path.exists(q) and not q.startswith(("LeanVM/Guest/Data/", "LeanVM/Guest/Pack/")):
            out |= closure(q)
    _CLOSURE[path] = out
    return out


def bound_here(x, text):
    """Whether the declaration binds `x` itself (a binder group `(x y : T)`, the names a `fun`, `∀`,
    `∃`, `intro`, `obtain`, `let`, `have` or a `match` pattern introduces), so `x` there is not the
    template of that name. Only the binders are read, never the expressions they range over."""
    e = re.escape(x)
    if re.search(r'[({]\s*(?:[\w\'.]+\s+)*' + e + r'(?:\s+[\w\'.]+)*\s*:', text):
        return True
    pats = [r'(?:\bfun\b|∀|∃|λ)\s*([^,:=∈<≤>()]*?)\s*(?:,|:|=>|↦|∈|<|≤)',
            r'\b(?:intro|rintro|obtain|rcases|cases|induction|let|have|set|generalize)\b([^:=\n]*?)(?::=|:|$)',
            r'^\s*\|\s*([^=\n]*?)=>']
    for pat in pats:
        for m in re.finditer(pat, text, re.M):
            if re.search(r'(?<![\w.\'])' + e + r'(?![\w\'])', m.group(1)):
                return True
    return False


TIE_EQ = re.compile(r'^theorem\s+\S+\s*:\s*([a-z][\w\']*)\s*=\s*([^:]*?)\s*:=\s*(?:by\s+decide\b|tbStmtsEqb_sound|stmtsEqb_sound|rfl\b)',
                    re.M | re.S)

ARGS = [re.compile(r'\bCompletes\w*\s+[^\s()]+\s+[^\s()]+\s+(\d+)\s+(\d+)\b'),
        re.compile(r'\bAgreeBelow\s+(\d+)\b'), re.compile(r'\bNBv\s+(\d+)\b'),
        re.compile(r'\bCompletes\w*\.append\s+\(m\s*:=\s*(\d+)\)'),
        re.compile(r'∀\s*(\w+)\s*<\s*(\d+)\s*,\s*σ\w*\s*\(\.n\s+\1\)')]

NUM = re.compile(r'(?<![\w.\'])(\d+)(?![\w.])')
VAL1 = re.compile(r'(?<![\w])(V\.n|\.n)\s+(\d+)(?![\w.])')
VALP = re.compile(r'(?<![\w])(V\.n|\.n)\s+\(')
POS = re.compile(r'(\.drop|\.take|\bdrop|\btake)\s+(\d+)(?![\w.])')


def paren_span(s, i):
    """From `(` at i, the index of its `)`."""
    d = 0
    for j in range(i, len(s)):
        if s[j] == "(": d += 1
        elif s[j] == ")":
            d -= 1
            if d == 0: return j
    return -1


def family_key(g):
    """The family of a specialization `f__L1_L2` (`f__L`) or of its loop `f__L1_L2_loop0`
    (`f__L_loop0`); none for another function."""
    m = re.fullmatch(r'(.+)__L\d+(?:_L\d+)*((?:_loop\d+)?)', g)
    return m.group(1) + "__L" + m.group(2) if m else None


def classify(path, src, overrides, vals, stmts, cnames, ties, families, where):
    code, doc = mask_comments(src)
    filefs = functions(code, cnames)
    spans = decls(code)

    def fn_at(i):
        """The function a literal at `i` reads: its declaration's, else the file's, if unique."""
        def chosen(o): return (("family", o), None) if o in families else (o, None)
        fs = set()
        for a, b, n in spans:
            if a <= i < b:
                if n.split(".")[-1] in overrides: return chosen(overrides[n.split(".")[-1]])
                text = code[a:b]
                # the functions every template and body reference of the declaration is tied to: a
                # generic builder tied to many (`cst`, a shared walk) narrows nothing, a template of
                # one function narrows to it, templates of two functions leave none
                sets = [{g} for g in functions(text, cnames)]
                seen = closure(path)
                sets += [ties[x] for x in set(IDENT.findall(text)) | {n}
                         if x in ties and where.get(x) in seen and (x == n or not bound_here(x, text))]
                if sets:
                    fs = set.intersection(*sets)
                    if not fs:
                        return None, "templates of different functions: " + ",".join(sorted(set.union(*sets))[:3]) + ",…"
                break
        # the map's function for the file, where the declaration's own evidence names none
        if not fs and "" in overrides: return chosen(overrides[""])
        # no fallback to the file's functions: a declaration that names no tied template and no body
        # (a lemma on a renumbered arm, `σ (.n 139)` of `rtTwo`) may be in another numbering
        if len(fs) == 1: return next(iter(fs)), None
        keys = {family_key(g) for g in fs}
        if len(keys) == 1 and None not in keys:
            k = keys.pop()
            # a template of several specializations is named over the whole family: its value has
            # one name in every specialization (`valf%` checks it), or the literal is flagged
            if len(fs) > 1 and set(fs) <= families.get(k, set()): return ("family", k), None
        return None, ("no function" if not fs else f"{len(fs)} functions " + ",".join(sorted(fs)[:3]) + ",…")

    def name_of(f, k, kind="value"):
        """The name of value `k` of `f` (or of every function of a family), or why there is none."""
        fs = tuple(sorted(families[f[1]])) if f[0:1] == ("family",) else f if isinstance(f, tuple) else (f,)
        ns = set()
        for g in fs:
            t = vals.get(g, {})
            if k >= len(t): return None, f"{kind} past {g}'s {len(t)}"
            ns.add(t[k])
        if len(ns) > 1: return None, f"{kind}: its names differ in " + ",".join(fs)
        return ns.pop(), None

    def cite(f, name):
        if f[0:1] == ("family",):
            used.add(f[1])
            base, suffix = f[1].split("__L", 1)
            return f'valf% «{base}» ' + (f"«{suffix}» " if suffix else "") + f'"{name}"'
        fs = f if isinstance(f, tuple) else (f,)
        used.update(fs)
        return "val% " + " ".join(f"«{g}»" for g in fs) + f' "{name}"'

    rows, edits, claimed, used = [], [], set(), set()

    def line(i): return src.count("\n", 0, i) + 1

    # values: `.n k`
    for m in VAL1.finditer(code):
        k, a, b = int(m.group(2)), m.start(2), m.end(2)
        claimed.add(a)
        f, why_f = fn_at(a)
        if not f:
            rows.append((line(a), "flagged", m.group(2), "value; " + why_f)); continue
        name, why = name_of(f, k)
        if not name:
            rows.append((line(a), "flagged", m.group(2), why)); continue
        rows.append((line(a), "value" if isinstance(f, str) else "value (family)", m.group(2), name))
        edits.append((a, b, "(" + cite(f, name) + ")"))
    # values: `.n (...)`
    for m in VALP.finditer(code):
        o = m.end() - 1
        c = paren_span(code, o)
        inner = code[o + 1:c]
        lits = [(x.start() + o + 1, x.group(1)) for x in NUM.finditer(inner)]
        for a, _ in lits: claimed.add(a)
        f, why_f = fn_at(o)
        if re.fullmatch(r'\s*\d+(\s*\+\s*\d+)*\s*', inner):
            k = sum(int(x) for _, x in lits)
            if not f:
                rows.append((line(o), "flagged", inner.strip(), "value; " + why_f)); continue
            name, why = name_of(f, k)
            if not name:
                rows.append((line(o), "flagged", inner.strip(), why)); continue
            rows.append((line(o), "value" if isinstance(f, str) else "value (family)", inner.strip(), name))
            edits.append((o, c + 1, "(" + cite(f, name) + ")"))
            continue
        # a parametric index: when every other summand is a numeral times a variable, its additive
        # numeral is a value's number (the index at zero), a numeral next to `*` a stride, which the
        # template's tie checks; a numeral added to a bare variable (`b + 6`) is an offset from a
        # base the tool cannot name
        terms = [t.strip() for t in re.split(r'\+(?![^()]*\))', inner)]
        strided = all(re.fullmatch(r'\d+', t) or re.fullmatch(r'\d+\s*\*\s*[\w\'.]+|[\w\'.]+\s*\*\s*\d+', t) for t in terms)
        for a, x in lits:
            j = a - (o + 1)
            left, right = inner[:j].rstrip(), inner[j + len(x):].lstrip()
            if left.endswith("*") or right.startswith("*"):
                rows.append((line(a), "stride", x, inner.strip())); continue
            if not strided or not (left == "" or left.endswith("+") or left.endswith("(")) or not (right == "" or right.startswith("+") or right.startswith(")")):
                rows.append((line(a), "flagged", x, "offset or parametric index " + inner.strip())); continue
            # the numeral is the index at zero only if zero is in the template's range, which the
            # text does not say (`4 * k + 76` serves `k ≥ 1`): flagged, never named
            rows.append((line(a), "flagged", x, "strided base " + inner.strip()))
    # literals in argument places that hold a value's number (`Completes C rd lo hi`, `AgreeBelow k`,
    # a template's base `(b := k)`, `NBv k`, `∀ k < n, σ …`)
    for pat in ARGS:
        for m in pat.finditer(code):
            for gi in range(1, (m.lastindex or 0) + 1):
                a, b = m.start(gi), m.end(gi)
                if a < 0 or a in claimed or not m.group(gi).isdigit(): continue
                claimed.add(a)
                f, why_f = fn_at(a)
                if not f:
                    rows.append((line(a), "flagged", m.group(gi), "argument value; " + why_f)); continue
                name, why = name_of(f, int(m.group(gi)), "argument value")
                if not name:
                    rows.append((line(a), "flagged", m.group(gi), why)); continue
                rows.append((line(a), "argument value", m.group(gi), name))
                edits.append((a, b, "(" + cite(f, name) + ")"))
    # positions: `drop k` / `take k`
    for m in POS.finditer(code):
        a, b = m.start(2), m.end(2)
        if a in claimed: continue
        claimed.add(a)
        before = code[max(0, m.start() - 80):m.start()].rstrip()
        on_body = before.endswith(".body") or before.endswith("body)") or re.search(r'\.body\s*$', before)
        k = int(m.group(2))
        f, why_f = fn_at(a)
        if not on_body:
            if k >= 10: rows.append((line(a), "flagged", m.group(2), "position not on a body (relative or a template's)"))
            else: rows.append((line(a), "other", m.group(2), "small"))
            continue
        if not f or not isinstance(f, str):
            rows.append((line(a), "flagged", m.group(2), "position; " + (why_f or "a family"))); continue
        name = stmts.get(f, {}).get(k)
        if name is None:
            rows.append((line(a), "flagged", m.group(2), f"statement {k} of {f} names no new value")); continue
        rows.append((line(a), "position", m.group(2), name))
        edits.append((a, b, f'(pos% «{f}» "{name}")')); used.add(f)
    # every other literal
    for m in NUM.finditer(code):
        a = m.start(1)
        if a in claimed: continue
        x = m.group(1)
        ctx = code[max(0, a - 12):a]
        after = code[m.end(1):m.end(1) + 3]
        if len(x) < 3:
            rows.append((line(a), "other", x, "small")); continue
        if re.search(r'word\s*\(?$', ctx) or re.search(r'\^\s*\(?$', ctx) or after.lstrip().startswith("^"):
            rows.append((line(a), "other", x, "word or power")); continue
        if re.search(r'(maxRecDepth|maxHeartbeats|extractLsb\'(\s+\d+)?|MemOK\s+\w+)\s+$', code[max(0, a - 30):a]) or int(x) >= 2 ** 32:
            rows.append((line(a), "other", x, "option, bit range or word-sized")); continue
        rows.append((line(a), "flagged", x, "bare literal: " + code[max(0, a - 30):m.end(1) + 10].replace("\n", " ").strip()))
    # literals in docs (counted, never rewritten)
    for m in NUM.finditer(src):
        if doc[m.start(1)] and len(m.group(1)) >= 3:
            rows.append((line(m.start(1)), "doc", m.group(1), "in a comment"))
    return used, rows, edits


def add_imports(src, fs):
    imps = ["import LeanVM.Guest.ValRef"] + [f"import LeanVM.Guest.Data.ValNames.«{f}»" for f in sorted(fs)]
    lines = src.split("\n")
    last = max((i for i, l in enumerate(lines) if re.match(r'(public |meta )*import ', l)), default=None)
    have = set(l.strip() for l in lines)
    new = [x for x in imps if x not in have]
    if last is None or not new: return src
    return "\n".join(lines[:last + 1] + new + lines[last + 1:])


def candidates(p, src, vals, cnames):
    """The functions a file without one may be about, with the evidence, for a person to decide
    (`--fn-map`): the functions it names (`name%`, a compiled name in quotes, an identifier with a
    function's stable name), those its imports read, kept when every number `.n k` it spells is one
    of their values."""
    code, _ = mask_comments(src)
    ks = [int(k) for k in re.findall(r'(?<![\w])(?:V\.n|\.n)\s+(\d+)', code)]
    ev = {}
    for g in re.findall(r'name%\s+«?([A-Za-z0-9_]+)»?', code): ev.setdefault(g, set()).add("name%")
    for n in re.findall(r'"([^"]+)"', src):
        if n in cnames: ev.setdefault(cnames[n], set()).add("quoted name")
    for g in vals:
        if len(g) > 4 and re.search(r'\b' + re.escape(g) + r'\b', code): ev.setdefault(g, set()).add("identifier")
    for imp in re.findall(r'^(?:public\s+)?import\s+(LeanVM\.Guest\.B1\.\S+)', src, re.M):
        q = imp.replace(".", "/") + ".lean"
        if os.path.exists(q):
            for g in functions(mask_comments(open(q, encoding="utf-8").read())[0], cnames):
                ev.setdefault(g, set()).add("import " + imp.split(".")[-1])
    keep = {g: e for g, e in ev.items() if all(k < len(vals.get(g, {})) for k in ks)}
    # a family's specializations as one candidate, `f__L` (`valf%`)
    fam = {}
    for g in keep:
        k = family_key(g)
        if k: fam.setdefault(k, []).append(g)
    out = []
    for k, gs in fam.items():
        if len(gs) > 1:
            out.append((k, f"{len(gs)} specializations"))
            for g in gs: keep.pop(g)
    out += [(g, ",".join(sorted(e))) for g, e in keep.items()]
    return sorted(out) or [("-", "none")]


def main():
    args = sys.argv[1:]
    write = "--write" in args
    fn = args[args.index("--fn") + 1] if "--fn" in args else None
    dump = args[args.index("--dump") + 1] if "--dump" in args else None
    report = args[args.index("--report") + 1] if "--report" in args else None
    skip = {i + 1 for i, a in enumerate(args) if a in ("--fn", "--dump", "--report", "--fn-map")}
    suggest = "--suggest" in args
    files = [a for i, a in enumerate(args) if not a.startswith("--") and i not in skip]
    vals, stmts = load_names(dump)
    families = {}
    for g in vals:
        k = family_key(g)
        if k: families.setdefault(k, set()).add(g)
    cnames = compiled_names()
    ties, where = global_ties()
    # the map: `FILE F` (the file's function), `FILE@decl F` (a declaration's), `tie T F` (a
    # template the source ties by a check the tool cannot read); `F` a function or a family `f__L…`
    fnmap = {}
    mp = args[args.index("--fn-map") + 1] if "--fn-map" in args else os.path.join(os.path.dirname(__file__), "fnmap.tsv")
    if os.path.exists(mp):
        for l in open(mp, encoding="utf-8"):
            if not l.strip() or l.startswith("#"): continue
            w = l.split()
            if w[0] == "tie":
                if w[1] in where: ties[w[1]] = set(families.get(w[2], {w[2]}))
                else: print(f"tie {w[1]}: no definition of that name in one file", file=sys.stderr)
                continue
            f, _, d = w[0].partition("@")
            fnmap.setdefault(f, {})[d] = w[1]
    if fn:
        for p in files: fnmap.setdefault(p, {}).setdefault("", fn)
    # the ties the map adds reach the templates they name
    changed = True
    while changed:
        changed = False
        for x in list(ties):
            for y in BODIES.get(x, ()):
                if y in BODIES and y != x and not ties.get(y, set()) >= ties[x]:
                    ties.setdefault(y, set()).update(ties[x]); changed = True
    tot = {}
    out = open(report, "a", encoding="utf-8") if report else None
    for p in files:
        src = open(p, encoding="utf-8").read()
        f, rows, edits = classify(p, src, fnmap.get(p, {}), vals, stmts, cnames, ties, families, where)
        if suggest and any("no function" in r[3] for r in rows):
            print(f"{p}: candidates " + "; ".join(f"{g} ({why})" for g, why in candidates(p, src, vals, cnames)))
        c = {}
        for r in rows: c[r[1]] = c.get(r[1], 0) + 1
        for k, v in c.items(): tot[k] = tot.get(k, 0) + v
        print(f"{p}: functions {','.join(sorted(f)) or '-'}; " + ", ".join(f"{k} {v}" for k, v in sorted(c.items())))
        if out:
            for r in sorted(rows):
                out.write("\t".join([p] + [" ".join(str(x).split()) for x in r]) + "\n")
        if write and edits:
            for a, b, t in sorted(edits, reverse=True):
                src = src[:a] + t + src[b:]
            src = add_imports(src, f)
            open(p, "w", encoding="utf-8").write(src)
    print("total: " + ", ".join(f"{k} {v}" for k, v in sorted(tot.items())))


if __name__ == "__main__":
    main()
