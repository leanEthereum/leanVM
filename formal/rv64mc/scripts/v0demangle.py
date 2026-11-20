"""Rust v0 symbol names (RFC 2603) as a tree, and the two renderings `gen.py` needs: a stable key (rustc-demangle's
form without crate disambiguators or the instantiating crate) and Lean module components (CamelCase identifiers).
Standard library only. Raises `ValueError` on anything it does not parse."""

BASIC = {
    "a": "i8", "b": "bool", "c": "char", "d": "f64", "e": "str", "f": "f32", "h": "u8", "i": "isize", "j": "usize",
    "l": "i32", "m": "u32", "n": "i128", "o": "u128", "s": "i16", "t": "u16", "u": "()", "v": "...", "x": "i64",
    "y": "u64", "z": "!", "p": "_",
}


class Parser:
    def __init__(self, s):
        self.s = s
        self.i = 0

    def peek(self):
        return self.s[self.i] if self.i < len(self.s) else ""

    def eat(self, c):
        if self.peek() == c:
            self.i += 1
            return True
        return False

    def next(self):
        c = self.peek()
        if not c:
            raise ValueError("unexpected end")
        self.i += 1
        return c

    def base62(self):
        if self.eat("_"):
            return 0
        v = 0
        while True:
            c = self.next()
            if c == "_":
                return v + 1
            if c.isdigit():
                d = ord(c) - 48
            elif "a" <= c <= "z":
                d = ord(c) - 97 + 10
            elif "A" <= c <= "Z":
                d = ord(c) - 65 + 36
            else:
                raise ValueError(f"bad base-62 digit {c!r}")
            v = v * 62 + d

    def disambiguator(self):
        return self.base62() + 1 if self.eat("s") else 0

    def decimal(self):
        j = self.i
        if self.eat("0"):
            return 0
        while self.peek().isdigit():
            self.i += 1
        if j == self.i:
            raise ValueError("expected a number")
        return int(self.s[j : self.i])

    def ident(self):
        dis = self.disambiguator()
        if self.eat("u"):
            raise ValueError("punycode identifier")
        n = self.decimal()
        self.eat("_")
        name = self.s[self.i : self.i + n]
        if len(name) != n:
            raise ValueError("identifier past the end")
        self.i += n
        return dis, name

    def backref(self, f):
        pos = self.base62()
        if pos >= self.i:
            raise ValueError("forward backref")
        save, self.i = self.i, pos
        r = f()
        self.i = save
        return r

    def path(self):
        c = self.next()
        if c == "C":
            _, name = self.ident()
            return ("crate", name)
        if c == "M":
            self.disambiguator()
            impl = self.path()
            return ("inherent", impl, self.type())
        if c == "X":
            self.disambiguator()
            impl = self.path()
            t = self.type()
            return ("trait_impl", impl, t, self.path())
        if c == "Y":
            t = self.type()
            return ("trait_def", t, self.path())
        if c == "N":
            ns = self.next()
            parent = self.path()
            dis, name = self.ident()
            return ("nested", ns, parent, name, dis)
        if c == "I":
            p = self.path()
            args = []
            while not self.eat("E"):
                args.append(self.generic_arg())
            return ("generic", p, args)
        if c == "B":
            return self.backref(self.path)
        raise ValueError(f"bad path tag {c!r}")

    def generic_arg(self):
        if self.eat("L"):
            self.base62()
            return ("lifetime",)
        if self.eat("K"):
            return self.const()
        return self.type()

    def const(self):
        if self.eat("p"):
            return ("const", "_")
        if self.eat("B"):
            return self.backref(self.const)
        t = self.next()
        if t not in BASIC:
            raise ValueError(f"const of type {t!r}")
        neg = self.eat("n")
        j = self.i
        while self.peek() != "_":
            self.next()
        v = int(self.s[j : self.i] or "0", 16)
        self.i += 1
        if t == "b":
            return ("const", "true" if v else "false")
        return ("const", str(-v if neg else v))

    def binder(self):
        if self.eat("G"):
            self.base62()

    def type(self):
        c = self.peek()
        if c in BASIC:
            self.i += 1
            return ("basic", BASIC[c])
        self.i += 1
        if c == "A":
            t = self.type()
            return ("array", t, self.const())
        if c == "S":
            return ("slice", self.type())
        if c == "T":
            ts = []
            while not self.eat("E"):
                ts.append(self.type())
            return ("tuple", ts)
        if c in "RQ":
            if self.eat("L"):
                self.base62()
            return ("ref", c == "Q", self.type())
        if c in "PO":
            return ("ptr", c == "O", self.type())
        if c == "F":
            self.binder()
            self.eat("U")
            if self.eat("K"):
                if not self.eat("C"):
                    self.ident()
            ts = []
            while not self.eat("E"):
                ts.append(self.type())
            return ("fn", ts, self.type())
        if c == "D":
            self.binder()
            traits = []
            while not self.eat("E"):
                p = self.path()
                while self.eat("p"):
                    self.ident()
                    self.type()
                traits.append(p)
            if not self.eat("L"):
                raise ValueError("dyn without lifetime")
            self.base62()
            return ("dyn", traits)
        if c == "B":
            return self.backref(self.type)
        self.i -= 1
        return self.path()


def parse(sym):
    """The tree of a v0 symbol, and its instantiating crate's name (or None)."""
    if not sym.startswith("_R"):
        raise ValueError("not a v0 symbol")
    p = Parser(sym[2:])
    if p.peek().isdigit():
        p.decimal()
    tree = p.path()
    inst = None
    if p.i < len(p.s) and p.peek() in "CNB":
        it = p.path()
        inst = it[1] if it[0] == "crate" else key(it)
    if p.i < len(p.s) and p.peek() != ".":
        raise ValueError(f"trailing {p.s[p.i:]!r}")
    return tree, inst


def key(t, value=True):
    """rustc-demangle's rendering, without disambiguators: a path's arguments after `::<` in the value namespace
    (`value`), after `<` in a type."""
    k = t[0]
    if k == "crate":
        return t[1]
    if k == "nested":
        _, ns, parent, name, dis = t
        if ns.isupper():
            what = {"C": "closure", "S": "shim"}.get(ns, ns)
            return f"{key(parent, value)}::{{{what}{':' + name if name else ''}#{dis}}}"
        return f"{key(parent, value)}::{name}" if name else key(parent, value)
    if k == "inherent":
        return f"<{key(t[2], False)}>"
    if k in ("trait_impl", "trait_def"):
        ty, tr = (t[2], t[3]) if k == "trait_impl" else (t[1], t[2])
        return f"<{key(ty, False)} as {key(tr, False)}>"
    if k == "generic":
        args = [key(a, False) for a in t[2] if a[0] != "lifetime"]
        sep = "::<" if value else "<"
        return f"{key(t[1], value)}{sep}{', '.join(args)}>" if args else key(t[1], value)
    if k in ("basic", "const"):
        return t[1]
    if k == "array":
        return f"[{key(t[1], False)}; {key(t[2], False)}]"
    if k == "slice":
        return f"[{key(t[1], False)}]"
    if k == "tuple":
        return "(" + ", ".join(key(x, False) for x in t[1]) + (",)" if len(t[1]) == 1 else ")")
    if k == "ref":
        return ("&mut " if t[1] else "&") + key(t[2], False)
    if k == "ptr":
        return ("*mut " if t[1] else "*const ") + key(t[2], False)
    if k == "fn":
        return "fn(" + ", ".join(key(x, False) for x in t[1]) + ") -> " + key(t[2], False)
    if k == "dyn":
        return "dyn " + " + ".join(key(x, False) for x in t[1])
    raise ValueError(f"cannot render {k}")


def camel(name):
    """`eq_eval` -> `EqEval`; a leading digit gets an `N`."""
    s = "".join(w[:1].upper() + w[1:] for w in name.split("_") if w)
    s = "".join(c for c in s if c.isascii() and (c.isalnum()))
    if not s:
        s = "X"
    return "N" + s if s[0].isdigit() else s


BASIC_NAMES = {"()": "Unit", "...": "Dots", "!": "Never", "_": "Any"}


def compact(t):
    """A type or path, in a few CamelCase words: last path segments and their arguments."""
    k = t[0]
    if k == "crate":
        return camel(t[1])
    if k == "nested":
        _, ns, parent, name, dis = t
        if ns.isupper():
            return compact(parent) + ("Closure" if ns == "C" else "Shim") + str(dis)
        return camel(name) if name else compact(parent)
    if k == "inherent":
        return compact(t[2])
    if k in ("trait_impl", "trait_def"):
        ty, tr = (t[2], t[3]) if k == "trait_impl" else (t[1], t[2])
        return compact(ty) + "As" + compact(tr)
    if k == "generic":
        return compact(t[1]) + "".join(compact(a) for a in t[2] if a[0] != "lifetime")
    if k == "basic":
        return BASIC_NAMES.get(t[1], camel(t[1]))
    if k == "const":
        return camel(t[1].replace("-", "neg"))
    if k == "array":
        return "Arr" + compact(t[1]) + compact(t[2])
    if k == "slice":
        return "Slice" + compact(t[1])
    if k == "tuple":
        return "T" + "".join(compact(x) for x in t[1]) + "E"
    if k == "ref":
        return ("RefMut" if t[1] else "Ref") + compact(t[2])
    if k == "ptr":
        return ("PtrMut" if t[1] else "Ptr") + compact(t[2])
    if k == "fn":
        return "Fn" + "".join(compact(x) for x in t[1]) + "To" + compact(t[2])
    if k == "dyn":
        return "Dyn" + "".join(compact(x) for x in t[1])
    raise ValueError(f"cannot render {k}")


def components(t, cap):
    """Lean module components for a path; `cap(s)` shortens a long CamelCase word."""
    k = t[0]
    if k == "crate":
        return [camel(t[1])]
    if k == "nested":
        _, ns, parent, name, dis = t
        last = (("Closure" if ns == "C" else "Shim") + str(dis)) if ns.isupper() else camel(name)
        return components(parent, cap) + [last] if ns.isupper() or name else components(parent, cap)
    if k == "inherent":
        return components(t[1], cap) + [cap(compact(t[2]))]
    if k == "trait_impl":
        return components(t[1], cap) + [cap(compact(t[2])), cap("As" + compact(t[3]))]
    if k == "trait_def":
        return components(t[2], cap) + [cap("For" + compact(t[1]))]
    if k == "generic":
        cs = components(t[1], cap)
        args = "".join(compact(a) for a in t[2] if a[0] != "lifetime")
        return cs[:-1] + [cap(cs[-1] + args)] if args else cs
    raise ValueError(f"no components for {k}")
