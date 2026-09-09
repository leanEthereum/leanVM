//! Parser: a minimal indentation-based Python-like surface syntax → [`Ast`].
//!
//! This file holds the line-oriented part: the indentation structure, the
//! statement forms, and the top level's global constants. The rest is split by
//! the question it answers:
//!
//! - [`mod@expr`] reads structure out of a line, under one rule: a string
//!   literal is one opaque token, and every scan goes through `depth0`.
//! - [`mod@consts`] evaluates a constant at parse time, which five syntactic
//!   positions demand before lowering ever runs. It reads a constant as an
//!   INTEGER, deliberately, which is what makes a derived size right.
//! - [`mod@subst`] substitutes an expression for a name through a statement
//!   tree, which is how `unroll` and `Const` bind their variable.

use super::*;
use std::collections::BTreeMap;

mod consts;
mod expr;
mod subst;
pub use consts::parse_const;
use consts::{apply_replacements, const_int_expr, eval_const_int, gpow_bound, parse_f192_const, parse_gpow_bound};
use expr::{
    binding_name, call_args, is_ident, parse_expr, split_assign, split_aug, split_once_top, split_top, string_lit,
    strip_comment, strip_const_wrapper, top_level_cmp,
};
pub(crate) use subst::subst_stmts;
use subst::subst_var;
/// Parse zkDSL source (the Python-shaped surface syntax of `zkDSL.md`) into an
/// [`Ast`]. The `snark_lib` import is skipped; any other import is an error,
/// since a program is a single file.
pub fn parse(src: &str) -> Result<Ast, String> {
    parse_with_replacements(src, &BTreeMap::new())
}

/// Like [`parse`], but first substitutes compile-time **placeholders**: an
/// identifier that is a key of `replacements` becomes its value everywhere it
/// appears, which is how a host bakes sizes and flags into a program without
/// editing it. The top level then peels off the **global constants**, each
/// evaluated as a compile-time integer (or an `f192` literal / constant array)
/// and substituted into the `def`s below. See the "Placeholders" and "Global
/// constants" sections of `zkDSL.md`.
pub fn parse_with_replacements(src: &str, replacements: &BTreeMap<String, String>) -> Result<Ast, String> {
    // Substitution runs over the RAW source, before lines are split, so a
    // replacement carrying a newline would shift every line after it and make
    // every diagnostic below name the wrong one. It would also inject statements
    // at whatever indentation it landed on. Reject it instead.
    // A `#` truncates the rest of the line just as silently, and changes the
    // compiled program with no diagnostic at all.
    // A `"` reshapes the line just as a `#` does, now that a string literal is one
    // opaque token: an odd number of them swallows the rest of the line.
    if let Some((k, _)) = replacements
        .iter()
        .find(|(_, v)| v.contains('\n') || v.contains('#') || v.contains('"'))
    {
        return Err(format!(
            "placeholder `{k}` contains a newline, `#` or `\"`, which would reshape the line"
        ));
    }
    let src = apply_replacements(src, replacements);
    // (source line, indent, content) for each significant line. The source line
    // is what every diagnostic below names; blanks, comments and imports are
    // skipped, so the index into this vector is NOT it.
    let mut lines: Vec<Line> = Vec::new();
    for (src_line, raw) in src.lines().enumerate() {
        let no_comment = strip_comment(raw);
        if no_comment.trim().is_empty() {
            continue;
        }
        let t = no_comment.trim();
        if let Some(rest) = t.strip_prefix("import ").or_else(|| t.strip_prefix("from ")) {
            let module = rest.split_whitespace().next().unwrap_or("");
            if module != "snark_lib" {
                return Err(locate(
                    src_line + 1,
                    format!("file imports are not supported (only the `snark_lib` stub): `{t}`"),
                ));
            }
            continue; // the stub is for Python tooling; the compiler skips it
        }
        let indent = no_comment.len() - no_comment.trim_start().len();
        lines.push(Line {
            src: src_line + 1,
            indent,
            text: no_comment.trim().to_string(),
        });
    }
    // Peel off the leading top-level constant declarations (before any `def`),
    // each evaluated to a field value and rendered as a single decimal literal.
    // Building a `name → literal` map lets later constants and the functions
    // reference them by plain text substitution, so a constant works even in
    // positions that demand a parse-time literal (`StackBuf`, `**`, `assert log
    // _ < _`).
    let mut consts: BTreeMap<String, String> = BTreeMap::new();
    let mut const_arrays: Vec<(String, Vec<F192>)> = Vec::new();
    let mut start = 0;
    while start < lines.len() {
        let Line {
            src,
            indent,
            text: line,
        } = &lines[start];
        let at = |e: String| locate(*src, e);
        if *indent == 0 && (line.starts_with("def ") || line.starts_with('@')) {
            break;
        }
        if *indent != 0 {
            return Err(at(format!("unexpected indentation at top level: `{line}`")));
        }
        let (lhs, rhs) = split_assign(line).ok_or_else(|| {
            at(format!(
                "top level: expected `def`, a global constant `NAME = value`, or the `snark_lib` import, got `{line}`"
            ))
        })?;
        let name = lhs.trim().to_string();
        if !is_ident(&name) {
            return Err(at(format!(
                "global constant name must be a plain identifier: `{}`",
                lhs.trim()
            )));
        }
        if consts.contains_key(&name) || const_arrays.iter().any(|(n, _)| n == &name) {
            return Err(at(format!("global constant `{name}` is declared twice")));
        }
        // A scalar constant is substituted textually, so one named after a builtin
        // rewrites the builtin's own call sites: `match = 4` turned
        // `v = match(log(x), …)` into `4(log(x), …)`, whose diagnostic names
        // neither the constant nor `match`.
        if BUILTINS.contains(&name.as_str()) {
            return Err(at(format!(
                "`{name}` is a builtin, so a global constant of that name would be substituted \
                 into its own call sites. Rename it"
            )));
        }
        // Resolve earlier scalar constants inside the value first.
        let rhs = apply_replacements(rhs.trim(), &consts);
        let rhs = rhs.trim();
        if let Some(inner) = rhs.strip_prefix('[').and_then(|s| s.strip_suffix(']')) {
            // A constant array `NAME = [a, b, c]`: each element a compile-time
            // integer / field value. Not textually substituted, but carried to
            // lowering, indexed/measured there.
            let mut elems = Vec::new();
            for part in split_top(inner, ',') {
                let p = part.trim();
                if p.is_empty() {
                    continue; // tolerate a trailing comma
                }
                let elem = if let Some(v) = parse_f192_const(p) {
                    v.map_err(|e| at(format!("global constant array `{name}`: {e}")))?
                } else {
                    let n = eval_const_int(p).map_err(|e| at(format!("global constant array `{name}`: {e}")))?;
                    F192::new(n as u64, (n >> 64) as u64, 0)
                };
                elems.push(elem);
            }
            const_arrays.push((name, elems));
        } else {
            // A scalar constant: an `f192` literal, else a compile-time integer,
            // else a field-valued expression.
            if let Some(value) = parse_f192_const(rhs) {
                let v = value.map_err(|e| at(format!("global constant `{name}`: {e}")))?;
                consts.insert(name, format!("f192({},{},{})", v.c0, v.c1, v.c2));
            } else if let Ok(value) = eval_const_int(rhs) {
                consts.insert(name, value.to_string());
            } else {
                // `GEN ** 2` and friends. The ISA is written in g-powers, so this
                // is the natural spelling for a constant one, and it is not an
                // integer expression. Rendered as a decimal wherever the value
                // fits the low two limbs, so the constant still works in the
                // positions that demand a literal rather than only as a value.
                let v = parse_const(rhs).map_err(|e| at(format!("global constant `{name}`: {e}")))?;
                consts.insert(
                    name,
                    if v.c2 == 0 {
                        (v.c0 as u128 | ((v.c1 as u128) << 64)).to_string()
                    } else {
                        format!("f192({},{},{})", v.c0, v.c1, v.c2)
                    },
                );
            }
        }
        start += 1;
    }
    // Substitute the constants into every remaining (function) line, then parse.
    let func_lines: Vec<Line> = lines[start..]
        .iter()
        .map(|l| Line {
            src: l.src,
            indent: l.indent,
            text: apply_replacements(&l.text, &consts),
        })
        .collect();
    let mut p = Parser {
        lines: &func_lines,
        i: 0,
    };
    let mut funcs = Vec::new();
    while p.i < p.lines.len() {
        funcs.push(p.func()?);
    }
    // Two names that used to be accepted and then silently picked a winner.
    // A repeated `def` lowered both bodies and kept the last, and a name
    // beginning with `__` can collide with a compiler-generated one: a loop
    // helper is `__loopN`, and a `Const` specialization of `f` is `f__L1`, so a
    // user function called `f__L1` took the specialization's place and the call
    // ran the wrong body.
    for (i, f) in funcs.iter().enumerate() {
        if funcs[..i].iter().any(|g| g.name == f.name) {
            return Err(format!("function `{}` is defined twice", f.name));
        }
        if f.name.contains("__") {
            return Err(format!(
                "function name `{}` may not contain `__`, which is reserved for the names the \
                 compiler generates (a loop helper, a `Const` specialization)",
                f.name
            ));
        }
        // A builtin wins at the call site, so a function with a builtin's name is
        // never called and its body, constraints included, silently disappears.
        // `def const(x): assert x == 99` was skipped outright by `v = const(4)`,
        // and by whether the ARGUMENT folded, so one call site had two meanings.
        if BUILTINS.contains(&f.name.as_str()) {
            return Err(format!(
                "`{}` is a builtin, so a function of that name could never be called: \
                 the builtin takes every call site. Rename it",
                f.name
            ));
        }
    }
    infer_return_shapes(&mut funcs)?;
    Ok(Ast { funcs, const_arrays })
}

/// Every name the lowerer resolves before it looks for a user function. A `def`
/// may not take one of these, since the builtin would win and the body would be
/// dead code that still looked live.
const BUILTINS: &[&str] = &[
    "addr",
    "assert_in_k",
    "blake2s",
    "const",
    "f192",
    "hint_decompose_bits",
    "hint_decompose_bits_exponent",
    "hint_f192_limbs",
    "hint_log2_ceil",
    "hint_witness",
    "len",
    "match",
    "HeapBuf",
    "StackBuf",
];

/// Infer the compile-time representation of each tail-return value: a `StackBuf`
/// carries its static size, a `HeapBuf` stays a one-cell pointer (its allocation
/// hint ran in the creating function). Iterated to a fixed point, so a wrapper
/// may return a buffer produced by a function declared later.
fn infer_return_shapes(funcs: &mut [Func]) -> Result<(), String> {
    fn expr_shape(
        e: &Expr,
        locals: &HashMap<&str, Shape>,
        known: &HashMap<String, Vec<Shape>>,
    ) -> Result<Shape, String> {
        let fits = |n: u64| u32::try_from(n).map_err(|_| format!("StackBuf size {n} does not fit in u32"));
        Ok(match e {
            Expr::Var(v) => locals.get(v.as_str()).copied().unwrap_or(Shape::Scalar),
            Expr::StackBuf(n) => Shape::StackBuf(fits(*n)?),
            Expr::ListLit(es) => Shape::StackBuf(fits(es.len() as u64)?),
            Expr::Call(f, _) => known
                .get(f)
                .filter(|r| r.len() == 1)
                .and_then(|r| r.first())
                .copied()
                .unwrap_or(Shape::Scalar),
            _ => Shape::Scalar,
        })
    }

    fn scan(
        body: &[Stmt],
        params: &[Param],
        known: &HashMap<String, Vec<Shape>>,
        n_ret: usize,
    ) -> Result<Vec<Shape>, String> {
        // Seeded from the DECLARED shapes: a `s: StackBuf(n)` parameter is a run
        // here as much as a local one is, so `return s` returns the run rather
        // than reporting it used as a scalar.
        let mut locals: HashMap<&str, Shape> = params.iter().map(|p| (p.name.as_str(), p.shape())).collect();
        let mut returns = vec![Shape::Scalar; n_ret];
        for stmt in body {
            match &stmt.kind {
                StmtKind::Let(name, e) => {
                    let shape = expr_shape(e, &locals, known)?;
                    locals.insert(name.as_str(), shape);
                }
                StmtKind::LetTuple(names, f, _) => {
                    let shapes = known.get(f);
                    for (i, name) in names.iter().enumerate() {
                        let shape = shapes.and_then(|s| s.get(i)).copied().unwrap_or(Shape::Scalar);
                        locals.insert(name.as_str(), shape);
                    }
                }
                // `unroll` is straight-line expansion, so a binding in its last
                // copy remains visible afterward. One symbolic scan is enough
                // for representation shapes (the iteration value is scalar).
                StmtKind::Unroll { var, body, .. } => {
                    locals.insert(var.as_str(), Shape::Scalar);
                    for inner in body {
                        if let StmtKind::Let(name, e) = &inner.kind {
                            let shape = expr_shape(e, &locals, known)?;
                            locals.insert(name.as_str(), shape);
                        }
                    }
                }
                StmtKind::LetHintWitness { name, .. } => {
                    locals.insert(name.as_str(), Shape::Scalar);
                }
                StmtKind::Return(es) => {
                    returns = es
                        .iter()
                        .map(|e| expr_shape(e, &locals, known))
                        .collect::<Result<_, _>>()?;
                }
                _ => {}
            }
        }
        Ok(returns)
    }

    let mut known: HashMap<String, Vec<Shape>> = funcs
        .iter()
        .map(|f| (f.name.clone(), f.return_shapes.clone()))
        .collect();
    // A shape can only move from Scalar to one of the finite constructor
    // shapes (or acquire one through a call), so `funcs.len() + 1` rounds are
    // sufficient for the longest acyclic wrapper chain.
    for _ in 0..=funcs.len() {
        let next: HashMap<String, Vec<Shape>> = funcs
            .iter()
            .map(|f| Ok((f.name.clone(), scan(&f.body, &f.params, &known, f.return_shapes.len())?)))
            .collect::<Result<_, String>>()?;
        if next == known {
            break;
        }
        known = next;
    }
    for f in funcs {
        f.return_shapes = known
            .remove(&f.name)
            .expect("every function has inferred return shapes");
    }
    Ok(())
}

/// Parse a zkDSL source file (a `.py` file, since the DSL is Python-shaped, see
/// [`parse`]) with compile-time **placeholder** replacements (see
/// [`parse_with_replacements`]).
pub fn parse_file_with_replacements(
    path: impl AsRef<std::path::Path>,
    replacements: &BTreeMap<String, String>,
) -> Result<Ast, String> {
    let path = path.as_ref();
    let src = std::fs::read_to_string(path).map_err(|e| format!("cannot read `{}`: {e}", path.display()))?;
    parse_with_replacements(&src, replacements)
}

/// One significant source line: its 1-based position in the ORIGINAL file, its
/// indentation, and its text with comments stripped and constants substituted.
/// Prefix a diagnostic with the source line it came from, unless an inner frame
/// already named a more specific one.
/// Does the leading call span the WHOLE of `s`?
///
/// `call_args` strips the first `(` and the LAST `)`, so it also matches a line
/// where the call is only the first factor: `hint_witness("a") * f("b")` came
/// back with the stream name `a") * f("b`, and the rest of the line vanished.
/// A `)` that closes below depth zero means the call ended before the line did.
fn whole_call(s: &str) -> bool {
    let Some(inner) = s.find('(').map(|i| &s[i + 1..]) else {
        return false;
    };
    let (mut depth, mut in_str) = (0i32, false);
    for (i, c) in inner.bytes().enumerate() {
        if in_str {
            in_str = c != b'"';
            continue;
        }
        match c {
            b'"' => in_str = true,
            b'(' | b'[' => depth += 1,
            b')' | b']' => {
                depth -= 1;
                // The close that matches the call's own `(`. It has to be the
                // last thing on the line, or something followed the call.
                if depth < 0 {
                    return i + 1 == inner.len();
                }
            }
            _ => {}
        }
    }
    false
}

fn locate(line: usize, e: String) -> String {
    if e.starts_with("line ") {
        e
    } else {
        format!("line {line}: {e}")
    }
}

struct Line {
    src: usize,
    indent: usize,
    text: String,
}

struct Parser<'a> {
    lines: &'a [Line],
    i: usize,
}

impl Parser<'_> {
    /// The source line the cursor is on, for a diagnostic raised where no
    /// `func`/`stmt` frame is open: those two stamp the line they were ENTERED
    /// on, which is an enclosing header, not the line that is actually wrong.
    fn here(&self) -> usize {
        self.lines
            .get(self.i)
            .or_else(|| self.lines.last())
            .map_or(0, |l| l.src)
    }

    fn func(&mut self) -> Result<Func, String> {
        let here = self.lines.get(self.i).map_or(0, |l| l.src);
        self.func_inner().map_err(|e| locate(here, e))
    }

    fn func_inner(&mut self) -> Result<Func, String> {
        let mut line = &self.lines[self.i];
        // Optional `@inline` decorator on its own line before `def`.
        let inline = if let Some(dec) = line.text.strip_prefix('@') {
            if dec.trim() != "inline" {
                return Err(format!("unknown decorator `@{}` (only `@inline`)", dec.trim()));
            }
            self.i += 1;
            line = self.lines.get(self.i).ok_or("`@inline` must precede a `def`")?;
            true
        } else {
            false
        };
        // Re-stamped here: the decorator path advanced past its own line, so
        // `func`'s frame would name the `@inline` while quoting the `def`.
        let at_def = self.here();
        self.func_header(inline, line.indent, &line.text)
            .map_err(|e| locate(at_def, e))
    }

    fn func_header(&mut self, inline: bool, indent: usize, line: &str) -> Result<Func, String> {
        let header = line
            .strip_prefix("def ")
            .ok_or_else(|| format!("expected `def`, got `{line}`"))?;
        let header = header.strip_suffix(':').ok_or("function header needs `:`")?;
        let open = header.find('(').ok_or("function header needs `(`")?;
        let name = header[..open].trim().to_string();
        let params_str = header[open + 1..header.rfind(')').ok_or("missing `)`")?].trim();
        let mut params = Vec::new();
        if !params_str.is_empty() {
            for part in params_str.split(',') {
                if part.trim().is_empty() {
                    return Err(format!("`def {name}`: empty parameter (a trailing comma?)"));
                }
                // `x`, `x: Const` (compile-time, specialized), or
                // `x: StackBuf(n)` (a run of n cells, passed whole).
                let (param_name, annotation) = part.split_once(':').map_or((part, None), |(n, a)| (n, Some(a.trim())));
                let kind = match annotation {
                    None => ParamKind::Runtime(Shape::Scalar),
                    Some("Const") => ParamKind::Const,
                    Some(ann) => {
                        let size = ann.strip_prefix("StackBuf(").and_then(|r| r.strip_suffix(')')).ok_or_else(|| {
                            format!("unsupported parameter annotation `{ann}` (`Const`, or `StackBuf(n)` to pass a run of cells)")
                        })?;
                        let k =
                            eval_const_int(size).map_err(|e| format!("`def {name}`: StackBuf parameter size: {e}"))?;
                        let k = u32::try_from(k).map_err(|_| format!("`def {name}`: StackBuf({k}) is too large"))?;
                        if k == 0 {
                            return Err(format!("`def {name}`: a StackBuf parameter needs at least one cell"));
                        }
                        ParamKind::Runtime(Shape::StackBuf(k))
                    }
                };
                params.push(Param {
                    name: binding_name(param_name, "parameter name")?,
                    kind,
                });
            }
        }
        if let Some(dup) = params
            .iter()
            .enumerate()
            .find_map(|(i, p)| params[..i].iter().any(|q| q.name == p.name).then_some(&p.name))
        {
            return Err(format!("parameter `{dup}` is declared twice"));
        }
        self.i += 1;
        let body = self.block(indent)?;
        let n_ret = body
            .iter()
            .filter_map(|s| {
                if let StmtKind::Return(es) = &s.kind {
                    Some(es.len())
                } else {
                    None
                }
            })
            .max()
            .unwrap_or(0);
        Ok(Func {
            name,
            params,
            return_shapes: vec![Shape::Scalar; n_ret],
            body,
            inline,
        })
    }

    /// Parse a block: all statements indented strictly more than `parent`.
    fn block(&mut self, parent: usize) -> Result<Vec<Stmt>, String> {
        let mut stmts = Vec::new();
        let block_indent = match self.lines.get(self.i) {
            Some(Line { indent: ind, .. }) if *ind > parent => *ind,
            _ => return Err(locate(self.here(), "expected an indented block".into())),
        };
        while let Some(Line { indent: ind, .. }) = self.lines.get(self.i) {
            if *ind != block_indent {
                if *ind > parent && *ind > block_indent {
                    return Err(locate(self.here(), "inconsistent indentation".into()));
                }
                break;
            }
            stmts.push(self.stmt(block_indent)?);
        }
        Ok(stmts)
    }

    fn stmt(&mut self, indent: usize) -> Result<Stmt, String> {
        let here = self.lines.get(self.i).map_or(0, |l| l.src);
        self.stmt_inner(indent)
            .map(|kind| Stmt::new(here as u32, kind))
            .map_err(|e| locate(here, e))
    }

    fn stmt_inner(&mut self, indent: usize) -> Result<StmtKind, String> {
        let line = self.lines[self.i].text.as_str();
        if let Some(rest) = line.strip_prefix("for ") {
            // for VAR in mul_range(START, STOP): the counter walks gᵏ from START
            // to STOP, ×g each iteration (STOP is exclusive). Bounds are field
            // elements (powers of GEN), so the multiplicative walk is explicit.
            let rest = rest.strip_suffix(':').ok_or("`for` needs `:`")?;
            let (var, iter) = rest.split_once(" in ").ok_or("`for` needs `in`")?;
            // `for i in unroll(a, b):` is compile-time replication; the bounds
            // are integer expressions, evaluated at lowering (so a `Const`
            // parameter works as a bound).
            if let Some(parts) = call_args(iter, "unroll") {
                if parts.len() != 2 {
                    return Err("unroll needs `a, b` (compile-time integers)".into());
                }
                let (lo, hi) = (parse_expr(parts[0])?, parse_expr(parts[1])?);
                self.i += 1;
                let body = self.block(indent)?;
                return Ok(StmtKind::Unroll {
                    var: binding_name(var, "loop counter")?,
                    lo,
                    hi,
                    body,
                });
            }
            let parts = call_args(iter, "mul_range").ok_or("`for` needs `mul_range(start, stop)` or `unroll(a, b)`")?;
            if parts.len() != 2 {
                return Err("mul_range needs `start, stop`".into());
            }
            let lo = parse_gpow_bound(parts[0])?;
            // The stop bound: a compile-time power of GEN, or any expression,
            // a runtime g-power element the walk must be able to reach.
            let hi = match parse_gpow_bound(parts[1]) {
                Ok(hi) => {
                    if lo > hi {
                        return Err(format!("mul_range: start GEN**{lo} must not exceed stop GEN**{hi}"));
                    }
                    ForBound::Const(hi)
                }
                Err(_) => {
                    let stop = parse_expr(parts[1])?;
                    // A compile-time value that is not a power of GEN can never be
                    // REACHED: the counter walks by multiplication and exits on
                    // equality, so the loop runs forever at witness generation with
                    // no diagnostic. The `lo` side has always been checked, which
                    // made `mul_range(0, GEN ** 3)` a clean parse error while
                    // `mul_range(1, 10)` was a hang.
                    // A power of two reached `gpow_bound` above, so a literal here
                    // is one the multiplicative walk can never hit. This catches a
                    // bare `10` and a constant that substitutes to one; a value
                    // built by arithmetic (`5 * 2`) still slips through to the
                    // runtime path and still hangs, which wants a field-level
                    // constant folder the parser does not have.
                    if let Expr::Lit(n) = stop {
                        return Err(format!(
                            "mul_range stop bound `{n}` is not a power of GEN, so the multiplicative walk \
                             never reaches it: write `GEN ** k`"
                        ));
                    }
                    ForBound::Runtime(stop)
                }
            };
            self.i += 1;
            let body = self.block(indent)?;
            return Ok(StmtKind::For {
                var: binding_name(var, "loop counter")?,
                lo,
                hi,
                body,
            });
        }
        if let Some(rest) = line.strip_prefix("if ") {
            return self.if_stmt(rest, indent);
        }
        self.i += 1;
        if line == "return" {
            return Ok(StmtKind::Return(vec![]));
        }
        if let Some(rest) = line.strip_prefix("return ") {
            return Ok(StmtKind::Return(
                split_top(rest, ',')
                    .iter()
                    .map(|e| parse_expr(e))
                    .collect::<Result<_, _>>()?,
            ));
        }
        // `print(expr)` / `print("label", expr)`: prover-side debug print;
        // the label defaults to the argument's source text.
        if let Some(parts) = call_args(line, "print") {
            let (label, value) = match parts.as_slice() {
                [l, v] if l.trim().starts_with('"') => {
                    let l = string_lit(l).ok_or("print's label is a string literal: print(\"label\", expr)")?;
                    (l.to_string(), v.trim())
                }
                [v] => (v.trim().to_string(), v.trim()),
                _ => return Err("print takes `print(expr)` or `print(\"label\", expr)`".into()),
            };
            return Ok(StmtKind::Print {
                label,
                value: parse_expr(value)?,
            });
        }
        // `hint_witness(dest, "name")`: the string literal is not an
        // expression; parsed here. `whole_call` for the same reason as the
        // scalar form: the string arg is what lets a trailing `* f("b")`
        // vanish into the stream name instead of failing to parse.
        if let Some(parts) = call_args(line, "hint_witness").filter(|_| whole_call(line)) {
            let [dest, name] = parts.as_slice() else {
                return Err("hint_witness(dest, \"name\") takes two arguments".into());
            };
            let name = string_lit(name).ok_or("hint_witness's second argument is a string literal: \"name\"")?;
            return Ok(StmtKind::HintWitness {
                dest: parse_expr(dest)?,
                name: name.to_string(),
            });
        }
        if let Some(rest) = line.strip_prefix("assert ") {
            if let Some((a, b)) = split_once_top(rest, "==") {
                return Ok(StmtKind::AssertEq(parse_expr(a)?, parse_expr(b)?));
            }
            if let Some((a, b)) = split_once_top(rest, "!=") {
                return Ok(StmtKind::AssertNe(parse_expr(a)?, parse_expr(b)?));
            }
            // `assert log X < log Y` (`Y` a compile-time g-power, or any runtime
            // g-power) or `assert log X < k` (`k` an integer exponent) is a
            // range check in the exponent: proves `log_g(X) < k`.
            if let Some((a, b)) = split_once_top(rest, "<") {
                let x =
                    strip_log(a).ok_or("a `<` assert compares logs: `assert log X < log Y` or `assert log X < k`")?;
                let bound = match strip_log(b) {
                    // `log GEN ** k = k` when the bound folds to a power of GEN;
                    // otherwise it is a runtime g-power and the gadget derives
                    // `g^{k-1}` from it. A bound that folds to something else is a
                    // mistake rather than a runtime bound: `log 8` names the field
                    // element 8, whose g-log is nothing in particular, and taking it
                    // for a bound would fail only at witness generation.
                    Some(y) => {
                        let y = parse_expr(y)?;
                        match gpow_bound(&y) {
                            Ok(k) => LtBound::Const(k),
                            Err(e) if const_int_expr(&y).is_some() => return Err(e),
                            Err(_) => LtBound::Runtime(y),
                        }
                    }
                    // An integer bound folds like any parse-time size (`CAP + 1`).
                    None => match const_int_expr(&parse_expr(b)?) {
                        Some(k) => {
                            LtBound::Const(u64::try_from(k).map_err(|_| format!("log bound {k} does not fit in u64"))?)
                        }
                        None => {
                            return Err(format!(
                                "a log bound must be `log _` or a parse-time integer, got `{b}`"
                            ));
                        }
                    },
                };
                return Ok(StmtKind::AssertLt(parse_expr(x)?, bound));
            }
            return Err("`assert` needs `==`, `!=`, or `log _ < _`".into());
        }
        // Augmented assignment `x OP= rhs` (Python `*=`, `+=`, `//=`, `%=`,
        // `-=`) desugars to `x = x OP (rhs)`.
        let expanded = split_aug(line)?.map(|(lhs, op, rhs)| format!("{lhs} = {lhs} {op} ({rhs})"));
        let line = expanded.as_deref().unwrap_or(line);
        // Assignment or bare call.
        if let Some((lhs, rhs)) = split_assign(line) {
            // `names = match(…)` carries lambdas, which `parse_expr`
            // does not speak, so it gets its own parser.
            if rhs.trim_start().starts_with("match(") {
                return parse_match(lhs, rhs);
            }
            // `x = hint_witness("stream")`: one hinted value, no buffer. The
            // string is not an expression, so like the run form it is parsed
            // here rather than by `parse_expr`.
            if let Some(parts) = call_args(rhs.trim(), "hint_witness").filter(|_| whole_call(rhs.trim())) {
                let [stream] = parts.as_slice() else {
                    return Err(
                        "`x = hint_witness(\"stream\")` takes one argument; to fill a run, write \
                         `hint_witness(dest, \"stream\")` as a statement"
                            .into(),
                    );
                };
                let stream = string_lit(stream).ok_or("hint_witness's argument is a string literal: \"stream\"")?;
                return Ok(StmtKind::LetHintWitness {
                    name: binding_name(lhs, "binding name")?,
                    stream: stream.to_string(),
                });
            }
            let rhs_expr = parse_expr(rhs)?;
            // Indexed LHS `arr[idx] = value` is a heap store.
            if lhs.trim_end().ends_with(']') {
                let lhs = lhs.trim();
                let open = lhs.find('[').ok_or("malformed store target")?;
                let arr = parse_expr(&lhs[..open])?;
                let idx = parse_expr(&lhs[open + 1..lhs.len() - 1])?;
                return Ok(StmtKind::Store(arr, idx, rhs_expr));
            }
            let targets = split_top(lhs, ',');
            if targets.len() == 1 {
                return Ok(StmtKind::Let(binding_name(targets[0], "binding name")?, rhs_expr));
            }
            // Tuple assignment: RHS must be a call.
            if let Expr::Call(f, args) = rhs_expr {
                let names = targets
                    .iter()
                    .map(|t| binding_name(t, "binding name"))
                    .collect::<Result<Vec<_>, _>>()?;
                return Ok(StmtKind::LetTuple(names, f, args));
            }
            return Err("tuple assignment requires a call on the right".into());
        }
        // A bare comparison is not a statement, and `split_assign` used to split
        // one on its `=` into a binding named `x !`. In a verifier that is an
        // `assert` compiled to nothing, so name the fix rather than letting the
        // expression parser fail on an operator it does not have.
        // `while`/`elif`/`else` reach here as unknown keywords, not comparisons, so
        // suggesting `assert while x < y:` would be worse than the generic error.
        let keyword = ["while ", "elif ", "else", "for ", "def "]
            .iter()
            .any(|k| line.starts_with(k));
        if let Some(op) = top_level_cmp(line).filter(|_| !keyword) {
            let fix = if matches!(op, "==" | "!=") {
                format!("write `assert {line}`")
            } else {
                format!("`{op}` is not a predicate: order facts come from `assert log x < k`")
            };
            return Err(format!("`{line}` is a comparison, not a statement: {fix}"));
        }
        // Bare call statement.
        if let Expr::Call(f, args) = parse_expr(line)? {
            return Ok(StmtKind::Call(f, args));
        }
        Err(format!("statement has no effect: `{line}`"))
    }

    /// `if a == b:` / `if a != b:` (the current line, its `if `/`elif `
    /// prefix already stripped into `header`), with an optional `elif`/`else`
    /// tail at the same indent (an `elif` is sugar for an `else` holding a
    /// nested `if`).
    fn if_stmt(&mut self, header: &str, indent: usize) -> Result<StmtKind, String> {
        let cond = header.strip_suffix(':').ok_or("`if` needs `:`")?;
        let (cond, force_const) = match strip_const_wrapper(cond) {
            Some(inner) => (inner, true),
            // A near miss (`const (a == b)`, an unbalanced one) otherwise falls
            // through to an ordinary parse error that never says the word, so name
            // it here. Two things are NOT near misses: `const == 4`, a variable
            // that happens to be called `const`, since nothing follows the name but
            // the comparison; and a condition with a comparison of its own, since
            // `const(...)` is a value expression too, so `if const(k) == n:` is an
            // ordinary runtime test of a folded literal and rejecting it made the
            // two operand orders behave differently.
            None if top_level_cmp(cond).is_none()
                && cond
                    .trim_start()
                    .strip_prefix("const")
                    .is_some_and(|r| r.trim_start().starts_with('(')) =>
            {
                return Err(
                    "`const(...)` must wrap the WHOLE condition and balance its brackets: `if const(a == b):`".into(),
                );
            }
            None => (cond, false),
        };
        let (eq, l, r) = if let Some((l, r)) = split_once_top(cond, "==") {
            (true, l, r)
        } else if let Some((l, r)) = split_once_top(cond, "!=") {
            (false, l, r)
        } else {
            return Err("an `if` condition must be `a == b` or `a != b`".into());
        };
        let (lhs, rhs) = (parse_expr(l)?, parse_expr(r)?);
        self.i += 1;
        let then = self.block(indent)?;
        let mut els = Vec::new();
        if let Some(Line {
            indent: ind,
            text: line,
            ..
        }) = self.lines.get(self.i)
            && *ind == indent
        {
            if line == "else:" {
                self.i += 1;
                els = self.block(indent)?;
            } else if let Some(rest) = line.strip_prefix("elif ") {
                // `if_stmt` recurses into ITSELF for an `elif`, so no `stmt`
                // frame opens and the whole chain would report the first `if`.
                let at_elif = self.here();
                els = vec![Stmt::new(
                    at_elif as u32,
                    self.if_stmt(rest, indent).map_err(|e| locate(at_elif, e))?,
                )];
            }
        }
        Ok(StmtKind::If {
            eq,
            lhs,
            rhs,
            then,
            els,
            force_const,
        })
    }
}

type Aug<'a> = Option<(&'a str, &'static str, &'a str)>;

/// Strip a leading `log` token (`log x`, `log(x)`), if present. The token must
/// end at a boundary, so a variable named `logx` is not a log of `x`.
fn strip_log(s: &str) -> Option<&str> {
    let r = s.trim_start().strip_prefix("log")?;
    r.starts_with([' ', '(']).then_some(r)
}

/// `names = match(log(x), range(a, b), lambda i: expr, …)`: leanVM's
/// `match`, expanded at parse time: one arm per integer of the
/// contiguous `(range, lambda)` pairs, arm `j` being the lambda body with the
/// parameter substituted by the literal `j`. The union of the ranges must be
/// gapless and start at 0 (this compiler's `match` rule). Everything sits on
/// one line, since there is no line continuation.
fn parse_match(lhs: &str, rhs: &str) -> Result<StmtKind, String> {
    // A target is a name, or a `StackBuf` element, which the arms then write
    // into directly: the ABI already returns into cells the caller picks, so
    // `sb[i], e = match(…)` costs no copy where a name plus a store did.
    let targets = split_top(lhs, ',')
        .iter()
        .map(|t| match parse_expr(t)? {
            e @ (Expr::Var(_) | Expr::Index(..)) => Ok(e),
            other => Err(format!(
                "a `match` target must be a name or a StackBuf element, got `{other:?}`"
            )),
        })
        .collect::<Result<Vec<_>, _>>()?;
    let chunks = call_args(rhs, "match").ok_or("malformed `match(…)`")?;
    let (first, pairs) = chunks.split_first().ok_or("match needs arguments")?;
    let x = strip_log(first).ok_or("`match` matches logs: `match(log(x), …)`")?;
    let x = parse_expr(x)?;
    if pairs.is_empty() || !pairs.len().is_multiple_of(2) {
        return Err("match needs `range(a, b), lambda i: …` pairs after the scrutinee".into());
    }
    let mut arms = Vec::new();
    for pair in pairs.chunks(2) {
        let (lo, hi) = match parse_expr(pair[0])? {
            Expr::Call(f, args) if f == "range" => match args.as_slice() {
                [Expr::Lit(a), Expr::Lit(b)] if a < b => (*a, *b),
                _ => return Err("match needs `range(a, b)` with integer literals, a < b".into()),
            },
            other => return Err(format!("expected `range(a, b)`, got `{other:?}`")),
        };
        if lo != arms.len() as u128 {
            return Err(format!(
                "match ranges must be contiguous from 0: expected a range starting at {}, got {lo}",
                arms.len()
            ));
        }
        let lam = pair[1]
            .trim()
            .strip_prefix("lambda ")
            .ok_or("expected `lambda i: …` after each range")?;
        let (param, body) = split_once_top(lam, ":").ok_or("`lambda` needs `:`")?;
        let body = parse_expr(body)?;
        for j in lo..hi {
            arms.push(subst_var(&body, param.trim(), &Expr::Lit(j)));
        }
    }
    Ok(StmtKind::Match { targets, x, arms })
}
