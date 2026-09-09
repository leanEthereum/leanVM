//! Reading structure out of a line: where a line ends, where an operator sits,
//! and what an expression means.
//!
//! One rule governs all of it. **A string literal is one opaque token**, and
//! everything here that scans a line goes through [`depth0`], which skips both
//! bracketed and quoted text. Before it did, a `,` or a `]` spelled inside a
//! hint name moved an argument boundary, and [`strip_comment`]'s `#` truncated
//! the line from inside a string, in both cases producing a DIFFERENT program
//! that still parsed.
//!
//! Precedence is the usual one and is correct as it stands: `+` and `-` split
//! first, so they bind loosest; then `*`, `/`, `//` and `%`; then `**`, which
//! splits at its FIRST occurrence and recurses right, so it is
//! right-associative as in Python. There is no unary minus, since field
//! subtraction is `+`.

use super::*;

/// Parse an expression with `+` (lowest) then `*`, atoms being integer literals,
/// variables, calls `f(args)`, and parenthesised sub-expressions.
pub(super) fn parse_expr(s: &str) -> Result<Expr, String> {
    let s = s.trim();
    // `+` / `-` at top level (lowest precedence), left-associative. `-` is
    // compile-time integer subtraction (field subtraction is `+` = XOR).
    let (segs, ops) = split_add(s);
    if !ops.is_empty() {
        return fold_ops(&segs, &ops, |op, l, r| match op {
            b'+' => Expr::Add(l, r),
            _ => Expr::Sub(l, r),
        });
    }
    // `*`, `/`, `//`, `%` (bind tighter than `+`), skipping the two-char `**`.
    let (segs, ops) = split_mul(s);
    if !ops.is_empty() {
        return fold_ops(&segs, &ops, |op, l, r| match op {
            b'*' => Expr::Mul(l, r),
            b'/' => Expr::Div(l, r),
            b'd' => Expr::FieldDiv(l, r),
            _ => Expr::Mod(l, r),
        });
    }
    // `**` (compile-time power), tightest binding: `base ** k` with `k` an
    // integer literal (possibly large), or a parenthesised compile-time
    // integer expression like `GEN ** (2 * s + 1)`, evaluated at lowering,
    // so it can reference `unroll` counters and constants.
    if let Some((base, exp)) = split_once_top(s, "**") {
        let base = parse_expr(&base)?;
        let exp_e = parse_expr(&exp)?;
        return match base {
            // `GEN ** k`: a compile-time integer exponent (a literal or a
            // constant expression like `K_SKIP + 1`) folds to `g^k`; a runtime
            // expression (e.g. an `unroll` var) becomes `GenPow`, resolved at
            // lowering.
            Expr::Gen => match const_int_expr(&exp_e) {
                Some(k) => Ok(Expr::GPow(k)),
                None => Ok(Expr::GenPow(Box::new(exp_e))),
            },
            // Any other base with a compile-time exponent: square-and-multiply.
            _ => Ok(Expr::Pow(Box::new(base), Box::new(exp_e))),
        };
    }
    // Atom.
    if s.starts_with('(') && s.ends_with(')') {
        return parse_expr(&s[1..s.len() - 1]);
    }
    if s == "GEN" {
        return Ok(Expr::Gen);
    }
    if let Ok(n) = s.parse::<u128>() {
        return Ok(Expr::Lit(n));
    }
    // List literal `[a, b, …]`: an initialized StackBuf (only meaningful as
    // the RHS of an assignment; top-level constant arrays are parsed earlier).
    if s.starts_with('[') && s.ends_with(']') {
        let inner = s[1..s.len() - 1].trim();
        if inner.is_empty() {
            return Err("a list literal needs at least one element".into());
        }
        return Ok(Expr::ListLit(
            split_top(inner, ',')
                .iter()
                .map(|e| parse_expr(e))
                .collect::<Result<_, _>>()?,
        ));
    }
    // Index `base[idx]` or slice `base[lo:hi]` (binds tightest, like a call).
    if s.ends_with(']') {
        let open = s.find('[').ok_or_else(|| format!("unbalanced `]` in `{s}`"))?;
        let base = parse_expr(&s[..open])?;
        let inner = &s[open + 1..s.len() - 1];
        if let Some((lo, hi)) = split_once_top(inner, ":") {
            return Ok(Expr::Slice(
                Box::new(base),
                Box::new(parse_expr(&lo)?),
                Box::new(parse_expr(&hi)?),
            ));
        }
        let idx = parse_expr(inner)?;
        return Ok(Expr::Index(Box::new(base), Box::new(idx)));
    }
    if let Some(open) = s.find('(')
        && s.ends_with(')')
    {
        let name = s[..open].trim().to_string();
        let args_str = s[open + 1..s.len() - 1].trim();
        let mut args = if args_str.is_empty() {
            vec![]
        } else {
            split_top(args_str, ',')
                .iter()
                .map(|a| {
                    if let Some((key, value)) = split_once_top(a, "=") {
                        let key = key.trim();
                        if key.is_empty() || !key.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') {
                            return Err(format!("invalid keyword argument `{key}`"));
                        }
                        Ok(Expr::Call(format!("__kw_{key}"), vec![parse_expr(&value)?]))
                    } else {
                        parse_expr(a)
                    }
                })
                .collect::<Result<_, _>>()?
        };
        // `HeapBuf(n)` / `StackBuf(n)` are allocations, not ordinary calls. A size
        // that folds as parse-time integer arithmetic (`MAXQ + 1`, constants
        // already substituted) is a static size like a bare literal.
        // A cell count is a frame/heap size: reject one that does not fit rather
        // than wrapping it into a plausible small buffer.
        let cells = |n: u128| u64::try_from(n).map_err(|_| format!("{name} size {n} does not fit in u64"));
        if name == "HeapBuf" || name == "StackBuf" {
            let size = match args.as_slice() {
                [arg] => const_int_expr(arg),
                _ => None,
            };
            return match (name.as_str(), size) {
                ("HeapBuf", Some(n)) => Ok(Expr::HeapBuf(cells(n)?)),
                ("StackBuf", Some(n)) => Ok(Expr::StackBuf(cells(n)?)),
                ("HeapBuf", None) if args.len() == 1 => Ok(Expr::HeapBufDyn(Box::new(args.pop().unwrap()))),
                ("HeapBuf", None) => Err("HeapBuf(size) takes one argument".into()),
                _ => Err("StackBuf(n) needs a parse-time integer size".into()),
            };
        }
        return Ok(Expr::Call(name, args));
    }
    if s.chars().all(|c| c.is_alphanumeric() || c == '_') && !s.is_empty() {
        return Ok(Expr::Var(s.to_string()));
    }
    if s.is_empty() {
        return Err("expected an expression".into());
    }
    Err(format!("cannot parse expression `{s}`"))
}

/// Combine one tier's operands left-associatively: `node` builds the AST node
/// for each operator (as [`split_add`] / [`split_mul`] tag it).
fn fold_ops(segs: &[&str], ops: &[u8], node: impl Fn(u8, Box<Expr>, Box<Expr>) -> Expr) -> Result<Expr, String> {
    // An empty operand is an operator missing a side: a leading `-`, a trailing
    // operator, or two in a row. Naming it beats letting `parse_expr("")` report
    // an empty backtick, which is what every one of these used to say.
    if let Some(i) = segs.iter().position(|seg| seg.trim().is_empty()) {
        let (op, side) = if i == 0 {
            (ops[0], "left")
        } else {
            (ops[i - 1], "right")
        };
        // `split_mul` encodes the two divisions, so spell them back out.
        let shown = match op {
            b'/' => "//".to_string(),
            b'd' => "/".to_string(),
            c => (c as char).to_string(),
        };
        let hint = if op == b'-' && i == 0 {
            ": there is no unary minus, and field subtraction is `+`"
        } else {
            ""
        };
        return Err(format!("`{shown}` has no {side} operand{hint}"));
    }
    let mut acc = parse_expr(segs[0])?;
    for (&op, seg) in ops.iter().zip(&segs[1..]) {
        let rhs = Box::new(parse_expr(seg)?);
        acc = node(op, Box::new(acc), rhs);
    }
    Ok(acc)
}

/// The bytes of `s` that sit outside every `(…)` / `[…]` group, with their
/// index: the one scanner behind all the top-level splits below. Brackets
/// themselves are never yielded, so a separator that is a bracket never splits.
pub(super) fn depth0(s: &str) -> impl Iterator<Item = (usize, u8)> + '_ {
    let mut depth = 0i32;
    let mut in_str = false;
    s.as_bytes().iter().enumerate().filter_map(move |(i, &c)| {
        // A string literal is one opaque token. Without this every splitter
        // below reads the brackets and operators SPELLED INSIDE a stream name as
        // structure: `hint_witness(b, "a,b")` split into three arguments.
        if in_str {
            in_str = c != b'"';
            return None;
        }
        match c {
            b'"' => {
                in_str = true;
                None
            }
            b'(' | b'[' => {
                depth += 1;
                None
            }
            b')' | b']' => {
                depth -= 1;
                None
            }
            _ => (depth == 0).then_some((i, c)),
        }
    })
}

/// Split `s` at the top-level additive tier: operands and the `+` / `-`
/// operators between them. Left-associative; parenthesised/bracketed sub-terms
/// are left intact.
fn split_add(s: &str) -> (Vec<&str>, Vec<u8>) {
    let (mut segs, mut ops) = (Vec::new(), Vec::new());
    let mut start = 0usize;
    for (i, c) in depth0(s) {
        if c == b'+' || c == b'-' {
            segs.push(&s[start..i]);
            ops.push(c);
            start = i + 1;
        }
    }
    segs.push(&s[start..]);
    (segs, ops)
}

/// Split `s` at the top-level multiplicative tier: the operands and the
/// operators between them (`*`, `//` for floor-division, `/` for runtime field
/// division, `%` for remainder). A `**` power is left intact (bound tighter).
/// Left-associative.
fn split_mul(s: &str) -> (Vec<&str>, Vec<u8>) {
    let b = s.as_bytes();
    let (mut segs, mut ops) = (Vec::new(), Vec::new());
    let (mut start, mut next) = (0usize, 0usize);
    for (i, c) in depth0(s) {
        if i < next {
            continue; // the second `/` of a `//`, already consumed
        }
        let (op, len) = match c {
            b'*' if b.get(i + 1) == Some(&b'*') || (i > 0 && b[i - 1] == b'*') => continue, // `**`
            b'*' => (b'*', 1),
            b'/' if b.get(i + 1) == Some(&b'/') => (b'/', 2), // `//` compile-time floor-division
            b'/' => (b'd', 1),                                // `/` runtime field division
            b'%' => (b'%', 1),
            _ => continue,
        };
        segs.push(&s[start..i]);
        ops.push(op);
        next = i + len;
        start = next;
    }
    segs.push(&s[start..]);
    (segs, ops)
}

/// Split `s` once on a top-level multi-char operator `op`.
pub(super) fn split_once_top(s: &str, op: &str) -> Option<(String, String)> {
    let b = s.as_bytes();
    for (i, _) in depth0(s) {
        if b[i..].starts_with(op.as_bytes()) {
            return Some((s[..i].to_string(), s[i + op.len()..].to_string()));
        }
    }
    None
}

/// Split `s` on every top-level occurrence of the ASCII char `sep`.
pub(super) fn split_top(s: &str, sep: char) -> Vec<String> {
    let sep = sep as u8;
    let mut parts = Vec::new();
    let mut start = 0;
    for (i, c) in depth0(s) {
        if c == sep {
            parts.push(s[start..i].to_string());
            start = i + 1;
        }
    }
    parts.push(s[start..].to_string());
    parts
}

/// Split on a top-level BARE `=`: not part of `==`, not the tail of a
/// comparison (`!=`, `<=`, `>=`), and not the tail of a compound assignment
/// ([`split_aug`] owns those, and rejects the ones this language lacks).
/// Without the last two exclusions a bare `x != y` split into a binding named
/// `x !`, which in a verifier is an `assert` that compiled to nothing.
pub(super) fn split_assign(s: &str) -> Option<(String, String)> {
    let b = s.as_bytes();
    for (i, c) in depth0(s) {
        if c != b'=' || b.get(i + 1) == Some(&b'=') {
            continue;
        }
        if i > 0 && matches!(b[i - 1], b'=' | b'<' | b'>' | b'!' | b'+' | b'-' | b'*' | b'/' | b'%') {
            continue;
        }
        return Some((s[..i].to_string(), s[i + 1..].to_string()));
    }
    None
}

/// A top-level augmented assignment `lhs OP= rhs` -> `(lhs, "OP", rhs)`, for
/// OP in `+ - * // %`. `Ok(None)` for a plain `=` or a comparison (`==`, `!=`,
/// `<=`, `>=`); an `Err` for a compound spelling this language does not have.
/// The operator's `=` must sit at depth 0 and be immediately preceded by
/// exactly the operator characters.
///
/// The unsupported spellings must be REJECTED rather than declined: falling
/// through left [`split_assign`] to split the bare `=`, so `x /= 2` became a
/// binding named `x /` and the program silently kept the old `x`.
pub(super) fn split_aug(s: &str) -> Result<Aug, String> {
    let b = s.as_bytes();
    for (i, c) in depth0(s) {
        if c != b'=' {
            continue;
        }
        // Nothing to the left is no assignment at all; `split_assign` and the
        // binding-name check below give that its error.
        if i == 0 {
            return Ok(None);
        }
        // not `==` and not a comparison tail (`<=`, `>=`, `!=`)
        if b.get(i + 1) == Some(&b'=') || matches!(b[i - 1], b'=' | b'<' | b'>' | b'!') {
            return Ok(None);
        }
        let prev2 = b.get(i.wrapping_sub(2)).copied();
        let (op, plen): (&str, usize) = match b[i - 1] {
            b'+' => ("+", 1),
            b'-' => ("-", 1),
            b'%' => ("%", 1),
            b'*' if prev2 == Some(b'*') => {
                return Err("`**=` is not supported; write `x = x ** k`".into());
            }
            b'*' => ("*", 1),
            b'/' if prev2 == Some(b'/') => ("//", 2),
            b'/' => {
                return Err(
                    "`/=` is not supported; `/` is runtime field division, so write `x = x / y` (or `//=` for the \
                     compile-time floor division)"
                        .into(),
                );
            }
            _ => return Ok(None),
        };
        return Ok(Some((
            s[..i - plen].trim().to_string(),
            op,
            s[i + 1..].trim().to_string(),
        )));
    }
    Ok(None)
}

/// The top-level arguments of a `name(a, b, …)` call, or `None` when `line` is
/// not one. Zero arguments come back as one empty string, as [`split_top`]
/// gives them.
pub(super) fn call_args(line: &str, name: &str) -> Option<Vec<String>> {
    let inner = line.trim().strip_prefix(name)?.strip_prefix('(')?.strip_suffix(')')?;
    Some(split_top(inner, ','))
}

/// The contents of a `"…"` string literal.
pub(super) fn string_lit(s: &str) -> Option<&str> {
    s.trim().strip_prefix('"')?.strip_suffix('"')
}

/// `raw` without its trailing comment. A `#` inside a string literal is part of
/// the string: truncating there dropped the rest of the line, and the shortened
/// line usually still parsed.
pub(super) fn strip_comment(raw: &str) -> &str {
    let mut in_str = false;
    for (i, c) in raw.char_indices() {
        match c {
            '"' => in_str = !in_str,
            '#' if !in_str => return &raw[..i],
            _ => {}
        }
    }
    raw
}

/// The first top-level comparison operator in `s`. Used only on a line that
/// reached the bare-call fallback, so an `assert` or an assignment never gets
/// here and a comparison nested in a call sits at depth > 0.
pub(super) fn top_level_cmp(s: &str) -> Option<&'static str> {
    let b = s.as_bytes();
    for (i, c) in depth0(s) {
        let eq = b.get(i + 1) == Some(&b'=');
        match c {
            b'=' if eq => return Some("=="),
            b'!' if eq => return Some("!="),
            b'<' => return Some(if eq { "<=" } else { "<" }),
            b'>' => return Some(if eq { ">=" } else { ">" }),
            _ => {}
        }
    }
    None
}

/// A plain identifier: non-empty, starts with a letter or `_`, all
/// `[A-Za-z0-9_]` (no operators, brackets, or commas).
pub(super) fn is_ident(s: &str) -> bool {
    let mut cs = s.chars();
    matches!(cs.next(), Some(c) if c.is_alphabetic() || c == '_') && s.chars().all(|c| c.is_alphanumeric() || c == '_')
}

/// A binding or parameter name, validated. Anything else here is a mis-split
/// (`x /`, `x !`) or a top-level constant substituted into a binding position:
/// constants are replaced textually, so `V = 8` with `def scale(V)` arrives as a
/// parameter literally named `8` while the body's `V` reads the constant.
/// `zkDSL.md` §Global constants reserves the name; this enforces it.
pub(super) fn binding_name(raw: &str, what: &str) -> Result<String, String> {
    let n = raw.trim();
    if is_ident(n) {
        return Ok(n.to_string());
    }
    Err(format!(
        "`{n}` is not a valid {what}: a name must be a plain identifier. A top-level constant's name is \
         reserved, and is substituted before parsing, so a parameter or local may not reuse one."
    ))
}

/// The inside of a `const(...)` wrapping the WHOLE of `s`, or `None`.
///
/// `const(a) == b` is not one: its first `)` closes before the end, so the
/// wrapper is a subterm and the condition as a whole is an ordinary one.
pub(super) fn strip_const_wrapper(s: &str) -> Option<&str> {
    let inner = s.trim().strip_prefix("const(")?.strip_suffix(')')?;
    let mut depth = 0i32;
    for c in inner.bytes() {
        match c {
            b'(' | b'[' => depth += 1,
            b')' | b']' => {
                depth -= 1;
                if depth < 0 {
                    return None;
                }
            }
            _ => {}
        }
    }
    Some(inner)
}
