//! Evaluating a constant at parse time, and the one substitution that still
//! happens on text.
//!
//! Five syntactic positions demand a literal before lowering ever runs: a buffer
//! size, a `mul_range` bound, a range-check bound, a `match` range, and a
//! `case`. That is why a global constant is substituted rather than bound, and
//! it is the whole reason this module exists.
//!
//! A constant is read as a compile-time INTEGER, which is deliberate and
//! load-bearing: it is what makes a derived size come out right. So the same
//! text means different things here and in a value position, where it would fold
//! in the field with `+` as XOR. Neither reading is wrong, and `const(...)` is
//! how an author says which was meant (`zkDSL.md`, "`const(...)` in a value
//! position"). It is transparent here, a constant having only this reading.

use super::*;

/// Evaluate a compile-time **integer** constant expression: decimal literals
/// combined with `+ - * / // % **` and parentheses. This is ordinary integer
/// arithmetic (a global constant is a count, a size, an exponent), deliberately
/// distinct from runtime field arithmetic, so a derived size like `2 + (W - 1) *
/// V + LOG_LIFETIME` comes out right; a single `/` divides like `//` here.
/// References to earlier constants are already substituted to their decimal
/// values, so the input is pure arithmetic. Overflow, division by zero, and a
/// negative intermediate are errors.
pub(super) fn eval_const_int(s: &str) -> Result<u128, String> {
    parse_expr(s)
        .ok()
        .and_then(|e| const_int_expr(&e))
        .ok_or_else(|| format!("not a compile-time integer constant expression: `{}`", s.trim()))
}

/// Fold a compile-time INTEGER expression (literals combined with the usual
/// operators) to its value; `None` if any leaf is not a literal. Placeholders
/// are substituted before parsing, so `GEN ** (K_SKIP + 1)`-style exponents
/// fold here.
pub(super) fn const_int_expr(e: &Expr) -> Option<u128> {
    match e {
        Expr::Lit(k) => Some(*k),
        // `const(e)` asks for the integer reading, which is the only reading a
        // parse-time position has, so it is transparent rather than redundant. It
        // used to be a parse error in a `StackBuf` size and a `log` bound while
        // being accepted in a `HeapBuf` size, an `unroll` count and a `GEN **`
        // exponent, which is one construct with two meanings depending on where it
        // stood.
        Expr::Call(f, args) if f == "const" && args.len() == 1 => const_int_expr(&args[0]),
        Expr::Add(a, b) => const_int_expr(a)?.checked_add(const_int_expr(b)?),
        Expr::Sub(a, b) => const_int_expr(a)?.checked_sub(const_int_expr(b)?),
        Expr::Mul(a, b) => const_int_expr(a)?.checked_mul(const_int_expr(b)?),
        // A single `/` between compile-time integers is integer division: in a
        // constant (a count, a size), there is no field to divide in.
        Expr::Div(a, b) | Expr::FieldDiv(a, b) => match const_int_expr(b)? {
            0 => None,
            d => Some(const_int_expr(a)? / d),
        },
        Expr::Mod(a, b) => match const_int_expr(b)? {
            0 => None,
            d => Some(const_int_expr(a)? % d),
        },
        Expr::Pow(a, b) => const_int_expr(a)?.checked_pow(u32::try_from(const_int_expr(b)?).ok()?),
        _ => None,
    }
}

/// Evaluate a compile-time constant expression (integer literals, `GEN`,
/// `GEN ** k`, and `+`/`*` combinations of those) to its field element.
/// Used for the `# public_input: <elt>, <elt>` annotation of `.py` test
/// programs (see `tests/py_source.rs`).
pub fn parse_const(s: &str) -> Result<F192, String> {
    fn eval(e: &Expr) -> Result<F192, String> {
        match e {
            // An integer literal is the raw 128-bit bit pattern of a machine word.
            Expr::Lit(n) => Ok(F192::new(*n as u64, (*n >> 64) as u64, 0)),
            Expr::Gen => Ok(g_pow(1).into()),
            Expr::GPow(k) => Ok(g_pow_u128(*k).into()),
            Expr::Add(a, b) => Ok(eval(a)? + eval(b)?),
            Expr::Mul(a, b) => Ok(eval(a)? * eval(b)?),
            other => Err(format!("not a constant expression: `{other:?}`")),
        }
    }
    eval(&parse_expr(s)?)
}

pub(super) fn parse_f192_const(s: &str) -> Option<Result<F192, String>> {
    let inner = s.trim().strip_prefix("f192(")?.strip_suffix(')')?;
    let parts = split_top(inner, ',');
    Some((|| {
        if parts.len() != 3 {
            return Err("f192 needs exactly three limbs".into());
        }
        let mut limbs = [0u64; 3];
        for (i, p) in parts.iter().enumerate() {
            limbs[i] =
                u64::try_from(eval_const_int(p.trim())?).map_err(|_| "an f192 limb does not fit in u64".to_string())?;
        }
        Ok(F192::new(limbs[0], limbs[1], limbs[2]))
    })())
}

/// A range bound (`mul_range` bounds and `assert log _ < log _` bounds): a
/// compile-time power of the generator (`1` = `g^0`, `GEN` = `g^1`, or
/// `GEN ** k`), returning the exponent `k`. Both uses walk/compare exponents,
/// so the bound must name `g^k` explicitly (an element that is not a known
/// power of `g` has no usable exponent).
pub(super) fn gpow_bound(e: &Expr) -> Result<u64, String> {
    match e {
        // `g` is `x`, so the literal `2^k` IS `g^k`, and `1` is `g^0`. Rejecting
        // these used to make `mul_range(1, 8)` an error although it runs exactly
        // like `mul_range(1, GEN ** 3)`, and `mul_range(2, GEN ** 5)` an error
        // although `2 == GEN`. It also contradicted `gaddr_of`, which reads the
        // same literal as the same element.
        Expr::Lit(n) if (n.is_power_of_two() && *n < (1 << 64)) || *n == 1 => Ok(n.trailing_zeros() as u64),
        Expr::Gen => Ok(1),
        Expr::GPow(k) => u64::try_from(*k).map_err(|_| format!("bound exponent {k} does not fit in u64")),
        other => Err(format!(
            "a range bound must be a power of GEN (`1`, `GEN`, or `GEN ** k`), got `{other:?}`"
        )),
    }
}

pub(super) fn parse_gpow_bound(s: &str) -> Result<u64, String> {
    gpow_bound(&parse_expr(s)?)
}

/// Apply identifier-level **placeholder** replacements to source text before
/// parsing: each maximal run of alphanumeric characters and underscores that
/// equals a key of `replacements` is replaced by its value; other text,
/// including substrings of longer identifiers, is untouched. An empty map
/// returns the source unchanged.
pub(super) fn apply_replacements(src: &str, replacements: &BTreeMap<String, String>) -> String {
    if replacements.is_empty() {
        return src.to_string();
    }
    let mut out = String::with_capacity(src.len());
    let mut start = 0;
    let flush = |out: &mut String, word: &str| {
        out.push_str(replacements.get(word).map_or(word, String::as_str));
    };
    for (i, c) in src.char_indices() {
        if !(c.is_alphanumeric() || c == '_') {
            flush(&mut out, &src[start..i]);
            out.push(c);
            start = i + c.len_utf8();
        }
    }
    flush(&mut out, &src[start..]);
    out
}
