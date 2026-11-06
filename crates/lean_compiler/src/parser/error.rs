//! Why a zkDSL source does not parse.

/// A refusal of the parser, with the source line it names when one is known.
///
/// The line counts from 1 in the source as written, blank lines and comments included.
/// It is absent for a refusal about the program as a whole (a function defined twice, a malformed placeholder) and for a lone constant expression.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
#[error("{}{kind}", line.map_or_else(String::new, |line| format!("line {line}: ")))]
#[non_exhaustive]
pub struct ParseError {
    /// The 1-based source line the refusal names.
    pub line: Option<usize>,
    /// What is wrong there.
    pub kind: ParseErrorKind,
}

impl ParseError {
    /// Name `line` as the refusal's position, unless an inner frame already named a more specific one.
    pub(super) fn at(mut self, line: usize) -> Self {
        self.line.get_or_insert(line);
        self
    }
}

impl From<ParseErrorKind> for ParseError {
    fn from(kind: ParseErrorKind) -> Self {
        Self { line: None, kind }
    }
}

/// What a source line gets wrong.
///
/// Every quoted text is the line as the parser sees it: trimmed, comments stripped, and placeholders and global constants already substituted.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum ParseErrorKind {
    /// A construct is missing a piece, or has the wrong one.
    #[error("expected {expected}, got `{found}`")]
    Expected {
        /// What the construct needs at this point.
        expected: &'static str,
        /// The text that stands there instead.
        found: String,
    },
    /// A call-shaped construct takes a different number of arguments.
    #[error("`{call}` takes {expected}, got {got} argument(s)")]
    Arity {
        /// The construct called.
        call: &'static str,
        /// The argument list it takes.
        expected: &'static str,
        /// The number of arguments given.
        got: usize,
    },
    /// A placeholder's value would reshape the line it lands on.
    #[error("placeholder `{name}` contains a newline, `#` or `\"`, which would reshape the line")]
    PlaceholderReshapesLine {
        /// The placeholder's name.
        name: String,
    },
    /// A file imports a module other than the editor stub.
    #[error("file imports are not supported (only the `snark_lib` stub): `{statement}`")]
    UnsupportedImport {
        /// The import statement.
        statement: String,
    },
    /// A top-level line is indented.
    #[error("unexpected indentation of {indent} at top level: `{text}`")]
    TopLevelIndent {
        /// The line's indentation, in characters.
        indent: usize,
        /// The line.
        text: String,
    },
    /// A global constant's name is not a plain identifier.
    #[error("global constant name must be a plain identifier: `{name}`")]
    InvalidConstantName {
        /// The name as written.
        name: String,
    },
    /// A global constant is declared a second time.
    #[error("global constant `{name}` is declared twice")]
    DuplicateConstant {
        /// The constant's name.
        name: String,
    },
    /// A global constant takes a builtin's name, so its substitution would rewrite the builtin's call sites.
    #[error(
        "`{name}` is a builtin, so a global constant of that name would be substituted into its own call sites. Rename it"
    )]
    ConstantShadowsBuiltin {
        /// The builtin's name.
        name: String,
    },
    /// A global constant's value does not parse.
    #[error("global constant `{name}`: {kind}")]
    InConstant {
        /// The constant's name.
        name: String,
        /// Why its value does not parse.
        kind: Box<ParseErrorKind>,
    },
    /// A global constant's integer arithmetic does not fold.
    #[error("global constant `{name}`: `{value}` overflows a u128, goes negative or divides by zero")]
    ConstantOverflow {
        /// The constant's name.
        name: String,
        /// Its value as written.
        value: String,
    },
    /// A function is defined a second time.
    #[error("function `{name}` is defined twice")]
    DuplicateFunction {
        /// The function's name.
        name: String,
    },
    /// A function's name contains `__`, which compiler-generated names use.
    #[error(
        "function name `{name}` may not contain `__`, which is reserved for the names the compiler generates (a loop helper, a `Const` specialization)"
    )]
    ReservedFunctionName {
        /// The function's name.
        name: String,
    },
    /// A function takes a builtin's name, so no call could reach it.
    #[error(
        "`{name}` is a builtin, so a function of that name could never be called: the builtin takes every call site. Rename it"
    )]
    FunctionShadowsBuiltin {
        /// The builtin's name.
        name: String,
    },
    /// A decorator other than `@inline`.
    #[error("unknown decorator `@{decorator}` (only `@inline`)")]
    UnknownDecorator {
        /// The decorator's name.
        decorator: String,
    },
    /// An `@inline` ends the file.
    #[error("`@inline` must precede a `def`")]
    DanglingDecorator,
    /// A function header has an empty parameter.
    #[error("`def {function}`: empty parameter (a trailing comma?)")]
    EmptyParameter {
        /// The function's name.
        function: String,
    },
    /// A parameter annotation is neither `Const` nor `StackBuf(n)`.
    #[error("unsupported parameter annotation `{annotation}` (`Const`, or `StackBuf(n)` to pass a run of cells)")]
    UnsupportedAnnotation {
        /// The annotation as written.
        annotation: String,
    },
    /// A `StackBuf` parameter's size is not a compile-time integer.
    #[error("`def {function}`: StackBuf parameter size `{size}` is not a compile-time integer constant expression")]
    StackBufParamNotConst {
        /// The function's name.
        function: String,
        /// The size as written.
        size: String,
    },
    /// A `StackBuf` parameter's size exceeds a cell count.
    #[error("`def {function}`: StackBuf({size}) is too large, the limit being {max} cells")]
    StackBufParamTooLarge {
        /// The function's name.
        function: String,
        /// The size given.
        size: u128,
        /// The largest size a cell count holds.
        max: u32,
    },
    /// A `StackBuf` parameter has no cell.
    #[error("`def {function}`: a StackBuf parameter needs at least one cell")]
    EmptyStackBufParam {
        /// The function's name.
        function: String,
    },
    /// A parameter is declared a second time.
    #[error("`def {function}`: parameter `{name}` is declared twice")]
    DuplicateParameter {
        /// The function's name.
        function: String,
        /// The parameter's name.
        name: String,
    },
    /// A `Const` parameter is rebound inside an `if` or an `unroll`.
    #[error(
        "`def {function}`: `{param}` is a Const parameter, substituted as a literal into the body, so it cannot be rebound inside an `if` or an `unroll`; bind a new name"
    )]
    ConstParamRebound {
        /// The function's name.
        function: String,
        /// The parameter's name.
        param: String,
    },
    /// A name in a binding position is not a plain identifier.
    #[error(
        "`{name}` is not a valid {role}: a name must be a plain identifier. A top-level constant's name is reserved, and is substituted before parsing, so a parameter or local may not reuse one."
    )]
    InvalidName {
        /// The name as written.
        name: String,
        /// The position it stands in: a parameter, a binding, a loop counter.
        role: &'static str,
    },
    /// A block header is not followed by a more indented line.
    #[error("expected an indented block, deeper than indentation {parent}")]
    ExpectedBlock {
        /// The indentation of the header that opens the block.
        parent: usize,
    },
    /// A line inside a block is indented deeper than the block, with no header to open a new one.
    #[error("inconsistent indentation: the block is at {expected}, this line at {got}")]
    InconsistentIndent {
        /// The block's indentation.
        expected: usize,
        /// The line's indentation.
        got: usize,
    },
    /// An `unroll` counter is rebound inside an `if` or an `unroll`.
    #[error(
        "the `unroll` counter `{var}` is substituted as a literal into each copy of the body, so it cannot be rebound inside an `if` or an `unroll`; bind a new name"
    )]
    UnrollCounterRebound {
        /// The counter's name.
        var: String,
    },
    /// A `mul_range` starts past its stop.
    #[error("mul_range: start GEN**{start} must not exceed stop GEN**{stop}")]
    MulRangeBackwards {
        /// The start's exponent.
        start: u64,
        /// The stop's exponent.
        stop: u64,
    },
    /// A `mul_range` stop is a literal that is not a power of `GEN`, which the multiplicative walk never reaches.
    #[error(
        "mul_range stop bound `{stop}` is not a power of GEN, so the multiplicative walk never reaches it: write `GEN ** k`"
    )]
    UnreachableStop {
        /// The stop bound.
        stop: u128,
    },
    /// A range-check bound does not fit a `u64`.
    #[error("log bound {bound} does not fit in u64")]
    LogBoundTooLarge {
        /// The bound given.
        bound: u128,
    },
    /// The unsupported `**=`.
    #[error("`**=` is not supported; write `x = x ** k`")]
    PowAssign,
    /// The unsupported `/=`.
    #[error(
        "`/=` is not supported; `/` is runtime field division, so write `x = x / y` (or `//=` for the compile-time floor division)"
    )]
    FieldDivAssign,
    /// An equality written as a statement, which would check nothing.
    #[error("`{statement}` is a comparison, not a statement: write `assert {statement}`")]
    BareEquality {
        /// The statement.
        statement: String,
    },
    /// An order comparison written as a statement.
    #[error(
        "`{statement}` is a comparison, not a statement: `{op}` is not a predicate: order facts come from `assert log x < k`"
    )]
    BareOrder {
        /// The statement.
        statement: String,
        /// The comparison operator.
        op: &'static str,
    },
    /// A statement that is neither a binding, a store nor a call.
    #[error("statement has no effect: `{statement}`")]
    NoEffect {
        /// The statement.
        statement: String,
    },
    /// A `const(...)` that does not wrap the whole `if` condition.
    #[error(
        "`const(...)` must wrap the WHOLE condition and balance its brackets: `if const(a == b):`, got `{condition}`"
    )]
    PartialConstCondition {
        /// The condition.
        condition: String,
    },
    /// A parenthesised `log(...)` followed by more of the operand.
    #[error("`{operand}`: put the whole operand inside `log(…)`")]
    PartialLogOperand {
        /// The operand.
        operand: String,
    },
    /// The `match` ranges leave a gap or do not start at 0.
    #[error("match ranges must be contiguous from 0: expected a range starting at {expected}, got {got}")]
    MatchGap {
        /// Where the next range must start.
        expected: usize,
        /// Where it starts.
        got: u128,
    },
    /// An empty list literal.
    #[error("a list literal needs at least one element")]
    EmptyList,
    /// A `]` with no `[` before it.
    #[error("unbalanced `]` in `{text}`")]
    UnbalancedBracket {
        /// The expression.
        text: String,
    },
    /// A keyword argument whose key is not a plain identifier.
    #[error("invalid keyword argument `{key}`")]
    InvalidKeyword {
        /// The key as written.
        key: String,
    },
    /// A buffer's size exceeds a cell count.
    #[error("{buffer} size {size} does not fit in u32")]
    BufferTooLarge {
        /// The allocation: `HeapBuf` or `StackBuf`.
        buffer: String,
        /// The size given.
        size: u128,
    },
    /// An empty expression.
    #[error("expected an expression")]
    EmptyExpression,
    /// Text that is no expression.
    #[error("cannot parse expression `{text}`")]
    InvalidExpression {
        /// The text.
        text: String,
    },
    /// An operator with an empty side.
    #[error("`{op}` has no {side} operand")]
    MissingOperand {
        /// The operator.
        op: &'static str,
        /// The empty side: `left` or `right`.
        side: &'static str,
    },
    /// A leading `-`, which the language does not have.
    #[error("`-` has no left operand: there is no unary minus, and field subtraction is `+`")]
    UnaryMinus,
    /// A parse-time integer position holds something that does not fold.
    #[error("not a compile-time integer constant expression: `{text}`")]
    NotConstInt {
        /// The text.
        text: String,
    },
    /// A constant expression holds something other than literals, `GEN`, `+` and `*`.
    #[error("not a constant expression: `{found}`")]
    NotConstant {
        /// The offending subexpression, as the parser read it.
        found: String,
    },
    /// An `f192` limb does not fit a `u64`.
    #[error("the f192 limb {limb} does not fit in u64")]
    LimbTooLarge {
        /// The limb given.
        limb: u128,
    },
    /// A range-bound exponent does not fit a `u64`.
    #[error("bound exponent {exponent} does not fit in u64")]
    BoundExponentTooLarge {
        /// The exponent given.
        exponent: u128,
    },
    /// A range bound is not a compile-time power of `GEN`.
    #[error("a range bound must be a power of GEN (`1`, `GEN`, or `GEN ** k`), got `{found}`")]
    NotGenPower {
        /// The bound, as the parser read it.
        found: String,
    },
}
