//! The aggregation guest's source AST, after `placeholder_map`, as the Lean data
//! `formal/lean_vm/LeanVM/Guest/Data/Source.lean` (`LeanVM.Guest.Source`'s types), which the Lean
//! expansion lowers to the core IR; and the compiler's test programs
//! (`crates/lean_compiler/tests/programs`) with their public inputs and witness streams, as
//! `formal/lean_vm/tests/LeanVMTests/Guest/Programs.lean`, which the Lean tests expand and run.
//! The test regenerates both files and fails if either differs from the committed one;
//! `LEANVM_WRITE_GUEST=1` rewrites them.

use super::*;
use lean_compiler::{Ast, Expr, ForBound, Func, LtBound, ParamKind, Shape, Stmt, StmtKind, parse, parse_const};
use std::fmt::Write as _;

const PATH: &str = "../../formal/lean_vm/LeanVM/Guest/Data/Source.lean";
const PROGRAMS_PATH: &str = "../../formal/lean_vm/tests/LeanVMTests/Guest/Programs.lean";

fn string(s: &str) -> String {
    format!("{s:?}")
}

fn list(items: impl IntoIterator<Item = String>) -> String {
    format!("[{}]", items.into_iter().collect::<Vec<_>>().join(", "))
}

fn expr(e: &Expr) -> String {
    let bin = |c: &str, a: &Expr, b: &Expr| format!("(.{c} {} {})", expr(a), expr(b));
    match e {
        Expr::Lit(n) => format!("(.lit {n})"),
        Expr::Gen => ".gen".into(),
        Expr::GPow(k) => format!("(.gpow {k})"),
        Expr::GenPow(x) => format!("(.genPow {})", expr(x)),
        Expr::Pow(a, b) => bin("pow", a, b),
        Expr::Var(v) => format!("(.var {})", string(v)),
        Expr::Add(a, b) => bin("add", a, b),
        Expr::Mul(a, b) => bin("mul", a, b),
        Expr::Sub(a, b) => bin("sub", a, b),
        Expr::Div(a, b) => bin("div", a, b),
        Expr::Mod(a, b) => bin("mod", a, b),
        Expr::FieldDiv(a, b) => bin("fdiv", a, b),
        Expr::Call(f, args) => format!("(.call {} {})", string(f), list(args.iter().map(expr))),
        Expr::HeapBuf(n) => format!("(.heapBuf {n})"),
        Expr::HeapBufDyn(x) => format!("(.heapBufDyn {})", expr(x)),
        Expr::StackBuf(n) => format!("(.stackBuf {n})"),
        Expr::Index(a, i) => bin("index", a, i),
        Expr::Slice(a, lo, hi) => format!("(.slice {} {} {})", expr(a), expr(lo), expr(hi)),
        Expr::ListLit(es) => format!("(.list {})", list(es.iter().map(expr))),
    }
}

fn exprs(es: &[Expr]) -> String {
    list(es.iter().map(expr))
}

fn block(body: &[Stmt], indent: usize) -> String {
    if body.is_empty() {
        return "[]".into();
    }
    let pad = " ".repeat(indent);
    let items: Vec<String> = body.iter().map(|s| format!("{pad}{}", stmt(s, indent))).collect();
    format!("[\n{}]", items.join(",\n"))
}

fn stmt(s: &Stmt, indent: usize) -> String {
    let inner = indent + 2;
    let kind = match &s.kind {
        StmtKind::Let(x, e) => format!(".let_ {} {}", string(x), expr(e)),
        StmtKind::LetTuple(xs, f, args) => format!(
            ".letTuple {} {} {}",
            list(xs.iter().map(|x| string(x))),
            string(f),
            exprs(args)
        ),
        StmtKind::AssertEq(a, b) => format!(".assertEq {} {}", expr(a), expr(b)),
        StmtKind::AssertNe(a, b) => format!(".assertNe {} {}", expr(a), expr(b)),
        StmtKind::AssertLt(e, bound) => format!(
            ".assertLt {} {}",
            expr(e),
            match bound {
                LtBound::Const(k) => format!("(.const {k})"),
                LtBound::Runtime(b) => format!("(.runtime {})", expr(b)),
            }
        ),
        StmtKind::Call(f, args) => format!(".call {} {}", string(f), exprs(args)),
        StmtKind::HintWitness { dest, name } => format!(".hintWitness {} {}", expr(dest), string(name)),
        StmtKind::LetHintWitness { name, stream } => format!(".letHintWitness {} {}", string(name), string(stream)),
        StmtKind::Print { label, value } => format!(".print {} {}", string(label), expr(value)),
        StmtKind::If {
            eq,
            lhs,
            rhs,
            then,
            els,
            force_const,
        } => format!(
            ".ite {eq} {} {} {} {} {force_const}",
            expr(lhs),
            expr(rhs),
            block(then, inner),
            block(els, inner)
        ),
        StmtKind::Match { targets, x, arms } => format!(".match_ {} {} {}", exprs(targets), expr(x), exprs(arms)),
        StmtKind::Store(a, i, v) => format!(".store {} {} {}", expr(a), expr(i), expr(v)),
        StmtKind::For { var, lo, hi, body } => format!(
            ".for_ {} {lo} {} {}",
            string(var),
            match hi {
                ForBound::Const(k) => format!("(.const {k})"),
                ForBound::Runtime(b) => format!("(.runtime {})", expr(b)),
            },
            block(body, inner)
        ),
        StmtKind::Unroll { var, lo, hi, body } => {
            format!(
                ".unroll {} {} {} {}",
                string(var),
                expr(lo),
                expr(hi),
                block(body, inner)
            )
        }
        StmtKind::Return(es) => format!(".ret {}", exprs(es)),
        StmtKind::CallIfNe(a, b, f, args) => {
            format!(".callIfNe {} {} {} {}", expr(a), expr(b), string(f), exprs(args))
        }
    };
    format!(".mk {} ({kind})", s.line)
}

fn shape(s: &Shape) -> String {
    match s {
        Shape::Scalar => ".scalar".into(),
        Shape::StackBuf(n) => format!("(.stackBuf {n})"),
    }
}

fn func(f: &Func) -> String {
    func_at(f, 2)
}

fn func_at(f: &Func, indent: usize) -> String {
    let pad = " ".repeat(indent + 2);
    let params = list(f.params.iter().map(|p| {
        let kind = match p.kind {
            ParamKind::Const => ".const".into(),
            ParamKind::Runtime(s) => format!("(.runtime {})", shape(&s)),
        };
        format!("⟨{}, {kind}⟩", string(&p.name))
    }));
    format!(
        "{{ name := {}, params := {params}, returnShapes := {},\n{pad}inline := {},\n{pad}body := {} }}",
        string(&f.name),
        list(f.return_shapes.iter().map(shape)),
        f.inline,
        block(&f.body, indent + 4)
    )
}

fn render(ast: &Ast, kbc: usize) -> String {
    let mut out = String::new();
    writeln!(
        out,
        "/-\n  LeanVM.Guest.Data.Source\n\n  Generated by `guest_source_lean` \
         (crates/rec_aggregation/src/aggregation/guest_source.rs); do not\n  edit. The aggregation \
         guest's source AST after `placeholder_map`.\n-/\n\nmodule\n\npublic import LeanVM.Guest.Source\n\n\
         /-!\n# The aggregation guest's source\n\n`crates/rec_aggregation/guests/lean_ethereum.py` as \
         `lean_compiler::parse_with_replacements` returns it with\nthe deployed placeholders \
         (`placeholder_map`, at the bytecode's log size `bytecodeLog`): one definition\nper \
         function, then the constant arrays and the program.\n-/\n\nnamespace LeanVM.Guest.Data\n\n\
         open LeanVM.Guest.Source\n\n@[expose] public section\n\n/-- The log size of the bytecode \
         the placeholders are computed for. -/\ndef bytecodeLog : Nat := {kbc}\n"
    )
    .unwrap();
    for f in &ast.funcs {
        writeln!(
            out,
            "/-- `{}`. -/\ndef fn_{} : Func :=\n  {}\n",
            f.name,
            f.name,
            func(f)
        )
        .unwrap();
    }
    for (name, values) in &ast.const_arrays {
        let items = list(values.iter().map(|v| format!("({}, {}, {})", v.c0, v.c1, v.c2)));
        writeln!(
            out,
            "/-- The constant array `{name}`. -/\ndef arr_{name} : List (Nat × Nat × Nat) :=\n  {items}\n"
        )
        .unwrap();
    }
    let funcs = list(ast.funcs.iter().map(|f| format!("fn_{}", f.name)));
    let arrays = list(
        ast.const_arrays
            .iter()
            .map(|(name, _)| format!("({}, arr_{name})", string(name))),
    );
    writeln!(
        out,
        "/-- The guest. -/\ndef guest : Program :=\n  ⟨{funcs},\n   {arrays}⟩\n\nend\nend LeanVM.Guest.Data"
    )
    .unwrap();
    out
}

fn word(x: F192) -> String {
    format!("({}, {}, {})", x.c0, x.c1, x.c2)
}

/// The compiler's test programs, each with the public input and the witness streams its
/// annotations declare (`lean_compiler/tests/suite/py_source.rs`).
fn render_programs() -> String {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/../lean_compiler/tests/programs");
    let mut paths: Vec<_> = std::fs::read_dir(dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|x| x == "py"))
        .collect();
    paths.sort();
    let mut out = String::from(
        "/-\n  LeanVMTests.Guest.Programs\n\n  Generated by `guest_source_lean` \
         (crates/rec_aggregation/src/aggregation/guest_source.rs); do not\n  edit. The compiler's \
         test programs, `crates/lean_compiler/tests/programs/*.py`.\n-/\n\nimport LeanVM.Guest.Source\n\n\
         namespace LeanVMTests.Guest.Programs\n\nopen LeanVM.Guest.Source\n\n/-- A test program: its AST, \
         the public input it publishes and its witness streams, each word as its limbs. -/\n\
         structure TestProgram where\n  name : String\n  program : Program\n  publicInput : List (Nat × Nat × Nat)\n  \
         streams : List (String × List (List (Nat × Nat × Nat)))\n\n",
    );
    let mut names = Vec::new();
    for path in paths {
        let file = path.file_stem().unwrap().to_string_lossy().into_owned();
        let src = std::fs::read_to_string(&path).unwrap();
        let ast = parse(&src).unwrap();
        let mut public = vec![F192::ZERO; 2];
        let mut streams: BTreeMap<String, Vec<Vec<F192>>> = BTreeMap::new();
        for line in src.lines().map(str::trim) {
            if let Some(rest) = line.strip_prefix("# public_input:") {
                public = rest.split(',').map(|s| parse_const(s).unwrap()).collect();
            }
            if let Some(rest) = line.strip_prefix("# witness ") {
                let (name, vals) = rest.split_once(':').unwrap();
                let entry = vals.split(',').map(|s| parse_const(s).unwrap()).collect();
                streams.entry(name.trim().to_string()).or_default().push(entry);
            }
        }
        let funcs = list(ast.funcs.iter().map(|f| format!("\n    {}", func_at(f, 4))));
        let arrays = list(ast.const_arrays.iter().map(|(name, values)| {
            format!(
                "({}, {})",
                string(name),
                list(values.iter().map(|v| format!("({}, {}, {})", v.c0, v.c1, v.c2)))
            )
        }));
        let streams = list(streams.iter().map(|(k, es)| {
            format!(
                "({}, {})",
                string(k),
                list(es.iter().map(|e| list(e.iter().map(|&x| word(x)))))
            )
        }));
        writeln!(
            out,
            "/-- `{file}.py`. -/\ndef prog_{file} : TestProgram where\n  name := {}\n  program := ⟨{funcs},\n    {arrays}⟩\n  \
             publicInput := {}\n  streams := {streams}\n",
            string(&file),
            list(public.iter().map(|&x| word(x)))
        )
        .unwrap();
        names.push(format!("prog_{file}"));
    }
    writeln!(
        out,
        "/-- Every test program. -/\ndef all : List TestProgram := {}\n\nend LeanVMTests.Guest.Programs",
        list(names)
    )
    .unwrap();
    out
}

fn check(rel: &str, text: &str) {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(rel);
    if std::env::var_os("LEANVM_WRITE_GUEST").is_some() {
        std::fs::write(&path, text).unwrap();
    }
    let committed = std::fs::read_to_string(&path).unwrap_or_default();
    assert!(
        committed == text,
        "{} is stale; rerun with LEANVM_WRITE_GUEST=1",
        path.display()
    );
}

#[test]
fn guest_source_lean() {
    let kbc = unified_guest().prog.len().trailing_zeros() as usize;
    let ast = parse_with_replacements(include_str!("../../guests/lean_ethereum.py"), &placeholder_map(kbc))
        .expect("the repository aggregation guest must parse");
    check(PATH, &render(&ast, kbc));
    check(PROGRAMS_PATH, &render_programs());
}
