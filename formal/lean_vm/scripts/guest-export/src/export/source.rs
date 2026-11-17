//! The aggregation guest's source AST, after `placeholder_map`, as the Lean data
//! `LeanVM/Guest/Data/Source.lean` (`LeanVM.Guest.Source`'s types), which the Lean expansion
//! lowers to the core IR; and the compiler's test programs (`crates/zkdsl/tests/programs`)
//! with their public inputs and witness streams, as `tests/LeanVMTests/Guest/Programs.lean`.
//! Ported from the BLAKE2s-era `guest_source_lean`; new at `keccak-gkr`: `Expr::ListComp`
//! (`.listComp body var lo hi`, a `keccak_cells` argument).

use super::*;
use crate::compiler_overlay::{
    Ast, Expr, ForBound, Func, LtBound, ParamKind, Shape, Stmt, StmtKind, core_ir, expand, parse, parse_const,
    parse_with_constants, parse_with_replacements,
};
use std::collections::BTreeSet;
use std::fmt::Write as _;

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
        Expr::ListComp(body, var, lo, hi) => {
            format!("(.listComp {} {} {} {})", expr(body), string(var), expr(lo), expr(hi))
        }
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

fn render(ast: &Ast, consts: &[(String, String)], kbc: usize, input: &str) -> String {
    let mut out = String::new();
    writeln!(
        out,
        "/-\n  LeanVM.Guest.Data.Source\n\n  Generated by `guest-export` \
         (lean_vm/scripts/guest-export); do not\n  edit. The aggregation \
         guest's source AST after `placeholder_map`.\n-/\n\nmodule\n\npublic import LeanVM.Guest.Source\n\n\
         /-!\n# The aggregation guest's source\n\n`guests/lean_ethereum.py` as \
         `zkdsl::parse_with_replacements` returns it with\nthe deployed placeholders \
         (`placeholder_map`, at the bytecode's log size `bytecodeLog`): one definition\nper \
         function, then the constant arrays and the program. The global constants come first, `const_NAME`, the\nliterals the compiler substitutes for them.\n-/\n\nnamespace LeanVM.Guest.Data\n\n\
         open LeanVM.Guest.Source\n\n@[expose] public section\n\n/-- The log size of the bytecode \
         the placeholders are computed for. -/\ndef bytecodeLog : Nat := {kbc}\n\n\
         /-- The digest of the source and the placeholders (`aggregation`'s `input_digest`), which the compiled \
         guest carries\n(`guests/lean_ethereum.compiled`). -/\ndef inputDigest : String := \"{input}\"\n"
    )
    .unwrap();
    for (name, value) in consts {
        writeln!(out, "/-- The global constant `{name}`. -/\ndef const_{name} : Nat := {value}\n").unwrap();
    }
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
        let items = list(values.iter().map(|v| format!("({}, {})", v.c0, v.c1)));
        writeln!(
            out,
            "/-- The constant array `{name}`. -/\ndef arr_{name} : List (Nat × Nat) :=\n  {items}\n"
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

fn word(x: E) -> String {
    format!("({}, {})", x.c0, x.c1)
}

/// The compiler's test programs, each with the public input and the witness streams its
/// annotations declare (`zkdsl/tests/suite/py_source.rs`).
fn render_programs() -> String {
    let dir = concat!(env!("LEANVM_DIR"), "/crates/zkdsl/tests/programs");
    let mut paths: Vec<_> = std::fs::read_dir(dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|x| x == "py"))
        .collect();
    paths.sort();
    let mut out = String::from(
        "/-\n  LeanVMTests.Guest.Programs\n\n  Generated by `guest-export` \
         (lean_vm/scripts/guest-export); do not\n  edit. The compiler's \
         test programs, `crates/zkdsl/tests/programs/*.py`.\n-/\n\nimport LeanVM.Guest.Source\n\n\
         namespace LeanVMTests.Guest.Programs\n\nopen LeanVM.Guest.Source\n\n/-- A test program: its AST, \
         the public input it publishes and its witness streams, each word as its limbs. -/\n\
         structure TestProgram where\n  name : String\n  program : Program\n  publicInput : List (Nat × Nat)\n  \
         streams : List (String × List (List (Nat × Nat)))\n\n",
    );
    let mut names = Vec::new();
    for path in paths {
        let file = path.file_stem().unwrap().to_string_lossy().into_owned();
        let src = std::fs::read_to_string(&path).unwrap();
        let ast = parse(&src).unwrap();
        let mut public = vec![E::new(0, 0); 2];
        let mut streams: BTreeMap<String, Vec<Vec<E>>> = BTreeMap::new();
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
                list(values.iter().map(|v| format!("({}, {})", v.c0, v.c1)))
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
    let mut bare = |programs: Vec<(String, Ast)>, from: &str| {
        let mut names = Vec::new();
        for (name, ast) in programs {
            let funcs = list(ast.funcs.iter().map(|f| format!("\n    {}", func_at(f, 4))));
            let arrays = list(ast.const_arrays.iter().map(|(name, values)| {
                format!(
                    "({}, {})",
                    string(name),
                    list(values.iter().map(|v| format!("({}, {})", v.c0, v.c1)))
                )
            }));
            writeln!(
                out,
                "/-- `{from}` as `{name}`. -/\ndef prog_{name} : TestProgram where\n  name := {}\n  program := \
                 ⟨{funcs},\n    {arrays}⟩\n  publicInput := []\n  streams := []\n",
                string(&name)
            )
            .unwrap();
            names.push(format!("prog_{name}"));
        }
        names
    };
    let chains = bare(chain_programs(), "chain.py");
    let vm = bare(vm_programs(), "tests/vm");
    let frontend = bare(frontend_programs(), "tests/frontend");
    writeln!(
        out,
        "/-- Every test program. -/\ndef all : List TestProgram := {}\n\n/-- The verifiers' fixture program \
         (`crates/stable_prover/lean_vm_core/tests/verifiers/chain.py`) at each step count its users take. -/\n\
         def chains : List TestProgram := {}\n\n/-- The programs of the VM's and the prover's tests \
         (`crates/zkdsl/tests/vm/*.py`), a template at each of its counts. -/\ndef vm : List TestProgram := {}\n\n\
         /-- The front end's regression corpus (`tests/frontend/*.py`): `lake exe guest-backend core-text` compares \
         the core IR `Expand` gives each with `tests/frontend/*.core`. -/\ndef frontend : List TestProgram := \
         {}\n\nend LeanVMTests.Guest.Programs",
        list(names),
        list(chains),
        list(vm),
        list(frontend)
    )
    .unwrap();
    out
}

/// The `.py` files of a directory of this repository, by name.
fn corpus(dir: &str) -> Vec<(String, String)> {
    let dir = format!("{}/{dir}", env!("LEANVM_DIR"));
    let mut paths: Vec<_> = std::fs::read_dir(&dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|x| x == "py"))
        .collect();
    paths.sort();
    paths
        .into_iter()
        .map(|p| (p.file_stem().unwrap().to_string_lossy().into_owned(), std::fs::read_to_string(&p).unwrap()))
        .collect()
}

/// The templates among the VM's test programs, each with the counts its tests take for `STEPS_PLACEHOLDER`: the
/// instance at count `n` is named `<template><n>`.
const VM_TEMPLATES: [(&str, &[usize]); 1] = [("keccak_steps", &[0, 1, 3, 512, 513])];

/// The programs of the VM's and the prover's tests (`crates/zkdsl/tests/vm`), compiled by the Lean back end and
/// proved by the zkdsl suite.
fn vm_programs() -> Vec<(String, Ast)> {
    let mut out = Vec::new();
    for (name, src) in corpus("crates/zkdsl/tests/vm") {
        match VM_TEMPLATES.iter().find(|(t, _)| *t == name) {
            Some((_, counts)) => {
                for n in *counts {
                    let replacements = BTreeMap::from([("STEPS_PLACEHOLDER".to_string(), n.to_string())]);
                    out.push((format!("{name}{n}"), parse_with_replacements(&src, &replacements).unwrap()));
                }
            }
            None => out.push((name, parse(&src).unwrap())),
        }
    }
    out
}

/// The front end's regression corpus (`formal/lean_vm/tests/frontend`), expanded and not compiled.
fn frontend_programs() -> Vec<(String, Ast)> {
    corpus("formal/lean_vm/tests/frontend")
        .into_iter()
        .map(|(name, src)| {
            let ast = parse(&src).unwrap_or_else(|e| panic!("tests/frontend/{name}.py: {e}"));
            (name, ast)
        })
        .collect()
}

/// The step counts the verifiers' fixture program is compiled at: the fixture's own (`fixture.rs`), and the chain
/// cases of `scripts/export-rust.sh` (fixed and corpus).
const CHAIN_STEPS: [usize; 6] = [4, 16, 300, 1000, 5000, 16384];

/// The fixture program at each of [`CHAIN_STEPS`], named `chain<steps>`.
fn chain_programs() -> Vec<(String, Ast)> {
    let src = std::fs::read_to_string(concat!(
        env!("LEANVM_DIR"),
        "/crates/stable_prover/lean_vm_core/tests/verifiers/chain.py"
    ))
    .unwrap();
    CHAIN_STEPS
        .iter()
        .map(|n| {
            let replacements = BTreeMap::from([("LOOP_STEPS_PLACEHOLDER".to_string(), n.to_string())]);
            (format!("chain{n}"), parse_with_replacements(&src, &replacements).unwrap())
        })
        .collect()
}

/// The functions `e` calls.
fn calls_expr<'a>(e: &'a Expr, out: &mut Vec<&'a str>) {
    match e {
        Expr::Call(f, args) => {
            out.push(f);
            args.iter().for_each(|a| calls_expr(a, out));
        }
        Expr::GenPow(a) | Expr::HeapBufDyn(a) => calls_expr(a, out),
        Expr::Pow(a, b)
        | Expr::Add(a, b)
        | Expr::Mul(a, b)
        | Expr::Sub(a, b)
        | Expr::Div(a, b)
        | Expr::Mod(a, b)
        | Expr::FieldDiv(a, b)
        | Expr::Index(a, b) => {
            calls_expr(a, out);
            calls_expr(b, out);
        }
        Expr::Slice(a, b, c) | Expr::ListComp(a, _, b, c) => [a, b, c].into_iter().for_each(|x| calls_expr(x, out)),
        Expr::ListLit(es) => es.iter().for_each(|x| calls_expr(x, out)),
        Expr::Lit(_) | Expr::Gen | Expr::GPow(_) | Expr::Var(_) | Expr::HeapBuf(_) | Expr::StackBuf(_) => {}
    }
}

/// The functions a block calls, at any depth.
fn calls_block<'a>(body: &'a [Stmt], out: &mut Vec<&'a str>) {
    for s in body {
        let mut exprs: Vec<&Expr> = Vec::new();
        match &s.kind {
            StmtKind::Let(_, e) | StmtKind::HintWitness { dest: e, .. } | StmtKind::Print { value: e, .. } => {
                exprs.push(e)
            }
            StmtKind::LetTuple(_, f, args) | StmtKind::Call(f, args) => {
                out.push(f);
                exprs.extend(args);
            }
            StmtKind::AssertEq(a, b) | StmtKind::AssertNe(a, b) => exprs.extend([a, b]),
            StmtKind::AssertLt(a, bound) => {
                exprs.push(a);
                if let LtBound::Runtime(b) = bound {
                    exprs.push(b);
                }
            }
            StmtKind::LetHintWitness { .. } => {}
            StmtKind::If { lhs, rhs, then, els, .. } => {
                exprs.extend([lhs, rhs]);
                calls_block(then, out);
                calls_block(els, out);
            }
            StmtKind::Match { targets, x, arms } => {
                exprs.extend(targets);
                exprs.push(x);
                exprs.extend(arms);
            }
            StmtKind::Store(a, b, c) => exprs.extend([a, b, c]),
            StmtKind::For { hi, body, .. } => {
                if let ForBound::Runtime(e) = hi {
                    exprs.push(e);
                }
                calls_block(body, out);
            }
            StmtKind::Unroll { lo, hi, body, .. } => {
                exprs.extend([lo, hi]);
                calls_block(body, out);
            }
            StmtKind::Return(es) => exprs.extend(es),
            StmtKind::CallIfNe(a, b, f, args) => {
                out.push(f);
                exprs.extend([a, b]);
                exprs.extend(args);
            }
        }
        exprs.into_iter().for_each(|e| calls_expr(e, out));
    }
}

/// The aggregation tests' snippets (`crates/aggregation/snippets/*.py`, each a `main`), each parsed after the guest's
/// source up to its `main`, at the placeholders `replacements`, and kept to the functions its `main` reaches, which
/// are all a run can execute: `(name, the names kept in the guest's order, the snippet's main)`. Each kept function
/// must be the guest's own (`guest`), which is what lets the Lean data name them.
fn snippet_programs(guest: &Ast, replacements: &BTreeMap<String, String>) -> Vec<(String, Vec<String>, Func)> {
    let (helpers, _) = GUEST_SOURCE.split_once("\ndef main():").unwrap();
    let dir = concat!(env!("LEANVM_DIR"), "/crates/aggregation/snippets");
    let mut paths: Vec<_> = std::fs::read_dir(dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|x| x == "py"))
        .collect();
    paths.sort();
    paths
        .into_iter()
        .map(|path| {
            let name = path.file_stem().unwrap().to_string_lossy().into_owned();
            let src = format!("{helpers}\n{}", std::fs::read_to_string(&path).unwrap());
            let ast = parse_with_replacements(&src, replacements).unwrap();
            assert_eq!(format!("{:?}", ast.const_arrays), format!("{:?}", guest.const_arrays));
            let main = ast.funcs.last().unwrap().clone();
            assert_eq!(main.name, "main", "snippet {name}: its last function is not its `main`");
            let mut reached: BTreeSet<&str> = BTreeSet::new();
            let mut todo = vec!["main"];
            while let Some(f) = todo.pop() {
                let Some(def) = ast.funcs.iter().find(|d| d.name == f) else { continue };
                if reached.insert(&def.name) {
                    calls_block(&def.body, &mut todo);
                }
            }
            let kept: Vec<String> = ast
                .funcs
                .iter()
                .filter(|f| f.name != "main" && reached.contains(f.name.as_str()))
                .map(|f| {
                    let own = guest.funcs.iter().find(|g| g.name == f.name);
                    assert!(
                        own.is_some_and(|g| format!("{g:?}") == format!("{f:?}")),
                        "snippet {name}: `{}` is not the guest's",
                        f.name
                    );
                    f.name.clone()
                })
                .collect();
            (name, kept, main)
        })
        .collect()
}

/// `Snippets.lean`: each snippet's `main` and the guest functions it keeps, and its program.
fn render_snippets(snippets: &[(String, Vec<String>, Func)]) -> String {
    let mut out = String::from(
        "/-\n  LeanVMTests.Guest.Snippets\n\n  Generated by `guest-export` (lean_vm/scripts/guest-export); do not\n  \
         edit. The aggregation tests' snippets, `crates/aggregation/snippets/*.py`: each a `main`\n  over the \
         guest's helpers, at the guest's placeholders.\n-/\n\nimport LeanVM.Guest.Data.Source\n\n\
         namespace LeanVMTests.Guest.Snippets\n\nopen LeanVM.Guest.Source\n\n\
         /-- A snippet's program: the guest's functions it reaches, in the guest's order, then its `main`. -/\n\
         def program (keep : List String) (main : Func) : Program :=\n  \
         ⟨LeanVM.Guest.Data.guest.funcs.filter (fun f => keep.contains f.name) ++ [main], \
         LeanVM.Guest.Data.guest.constArrays⟩\n\n",
    );
    for (name, kept, main) in snippets {
        writeln!(
            out,
            "/-- `{name}.py`. -/\ndef main_{name} : Func :=\n  {}\n\n/-- The functions `{name}.py` reaches. -/\n\
             def keep_{name} : List String := {}\n",
            func(main),
            list(kept.iter().map(|k| string(k)))
        )
        .unwrap();
    }
    writeln!(
        out,
        "/-- Every snippet, by name. -/\ndef all : List (String × Program) := {}\n\nend LeanVMTests.Guest.Snippets",
        list(
            snippets
                .iter()
                .map(|(name, ..)| format!("({}, program keep_{name} main_{name})", string(name)))
        )
    )
    .unwrap();
    out
}

/// `Source.lean`, with the placeholders at the log size `kbc`, `Programs.lean` and `Snippets.lean`.
pub fn files(kbc: usize) -> Vec<File> {
    let replacements = placeholder_map(kbc);
    let (ast, consts) =
        parse_with_constants(GUEST_SOURCE, &replacements).expect("the repository aggregation guest must parse");
    let snippets = snippet_programs(&ast, &replacements);
    vec![
        File {
            path: "LeanVM/Guest/Data/Source.lean".into(),
            text: render(&ast, &consts, kbc, &hex(&input_digest(&replacements))),
        },
        File {
            path: "tests/LeanVMTests/Guest/Programs.lean".into(),
            text: render_programs(),
        },
        File {
            path: "tests/LeanVMTests/Guest/Snippets.lean".into(),
            text: render_snippets(&snippets),
        },
    ]
}

/// The core IR of the guest, with the placeholders at the log size `kbc`, and of each test program, as the Rust
/// front end expands them, in the canonical text (`core_ir::render`): `(name, text)`, the guest's named `guest`.
/// `lake exe guest-backend core-text` writes Lean's, and `scripts/frontend-diff` compares them.
pub fn core_texts(kbc: usize) -> Vec<(String, String)> {
    let (ast, _) = parse_with_constants(GUEST_SOURCE, &placeholder_map(kbc))
        .expect("the repository aggregation guest must parse");
    let mut out = vec![("guest".to_string(), core_ir::render(&expand(&ast)))];
    let dir = concat!(env!("LEANVM_DIR"), "/crates/zkdsl/tests/programs");
    let mut paths: Vec<_> = std::fs::read_dir(dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|x| x == "py"))
        .collect();
    paths.sort();
    for path in paths {
        let name = path.file_stem().unwrap().to_string_lossy().into_owned();
        let ast = parse(&std::fs::read_to_string(&path).unwrap()).unwrap();
        out.push((name, core_ir::render(&expand(&ast))));
    }
    for (name, ast) in chain_programs().into_iter().chain(vm_programs()).chain(frontend_programs()) {
        out.push((name, core_ir::render(&expand(&ast))));
    }
    out
}
