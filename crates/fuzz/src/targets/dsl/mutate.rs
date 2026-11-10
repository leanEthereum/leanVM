//! `dsl-mutate`: token- and line-level mutations of real sources, the hand-written corpus and the recursion guest.
//! `parse` must never panic; `compile` panics are triaged by [`CompileFailure::as_finding`]; a mutant that compiles
//! must run or fail with an `ExecError`, never panic; a mutant that runs must prove, and its proof verify.

use crate::programs::{self, CompileFailure};
use crate::{Ctx, Finding, Outcome, Severity, Source, catch};
use lean_compiler::{compile, parse_with_replacements};
use std::collections::BTreeMap;

const GUEST: &str = include_str!("../../../../rec_aggregation/guests/lean_ethereum.py");

/// Mutants that run longer than this are not proven.
const PROVE_CYCLES: usize = 1 << 16;

const NAMES: &[&str] = &[
    "GEN",
    "log",
    "main",
    "StackBuf",
    "HeapBuf",
    "keccak",
    "keccak_cells",
    "match",
    "range",
    "unroll",
    "mul_range",
    "const",
    "len",
    "f192",
    "return",
    "def",
    "if",
    "else",
    "elif",
    "for",
    "in",
    "lambda",
    "assert",
    "print",
    "hint_witness",
    "addr",
    "Const",
    "inline",
    "assert_in_k",
    "snark_lib",
    "import",
    "x",
    "i",
    "j",
    "_",
    "None",
];
const OPS: &[&str] = &[" + ", " * ", " / ", " // ", " % ", " - ", " ** ", " == ", " != ", " < "];
const EDGES: &[&str] = &[
    "0",
    "1",
    "2",
    "3",
    "16",
    "65535",
    "65536",
    "65537",
    "4294967295",
    "4294967296",
    "18446744073709551615",
    "18446744073709551616",
    "340282366920938463463374607431768211455",
    "340282366920938463463374607431768211456",
    "99999999999999999999999999999999999999999999999",
    "GEN ** 64",
    "GEN ** 65536",
    "GEN ** 4294967296",
];

pub fn run(src: &mut Source, ctx: &Ctx) -> Outcome {
    let corpus = programs::corpus_at(ctx.depth);
    let guest = src.chance(1, 16);
    let (name, base, spec) = if guest {
        ("guest", GUEST, None)
    } else {
        let spec = &corpus[src.below(corpus.len())];
        (spec.name, spec.source, Some(spec))
    };
    let mut lines: Vec<String> = base.lines().map(str::to_string).collect();
    let n = src.range(1, 4);
    let mut kinds = Vec::new();
    for _ in 0..n {
        let other = &corpus[src.below(corpus.len())];
        kinds.push(mutate(&mut lines, other.source, src));
    }
    for k in &kinds {
        ctx.note(format!("mutation {k}"));
    }
    let text = lines.join("\n") + "\n";
    let context = "dsl-mutate";
    let detail = |what: String| format!("{what}\nfrom {name}, mutations {kinds:?}\n\n{text}");
    if guest {
        return check_guest(&text, src, ctx, &detail);
    }
    let program = match programs::compile_source(&text) {
        Ok(p) => p,
        Err(f) => return triage(&f, ctx, context, &detail),
    };
    ctx.note("mutant compiled");
    let mut program = program;
    if let Some(spec) = spec {
        for (stream, entries) in &spec.witness {
            program.set_witness(stream.clone(), entries.clone());
        }
    }
    let (result, pi) = programs::execute(&program, None);
    let exec = match result {
        Ok(exec) => exec,
        Err(e) => {
            ctx.note(format!("mutant fails: {}", programs::fault_kind(&e.fault)));
            return Ok(());
        }
    };
    ctx.note("mutant runs");
    if exec.cycles > PROVE_CYCLES || !exec.unconstrained_reads.is_empty() || ctx.depth == 0 {
        return Ok(());
    }
    drop(exec);
    let rate = programs::log_inv_rate(src);
    match programs::prove_honest(&program, pi, rate, context) {
        Ok(Some(_)) => {
            ctx.note("mutant proved");
            Ok(())
        }
        Ok(None) => Ok(()),
        Err(mut f) => {
            f.detail = detail(f.detail);
            Err(f)
        }
    }
}

/// A refusal: a panic outside the compiler's documented rejections is the finding.
fn triage(f: &CompileFailure, ctx: &Ctx, context: &str, detail: &dyn Fn(String) -> String) -> Outcome {
    match f.as_finding(context) {
        Some(finding) if finding.severity < Severity::Low => Err(Finding {
            detail: detail(finding.detail.clone()),
            ..finding
        }),
        Some(_) => {
            ctx.note("documented compile panic");
            Ok(())
        }
        None => {
            ctx.note("parse error");
            Ok(())
        }
    }
}

/// The guest: its placeholders filled with small stand-ins (a scalar or a list), parsed and compiled. Running it
/// needs a real child proof's witness, which a mutant would not have.
fn check_guest(text: &str, src: &mut Source, ctx: &Ctx, detail: &dyn Fn(String) -> String) -> Outcome {
    let mut map = guest_placeholders().clone();
    // Now and then one placeholder takes an edge value instead.
    if src.chance(1, 4) && !map.is_empty() {
        let key = map.keys().nth(src.below(map.len())).unwrap().clone();
        let value = *src.pick(&[
            "0",
            "1",
            "[]",
            "[0]",
            "65536",
            "340282366920938463463374607431768211455",
            "GEN",
        ]);
        map.insert(key, value.to_string());
        ctx.note("guest: edge placeholder");
    }
    let ast = match catch(|| parse_with_replacements(text, &map)) {
        Ok(Ok(ast)) => ast,
        Ok(Err(_)) => {
            ctx.note("guest: parse error");
            return Ok(());
        }
        Err((message, location)) => {
            let f = Finding::panic(&message, &location).in_context("dsl-mutate guest");
            return Err(Finding {
                detail: detail(f.detail.clone()),
                ..f
            });
        }
    };
    ctx.note("guest: parsed");
    if ctx.depth == 0 {
        return Ok(());
    }
    match catch(|| compile(&ast)) {
        Ok(_) => {
            ctx.note("guest: compiled");
            Ok(())
        }
        Err((message, location)) => triage(
            &CompileFailure::CompilePanic { message, location },
            ctx,
            "dsl-mutate guest",
            detail,
        ),
    }
}

/// Stand-ins for the guest's placeholders under which the unmutated guest parses: a ramp for one indexed as an
/// array, a small integer otherwise, repaired one global constant at a time until the integer arithmetic of the
/// constants it feeds stays in range.
fn guest_placeholders() -> &'static BTreeMap<String, String> {
    static MAP: std::sync::OnceLock<BTreeMap<String, String>> = std::sync::OnceLock::new();
    MAP.get_or_init(|| {
        let ramp = format!(
            "[{}]",
            (0..64).map(|i| (2 * i).to_string()).collect::<Vec<_>>().join(", ")
        );
        let mut map = BTreeMap::new();
        let mut defs: BTreeMap<String, String> = BTreeMap::new();
        for line in GUEST.lines().filter(|l| !l.starts_with(' ')) {
            let line = line.split(" #").next().unwrap_or("");
            let Some((name, value)) = line.split_once(" = ") else {
                continue;
            };
            let (name, value) = (name.trim(), value.trim());
            defs.insert(name.to_string(), value.to_string());
            if value.ends_with("_PLACEHOLDER") {
                let array = GUEST.contains(&format!("{name}[")) || GUEST.contains(&format!("len({name})"));
                map.insert(value.to_string(), if array { ramp.clone() } else { "4".to_string() });
            }
        }
        const TRY: [&str; 10] = ["1", "2", "3", "8", "16", "32", "48", "64", "100", "300"];
        let mut tries: BTreeMap<String, usize> = BTreeMap::new();
        for _ in 0..400 {
            let Err(e) = parse_with_replacements(GUEST, &map) else {
                break;
            };
            let Some(failing) = e.split("global constant `").nth(1).and_then(|r| r.split('`').next()) else {
                break;
            };
            // The scalar placeholders the failing constant is computed from.
            let mut names = vec![failing.to_string()];
            let mut phs = Vec::new();
            let mut i = 0;
            while i < names.len() && i < 30 {
                if let Some(def) = defs.get(&names[i]) {
                    for w in def.split(|c: char| !(c.is_ascii_alphanumeric() || c == '_')) {
                        if w.ends_with("_PLACEHOLDER") {
                            phs.push(w.to_string());
                        } else if defs.contains_key(w) && !names.iter().any(|n| n == w) {
                            names.push(w.to_string());
                        }
                    }
                }
                i += 1;
            }
            let scalars: Vec<String> = phs.into_iter().filter(|p| !map[p].starts_with('[')).collect();
            if scalars.is_empty() {
                break;
            }
            let p = scalars[tries.values().sum::<usize>() % scalars.len()].clone();
            let n = tries.entry(p.clone()).or_insert(0);
            *n += 1;
            map.insert(p, TRY[*n % TRY.len()].to_string());
        }
        map
    })
}

/// One mutation of `lines`, named for notes.
fn mutate(lines: &mut Vec<String>, other: &str, src: &mut Source) -> &'static str {
    if lines.is_empty() {
        lines.push("def main():".into());
    }
    let i = src.below(lines.len());
    match src.below(14) {
        0 => {
            lines.remove(i);
            "delete line"
        }
        1 => {
            let l = lines[i].clone();
            lines.insert(i, l);
            "duplicate line"
        }
        2 => {
            let j = src.below(lines.len());
            lines.swap(i, j);
            "swap lines"
        }
        3 => {
            let l = &mut lines[i];
            match src.below(4) {
                0 => l.insert_str(0, "    "),
                1 => l.insert(0, '\t'),
                2 => l.insert(0, ' '),
                _ => {
                    let trimmed = l.trim_start().to_string();
                    *l = trimmed;
                }
            }
            "indentation"
        }
        4 | 5 => {
            if replace_token(&mut lines[i], src, |t| OPS.contains(&t), OPS) {
                "operator"
            } else {
                "none"
            }
        }
        6 | 7 => {
            let digits = |t: &str| !t.is_empty() && t.trim().chars().all(|c| c.is_ascii_digit());
            if replace_word(&mut lines[i], src, digits, EDGES) {
                "integer edge"
            } else {
                "none"
            }
        }
        8 => {
            let ident = |t: &str| t.chars().next().is_some_and(|c| c.is_ascii_alphabetic() || c == '_');
            if replace_word(&mut lines[i], src, ident, NAMES) {
                "name"
            } else {
                "none"
            }
        }
        9 => {
            match lines.iter().position(|l| l.starts_with("def ") && src.chance(1, 2)) {
                Some(d) => lines.insert(d, "@inline".into()),
                None => lines.insert(i, "@inline".into()),
            }
            "@inline"
        }
        10 => {
            // A slice bound moved.
            let l = &mut lines[i];
            match l.find(':').filter(|&c| l[..c].contains('[')) {
                Some(c) => {
                    let delta = *src.pick(&["+ 1", "- 1", "+ 13", "* 0", "+ 65536"]);
                    l.insert_str(c, &format!(" {delta}"));
                    "slice bound"
                }
                None => "none",
            }
        }
        11 => match lines.iter().position(|l| l.trim_start().starts_with("assert")) {
            Some(a) => {
                lines.remove(a);
                "remove assert"
            }
            None => "none",
        },
        12 => {
            let others: Vec<&str> = other.lines().collect();
            if !others.is_empty() {
                lines.insert(i, others[src.below(others.len())].to_string());
            }
            "splice line"
        }
        _ => {
            // A token removed: an unbalanced bracket, a missing operand.
            let l = &mut lines[i];
            if !l.is_empty() {
                let at = src.below(l.len());
                if l.is_char_boundary(at) && l.is_char_boundary(at + 1) {
                    l.remove(at);
                }
            }
            "delete char"
        }
    }
}

/// Replace one occurrence of an operator in `line` with another.
fn replace_token(line: &mut String, src: &mut Source, is: impl Fn(&str) -> bool, with: &[&str]) -> bool {
    let hits: Vec<(usize, &str)> = OPS
        .iter()
        .flat_map(|op| line.match_indices(op).map(|(i, _)| (i, *op)).collect::<Vec<_>>())
        .filter(|(_, t)| is(t))
        .collect();
    if hits.is_empty() {
        return false;
    }
    let (at, op) = hits[src.below(hits.len())];
    let new = *src.pick(with);
    line.replace_range(at..at + op.len(), new);
    true
}

/// Replace one word (a run of identifier characters) that `is` accepts.
fn replace_word(line: &mut String, src: &mut Source, is: impl Fn(&str) -> bool, with: &[&str]) -> bool {
    let mut words = Vec::new();
    let mut start = None;
    for (i, c) in line.char_indices().chain([(line.len(), ' ')]) {
        let word = c.is_ascii_alphanumeric() || c == '_';
        match (word, start) {
            (true, None) => start = Some(i),
            (false, Some(s)) => {
                words.push((s, i));
                start = None;
            }
            _ => {}
        }
    }
    let words: Vec<(usize, usize)> = words.into_iter().filter(|&(s, e)| is(&line[s..e])).collect();
    if words.is_empty() {
        return false;
    }
    let (s, e) = words[src.below(words.len())];
    line.replace_range(s..e, src.pick(with));
    true
}
