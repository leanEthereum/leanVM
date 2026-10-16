//! The designs of a grid of tree shapes, as `checkdesign` compares them with the Lean model of `Design`.

use super::design::{Design, Level};
use super::reduce::{DenseReduced, MatrixReduced, NodeClaims, Reduced};
use super::statement::{Kind, Section, TreeStatement};
use super::*;
use crate::cpu::ProofKind;
use crate::rec::circuit::{Builder, Ew, Kw};
use crate::rec::fixed::FixedColumn;
use crate::rec::table::Table;
use crate::rec::verifier::FixedHint;
use crate::rv::Region;
use crate::rv::asm::*;
use crate::tables::{CircuitId, N_CIRCUITS};
use std::fmt::Write;

/// The committed summaries, which `checkdesign` reads.
const SUMMARIES: &str = "../../verification/circuits/fixtures/design-summaries.txt";

/// A program of a few instructions, whose shape fixes only the dense polynomials' variables.
fn program() -> Program {
    let text = Asm::new()
        .li(Reg::T0, Region::ADVICE.base())
        .load(Ld, Reg::A0, 0, Reg::T0)
        .exit()
        .finish();
    Program::new(&text, Region::TEXT.base(), vec![3, 5], 2, 0).expect("a valid program")
}

/// A design as `checkdesign` reads it: its places, tiers, kinds, unions, variables and statement.
fn summary(d: &Design<'_>) -> String {
    let mut s = String::new();
    let places: Vec<String> = (d.places.iter())
        .map(|p| match p.level {
            Level::First => format!("{}:F", p.tier),
            Level::Node(a) => format!("{}:N:{a}", p.tier),
            Level::Wrap => format!("{}:W", p.tier),
        })
        .collect();
    let _ = writeln!(s, "places {}", places.join(" "));
    let tiers: Vec<String> = (d.tiers.iter())
        .map(|t| format!("{}-{}", t.places.start, t.places.end))
        .collect();
    let _ = writeln!(s, "tiers {}", tiers.join(" "));
    let codes: Vec<String> = (0..d.places.len()).map(|p| d.code(p).to_string()).collect();
    let _ = writeln!(s, "codes {}", codes.join(" "));
    let positions: Vec<String> = (0..40)
        .map(|c| d.position(c).map_or_else(|| "-".to_owned(), |p| p.to_string()))
        .collect();
    let _ = writeln!(s, "positions {}", positions.join(" "));
    let unions: Vec<String> = (0..d.places.len())
        .map(|p| {
            d.union_shape(p).map_or_else(
                || "-".to_owned(),
                |u| {
                    format!(
                        "{}:{}:{}:{}",
                        u.arity,
                        u.children.chunks,
                        u.declared.chunks,
                        u8::from(u.optional)
                    )
                },
            )
        })
        .collect();
    let _ = writeln!(s, "unions {}", unions.join(" "));
    let [v0, v1, v2, v3] = d.vars.0;
    let _ = writeln!(s, "vars {v0} {v1} {v2} {v3}");
    let kappas: Vec<String> = d.tiers.iter().map(|t| t.fixed.kappa().to_string()).collect();
    let _ = writeln!(s, "kappas {}", kappas.join(" "));
    let _ = writeln!(s, "statement {} {}", d.statement.len(), d.statement.polys().len());
    let _ = writeln!(s, "{}", d.statement.edge_line(&d.vars.0).trim_start_matches("edge "));
    s.push_str(&carried(d));
    s.push_str(&exposed(d, d.statement.range(Section::DensePoint).len(), [true; 4]));
    s.push_str(&exposed(d, d.vars.0[0], [true, true, false, false]));
    s.push_str(&fixed(d, "fixed"));
    if d.claims.is_none() {
        s.push_str(&node_digest(d.arity));
    }
    s
}

/// The digest `Kind::Node::digest_rows` computes of `arity` children's digests, child `i`'s words `4i + 1` to `4i + 4`,
/// as its words.
fn node_digest(arity: usize) -> String {
    let mut b = Builder::new();
    let items: Vec<[Kw; 4]> = (0..arity as u64)
        .map(|i| {
            let d = b.free_d([4 * i + 1, 4 * i + 2, 4 * i + 3, 4 * i + 4]);
            b.d_to_k(d)
        })
        .collect();
    let digest = Kind::Node.digest_rows(&mut b, &items);
    let words: Vec<String> = b.d(digest).iter().map(ToString::to_string).collect();
    format!("digest {arity} {}\n", words.join(" "))
}

/// Claims as one summary line: their edge lines without `edge`, joined by `|`.
fn claim_line(name: &str, claims: &NodeClaims<Ew>) -> String {
    let text = claims.edge_lines();
    let lines: Vec<&str> = text.lines().map(|l| l.trim_start_matches("edge ")).collect();
    format!("{name} {}\n", lines.join(" | "))
}

/// The claims `Design::carried` takes from a statement whose word `i` is wire `i`, its scale the wire after them.
fn carried(d: &Design<'_>) -> String {
    let n = d.statement.len();
    let words = (0..n)
        .map(|i| Ew(u32::try_from(i).expect("a small statement")))
        .collect();
    let statement = TreeStatement::new(d.statement, words);
    let mut claims = NodeClaims::default();
    d.carried(
        &statement,
        Ew(u32::try_from(n).expect("a small statement")),
        &mut claims,
    );
    claim_line("carried", &claims)
}

/// The words `Reduced::statement` exposes for a reduction of `rounds` rounds that reduced the polynomials `present`,
/// as their values: each of the reduction's outputs is a free word of value `1000 + i`, in order the point, the present
/// values, the row point, the column point and the matrices' values; the kind is 7 and the digest's words 1 to 4.
fn exposed(d: &Design<'_>, rounds: usize, present: [bool; 4]) -> String {
    let mut b = Builder::new();
    let mut next = 1000;
    let mut free = |b: &mut Builder| {
        next += 1;
        b.free_e(F192::new(next - 1, 0, 0))
    };
    let point = (0..rounds).map(|_| free(&mut b)).collect();
    let values = present.map(|p| p.then(|| free(&mut b)));
    let n_matrix = d.statement.range(Section::Rows).len();
    let rows = (0..n_matrix).map(|_| free(&mut b)).collect();
    let cols = (0..n_matrix).map(|_| free(&mut b)).collect();
    let matrices = (0..N_CIRCUITS).map(|_| [free(&mut b), free(&mut b)]).collect();
    let reduced = Reduced {
        dense: DenseReduced { point, values },
        matrices: MatrixReduced {
            rows,
            cols,
            values: matrices,
        },
    };
    let digest = b.free_d([1, 2, 3, 4]);
    let statement = TreeStatement::from_reduced(&mut b, d.statement, 7, digest, &reduced);
    let words: Vec<String> = (statement.words().iter())
        .map(|&w| {
            let x = b.e(w);
            format!("{}:{}:{}", x.c0, x.c1, x.c2)
        })
        .collect();
    let present: Vec<String> = present.iter().map(|&p| u8::from(p).to_string()).collect();
    format!("exposed {rounds} {} {}\n", present.join(""), words.join(" "))
}

/// Each tier's fixed claim (`Design::fixed_claim`) on a hint of every fixed column, in order, at its prefix of one
/// point: the point's coordinates are wires `0..n`, the hints' values the wires after them, the kind's bits the wires
/// after those. The line states each column's variables, from which `checkdesign` places the stack.
fn fixed(d: &Design<'_>, name: &str) -> String {
    let mut s = String::new();
    for (tier, t) in d.tiers.iter().enumerate() {
        let taus: Vec<usize> = (0..FixedColumn::COUNT)
            .map(|c| t.fixed.tau(FixedColumn::at(c)))
            .collect();
        let n = taus.iter().copied().max().unwrap_or(0);
        let wire = |i: usize| Ew(u32::try_from(i).expect("a small label"));
        let point: Vec<Ew> = (0..n).map(wire).collect();
        let hints: Vec<FixedHint> = (taus.iter().enumerate())
            .map(|(c, &tau)| FixedHint {
                column: FixedColumn::at(c),
                point: point[..tau].to_vec(),
                value: wire(n + c),
            })
            .collect();
        let bits = crate::log2_ceil_usize(t.places.len());
        let top: Vec<Ew> = (0..bits).map(|j| wire(n + taus.len() + j)).collect();
        let claims = NodeClaims {
            bound: Vec::new(),
            dense: vec![d.fixed_claim(&hints, &top, tier)],
            matrices: Vec::new(),
        };
        let taus: Vec<String> = taus.iter().map(ToString::to_string).collect();
        let line = claim_line("", &claims);
        let _ = write!(s, "{name} {tier} {} {} {} |{line}", bits, taus.len(), taus.join(" "));
    }
    s
}

/// The two scalars `NodeClaims::bind_state` binds of a final state of words 1 to 4, as their values.
fn bound() -> String {
    let mut b = Builder::new();
    let state = b.free_d([1, 2, 3, 4]);
    let mut claims = NodeClaims::default();
    claims.bind_state(&mut b, state);
    let words: Vec<String> = (claims.bound.iter())
        .map(|&w| {
            let x = b.e(w);
            format!("{}:{}:{}", x.c0, x.c1, x.c2)
        })
        .collect();
    format!("bind {}\n", words.join(" "))
}

/// Heights other than zero, different per table and per tier, so that the fixed columns' stack places columns of
/// several sizes.
fn heights(tiers: usize) -> Vec<PerRecTable<usize>> {
    let rows = [[3, 0, 5, 2, 4, 1], [1, 4, 0, 3, 2, 5]];
    (0..tiers)
        .map(|t| {
            let mut h = PerRecTable::default();
            for (table, &tau) in Table::ALL.iter().zip(&rows[t % 2]) {
                h[*table] = tau;
            }
            h
        })
        .collect()
}

/// The grid's shapes: arities around the edges Tree::new checks, and claim-set trees of one tier and of two whose
/// small tier is within, at, and past the tree's.
fn grid() -> Vec<(usize, usize, Option<ClaimShape>)> {
    let cap = |claims, groups| Capacity { claims, groups };
    let mut shapes = Vec::new();
    for arity_0 in [0, 1, 2, 3, 5] {
        for arity in [0, 1, 2, 3, 4, 7] {
            shapes.push((arity_0, arity, None));
            for large in [cap(1, 1), cap(12, 4), cap(100, 9)] {
                shapes.push((arity_0, arity, Some(ClaimShape::new(large))));
            }
            let large = cap(12, 4);
            for small_arity in [1, 2, 3, arity, arity + 1] {
                for capacity in [cap(5, 2), cap(12, 4), cap(13, 4), cap(12, 5)] {
                    let small = Some(Tier {
                        arity: small_arity,
                        capacity,
                    });
                    let shape = (arity_0, arity, Some(ClaimShape { capacity: large, small }));
                    if !shapes.contains(&shape) {
                        shapes.push(shape);
                    }
                }
            }
        }
    }
    shapes
}

/// Every grid shape: whether `Tree::new` refuses its arities or small tier, and if not, its design.
fn summaries() -> String {
    let program = program();
    let rate = Rate::MIN;
    let measured = LeafShape::measured(&program.measure(&[1]).expect("the run halts"), rate);
    // A leaf shape no proof has, so that `Tree::new` stops at the leaf's shape once the arities pass.
    let refused = LeafShape::new(measured.taus().map(|_| 99), rate, ProofKind::Plain);
    let mut out = format!("consts {} {}\n", CircuitId::MAX_K_LOG, N_CIRCUITS);
    out.push_str(&bound());
    for (arity_0, arity, claims) in grid() {
        let claim_words = claims.map_or_else(
            || "none".to_owned(),
            |c| {
                let large = format!("{} {}", c.capacity.claims, c.capacity.groups);
                c.small.map_or_else(
                    || format!("{large} -"),
                    |s| format!("{large} {} {} {}", s.arity, s.capacity.claims, s.capacity.groups),
                )
            },
        );
        let _ = writeln!(out, "shape {arity_0} {arity} {claim_words}");
        let shape = TreeShape {
            leaf: refused,
            arity_0,
            arity,
            rate,
            claims,
        };
        match Tree::new(&program, shape) {
            Err(TreeError::Arity { .. }) => out.push_str("reject arity\n"),
            Err(TreeError::SmallTier { .. }) => out.push_str("reject small\n"),
            Err(TreeError::LeafShape(_)) => {
                out.push_str("accept\n");
                let shape = TreeShape {
                    leaf: measured,
                    ..shape
                };
                let tiers = claims.map_or(1, |c| c.tiers());
                let taus = vec![PerRecTable::default(); tiers];
                let d = Design::new(&program, &shape, &taus).expect("a design at zero heights");
                out.push_str(&summary(&d));
                let d = Design::new(&program, &shape, &heights(tiers)).expect("a design at heights");
                let kappas: Vec<String> = d.tiers.iter().map(|t| t.fixed.kappa().to_string()).collect();
                let _ = writeln!(out, "hkappas {}", kappas.join(" "));
                out.push_str(&fixed(&d, "hfixed"));
            }
            Err(e) => panic!("shape {arity_0} {arity} {claims:?}: {e}"),
            Ok(_) => panic!("a tree of a leaf shape no proof has"),
        }
        out.push_str("end\n");
    }
    out
}

/// The committed summaries are the designs: `LEANVM_BLESS=1` rewrites them.
#[test]
fn the_design_summaries_are_the_designs() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(SUMMARIES);
    let built = summaries();
    if std::env::var_os("LEANVM_BLESS").is_some() {
        std::fs::write(&path, &built).expect("the fixture is writable");
    }
    let committed = std::fs::read_to_string(&path).expect("the committed summaries");
    assert!(
        committed == built,
        "the design summaries changed: rerun with LEANVM_BLESS=1"
    );
}
