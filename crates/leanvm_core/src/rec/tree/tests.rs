use super::claims::{Bits, DenseClaim, DenseTerm, MatrixClaim, NodeClaims};
use super::reduce::{DenseProver, DenseVars, LABEL, MatrixProver, MatrixReduced};
use super::statement::{Section, digest_halves_rows};
use super::*;
use crate::arith::{Arith, Native};
use crate::rec::circuit::{Assignment, Builder, Kw};
use crate::rv::asm::*;
use fiat_shamir::transcript::{Challenger, ProverState, Transmitter, VerifierState};
use primitives::multilinear::mle_eval;
use primitives::test_rng::Rng;
use std::sync::OnceLock;

// A program whose output is its one advice word, after a loop that reads every framework block.
fn program() -> &'static Program {
    static PROGRAM: OnceLock<Program> = OnceLock::new();
    PROGRAM.get_or_init(|| {
        let text = Asm::new()
            .li(Reg::T0, crate::rv::Region::ADVICE.base())
            .load(Ld, Reg::A0, 0, Reg::T0)
            .li(Reg::T1, 9)
            .label("loop")
            .i(Addi, Reg::T1, Reg::T1, -1)
            .branch(Bne, Reg::T1, Reg::ZERO, "loop")
            .exit()
            .finish();
        Program::new(&text, crate::rv::Region::TEXT.base(), vec![3, 5], 2, 0).expect("a valid program")
    })
}

// Four leaves of distinct outputs, a tree of first level 2 and arity 2 over them, and its proofs.
struct Fixture {
    tree: Tree<'static>,
    leaves: Vec<(Proof, [u64; 4])>,
    firsts: [TreeProof; 2],
    root: TreeProof,
}

fn fixture() -> &'static Fixture {
    static FIXTURE: OnceLock<Fixture> = OnceLock::new();
    FIXTURE.get_or_init(|| {
        let leaves: Vec<(Proof, [u64; 4])> = (1..=4)
            .map(|advice| {
                let (proof, output, _) = program().prove(&[advice], Rate::MIN).expect("the run halts");
                (proof, output)
            })
            .collect();
        let shape = LeafShape::of(&leaves[0].0).expect("a canonical announcement");
        let tree = Tree::new(program(), shape, 2, 2, Rate::MIN).expect("a tree");
        let firsts = [0, 2].map(|i| {
            let pair = [
                Leaf::new(&leaves[i].0, leaves[i].1),
                Leaf::new(&leaves[i + 1].0, leaves[i + 1].1),
            ];
            tree.prove_first(&pair).expect("honest leaves")
        });
        let root = tree.prove_node(&firsts).expect("honest children");
        Fixture {
            tree,
            leaves,
            firsts,
            root,
        }
    })
}

impl Fixture {
    fn outputs(&self) -> Vec<[u64; 4]> {
        self.leaves.iter().map(|l| l.1).collect()
    }

    fn pairs(&self) -> Vec<Leaf<'_>> {
        self.leaves.iter().map(|(p, o)| Leaf::new(p, *o)).collect()
    }
}

#[test]
fn a_tree_verifies_and_binds_its_leaves_in_order() {
    let f = fixture();
    let outputs = f.outputs();
    assert_eq!((f.firsts[0].kind(), f.root.kind()), (Kind::First, Kind::Node));
    f.tree.verify(&f.root, &outputs).expect("the root");
    f.tree
        .verify(&f.firsts[1], &outputs[2..])
        .expect("a first-level node is the root of its leaves");

    let mut wrong = outputs.clone();
    wrong[3][0] ^= 1;
    assert_eq!(f.tree.verify(&f.root, &wrong), Err(TreeError::Outputs));
    let mut swapped = outputs.clone();
    swapped.swap(0, 1);
    assert_eq!(f.tree.verify(&f.root, &swapped), Err(TreeError::Outputs));
    assert_eq!(
        f.tree.verify(&f.root, &outputs[..3]),
        Err(TreeError::LeafCount {
            leaves: 3,
            arity_0: 2,
            arity: 2
        })
    );
    assert_eq!(
        f.tree.verify(&f.root, &outputs[..2]),
        Err(TreeError::Kind {
            leaves: 2,
            expected: Kind::First,
            got: Kind::Node
        })
    );
}

#[test]
fn one_leaf_is_a_root() {
    let f = fixture();
    let shape = LeafShape::of(&f.leaves[0].0).expect("a canonical announcement");
    let tree = Tree::new(program(), shape, 1, 2, Rate::MIN).expect("a tree");
    let root = tree.prove(&f.pairs()[..1]).expect("an honest leaf");
    tree.verify(&root, &[f.leaves[0].1]).expect("the root of one leaf");
    assert_eq!(tree.verify(&root, &[f.leaves[1].1]), Err(TreeError::Outputs));

    // A first-level node of that tree is no child of a tree of another first level.
    let child = tree.prove_first(&f.pairs()[1..2]).expect("an honest leaf");
    assert!(matches!(
        f.tree.prove_node(&[f.firsts[0].clone(), child]),
        Err(TreeError::Child { index: 1, .. })
    ));
}

#[test]
fn what_a_prover_is_handed_is_checked() {
    let f = fixture();
    let shape = LeafShape::of(&f.leaves[0].0).expect("a canonical announcement");
    for (arity_0, arity) in [(2, 1), (0, 2)] {
        assert!(matches!(
            Tree::new(program(), shape, arity_0, arity, Rate::MIN),
            Err(TreeError::Arity { .. })
        ));
    }
    assert_eq!(
        f.tree.prove_node(&f.firsts[..1]).map(|_| ()),
        Err(TreeError::Children { expected: 2, got: 1 })
    );

    // A leaf that does not verify, and one of another shape.
    let pairs = f.pairs();
    let mut forged = f.leaves[1].0.clone();
    let mid = forged.stream.len() / 2;
    forged.stream[mid] += F192::ONE;
    assert!(matches!(
        f.tree.prove_first(&[pairs[0], Leaf::new(&forged, f.leaves[1].1)]),
        Err(TreeError::Leaf { index: 1, .. })
    ));
    let (longer, output, _) = program()
        .prove(&[7], Rate::new(2).expect("a rate"))
        .expect("the run halts");
    assert_eq!(
        f.tree.prove_first(&[Leaf::new(&longer, output), pairs[1]]).map(|_| ()),
        Err(TreeError::ForeignLeaf { index: 0 })
    );

    // A child whose statement is not its proof's.
    let mut changed = f.firsts[1].clone();
    changed.words[5] += F192::ONE;
    assert!(matches!(
        f.tree.prove_node(&[f.firsts[0].clone(), changed]),
        Err(TreeError::Child { index: 1, .. })
    ));
}

// A root over subtrees of two depths states no balanced tree: its count or its digest refuses it.
#[test]
fn mixed_levels_are_refused_at_the_root() {
    let f = fixture();
    let mixed = f
        .tree
        .prove_node(&[f.root.clone(), f.firsts[0].clone()])
        .expect("a node verifies either kind");
    let mut outputs = f.outputs();
    outputs.extend_from_slice(&f.outputs()[..2]);
    assert!(matches!(
        f.tree.verify(&mixed, &outputs),
        Err(TreeError::LeafCount { .. })
    ));
    outputs.extend_from_slice(&f.outputs()[2..]);
    assert_eq!(f.tree.verify(&mixed, &outputs), Err(TreeError::Outputs));
}

// The reduction an honest prover proves, as its rows read it.
fn honest_reduction(f: &Fixture, rows: &design::NodeRows) -> RawProof {
    let proof = rows.claim_values().prove(&f.tree.design.vars, &f.tree.tables);
    RawProof {
        stream: proof.stream,
        merkle: Vec::new(),
    }
}

// The circuit a prover's rows build, at the nodes' heights.
fn proven_circuit(f: &Fixture, rows: design::NodeRows) -> Circuit {
    let reduction = honest_reduction(f, &rows);
    let Finished {
        mut circuit, failures, ..
    } = rows.reduce(&f.tree.design, ProofSource::Proof(&reduction));
    assert!(failures.is_empty(), "{failures:?}");
    circuit.floor = f.tree.design.taus;
    circuit
}

#[test]
fn a_proven_circuit_is_the_shapes() {
    let f = fixture();
    let d = &f.tree.design;
    let leaves: Vec<LeafWitness> = (f.leaves[..2].iter())
        .map(|(proof, output)| LeafWitness {
            raw: program().verify_to_raw(output, proof).expect("an honest leaf"),
            output: *output,
        })
        .collect();
    let rows = d.first(&Witness::Prove {
        items: &leaves,
        tables: &f.tree.tables,
    });
    assert!(
        &proven_circuit(f, rows) == f.tree.circuit(Kind::First),
        "the leaves build another circuit"
    );

    let raw = |p: &TreeProof| f.tree.read(p).expect("an honest child");
    let statements = f
        .firsts
        .each_ref()
        .map(|p| TreeStatement::new(d.statement, p.words.clone()));
    let items: Vec<ChildWitness<'_>> = (f.firsts.iter().zip(&statements))
        .map(|(p, statement)| ChildWitness {
            statement,
            raw: raw(p),
            columns: &f.tree.columns[Kind::First as usize],
        })
        .collect();
    let rows = d.node(&Witness::Prove {
        items: &items,
        tables: &f.tree.tables,
    });
    assert!(
        &proven_circuit(f, rows) == f.tree.circuit(Kind::Node),
        "the children build another circuit"
    );
}

// A fake first-level node's circuit: its leaves' outputs are free wires, its claims an honest statement's.
fn fake_first(tree: &Tree<'_>, honest: &TreeProof, outputs: &[[u64; 4]]) -> (Circuit, Assignment) {
    let mut b = Builder::new();
    let items: Vec<[Kw; 4]> = outputs.iter().map(|o| o.map(|w| b.free_k(w))).collect();
    let digest = Kind::First.digest_rows(&mut b, &items);
    let mut words = vec![b.e_const(F192::ZERO)];
    words.extend(digest_halves_rows(&mut b, digest));
    words.extend(
        honest.words[tree.design.statement.range(Section::Digest).end..]
            .iter()
            .map(|&w| b.free_e(w)),
    );
    for w in words {
        b.expose_e(w);
    }
    let Finished {
        mut circuit,
        assignment,
        failures,
    } = b.finish();
    assert!(failures.is_empty(), "{failures:?}");
    circuit.floor = tree.design.taus;
    (circuit, assignment)
}

// An honest node's rows over a child circuit the tree does not have hold, and only the root's settlement of the fixed polynomial refuses it.
#[test]
fn a_fake_child_circuit_is_refused_at_the_root() {
    let f = fixture();
    let d = &f.tree.design;
    let fake_outputs = [[0xdead, 1, 2, 3], [0xbeef, 4, 5, 6]];
    let (fake, assignment) = fake_first(&f.tree, &f.firsts[0], &fake_outputs);
    assert_eq!(fake.heights(), d.taus, "the fake has the nodes' heights");
    let words: Vec<F192> = (assignment.statement().iter())
        .map(|l| F192::new(l[0], l[1], l[2]))
        .collect();
    let child = TreeProof {
        kind: Kind::First,
        words,
        proof: fake.prove(&assignment, d.iv, d.rate).expect("the fake fits"),
        rate: d.rate,
    };
    assert!(
        f.tree.read(&child).is_err(),
        "natively, the fake is no first-level node"
    );
    let limbs: Vec<[u64; 4]> = child.words.iter().map(|w| [w.c0, w.c1, w.c2, 0]).collect();
    let raw = fake
        .verify_to_raw(&limbs, d.iv, d.rate, &child.proof)
        .expect("the fake proves its own circuit");

    // The prover hands the rows the fake's fixed columns, and its fixed polynomial the fake's half.
    let columns = FixedColumns::of(&fake, &d.taus);
    let mut tables = f.tree.tables.clone();
    tables.0[DensePoly::Fixed as usize] = d.fixed.polynomial([&columns, &f.tree.columns[Kind::Node as usize]]);
    let statement = TreeStatement::new(d.statement, child.words);
    let items: Vec<ChildWitness<'_>> = (0..2)
        .map(|_| ChildWitness {
            statement: &statement,
            raw: raw.clone(),
            columns: &columns,
        })
        .collect();
    let witness = |tables| Witness::Prove { items: &items, tables };
    let outputs = [fake_outputs, fake_outputs].concat();

    // An honest reduction over the tree's polynomials fails on the fake's hints.
    let honest = f.tree.prove_rows(d.node(&witness(&f.tree.tables)), Kind::Node);
    assert!(
        matches!(&honest, Err(TreeError::Unsatisfied(check)) if check.starts_with("reduction")),
        "{:?}",
        honest.map(|p| p.kind())
    );

    // Reduced over the forged polynomial, every row holds and the root's proof verifies.
    let rows = d.node(&witness(&tables));
    let reduction = rows.claim_values().prove(&d.vars, &tables);
    let reduction = RawProof {
        stream: reduction.stream,
        merkle: Vec::new(),
    };
    let Finished {
        assignment, failures, ..
    } = rows.reduce(d, ProofSource::Proof(&reduction));
    assert!(failures.is_empty(), "{failures:?}");
    let root = TreeProof {
        kind: Kind::Node,
        words: (assignment.statement().iter())
            .map(|l| F192::new(l[0], l[1], l[2]))
            .collect(),
        proof: (f.tree.circuit(Kind::Node).prove(&assignment, d.iv, d.rate)).expect("the node fits"),
        rate: d.rate,
    };
    f.tree.read(&root).expect("the root's recursion proof verifies");
    assert_eq!(
        f.tree.verify(&root, &outputs),
        Err(TreeError::Claim(FalseClaim::Dense(DensePoly::Fixed)))
    );
}

// Which of a reduction's outputs a forging prover moves along its final identity.
#[derive(Clone, Copy, Debug)]
enum Forge {
    Dense,
    Matrix,
}

// Move the first two values against each other along `sum_i weights_i values_i`, which stays as it was.
fn shift(values: &mut [F192], weights: &[F192]) {
    let delta = F192::new(1, 2, 3);
    values[0] += delta;
    values[1] += delta * weights[0] * weights[1].inv();
}

// The honest reduction of `claims`, its dense or its matrix outputs moved along their final identity.
fn forged_reduction(vars: &DenseVars, tables: &DenseTables, claims: &NodeClaims<F192>, forge: Forge) -> RawProof {
    let mut ps = ProverState::from_label(LABEL);
    ps.add_scalars(&claims.bound);

    let theta = ps.sample();
    let mut dense = DenseProver::new(vars, tables, &claims.dense, theta);
    let point: Vec<F192> = (0..dense.rounds())
        .map(|i| {
            ps.add_scalars(&dense.round(i));
            let r = ps.sample();
            dense.bind(i, r);
            r
        })
        .collect();
    let mut values = dense.finals();
    if matches!(forge, Forge::Dense) {
        let n_terms = claims.dense.iter().map(|c| c.terms.len()).sum();
        let powers = Native.powers(theta, n_terms);
        let weights: Vec<F192> = (vars.final_weights(&mut Native, &claims.dense, &powers, &point))
            .into_iter()
            .flatten()
            .collect();
        shift(&mut values, &weights);
    }
    ps.add_scalars(&values);

    let theta = ps.sample();
    let mut rows = MatrixProver::new(&claims.matrices, theta);
    let r: Vec<F192> = (0..crate::class_flock::max_k_log())
        .map(|i| {
            ps.add_scalars(&rows.round(i));
            let x = ps.sample();
            rows.bind(i, x);
            x
        })
        .collect();
    let mut cols = rows.columns(&claims.matrices, &r);
    let s: Vec<F192> = (0..crate::class_flock::max_k_log())
        .map(|i| {
            ps.add_scalars(&cols.round(i));
            let x = ps.sample();
            cols.bind(i, x);
            x
        })
        .collect();
    let mut values = cols.finals();
    if matches!(forge, Forge::Matrix) {
        let powers = Native.powers(theta, claims.matrices.len());
        let weights = MatrixReduced::final_weights(&mut Native, &claims.matrices, &powers, &r, &s);
        shift(&mut values, weights.as_flattened());
    }
    ps.add_scalars(&values);
    let proof = ps.into_proof();
    RawProof {
        stream: proof.stream,
        merkle: Vec::new(),
    }
}

// A first-level node whose reduction a cheating prover forged: its rows hold, its claims are false.
fn forged_first(f: &Fixture, forge: Forge) -> TreeProof {
    let d = &f.tree.design;
    let items: Vec<LeafWitness> = (f.leaves[..2].iter())
        .map(|(proof, output)| LeafWitness {
            raw: program().verify_to_raw(output, proof).expect("an honest leaf"),
            output: *output,
        })
        .collect();
    let rows = d.first(&Witness::Prove {
        items: &items,
        tables: &f.tree.tables,
    });
    let reduction = forged_reduction(&d.vars, &f.tree.tables, &rows.claim_values(), forge);
    let Finished {
        assignment, failures, ..
    } = rows.reduce(d, ProofSource::Proof(&reduction));
    assert!(failures.is_empty(), "{forge:?}: {failures:?}");
    TreeProof {
        kind: Kind::First,
        words: (assignment.statement().iter())
            .map(|l| F192::new(l[0], l[1], l[2]))
            .collect(),
        proof: (f.tree.circuit(Kind::First).prove(&assignment, d.iv, d.rate)).expect("the node fits"),
        rate: d.rate,
    }
}

// Reduced claims that satisfy every row and are false: the root refuses them, and an honest node cannot carry them.
#[test]
fn forged_reduced_claims_are_refused() {
    let f = fixture();
    let outputs = &f.outputs()[..2];
    for (forge, refusal) in [
        (Forge::Dense, FalseClaim::Dense(DensePoly::Bytecode)),
        (
            Forge::Matrix,
            FalseClaim::Matrix {
                table: crate::tables::ClassSpec::ALL[0].name,
                part: Part::Class,
            },
        ),
    ] {
        let forged = forged_first(f, forge);
        assert_eq!(
            f.tree.verify(&forged, outputs),
            Err(TreeError::Claim(refusal)),
            "{forge:?}"
        );
        let carried = f.tree.prove_node(&[forged, f.firsts[1].clone()]);
        assert!(
            matches!(&carried, Err(TreeError::Unsatisfied(check)) if check.starts_with("reduction")),
            "{forge:?}: {:?}",
            carried.map(|p| p.kind())
        );
    }
}

#[test]
fn tree_proof_bytes_round_trip() {
    let f = fixture();
    let bytes = f.root.to_bytes();
    assert_eq!(TreeProof::from_bytes(&bytes).as_ref(), Some(&f.root));
    for cut in [0, 1, 5, 29, bytes.len() / 2, bytes.len() - 1] {
        assert_eq!(TreeProof::from_bytes(&bytes[..cut]), None, "cut at {cut}");
    }
    assert_eq!(TreeProof::from_bytes(&[&bytes[..], &[0]].concat()), None);
    let mut kind = bytes.clone();
    kind[5] = 2;
    assert_eq!(TreeProof::from_bytes(&kind), None, "a kind that is no bit");
    let mut rate = bytes;
    rate[0] = 0;
    assert_eq!(TreeProof::from_bytes(&rate), None, "a rate out of range");
}

// Claims on three tables at random points, one of several terms with public bits, a kind bit and a scale.
fn dense_claims(rng: &mut Rng, tables: &DenseTables, vars: &DenseVars) -> Vec<DenseClaim<F192>> {
    let mut claims = Vec::new();
    for poly in DensePoly::ALL {
        let table = &tables.0[poly as usize];
        for _ in 0..2 {
            let point = rng.ext_vec(vars.0[poly as usize]);
            let value = mle_eval(table, &point);
            claims.push(DenseClaim::at(poly, point, None, value));
        }
    }
    let n = vars.0[DensePoly::Fixed as usize];
    let low = rng.ext_vec(n - 3);
    let term = |n_low: usize, bits: usize, top: u64, scale: F192| {
        let mut point = low[..n_low].to_vec();
        point.extend((0..n - 1 - n_low).map(|i| F192::new((bits >> i & 1) as u64, 0, 0)));
        point.push(F192::new(top, 0, 0));
        DenseTerm {
            n_low,
            bits: Bits {
                value: bits,
                len: n - 1 - n_low,
            },
            top: Some(F192::new(top, 0, 0)),
            scale: Some(scale),
            value: mle_eval(&tables.0[DensePoly::Fixed as usize], &point),
        }
    };
    claims.push(DenseClaim {
        poly: DensePoly::Fixed,
        low: low.clone(),
        terms: vec![
            term(n - 3, 1, 0, rng.ext()),
            term(n - 4, 2, 1, rng.ext()),
            term(n - 3, 0, 1, F192::ZERO),
        ],
    });
    claims
}

#[test]
fn the_dense_reduction_reduces_to_the_polynomials() {
    let mut rng = Rng::new(17);
    let vars = DenseVars([3, 6, 7]);
    let tables = DenseTables(vars.0.map(|n| (0..1 << n).map(|_| F64(rng.next_u64())).collect()));
    let claims = dense_claims(&mut rng, &tables, &vars);
    let prove = |claims: &[DenseClaim<F192>], forge: bool| {
        let mut ps = ProverState::from_label(LABEL);
        if forge {
            // A cheating prover: honest rounds, then values that meet the final identity of the claims as stated.
            let theta = ps.sample();
            let mut p = DenseProver::new(&vars, &tables, claims, theta);
            let n_terms = claims.iter().map(|c| c.terms.len()).sum();
            let powers = Native.powers(theta, n_terms);
            let terms = claims.iter().flat_map(|c| &c.terms);
            let mut claim = (terms.zip(&powers)).fold(F192::ZERO, |acc, (t, &w)| {
                acc + w * t.scale.unwrap_or(F192::ONE) * t.value
            });
            let point: Vec<F192> = (0..p.rounds())
                .map(|i| {
                    let [c0, c2] = p.round(i);
                    ps.add_scalars(&[c0, c2]);
                    let r = ps.sample();
                    claim = c0 + (claim + c2) * r + c2 * r * r;
                    p.bind(i, r);
                    r
                })
                .collect();
            let weights: Vec<F192> = vars
                .final_weights(&mut Native, claims, &powers, &point)
                .into_iter()
                .flatten()
                .collect();
            let mut values = p.finals();
            let rest = (values.iter().zip(&weights).skip(1)).fold(F192::ZERO, |acc, (&v, &w)| acc + v * w);
            values[0] = (claim + rest) * weights[0].inv();
            ps.add_scalars(&values);
        } else {
            DenseProver::prove(&mut ps, &vars, &tables, claims);
        }
        ps.into_proof()
    };
    let verify = |claims: &[DenseClaim<F192>], proof| {
        let mut vs = VerifierState::from_label(LABEL, proof);
        vars.verify(&mut vs, claims)
    };

    let proof = prove(&claims, false);
    let reduced = verify(&claims, &proof).expect("an honest reduction");
    for poly in DensePoly::ALL {
        let point = &reduced.point[..vars.0[poly as usize]];
        assert_eq!(
            reduced.values[poly as usize],
            Some(mle_eval(&tables.0[poly as usize], point)),
            "{poly:?}"
        );
    }

    // A false claim: the honest prover's reduction is refused, and a cheating prover's reduces it to a false value.
    let mut false_claims = claims;
    false_claims[6].terms[1].value += F192::ONE;
    assert_eq!(
        verify(&false_claims, &proof).err(),
        Some(super::reduce::ReduceError::Dense)
    );
    let forged = prove(&false_claims, true);
    let reduced = verify(&false_claims, &forged).expect("the forgery meets the final identity");
    let falsified = DensePoly::ALL.into_iter().filter(|&poly| {
        let point = &reduced.point[..vars.0[poly as usize]];
        reduced.values[poly as usize] != Some(mle_eval(&tables.0[poly as usize], point))
    });
    assert!(falsified.count() > 0, "a false claim reduced to true values");
}

// Each circuit's matrices at random points: a lincheck claim and both carried claims, on three circuits.
fn matrix_claims(rng: &mut Rng) -> Vec<MatrixClaim<F192>> {
    let k_skip = flock::zerocheck::K_SKIP;
    let mut claims = Vec::new();
    for f in [0, 3, crate::rec::table::HashFlock::index()] {
        let circuit = crate::class_flock::circuit(f);
        let k = circuit.k_log();
        let form = flock::lincheck::MatrixForm {
            alpha: rng.ext(),
            z_skip: rng.ext(),
            x_inner_rest: rng.ext_vec(k - k_skip),
            r_inner_rest: rng.ext_vec(k - k_skip),
            s_hat_v: rng.ext_vec(1 << k_skip),
        };
        let value = form.evaluate(circuit);
        claims.push(MatrixClaim::fresh(f, &crate::cpu::Claim { point: form, value }));
        let (rows, cols) = (rng.ext_vec(k), rng.ext_vec(k));
        let (ra, rb) = circuit.row_values(&eq_table(&cols));
        let u = eq_table(&rows);
        let dot = |r: &[F192]| u.iter().zip(r).fold(F192::ZERO, |acc, (&x, &y)| acc + x * y);
        claims.extend(MatrixClaim::carried(f, k, &rows, &cols, [dot(&ra), dot(&rb)]));
    }
    claims
}

#[test]
fn the_matrix_reduction_reduces_to_the_matrices() {
    let mut rng = Rng::new(9);
    let claims = matrix_claims(&mut rng);
    let prove = |claims: &[MatrixClaim<F192>]| {
        let mut ps = ProverState::from_label(LABEL);
        MatrixProver::prove(&mut ps, claims);
        ps.into_proof()
    };
    let verify = |claims: &[MatrixClaim<F192>], proof| {
        let mut vs = VerifierState::from_label(LABEL, proof);
        MatrixReduced::verify(&mut vs, claims)
    };
    let proof = prove(&claims);
    let reduced = verify(&claims, &proof).expect("an honest reduction");
    for (f, values) in reduced.values.iter().enumerate() {
        let circuit = crate::class_flock::circuit(f);
        let k = circuit.k_log();
        let (ra, rb) = circuit.row_values(&eq_table(&reduced.cols[..k]));
        let u = eq_table(&reduced.rows[..k]);
        let dot = |r: &[F192]| u.iter().zip(r).fold(F192::ZERO, |acc, (&x, &y)| acc + x * y);
        assert_eq!(*values, [dot(&ra), dot(&rb)], "circuit {f}");
    }
    for c in [0, 2] {
        let mut false_claims = claims.clone();
        false_claims[c].value += F192::ONE;
        assert_eq!(
            verify(&false_claims, &proof).err(),
            Some(super::reduce::ReduceError::Matrix),
            "claim {c}"
        );
    }
}
