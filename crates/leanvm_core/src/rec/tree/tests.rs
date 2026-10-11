use super::claims::{Bits, DenseClaim, DenseTerm, MatrixClaim, NodeClaims};
use super::reduce::{DenseProver, DenseVars, LABEL, MatrixProver, MatrixReduced, ReduceError};
use super::statement::{Section, digest_halves_rows};
use super::*;
use crate::cpu::{Claim, Prover};
use crate::rec::circuit::{Assignment, Builder, Kw};
use crate::rec::table::HashFlock;
use crate::rec::xmss::{XmssBatch, XmssClaim, XmssProof, XmssSignature};
use crate::rv::Region;
use crate::rv::asm::*;
use crate::tables::TableId;
use design::NodeRows;
use fiat_shamir::arith::{Arith, Native};
use fiat_shamir::transcript::{Challenger, ProverState, Transmitter, VerifierState};
use flock::lincheck::MatrixForm;
use leanxmss_host::{LEAF_INDEX, MESSAGE};
use primitives::multilinear::mle_eval;
use primitives::test_util::Rng;
use std::sync::LazyLock;

// A program whose output is its one advice word, after a loop that reads every framework block.
fn program() -> &'static Program {
    static PROGRAM: LazyLock<Program> = LazyLock::new(|| {
        let text = Asm::new()
            .li(Reg::T0, Region::ADVICE.base())
            .load(Ld, Reg::A0, 0, Reg::T0)
            .li(Reg::T1, 9)
            .label("loop")
            .i(Addi, Reg::T1, Reg::T1, -1)
            .branch(Bne, Reg::T1, Reg::ZERO, "loop")
            .exit()
            .finish();
        Program::new(&text, Region::TEXT.base(), vec![3, 5], 2, 0).expect("a valid program")
    });
    &PROGRAM
}

// The 2 to 1 shape at the lowest rate.
const PAIRS: TreeShape = TreeShape {
    arity_0: 2,
    arity: 2,
    rate: Rate::MIN,
};

// Four leaves of distinct outputs, a tree of first level 2 and arity 2 over them, and its proofs.
struct Fixture {
    tree: Tree<'static>,
    leaves: Vec<(Proof, Output)>,
    firsts: [TreeProof; 2],
    root: TreeProof,
}

fn runs(shape: LeafShape) -> Leaves<'static> {
    Leaves::Runs {
        program: program(),
        shape,
    }
}

fn fixture() -> &'static Fixture {
    static FIXTURE: LazyLock<Fixture> = LazyLock::new(|| {
        let leaves: Vec<(Proof, Output)> = (1..=4)
            .map(|advice| {
                let run = Prover::new(Rate::MIN)
                    .prove(program(), &[advice])
                    .expect("the run halts");
                (run.proof, run.output)
            })
            .collect();
        let shape = LeafShape::of(&leaves[0].0).expect("a canonical announcement");
        let tree = Tree::new(&[runs(shape)], PAIRS).expect("a tree");
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
    });
    &FIXTURE
}

impl Fixture {
    fn outputs(&self) -> Vec<Output> {
        self.leaves.iter().map(|l| l.1).collect()
    }

    fn statements(&self) -> Vec<LeafStatement> {
        self.leaves.iter().map(|l| l.1.into()).collect()
    }

    fn pairs(&self) -> Vec<Leaf<'_>> {
        self.leaves.iter().map(|(p, o)| Leaf::new(p, *o)).collect()
    }
}

// The balanced tree over these leaves' outputs.
fn balanced(outputs: &[Output], shape: &TreeShape) -> Result<Subtree, TreeError> {
    Subtree::balanced(outputs.iter().map(|&o| o.into()).collect(), shape)
}

#[test]
fn a_tree_verifies_and_binds_its_leaves_in_order() {
    let f = fixture();
    let outputs = f.outputs();
    assert_eq!((f.firsts[0].kind(), f.root.kind()), (Kind::First(0), Kind::Node));
    let verify = |root, outputs: &[Output]| f.tree.verify(root, &balanced(outputs, &PAIRS)?);
    verify(&f.root, &outputs).expect("the root");
    verify(&f.firsts[1], &outputs[2..]).expect("a first-level node is the root of its leaves");

    let mut wrong = outputs.clone();
    let [a0, a1, a2, a3] = *wrong[3].words();
    wrong[3] = Output::new([a0 ^ 1, a1, a2, a3]);
    assert_eq!(verify(&f.root, &wrong), Err(TreeError::Digest));
    let mut swapped = outputs.clone();
    swapped.swap(0, 1);
    assert_eq!(verify(&f.root, &swapped), Err(TreeError::Digest));
    assert_eq!(
        verify(&f.root, &outputs[..3]),
        Err(TreeError::LeafCount {
            leaves: 3,
            arity_0: 2,
            arity: 2
        })
    );
    assert_eq!(
        verify(&f.root, &outputs[..2]),
        Err(TreeError::Kind {
            expected: Kind::First(0),
            got: Kind::Node
        })
    );
}

#[test]
fn one_leaf_is_a_root() {
    let f = fixture();
    let shape = LeafShape::of(&f.leaves[0].0).expect("a canonical announcement");
    let single = TreeShape { arity_0: 1, ..PAIRS };
    let tree = Tree::new(&[runs(shape)], single).expect("a tree");
    let root = tree.prove(&f.pairs()[..1]).expect("an honest leaf");
    tree.verify(&root, &balanced(&[f.leaves[0].1], &single).expect("one leaf"))
        .expect("the root of one leaf");
    assert_eq!(
        tree.verify(&root, &balanced(&[f.leaves[1].1], &single).expect("one leaf")),
        Err(TreeError::Digest)
    );

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
            Tree::new(
                &[runs(shape)],
                TreeShape {
                    arity_0,
                    arity,
                    ..PAIRS
                }
            ),
            Err(TreeError::Arity { .. })
        ));
    }
    for families in [&[][..], &[runs(shape), runs(shape)]] {
        assert!(matches!(Tree::new(families, PAIRS), Err(TreeError::Families)));
    }
    assert_eq!(
        f.tree.prove_node(&f.firsts[..1]).map(|_| ()),
        Err(TreeError::Children { expected: 2, got: 1 })
    );

    // A leaf that does not verify, and one of another shape.
    let pairs = f.pairs();
    let mut forged = f.leaves[1].0.clone();
    let mid = forged.0.stream.len() / 2;
    forged.0.stream[mid] += F192::ONE;
    assert!(matches!(
        f.tree
            .prove_first(&[pairs[0].clone(), Leaf::new(&forged, f.leaves[1].1)]),
        Err(TreeError::Leaf { index: 1, .. })
    ));
    let ProvenRun {
        proof: longer, output, ..
    } = (Prover::new(Rate::new(2).expect("a rate")).prove(program(), &[7])).expect("the run halts");
    assert_eq!(
        f.tree
            .prove_first(&[Leaf::new(&longer, output), pairs[1].clone()])
            .map(|_| ()),
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

// A root over subtrees of two depths verifies against its own topology only.
#[test]
fn a_root_states_its_topology() {
    let f = fixture();
    let mixed = f
        .tree
        .prove_node(&[f.root.clone(), f.firsts[0].clone()])
        .expect("a node verifies any kind");
    let pairs = |o: &[Output]| Subtree::First(o.iter().map(|&o| o.into()).collect());
    let outputs = f.outputs();
    let topology = Subtree::Node(vec![
        balanced(&outputs, &PAIRS).expect("four leaves"),
        pairs(&outputs[..2]),
    ]);
    f.tree.verify(&mixed, &topology).expect("the root of its topology");
    let flipped = Subtree::Node(vec![
        pairs(&outputs[..2]),
        balanced(&outputs, &PAIRS).expect("four leaves"),
    ]);
    assert_eq!(f.tree.verify(&mixed, &flipped), Err(TreeError::Digest));
    let mut six = outputs.clone();
    six.extend_from_slice(&outputs[..2]);
    assert!(matches!(
        balanced(&six, &PAIRS),
        Err(TreeError::LeafCount { leaves: 6, .. })
    ));
}

// The reduction an honest prover proves, as its rows read it.
fn honest_reduction(tree: &Tree<'_>, rows: &NodeRows) -> RawProof {
    let proof = rows.claim_values().prove(&tree.design.vars, &tree.tables);
    RawProof {
        stream: proof.stream,
        merkle: Vec::new(),
    }
}

// The circuit a prover's rows build, at the nodes' heights.
fn proven_circuit(tree: &Tree<'_>, rows: NodeRows) -> Circuit {
    let reduction = honest_reduction(tree, &rows);
    let Finished {
        mut circuit, failures, ..
    } = rows.reduce(&tree.design, ProofSource::Proof(&reduction));
    assert!(failures.is_empty(), "{failures:?}");
    circuit.floor = tree.design.taus;
    circuit
}

#[test]
fn a_proven_circuit_is_the_shapes() {
    let f = fixture();
    let d = &f.tree.design;
    let leaves: Vec<LeafWitness> = (f.leaves[..2].iter())
        .map(|(proof, output)| LeafWitness {
            raw: program().verify_to_raw(*output, proof).expect("an honest leaf"),
            output: *output.words(),
        })
        .collect();
    let Family::Runs(shape) = &d.families[0] else {
        panic!("a tree of RISC-V proofs")
    };
    let rows = d.first_runs(
        Kind::First(0),
        shape,
        &NodeInputs::Prove {
            items: &leaves,
            tables: &f.tree.tables,
        },
    );
    assert!(
        &proven_circuit(&f.tree, rows) == f.tree.circuit(Kind::First(0)),
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
            columns: &f.tree.columns[Kind::First(0).code()],
        })
        .collect();
    let rows = d.node(&NodeInputs::Prove {
        items: &items,
        tables: &f.tree.tables,
    });
    assert!(
        &proven_circuit(&f.tree, rows) == f.tree.circuit(Kind::Node),
        "the children build another circuit"
    );
}

// A fake first-level node's circuit: its leaves' outputs are free wires, its claims an honest statement's.
fn fake_first(tree: &Tree<'_>, honest: &TreeProof, outputs: &[[u64; 4]]) -> (Circuit, Assignment) {
    let mut b = Builder::new();
    let items: Vec<[Kw; 4]> = outputs.iter().map(|o| o.map(|w| b.free_k(w))).collect();
    let digest = Level::Runs.digest_rows(&mut b, &items);
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

// A circuit's proof of its assignment's statement, as a tree proof of a kind.
fn tree_proof(tree: &Tree<'_>, kind: Kind, circuit: &Circuit, assignment: &Assignment) -> TreeProof {
    let d = &tree.design;
    TreeProof {
        kind,
        words: (assignment.statement().iter())
            .map(|l| F192::new(l[0], l[1], l[2]))
            .collect(),
        proof: circuit.prove(assignment, d.iv, d.rate).expect("the circuit fits"),
        rate: d.rate,
    }
}

// Reduce rows over the given tables, as a cheating prover holding them would, and prove the circuit of their kind.
fn proven_over(tree: &Tree<'_>, kind: Kind, rows: NodeRows, tables: &DenseTables) -> TreeProof {
    let d = &tree.design;
    let reduction = rows.claim_values().prove(&d.vars, tables);
    let reduction = RawProof {
        stream: reduction.stream,
        merkle: Vec::new(),
    };
    let Finished {
        assignment, failures, ..
    } = rows.reduce(d, ProofSource::Proof(&reduction));
    assert!(failures.is_empty(), "{failures:?}");
    tree_proof(tree, kind, tree.circuit(kind), &assignment)
}

// An honest node's rows over a child circuit the tree does not have hold, and only the root's settlement of the fixed polynomial refuses it.
#[test]
fn a_fake_child_circuit_is_refused_at_the_root() {
    let f = fixture();
    let d = &f.tree.design;
    let fake_outputs = [[0xdead, 1, 2, 3], [0xbeef, 4, 5, 6]];
    let (fake, assignment) = fake_first(&f.tree, &f.firsts[0], &fake_outputs);
    assert_eq!(fake.heights(), d.taus, "the fake has the nodes' heights");
    let child = tree_proof(&f.tree, Kind::First(0), &fake, &assignment);
    assert!(
        f.tree.read(&child).is_err(),
        "natively, the fake is no first-level node"
    );
    let limbs: Vec<[u64; 4]> = child.words.iter().map(|w| [w.c0, w.c1, w.c2, 0]).collect();
    let raw = fake
        .verify_to_raw(&limbs, d.iv, d.rate, &child.proof)
        .expect("the fake proves its own circuit");

    // The prover hands the rows the fake's fixed columns, and its fixed polynomial the fake's stack.
    let columns = FixedColumns::of(&fake, &d.taus);
    let mut tables = f.tree.tables.clone();
    tables.0[DensePoly::Fixed as usize] = d.node_polynomial(&[&columns, &f.tree.columns[Kind::Node.code()]]);
    let statement = TreeStatement::new(d.statement, child.words);
    let items: Vec<ChildWitness<'_>> = (0..2)
        .map(|_| ChildWitness {
            statement: &statement,
            raw: raw.clone(),
            columns: &columns,
        })
        .collect();
    let inputs = |tables| NodeInputs::Prove { items: &items, tables };
    let outputs: Vec<Output> = [fake_outputs, fake_outputs]
        .concat()
        .into_iter()
        .map(Output::new)
        .collect();

    // An honest reduction over the tree's polynomials fails on the fake's hints.
    let honest = f.tree.prove_rows(d.node(&inputs(&f.tree.tables)), Kind::Node);
    assert!(
        matches!(&honest, Err(TreeError::Unsatisfied(check)) if check.scope()[0] == "reduction"),
        "{:?}",
        honest.map(|p| p.kind())
    );

    // Reduced over the forged polynomial, every row holds and the root's proof verifies.
    let root = proven_over(&f.tree, Kind::Node, d.node(&inputs(&tables)), &tables);
    f.tree.read(&root).expect("the root's recursion proof verifies");
    assert_eq!(
        f.tree.verify(&root, &balanced(&outputs, &PAIRS).expect("four leaves")),
        Err(TreeError::Claim(FalseClaim::Dense(DensePoly::Fixed)))
    );
}

// Four signers' leanXMSS claims and signatures, one signature per batch, and each one's proof.
struct Signed {
    batch: XmssBatch,
    claims: Vec<XmssClaim>,
    proofs: Vec<XmssProof>,
}

fn signed() -> &'static Signed {
    static SIGNED: LazyLock<Signed> = LazyLock::new(|| {
        let batch = XmssBatch::new(1, Rate::MIN).expect("one signature fits");
        let (claims, proofs) = (leanxmss_host::signers(4).into_iter())
            .map(|(pk, s)| {
                let claim = XmssClaim {
                    public_param: pk.public_param,
                    merkle_root: pk.merkle_root,
                    epoch: LEAF_INDEX,
                    message: MESSAGE,
                };
                let signature = XmssSignature {
                    chain_tips: s.chain_tips,
                    randomness: s.randomness,
                    merkle_proof: s.merkle_proof,
                };
                let proof = batch.prove(&[claim], &[signature]).expect("an honest signature");
                (claim, proof)
            })
            .unzip();
        Signed { batch, claims, proofs }
    });
    &SIGNED
}

impl Signed {
    fn leaves(&self) -> Vec<Leaf<'_>> {
        (self.claims.iter().zip(&self.proofs))
            .map(|(c, p)| self.batch.leaf(&[*c], p).expect("one claim"))
            .collect()
    }

    fn statements(&self) -> Vec<LeafStatement> {
        (self.claims.iter())
            .map(|c| self.batch.statement(&[*c]).expect("one claim"))
            .collect()
    }
}

// A 2 to 1 tree over the leanXMSS proofs, its two first-level nodes and the node over them.
struct XmssTree {
    tree: Tree<'static>,
    firsts: [TreeProof; 2],
    node: TreeProof,
}

fn xmss_tree() -> &'static XmssTree {
    static TREE: LazyLock<XmssTree> = LazyLock::new(|| {
        let s = signed();
        let tree = Tree::new(&[s.batch.leaves()], PAIRS).expect("a tree");
        let leaves = s.leaves();
        let firsts = [0, 2].map(|i| tree.prove_first(&leaves[i..i + 2]).expect("honest leaves"));
        let node = tree.prove_node(&firsts).expect("honest children");
        XmssTree { tree, firsts, node }
    });
    &TREE
}

#[test]
fn an_xmss_tree_binds_its_statements() {
    let (s, x) = (signed(), xmss_tree());
    let statements = s.statements();
    let leaves = s.leaves();
    assert_eq!(x.tree.kinds(), [Kind::First(0), Kind::Node]);
    assert_eq!((x.firsts[0].kind(), x.node.kind()), (Kind::First(0), Kind::Node));
    let four = Subtree::balanced(statements.clone(), &PAIRS).expect("four leaves");
    x.tree.verify(&x.node, &four).expect("the node");
    x.tree
        .verify(&x.firsts[1], &Subtree::First(statements[2..].to_vec()))
        .expect("a first-level node is the root of its leaves");

    // A node over nodes.
    let root = x
        .tree
        .prove_node(&[x.node.clone(), x.node.clone()])
        .expect("honest children");
    x.tree
        .verify(&root, &Subtree::Node(vec![four.clone(), four]))
        .expect("the root over two nodes");

    // Mutation: one claim's message, or two leaves swapped.
    //
    //     the leaves' statements' hashes are the first-level digest's items
    //     → another digest
    let mut changed = s.claims[3];
    changed.message[0] ^= 1;
    let mut forged = statements.clone();
    forged[3] = s.batch.statement(&[changed]).expect("one claim");
    let verify = |leaves: Vec<LeafStatement>| x.tree.verify(&x.node, &Subtree::balanced(leaves, &PAIRS)?);
    assert_eq!(verify(forged), Err(TreeError::Digest));
    let mut swapped = statements;
    swapped.swap(0, 1);
    assert_eq!(verify(swapped), Err(TreeError::Digest));
    let outputs = vec![LeafStatement::from(Output::new([0; 4])); 4];
    assert_eq!(verify(outputs), Err(TreeError::ForeignLeaf { index: 0 }));

    // A leaf whose claims are not its proof's.
    let wrong = s.batch.leaf(&[changed], &s.proofs[3]).expect("one claim");
    assert!(matches!(
        x.tree.prove_first(&[leaves[0].clone(), wrong]),
        Err(TreeError::Leaf { index: 1, .. })
    ));
    // A leaf of another batch size.
    let pair = XmssBatch::new(2, Rate::MIN).expect("two signatures fit");
    let other = pair.leaf(&s.claims[..2], &s.proofs[0]).expect("two claims");
    assert_eq!(
        x.tree.prove_first(&[leaves[0].clone(), other]).map(|_| ()),
        Err(TreeError::ForeignLeaf { index: 1 })
    );
}

#[test]
fn a_four_to_one_xmss_tree_verifies() {
    let s = signed();
    let shape = TreeShape {
        arity_0: 4,
        arity: 4,
        rate: Rate::MIN,
    };
    let tree = Tree::new(&[s.batch.leaves()], shape).expect("a tree");
    let first = tree.prove_first(&s.leaves()).expect("honest leaves");
    let leaves = Subtree::First(s.statements());
    tree.verify(&first, &leaves).expect("a first-level root");
    let node = tree.prove_node(&vec![first; 4]).expect("honest children");
    tree.verify(&node, &Subtree::Node(vec![leaves; 4])).expect("the node");
}

// An honest first-level node's rows over a leaf circuit the tree does not have hold, and only the root's settlement of the
// leaves' fixed polynomial refuses it: its leaves state forged claims no signature backs.
#[test]
fn a_fake_leaf_circuit_is_refused_at_the_root() {
    let (s, x) = (signed(), xmss_tree());
    let d = &x.tree.design;
    let Family::Circuit(family) = &d.families[0] else {
        panic!("a tree of leanXMSS proofs")
    };
    let leaf = &family.leaf;
    let kind = Kind::First(0);

    // The honest leaves' rows build the tree's circuit.
    let honest: Vec<CircuitWitness<'_>> = (s.claims[..2].iter().zip(&s.proofs))
        .map(|(c, p)| {
            let Leaf(LeafProof::Circuit { statement, proof, .. }) = s.batch.leaf(&[*c], p).expect("one claim") else {
                panic!("a circuit's leaf")
            };
            CircuitWitness {
                raw: (leaf
                    .circuit
                    .verify_to_raw_with(&statement, leaf.iv, leaf.rate, proof, leaf.columns))
                .expect("an honest leaf"),
                statement,
                columns: leaf.columns,
            }
        })
        .collect();
    let inputs = NodeInputs::Prove {
        items: &honest,
        tables: &x.tree.tables,
    };
    assert!(
        &proven_circuit(&x.tree, d.first_circuit(kind, family, &inputs)) == x.tree.circuit(kind),
        "the leaves build another circuit"
    );

    // A fake circuit of the leaves' heights stating a forged claim.
    let mut forged = s.claims[0];
    forged.merkle_root[0] ^= 1;
    let statement = s.batch.statement(&[forged]).expect("one claim");
    let LeafStatement(Stated::Circuit { words, .. }) = &statement else {
        panic!("a circuit's statement")
    };
    let mut b = Builder::new();
    for w in words {
        let wire = b.free_e(F192::new(w[0], w[1], w[2]));
        b.expose_e(wire);
    }
    let Finished {
        mut circuit,
        assignment,
        failures,
    } = b.finish();
    assert!(failures.is_empty(), "{failures:?}");
    circuit.floor = leaf.circuit.heights();
    assert_eq!(
        circuit.heights(),
        leaf.circuit.heights(),
        "the fake has the leaves' heights"
    );
    let proof = circuit.prove(&assignment, leaf.iv, leaf.rate).expect("the fake fits");
    assert!(
        (leaf
            .circuit
            .verify_to_raw_with(words, leaf.iv, leaf.rate, &proof, leaf.columns))
        .is_err(),
        "natively, the fake is no leanXMSS proof"
    );
    let columns = FixedColumns::of(&circuit, &leaf.circuit.heights());
    let raw = circuit
        .verify_to_raw(words, leaf.iv, leaf.rate, &proof)
        .expect("the fake proves its own circuit");
    let items: Vec<CircuitWitness<'_>> = (0..2)
        .map(|_| CircuitWitness {
            statement: words.clone(),
            raw: raw.clone(),
            columns: &columns,
        })
        .collect();
    let mut tables = x.tree.tables.clone();
    tables.0[DensePoly::Leaf as usize] = d.leaf_polynomial(&[&columns]);
    let inputs = |tables| NodeInputs::Prove { items: &items, tables };

    // An honest reduction over the tree's polynomials fails on the fake's hints.
    let honest = x
        .tree
        .prove_rows(d.first_circuit(kind, family, &inputs(&x.tree.tables)), kind);
    assert!(
        matches!(&honest, Err(TreeError::Unsatisfied(check)) if check.scope()[0] == "reduction"),
        "{:?}",
        honest.map(|p| p.kind())
    );

    // Reduced over the forged polynomial, every row holds and the root's proof verifies.
    let root = proven_over(&x.tree, kind, d.first_circuit(kind, family, &inputs(&tables)), &tables);
    x.tree.read(&root).expect("the root's recursion proof verifies");
    let expected = Subtree::First(vec![statement.clone(), statement]);
    assert_eq!(
        x.tree.verify(&root, &expected),
        Err(TreeError::Claim(FalseClaim::Dense(DensePoly::Leaf)))
    );
    // A node carrying the fake's claims cannot reduce them honestly.
    assert!(matches!(
        x.tree.prove_node(&[root, x.firsts[1].clone()]),
        Err(TreeError::Unsatisfied(check)) if check.scope()[0] == "reduction"
    ));
}

// A tree of two leaf families: RISC-V proofs and leanXMSS proofs, one node over a first-level node of each.
#[test]
fn a_mixed_tree_verifies_against_its_topology() {
    let (f, s) = (fixture(), signed());
    let shape = LeafShape::of(&f.leaves[0].0).expect("a canonical announcement");
    let tree = Tree::new(&[runs(shape), s.batch.leaves()], PAIRS).expect("a tree");
    assert_eq!(tree.kinds(), [Kind::First(0), Kind::Node, Kind::First(1)]);
    let runs_first = tree.prove_first(&f.pairs()[..2]).expect("honest RISC-V leaves");
    let xmss_first = tree.prove_first(&s.leaves()[..2]).expect("honest leanXMSS leaves");
    assert_eq!((runs_first.kind(), xmss_first.kind()), (Kind::First(0), Kind::First(1)));
    let (outputs, statements) = (
        Subtree::First(f.statements()[..2].to_vec()),
        Subtree::First(s.statements()[..2].to_vec()),
    );
    tree.verify(&xmss_first, &statements)
        .expect("a first-level root of leanXMSS proofs");
    tree.verify(&runs_first, &outputs)
        .expect("a first-level root of RISC-V proofs");

    let root = tree
        .prove_node(&[runs_first, xmss_first.clone()])
        .expect("a node over both families");
    let topology = Subtree::Node(vec![outputs.clone(), statements.clone()]);
    tree.verify(&root, &topology).expect("the mixed root");
    assert_eq!(
        tree.verify(&root, &Subtree::Node(vec![statements.clone(), outputs])),
        Err(TreeError::Digest)
    );
    let up = tree.prove_node(&[root, xmss_first]).expect("a node over a node");
    tree.verify(&up, &Subtree::Node(vec![topology, statements]))
        .expect("a root over both depths");

    // A tree of RISC-V proofs only has no kind for a leanXMSS first-level node.
    assert_eq!(
        f.tree
            .prove_node(&[
                f.firsts[0].clone(),
                tree.prove_first(&s.leaves()[2..]).expect("honest leaves")
            ])
            .map(|_| ()),
        Err(TreeError::ForeignChild { index: 1 })
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
            ps.add_scalars(&dense.message());
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
    let r: Vec<F192> = (0..FlockId::MAX_K_LOG)
        .map(|i| {
            ps.add_scalars(&rows.message());
            let x = ps.sample();
            rows.bind(i, x);
            x
        })
        .collect();
    let mut cols = rows.columns(&claims.matrices, &r);
    let s: Vec<F192> = (0..FlockId::MAX_K_LOG)
        .map(|i| {
            ps.add_scalars(&cols.message());
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
            raw: program().verify_to_raw(*output, proof).expect("an honest leaf"),
            output: *output.words(),
        })
        .collect();
    let Family::Runs(shape) = &d.families[0] else {
        panic!("a tree of RISC-V proofs")
    };
    let rows = d.first_runs(
        Kind::First(0),
        shape,
        &NodeInputs::Prove {
            items: &items,
            tables: &f.tree.tables,
        },
    );
    let reduction = forged_reduction(&d.vars, &f.tree.tables, &rows.claim_values(), forge);
    let Finished {
        assignment, failures, ..
    } = rows.reduce(d, ProofSource::Proof(&reduction));
    assert!(failures.is_empty(), "{forge:?}: {failures:?}");
    tree_proof(&f.tree, Kind::First(0), f.tree.circuit(Kind::First(0)), &assignment)
}

// Reduced claims that satisfy every row and are false: the root refuses them, and an honest node cannot carry them.
#[test]
fn forged_reduced_claims_are_refused() {
    let f = fixture();
    let outputs = balanced(&f.outputs()[..2], &PAIRS).expect("two leaves");
    for (forge, refusal) in [
        (Forge::Dense, FalseClaim::Dense(DensePoly::Bytecode)),
        (
            Forge::Matrix,
            FalseClaim::Matrix {
                table: TableId::ALU.name(),
                part: Part::Class,
            },
        ),
    ] {
        let forged = forged_first(f, forge);
        assert_eq!(
            f.tree.verify(&forged, &outputs),
            Err(TreeError::Claim(refusal)),
            "{forge:?}"
        );
        let carried = f.tree.prove_node(&[forged, f.firsts[1].clone()]);
        assert!(
            matches!(&carried, Err(TreeError::Unsatisfied(check)) if check.scope()[0] == "reduction"),
            "{forge:?}: {:?}",
            carried.map(|p| p.kind())
        );
    }
}

#[test]
fn tree_proof_bytes_round_trip() {
    let f = fixture();
    let bytes = f.root.to_bytes();
    assert_eq!(TreeProof::from_bytes(&bytes).as_ref(), Ok(&f.root));

    // Cuts inside the header, inside the body's prefix, and inside the recursion proof.
    for cut in [0, 1, 5, 6, 11, 35, bytes.len() / 2, bytes.len() - 1] {
        assert_eq!(
            TreeProof::from_bytes(&bytes[..cut]),
            Err(DecodeError::Malformed),
            "cut at {cut}"
        );
    }
    assert_eq!(
        TreeProof::from_bytes(&[&bytes[..], &[0]].concat()),
        Err(DecodeError::Malformed)
    );

    // The body starts after the 6-byte header.
    //
    //     | header: 6 | rate: 1 | n_words: 4 | kind word: c0 c1 c2 ...
    //     byte 6 = the rate, bytes 11, 19 = the kind word's first and second limbs' low bytes
    let mut kind = bytes.clone();
    kind[11] = 2;
    assert_eq!(
        TreeProof::from_bytes(&kind).map(|p| p.kind()),
        Ok(Kind::First(1)),
        "a code past this tree's kinds decodes, and the tree refuses it"
    );
    kind[19] = 1;
    assert_eq!(
        TreeProof::from_bytes(&kind),
        Err(DecodeError::Malformed),
        "a kind word that is no code"
    );
    let mut rate = bytes;
    rate[6] = 0;
    assert_eq!(
        TreeProof::from_bytes(&rate),
        Err(DecodeError::Malformed),
        "a rate out of range"
    );
}

// Claims on four tables at random points, one of several terms with public bits, two kind bits and a scale.
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
    let term = |n_low: usize, bits: usize, top: usize, scale: F192| {
        let bit = |x: usize, i: usize| F192::new((x >> i & 1) as u64, 0, 0);
        let top: Vec<F192> = (0..2).map(|i| bit(top, i)).collect();
        let mut point = low[..n_low].to_vec();
        point.extend((0..n - 2 - n_low).map(|i| bit(bits, i)));
        point.extend(&top);
        DenseTerm {
            n_low,
            bits: Bits {
                value: bits,
                len: n - 2 - n_low,
            },
            top,
            scale: Some(scale),
            value: mle_eval(&tables.0[DensePoly::Fixed as usize], &point),
        }
    };
    claims.push(DenseClaim {
        poly: DensePoly::Fixed,
        low: low.clone(),
        terms: vec![
            term(n - 3, 1, 0, rng.ext()),
            term(n - 4, 2, 3, rng.ext()),
            term(n - 3, 0, 2, F192::ZERO),
        ],
    });
    claims
}

#[test]
fn the_dense_reduction_reduces_to_the_polynomials() {
    let mut rng = Rng::new(17);
    let vars = DenseVars([3, 6, 5, 7]);
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
                    let [c0, c2] = p.message();
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
    false_claims[8].terms[1].value += F192::ONE;
    assert_eq!(verify(&false_claims, &proof).err(), Some(ReduceError::Dense));
    let forged = prove(&false_claims, true);
    let reduced = verify(&false_claims, &forged).expect("the forgery meets the final identity");
    let falsified = DensePoly::ALL.into_iter().filter(|&poly| {
        let point = &reduced.point[..vars.0[poly as usize]];
        reduced.values[poly as usize] != Some(mle_eval(&tables.0[poly as usize], point))
    });
    assert!(falsified.count() > 0, "a false claim reduced to true values");
}

// A claim on `poly` whose terms each weigh one block: `(n_low, bits)` names the `2^n_low` entries at `bits << n_low`.
fn block_claim(
    rng: &mut Rng,
    tables: &DenseTables,
    vars: &DenseVars,
    poly: DensePoly,
    blocks: &[(usize, usize)],
) -> DenseClaim<F192> {
    let n = vars.0[poly as usize];
    let low = rng.ext_vec(n);
    let mut terms = Vec::new();
    for &(n_low, bits) in blocks {
        let mut point = low[..n_low].to_vec();
        point.extend((0..n - n_low).map(|i| F192::new((bits >> i & 1) as u64, 0, 0)));
        terms.push(DenseTerm {
            n_low,
            bits: Bits {
                value: bits,
                len: n - n_low,
            },
            top: Vec::new(),
            scale: Some(rng.ext()),
            value: mle_eval(&tables.0[poly as usize], &point),
        });
    }
    DenseClaim { poly, low, terms }
}

#[test]
fn the_dense_reduction_reduces_claims_on_a_prefix() {
    // Weights zero past a prefix whose length is odd at several rounds, so the prover evaluates the table past it. The
    // blocks of the image and the fixed polynomial have one or two low points, so their weights stay factored for a few
    // rounds; the bytecode's has three, written out at once.
    let mut rng = Rng::new(23);
    let vars = DenseVars([3, 5, 6, 14]);
    let tables = DenseTables(vars.0.map(|n| (0..1 << n).map(|_| F64(rng.next_u64())).collect()));
    let mut claims: Vec<DenseClaim<F192>> = (0..3)
        .map(|_| {
            let point = rng.ext_vec(3);
            let value = mle_eval(&tables.0[DensePoly::Bytecode as usize], &point);
            DenseClaim::at(DensePoly::Bytecode, point, None, value)
        })
        .collect();
    claims.push(block_claim(&mut rng, &tables, &vars, DensePoly::Image, &[(1, 2)]));
    claims.push(block_claim(
        &mut rng,
        &tables,
        &vars,
        DensePoly::Leaf,
        &[(3, 5), (1, 3)],
    ));
    claims.push(block_claim(
        &mut rng,
        &tables,
        &vars,
        DensePoly::Fixed,
        &[(2, 0xAAA), (5, 7), (2, 0xAAA)],
    ));
    claims.push(block_claim(&mut rng, &tables, &vars, DensePoly::Fixed, &[(5, 7)]));
    let mut ps = ProverState::from_label(LABEL);
    DenseProver::prove(&mut ps, &vars, &tables, &claims);
    let proof = ps.into_proof();
    let mut vs = VerifierState::from_label(LABEL, &proof);
    let reduced = vars.verify(&mut vs, &claims).expect("an honest reduction");
    for poly in DensePoly::ALL {
        let point = &reduced.point[..vars.0[poly as usize]];
        assert_eq!(
            reduced.values[poly as usize],
            Some(mle_eval(&tables.0[poly as usize], point)),
            "{poly:?}"
        );
    }
}

// Each circuit's matrices at random points: lincheck claims and both carried claims, on three circuits.
//
// The lincheck claims share their points as one batch leaves them: one alpha and one skip point, the other coordinates
// prefixes of shared ones; circuit 0 has a second claim at its first's point with other slices.
fn matrix_claims(rng: &mut Rng) -> Vec<MatrixClaim<F192>> {
    let k_skip = flock::zerocheck::K_SKIP;
    let (alpha, z_skip) = (rng.ext(), rng.ext());
    let (x, r) = (rng.ext_vec(16), rng.ext_vec(16));
    let mut claims = Vec::new();
    let first = FlockId::ALL[0];
    for (i, f) in [first, first, FlockId::ALL[3], HashFlock::FLOCK]
        .into_iter()
        .enumerate()
    {
        let circuit = f.circuit();
        let k = circuit.k_log();
        let form = MatrixForm {
            alpha,
            z_skip,
            x_inner_rest: x[..k - k_skip].to_vec(),
            r_inner_rest: r[..k - k_skip].to_vec(),
            s_hat_v: rng.ext_vec(1 << k_skip),
        };
        let value = form.evaluate(circuit);
        claims.push(MatrixClaim::fresh(f, &Claim { point: form, value }));
        if i == 0 {
            continue;
        }
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
    for (f, values) in FlockId::ALL.into_iter().zip(&reduced.values) {
        let circuit = f.circuit();
        let k = circuit.k_log();
        let (ra, rb) = circuit.row_values(&eq_table(&reduced.cols[..k]));
        let u = eq_table(&reduced.rows[..k]);
        let dot = |r: &[F192]| u.iter().zip(r).fold(F192::ZERO, |acc, (&x, &y)| acc + x * y);
        assert_eq!(*values, [dot(&ra), dot(&rb)], "{f:?}");
    }
    for c in [0, 2] {
        let mut false_claims = claims.clone();
        false_claims[c].value += F192::ONE;
        assert_eq!(
            verify(&false_claims, &proof).err(),
            Some(ReduceError::Matrix),
            "claim {c}"
        );
    }
}
