//! An aggregation tree: its key, its prover and its verifier.

use super::{CircuitStats, Kind, Leaf, LeafShape, TableStats, TreeError, TreeProof};
use crate::{Output, Program, Rate};
use leanvm_core::rec::table::Table;
use leanvm_core::rec::tree;

/// How a tree is shaped.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TreeShape {
    /// The shape every leaf proof shares.
    pub leaf: LeafShape,
    /// The leaf proofs a first-level node verifies, at least one.
    pub arity_0: usize,
    /// The tree proofs a higher node verifies, at least two.
    pub arity: usize,
    /// The commitment rate of every tree proof.
    pub rate: Rate,
}

/// An aggregation tree over proofs of one program.
///
/// It is the tree's verifying key, and what its prover needs.
///
/// It is built from the program and the shape alone, before any proof exists.
pub struct Tree<'p>(tree::Tree<'p>);

impl<'p> Tree<'p> {
    /// The tree over proofs of a program, shaped as given.
    ///
    /// # Errors
    ///
    /// - Arities that make no tree: a first level of no leaf, or nodes of fewer than two children.
    /// - A leaf shape no proof of the program has.
    /// - Circuits too large for one commitment.
    pub fn new(program: &'p Program, shape: TreeShape) -> Result<Self, TreeError> {
        // The recursion machine checks the arities, then builds both kinds of node's circuits.
        let TreeShape {
            leaf,
            arity_0,
            arity,
            rate,
        } = shape;
        tree::Tree::new(&program.0, leaf.0, arity_0, arity, rate).map(Self)
    }

    /// Prove a first-level node over its leaves, in order.
    ///
    /// # Errors
    ///
    /// - The wrong number of leaves.
    /// - A leaf of another shape.
    /// - A leaf that does not verify.
    pub fn prove_first(&self, leaves: &[Leaf<'_>]) -> Result<TreeProof, TreeError> {
        // A leaf is a reference and four words, so the copy is cheap.
        let leaves: Vec<_> = leaves.iter().map(|leaf| leaf.as_core()).collect();
        self.0.prove_first(&leaves).map(TreeProof)
    }

    /// Prove a higher node over its children, in order.
    ///
    /// # Errors
    ///
    /// - The wrong number of children.
    /// - A child that does not verify.
    pub fn prove_node(&self, children: &[TreeProof]) -> Result<TreeProof, TreeError> {
        // Why: the recursion machine takes its own proofs by slice.
        // So each child is copied out of its wrapper.
        // A proof is small next to the node's proving work.
        let children: Vec<_> = children.iter().map(|child| child.0.clone()).collect();
        self.0.prove_node(&children).map(TreeProof)
    }

    /// Prove the whole tree over its leaves, in order, up to the root.
    ///
    /// # Errors
    ///
    /// - A leaf count no tree of these arities has.
    /// - A leaf the first level refuses.
    pub fn prove(&self, leaves: &[Leaf<'_>]) -> Result<TreeProof, TreeError> {
        // The first level, then each level of nodes, up to the root.
        let leaves: Vec<_> = leaves.iter().map(|leaf| leaf.as_core()).collect();
        self.0.prove(&leaves).map(TreeProof)
    }

    /// Check that a root proves every leaf of the tree, with these outputs in this order.
    ///
    /// # Errors
    ///
    /// The first check that refuses:
    ///
    /// - the root's kind or rate,
    /// - its proof,
    /// - its digest of the outputs,
    /// - a claim it carries.
    pub fn verify(&self, root: &TreeProof, outputs: &[Output]) -> Result<(), TreeError> {
        // The root's digest is over the outputs' words, in leaf order.
        let outputs: Vec<[u64; 4]> = outputs.iter().map(|output| *output.words()).collect();
        self.0.verify(&root.0, &outputs)
    }

    /// What the circuit of one kind of node costs.
    #[must_use]
    pub fn stats(&self, kind: Kind) -> CircuitStats {
        // The circuit's rows per table, and the padded heights it is proven at.
        let circuit = self.0.circuit(kind);
        let (rows, heights) = (circuit.row_counts(), circuit.heights());

        // One entry per table of the recursion machine, in its order.
        let tables = (Table::ALL.iter())
            .map(|&table| TableStats {
                name: table.name(),
                rows: rows[table as usize],
                height_log: heights[table as usize],
            })
            .collect();

        // Invariant: building the tree refused any circuit that fits no commitment.
        let committed = circuit.committed_words().expect("a tree's circuits fit one commitment");
        CircuitStats { tables, committed }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ProvenRun, Prover, fixtures};

    #[test]
    fn a_root_states_its_leaves_outputs_in_order() {
        // Two runs of the preimage guest, on two messages, so the leaves' outputs differ.
        let prover = Prover::new(Rate::MIN);
        let (guest, advice, _) = fixtures::preimage(b"leanVM");
        let runs: Vec<ProvenRun> = [b"leanVM".as_slice(), b"LEANvm"]
            .into_iter()
            .map(|message| {
                let (_, advice, _) = fixtures::preimage(message);
                prover.prove(&guest, &advice).expect("the run exits")
            })
            .collect();
        let outputs = [runs[0].output, runs[1].output];
        assert_ne!(outputs[0], outputs[1]);

        // A tree's key needs no proof: a measured run gives the shape its proof announces.
        let leaf = LeafShape::of(&runs[0].proof).expect("an announced shape");
        let measured = guest.measure(&advice).expect("the run exits");
        assert_eq!(LeafShape::measured(&measured, Rate::MIN), leaf);

        // One first-level node over both leaves: it is the root.
        //
        //     root (first-level)
        //       /        \
        //   "leanVM"   "LEANvm"
        let shape = TreeShape {
            leaf,
            arity_0: 2,
            arity: 2,
            rate: Rate::MIN,
        };
        let tree = Tree::new(&guest, shape).expect("a tree");
        let leaves: Vec<Leaf<'_>> = runs.iter().map(Leaf::from).collect();
        let root = tree.prove(&leaves).expect("honest leaves");
        assert_eq!(root.kind(), Kind::First);

        // The root survives its bytes.
        let root = TreeProof::from_bytes(&root.to_bytes()).expect("a tree proof's own bytes");
        tree.verify(&root, &outputs).unwrap();

        // The digest binds the order: the same outputs swapped are refused.
        assert_eq!(tree.verify(&root, &[outputs[1], outputs[0]]), Err(TreeError::Outputs));
    }

    #[test]
    fn arities_that_make_no_tree_are_refused() {
        // Fixture state: a valid leaf shape, so only the arities can be at fault.
        let program = fixtures::fibonacci(90);
        let leaf = LeafShape::of(&fixtures::fibonacci_run().proof).expect("an announced shape");

        //     arity_0 = 0  → a first-level node over no leaf
        //     arity   = 1  → a node that only copies its child
        for (arity_0, arity) in [(0, 2), (1, 1)] {
            let shape = TreeShape {
                leaf,
                arity_0,
                arity,
                rate: Rate::MIN,
            };
            assert!(matches!(Tree::new(&program, shape), Err(TreeError::Arity { .. })));
        }
    }
}
