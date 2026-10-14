//! A claim-set tree is its leaf program's: a leanXMSS tree and a leanSPHINCS tree never take each other's leaves,
//! aggregates or roots, so the two schemes' claims never mix.

use leanvm::aggregate::{
    Aggregate, Capacity, ClaimGroup, ClaimLeaf, ClaimSet, ClaimShape, Leaf, LeafShape, Leaves, Tree, TreeError,
    TreeShape,
};
use leanvm::{Program, ProvenRun, Prover, Rate};

const CAPACITY: Capacity = Capacity { claims: 8, groups: 2 };

/// The claim set a tree takes for a program's signer set, from its label groups.
fn claim_set(groups: Vec<([u64; 6], Vec<[u64; 4]>)>) -> ClaimSet {
    ClaimSet {
        groups: (groups.into_iter())
            .map(|(label, members)| ClaimGroup { label, members })
            .collect(),
    }
}

#[test]
fn leanxmss_and_leansphincs_trees_do_not_combine() {
    let (xmss, sphincs) = (leanxmss_host::batch(2), leansphincs_host::batch(2));
    let programs = [leanxmss_host::ELF, leansphincs_host::ELF].map(|elf| Program::from_elf(elf).expect("an ELF file"));
    let sets = [
        claim_set(xmss.set.label_groups()),
        claim_set(sphincs.set.label_groups()),
    ];
    let advice = [&xmss.run.advice, &sphincs.run.advice];
    let prover = Prover::new(Rate::MIN);
    let runs: Vec<ProvenRun> = (programs.iter().zip(advice))
        .map(|(program, advice)| prover.prove(program, advice).expect("an honest run"))
        .collect();
    let trees: Vec<Tree<'_>> = (programs.iter().zip(&runs))
        .map(|(program, run)| {
            let leaves = Leaves::Runs {
                program,
                shape: LeafShape::of(&run.proof).expect("a canonical announcement"),
            };
            let shape = TreeShape {
                arity_0: 1,
                arity: 2,
                rate: Rate::MIN,
                claims: Some(ClaimShape::new(CAPACITY)),
            };
            Tree::new(leaves, shape).expect("a tree")
        })
        .collect();
    let firsts: Vec<Aggregate> = (0..2)
        .map(|i| {
            let leaf = ClaimLeaf::new(Leaf::from(&runs[i]), &sets[i]);
            trees[i].aggregate_leaves(&[leaf], None).expect("an honest leaf")
        })
        .collect();
    // A node of one child, its other place absent.
    let nodes: Vec<Aggregate> = (0..2)
        .map(|i| trees[i].aggregate(&[&firsts[i]], None).expect("an honest child"))
        .collect();

    for (i, j) in [(0, 1), (1, 0)] {
        let tree = &trees[i];
        tree.verify_claims(&nodes[i].proof, &nodes[i].claims)
            .expect("its own root");
        // The other scheme's leaf, with its own set.
        let leaf = ClaimLeaf::new(Leaf::from(&runs[j]), &sets[j]);
        let refused = tree.aggregate_leaves(&[leaf], None);
        assert!(
            matches!(
                refused,
                Err(TreeError::ForeignLeaf { index: 0 } | TreeError::Leaf { index: 0, .. })
            ),
            "{refused:?}"
        );
        // The other scheme's first-level aggregate and node: not children, alone or beside one of this tree's, and
        // not this tree's roots.
        for child in [&firsts[j], &nodes[j]] {
            let refused = tree.aggregate(&[child], None);
            assert!(
                matches!(refused, Err(TreeError::Child { index: 0, .. } | TreeError::Circuit(_))),
                "{refused:?}"
            );
            let refused = tree.aggregate(&[&firsts[i], child], None);
            assert!(
                matches!(refused, Err(TreeError::Child { index: 1, .. } | TreeError::Circuit(_))),
                "{refused:?}"
            );
            let refused = tree.verify_claims(&child.proof, &child.claims);
            assert!(
                matches!(refused, Err(TreeError::Root(_) | TreeError::Circuit(_))),
                "{refused:?}"
            );
        }
    }
}
