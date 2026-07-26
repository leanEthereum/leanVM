// Credits:
// - whir-p3 (https://github.com/tcoratger/whir-p3) (MIT and Apache-2.0 licenses).
// - Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use field::BasedVectorSpace;
use field::ExtensionField;
use field::PackedValue;
use field::PrimeCharacteristicRing;
use koala_bear::{KoalaBear, default_koalabear_poseidon1_16};
use poly::*;

use symetric::merkle::unpack_array;
use tracing::instrument;
use utils::log2_ceil_usize;
use zk_alloc::ArenaVec;

use crate::Dimensions;
use crate::Matrix;
use crate::utils::flatten_to_base_arena;
pub use symetric::DIGEST_ELEMS;

pub(crate) type RoundMerkleTree<F> = WhirMerkleTree<F, DIGEST_ELEMS>;

pub(crate) fn merkle_commit<EF: ExtensionField<KoalaBear>>(
    matrix: Matrix<EF, ArenaVec<EF>>,
    full_n_cols: usize,
    effective_n_cols: usize,
) -> ([KoalaBear; DIGEST_ELEMS], RoundMerkleTree<KoalaBear>) {
    let dim = <EF as BasedVectorSpace<KoalaBear>>::DIMENSION;
    let base_values = flatten_to_base_arena::<KoalaBear, EF>(matrix.values);
    let base_matrix = Matrix::new(base_values, matrix.width * dim);
    let tree = build_merkle_tree_koalabear(base_matrix, full_n_cols * dim, effective_n_cols * dim);
    (tree.root(), tree)
}

#[instrument(name = "build merkle tree", skip_all)]
fn build_merkle_tree_koalabear(
    leaf: Matrix<KoalaBear, ArenaVec<KoalaBear>>,
    full_base_width: usize,
    effective_base_width: usize,
) -> RoundMerkleTree<KoalaBear> {
    // Leaf hashing is an overwrite sponge (raw permutation); the 2->1 tree climb is compression.
    // `perm` (Poseidon16) implements both `Permutation` and `Compression`, so it serves both roles.
    let perm = default_koalabear_poseidon1_16();
    let n_zero_suffix_rate_chunks = (full_base_width - effective_base_width) / 8;
    let iv_first = KoalaBear::from_usize(full_base_width);
    let scalar_state = symetric::precompute_zero_suffix_state::<KoalaBear, _, 16, 8, DIGEST_ELEMS>(
        &perm,
        iv_first,
        n_zero_suffix_rate_chunks,
    );
    let packed_state: [PFPacking<KoalaBear>; 16] =
        std::array::from_fn(|i| PFPacking::<KoalaBear>::from_fn(|_| scalar_state[i]));
    let first_layer = first_digest_layer_with_initial_state::<PFPacking<KoalaBear>, _, _, DIGEST_ELEMS, 16, 8>(
        &perm,
        &leaf,
        &packed_state,
        effective_base_width,
    );
    let tree = symetric::merkle::MerkleTree::from_first_layer::<PFPacking<KoalaBear>, _, 16>(&perm, first_layer);
    WhirMerkleTree {
        leaf,
        tree,
        full_leaf_base_width: full_base_width,
    }
}

pub(crate) fn merkle_open<EF: ExtensionField<KoalaBear>>(
    merkle_tree: &RoundMerkleTree<KoalaBear>,
    index: usize,
) -> (Vec<EF>, Vec<[KoalaBear; DIGEST_ELEMS]>) {
    let (inner_leaf, proof) = merkle_tree.open(index);
    (EF::reconstitute_from_base(inner_leaf), proof)
}

pub(crate) fn merkle_verify<EF: ExtensionField<KoalaBear>>(
    merkle_root: [KoalaBear; DIGEST_ELEMS],
    index: usize,
    dimension: Dimensions,
    data: Vec<EF>,
    proof: &Vec<[KoalaBear; DIGEST_ELEMS]>,
) -> bool {
    let perm = default_koalabear_poseidon1_16();
    let log_max_height = utils::log2_strict_usize(dimension.height);
    let base_data = EF::flatten_to_base(data);
    symetric::merkle::merkle_verify::<_, _, _, DIGEST_ELEMS, 16, 8>(
        &perm,
        &perm,
        &merkle_root,
        log_max_height,
        index,
        &base_data,
        proof,
    )
}

#[derive(Debug, Clone)]
pub struct WhirMerkleTree<F, const DIGEST_ELEMS: usize> {
    pub(crate) leaf: Matrix<F, ArenaVec<F>>,
    pub(crate) tree: symetric::merkle::MerkleTree<F, DIGEST_ELEMS>,
    full_leaf_base_width: usize,
}

impl<F: field::PrimeCharacteristicRing + Send + Sync, const DIGEST_ELEMS: usize> WhirMerkleTree<F, DIGEST_ELEMS> {
    #[must_use]
    pub fn root(&self) -> [F; DIGEST_ELEMS] {
        self.tree.root()
    }

    pub fn open(&self, index: usize) -> (Vec<F>, Vec<[F; DIGEST_ELEMS]>) {
        let log_height = log2_ceil_usize(self.leaf.height());
        let mut opening: Vec<F> = self.leaf.row(index).unwrap().collect();
        opening.resize(self.full_leaf_base_width, F::default());
        let proof = self.tree.open_siblings(index, log_height);
        (opening, proof)
    }
}

#[instrument(name = "first digest layer", level = "debug", skip_all)]
fn first_digest_layer_with_initial_state<
    P,
    Perm,
    LV,
    const DIGEST_ELEMS: usize,
    const WIDTH: usize,
    const RATE: usize,
>(
    perm: &Perm,
    matrix: &Matrix<P::Value, LV>,
    packed_initial_state: &[P; WIDTH],
    effective_base_width: usize,
) -> ArenaVec<[P::Value; DIGEST_ELEMS]>
where
    P: PackedValue + Default,
    LV: AsRef<[P::Value]> + Send + Sync,
    P::Value: Default + Copy + Send + Sync,
    Perm: koala_bear::symmetric::Permutation<[P::Value; WIDTH]> + koala_bear::symmetric::Permutation<[P; WIDTH]>,
{
    let width = P::WIDTH;
    let height = matrix.height();
    assert!(height.is_multiple_of(width));
    let n_pad = (RATE - effective_base_width % RATE) % RATE;

    let mut digests = unsafe { ArenaVec::uninitialized(height) };

    parallel::par_chunks_mut(&mut digests, width, |i, digests_chunk| {
        let first_row = i * width;
        let rtl_iter = matrix.vertically_packed_row_rtl::<P>(first_row, effective_base_width, n_pad);
        let packed_digest: [P; DIGEST_ELEMS] =
            symetric::hash_rtl_iter_with_initial_state::<_, _, _, WIDTH, RATE, DIGEST_ELEMS>(
                perm,
                rtl_iter,
                packed_initial_state,
            );
        for (dst, src) in digests_chunk.iter_mut().zip(unpack_array(packed_digest)) {
            *dst = src;
        }
    });

    digests
}
