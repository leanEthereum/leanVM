use field::TwoAdicField;
use serde::{Deserialize, Serialize};

use crate::{DIGEST_LEN_FE, MerklePath, MerklePaths};

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct PrunedMerklePaths<Data, F> {
    pub leaf_data: Vec<Vec<Data>>,
    pub sibling_hashes: Vec<[F; DIGEST_LEN_FE]>,
}

impl<Data: Clone, F: Clone> MerklePaths<Data, F> {
    pub fn prune(self) -> PrunedMerklePaths<Data, F>
    where
        Data: Default + PartialEq,
    {
        assert!(!self.0.is_empty());
        let merkle_height = self.0[0].sibling_hashes.len();

        let mut deduped = self.0;
        deduped.sort_by_key(|p| p.leaf_index);
        deduped.dedup_by_key(|p| p.leaf_index);

        let default = Data::default();
        let leaf_len = deduped[0].leaf_data.len();
        let mut n_trailing_zeros = 0;
        for offset in (0..leaf_len).rev() {
            if deduped.iter().any(|p| p.leaf_data[offset] != default) {
                break;
            }
            n_trailing_zeros += 1;
        }

        let mut sibling_hashes = Vec::new();
        let mut nodes: Vec<(usize, usize)> = deduped.iter().enumerate().map(|(i, p)| (p.leaf_index, i)).collect();
        for lvl in 0..merkle_height {
            let mut parents = Vec::with_capacity(nodes.len());
            let mut i = 0;
            while i < nodes.len() {
                let (idx, path) = nodes[i];
                if idx & 1 == 0 && nodes.get(i + 1).is_some_and(|&(j, _)| j == (idx | 1)) {
                    i += 2;
                } else {
                    sibling_hashes.push(deduped[path].sibling_hashes[lvl].clone());
                    i += 1;
                }
                parents.push((idx >> 1, path));
            }
            nodes = parents;
        }

        PrunedMerklePaths {
            leaf_data: deduped
                .into_iter()
                .map(|p| {
                    let effective_len = p.leaf_data.len() - n_trailing_zeros;
                    p.leaf_data[..effective_len].to_vec()
                })
                .collect(),
            sibling_hashes,
        }
    }
}

impl<Data: Clone, F: TwoAdicField> PrunedMerklePaths<Data, F> {
    pub fn restore(
        mut self,
        queried_indices: &[usize],
        merkle_height: usize,
        full_leaf_len: usize,
        hash_leaf: &impl Fn(&[Data]) -> [F; DIGEST_LEN_FE],
        hash_combine: &impl Fn(&[F; DIGEST_LEN_FE], &[F; DIGEST_LEN_FE]) -> [F; DIGEST_LEN_FE],
    ) -> Option<MerklePaths<Data, F>>
    where
        Data: Default,
    {
        assert!(merkle_height <= F::TWO_ADICITY); // prover height not part of the transcript, it can be trusted

        let mut leaf_indices = queried_indices.to_vec();
        leaf_indices.sort_unstable();
        leaf_indices.dedup();
        assert!(!leaf_indices.is_empty() && *leaf_indices.last().unwrap() < 1 << merkle_height); // sanity check, not part of the transcript
        if self.leaf_data.len() != leaf_indices.len() {
            return None;
        }
        let sent_len = self.leaf_data[0].len();
        if sent_len > full_leaf_len || self.leaf_data.iter().any(|d| d.len() != sent_len) {
            return None;
        }
        self.leaf_data
            .iter_mut()
            .for_each(|d| d.resize(full_leaf_len, Data::default()));

        let mut supplied = self.sibling_hashes.iter();
        let mut known: Vec<Vec<(usize, [F; DIGEST_LEN_FE])>> = Vec::with_capacity(merkle_height);
        let mut nodes: Vec<(usize, [F; DIGEST_LEN_FE])> = leaf_indices
            .iter()
            .zip(&self.leaf_data)
            .map(|(&idx, data)| (idx, hash_leaf(data)))
            .collect();
        for _ in 0..merkle_height {
            let mut level = Vec::with_capacity(2 * nodes.len());
            let mut parents = Vec::with_capacity(nodes.len());
            let mut i = 0;
            while i < nodes.len() {
                let idx = nodes[i].0;
                let paired = idx & 1 == 0 && nodes.get(i + 1).is_some_and(|&(j, _)| j == (idx | 1));
                let (left, right) = if paired {
                    (nodes[i].1, nodes[i + 1].1)
                } else if idx & 1 == 0 {
                    (nodes[i].1, *supplied.next()?)
                } else {
                    (*supplied.next()?, nodes[i].1)
                };
                parents.push((idx >> 1, hash_combine(&left, &right)));
                level.push((idx & !1, left));
                level.push((idx | 1, right));
                i += if paired { 2 } else { 1 };
            }
            known.push(level);
            nodes = parents;
        }
        if supplied.next().is_some() {
            return None; // reject extra siblings
        }

        let restored: Vec<MerklePath<Data, F>> = leaf_indices
            .iter()
            .zip(self.leaf_data)
            .map(|(&leaf_index, leaf_data)| {
                let sibling_hashes = (0..merkle_height)
                    .map(|lvl| {
                        let sibling_idx = (leaf_index >> lvl) ^ 1;
                        let level = &known[lvl];
                        let pos = level.binary_search_by_key(&sibling_idx, |&(j, _)| j).ok()?;
                        Some(level[pos].1)
                    })
                    .collect::<Option<Vec<_>>>()?;
                Some(MerklePath {
                    leaf_data,
                    sibling_hashes,
                    leaf_index,
                })
            })
            .collect::<Option<Vec<_>>>()?;

        Some(MerklePaths(
            queried_indices
                .iter()
                .map(|qi| {
                    let slot = leaf_indices.binary_search(qi).ok()?;
                    restored.get(slot).cloned()
                })
                .collect::<Option<Vec<_>>>()?,
        ))
    }
}
