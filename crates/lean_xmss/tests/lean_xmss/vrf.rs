use lean_xmss::*;
use sha2::{Digest as _, Sha256};

fn node(left: &VrfNode, right: &VrfNode) -> VrfNode {
    Sha256::new().chain_update(left).chain_update(right).finalize().into()
}

fn seed() -> [u8; 32] {
    Sha256::digest(b"leanxmss vrf test").into()
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

/// A VRF tree built in full up to a power of two of leaves, to check states against.
struct Reference {
    layers: Vec<Vec<VrfNode>>,
    top: [VrfNode; VRF_TREE_DEPTH + 1],
    zeros: [VrfNode; VRF_TREE_DEPTH],
}

impl Reference {
    fn new(seed: [u8; 32], leaves: u64, depth: usize) -> Self {
        let mut zeros = [[0; VRF_NODE_LEN]; VRF_TREE_DEPTH];
        for level in 1..VRF_TREE_DEPTH {
            zeros[level] = node(&zeros[level - 1], &zeros[level - 1]);
        }
        let mut layers = vec![vec![[0; VRF_NODE_LEN]; 1 << depth]];
        for i in 0..leaves {
            layers[0][i as usize] = Sha256::new()
                .chain_update(seed)
                .chain_update(i.to_le_bytes())
                .finalize()
                .into();
        }
        for level in 0..depth {
            let up = layers[level]
                .as_chunks()
                .0
                .iter()
                .map(|[left, right]| node(left, right));
            layers.push(up.collect());
        }
        let mut top = [[0; VRF_NODE_LEN]; VRF_TREE_DEPTH + 1];
        top[depth] = layers[depth][0];
        for level in depth..VRF_TREE_DEPTH {
            top[level + 1] = node(&top[level], &zeros[level]);
        }
        Self { layers, top, zeros }
    }

    fn node(&self, level: usize, index: u64) -> VrfNode {
        if level < self.layers.len() && index < self.layers[level].len() as u64 {
            self.layers[level][index as usize]
        } else if level >= self.layers.len() - 1 && index == 0 {
            self.top[level]
        } else {
            self.zeros[level]
        }
    }

    fn root(&self) -> VrfNode {
        self.top[VRF_TREE_DEPTH]
    }

    fn proof(&self, slot: u32) -> VrfProof {
        std::array::from_fn(|i| match i {
            0 => self.node(0, u64::from(slot)),
            _ => self.node(i - 1, u64::from(slot >> (i - 1)) ^ 1),
        })
    }

    fn check(&self, key: &VrfKey, state: &VrfState) {
        let proof = key.proof(state);
        assert_eq!(proof, self.proof(state.slot()), "slot {}", state.slot());
        assert_eq!(key.root(state), self.root(), "slot {}", state.slot());
        assert!(verify_vrf_proof(&self.root(), u64::from(state.slot()), &proof));
    }
}

/// The vector of the Lighthouse and ethPandaOps genesis tooling: the seed is
/// `SHA-256("vrf-seed" | BLS secret key)` and the first `2^20` leaves are filled.
#[test]
fn vrf_devnet_vector() {
    let secret: [u8; 32] = [
        0x28, 0x92, 0xf3, 0xba, 0x47, 0x5c, 0x36, 0x40, 0xa6, 0x7f, 0xe7, 0x30, 0x79, 0x8a, 0xd9, 0xc4, 0xee, 0xd3,
        0xa6, 0xd9, 0x34, 0xdb, 0x85, 0xf9, 0x1c, 0x41, 0xcf, 0xc8, 0x37, 0xce, 0x88, 0x34,
    ];
    let seed = Sha256::new()
        .chain_update(b"vrf-seed")
        .chain_update(secret)
        .finalize()
        .into();
    let key = VrfKey::new(seed, DEFAULT_VRF_LEAVES).unwrap();
    let root = key.root(&key.state(0).unwrap());
    assert_eq!(
        hex(&root),
        "0fc00857fdae6d29c18f54563c64e166b1fff1c6d943bb2c43e8b096bb60585e"
    );
}

/// The same state and root as the Go implementation gives for this seed.
#[test]
fn vrf_shared_vector() {
    let key = VrfKey::new(seed(), DEFAULT_VRF_LEAVES).unwrap();
    let state = key.state(777_777).unwrap();
    assert_eq!(
        hex(&Sha256::digest(state.to_bytes())),
        "e3e4bc109e1b45f4a20015719ed55cb3e1d507c85c76c9605abcd83afbaace1f"
    );
    assert_eq!(
        hex(&key.root(&state)),
        "85f4614748229923af260c44d82b3ac380c4b32e3e3bfd9f8a57684e2b90d93e"
    );
}

#[test]
fn vrf_default_fill() {
    let key = VrfKey::new(seed(), DEFAULT_VRF_LEAVES).unwrap();
    let reference = Reference::new(seed(), DEFAULT_VRF_LEAVES, 20);
    for slot in [0, 5, (1 << 20) - 1, 1 << 20, (1 << 31) - 1] {
        reference.check(&key, &key.state(slot).unwrap());
    }
    let mut state = key.state((1 << 19) - 100).unwrap();
    for _ in 0..200 {
        state = key.advance(&state, state.slot() + 1).unwrap();
        reference.check(&key, &state);
    }
    for _ in 0..40 {
        state = key.advance(&state, state.slot() + 997).unwrap();
        reference.check(&key, &state);
    }
    for shift in 1..VRF_TREE_DEPTH {
        for slot in [(1 << shift) - 1, 1 << shift] {
            state = key.advance(&state, slot).unwrap();
            reference.check(&key, &state);
        }
    }
    for slot in [(1 << 20) + 7, (1 << 20) - 3, 12345, 0, (1 << 31) - 1, 1] {
        state = key.advance(&state, slot).unwrap();
        reference.check(&key, &state);
    }
}

/// Every slot around the last filled leaf, for fills that are and are not a power of two.
#[test]
fn vrf_small_fills() {
    for leaves in [0, 1, 2, 3, 1000, 1024] {
        let key = VrfKey::new(seed(), leaves).unwrap();
        let reference = Reference::new(seed(), leaves, 10);
        let mut walk = key.state(0).unwrap();
        for slot in 0..2200 {
            let state = key.state(slot).unwrap();
            reference.check(&key, &state);
            walk = key.advance(&walk, slot).unwrap();
            assert_eq!(walk, state, "{leaves} leaves, slot {slot}");
        }
        for i in 0..3000u32 {
            walk = key.advance(&walk, (i * i * 7919 + i * 104_729) % 2200).unwrap();
            reference.check(&key, &walk);
        }
    }
}

#[test]
fn vrf_state_encoding() {
    let key = VrfKey::new(seed(), 1024).unwrap();
    let reference = Reference::new(seed(), 1024, 10);
    let state = key.state(777).unwrap();
    let mut bytes = state.to_bytes();
    let decoded = VrfState::from_bytes(&bytes).unwrap();
    assert_eq!(decoded, state);
    reference.check(&key, &key.advance(&decoded, 900).unwrap());

    bytes[100] ^= 1;
    assert_ne!(key.root(&VrfState::from_bytes(&bytes).unwrap()), reference.root());
    bytes[3] = 0x80;
    assert_eq!(VrfState::from_bytes(&bytes), None);
}

#[test]
fn vrf_bounds() {
    assert_eq!(VrfKey::new(seed(), (1 << 31) + 1), None);
    assert!(VrfKey::new(seed(), 1 << 31).is_some());
    let key = VrfKey::new(seed(), 16).unwrap();
    assert_eq!(key.state(1 << 31), None);
    let state = key.state(9).unwrap();
    assert_eq!(key.advance(&state, 1 << 31), None);

    let mut proof = key.proof(&state);
    let root = key.root(&state);
    assert!(verify_vrf_proof(&root, 9 + (1 << 31), &proof));
    assert!(!verify_vrf_proof(&root, 10, &proof));
    proof[0][0] ^= 1;
    assert!(!verify_vrf_proof(&root, 9, &proof));
}
