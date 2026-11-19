use lean_xmss::*;

fn node(left: &VrfNode, right: &VrfNode) -> VrfNode {
    keccak256::hash_pair(left, right)
}

/// `SHA-256("leanxmss vrf test")`.
fn seed() -> [u8; 32] {
    [
        0xc1, 0x2c, 0x02, 0x72, 0x17, 0xe3, 0xdc, 0xc0, 0xfb, 0x70, 0x35, 0x19, 0x3b, 0x3f, 0x51, 0x84, 0xbd, 0x0f,
        0xa6, 0xd5, 0x66, 0xdb, 0x50, 0x86, 0x9d, 0x73, 0x0d, 0x7f, 0x99, 0x08, 0x0d, 0x9b,
    ]
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
            layers[0][i as usize] = keccak256::hash(&[&seed[..], &i.to_le_bytes()].concat());
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
/// `SHA-256("vrf-seed" | BLS secret key)`, here of the key `0x2892f3ba…ce8834`, and the first `2^20` leaves
/// are filled.
#[test]
fn vrf_devnet_vector() {
    let seed = [
        0x8b, 0x6f, 0xe7, 0xf8, 0xe9, 0xb2, 0xa6, 0xe0, 0xeb, 0xf8, 0xfd, 0x5a, 0x7b, 0x39, 0x91, 0x32, 0x9a, 0xff,
        0xcd, 0x3f, 0xf9, 0x1a, 0xec, 0x15, 0x9d, 0x33, 0xe4, 0xb4, 0xde, 0xda, 0xc9, 0x40,
    ];
    let key = VrfKey::new(seed, DEFAULT_VRF_LEAVES).unwrap();
    let root = key.root(&key.state(0).unwrap());
    assert_eq!(
        hex(&root),
        "46f6772a35c14c7f8467e9d8791450ed3c6853191129876fc50e769ec9bac18d"
    );
}

/// The same state and root as the Go implementation gives for this seed.
#[test]
fn vrf_shared_vector() {
    let key = VrfKey::new(seed(), DEFAULT_VRF_LEAVES).unwrap();
    let state = key.state(777_777).unwrap();
    assert_eq!(
        hex(&keccak256::hash(&state.to_bytes())),
        "63b553b8e581093f7c4631b22aba29bd0ce06d015872f910844ee09c6ca76546"
    );
    assert_eq!(
        hex(&key.root(&state)),
        "c2ea7ef9c148cbef3fae2b336c6772d7e815f3dba924abc25e1451ce196b9a37"
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
