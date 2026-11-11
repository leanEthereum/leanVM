// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity 0.8.38;

/// leanXMSS verification in plain Solidity, a port of `lean_xmss::verify` in `crates/signatures`.
contract XmssVerifierA {
    uint256 internal constant N = 16;
    /// Digit size in bits.
    uint256 internal constant W = 2;
    uint256 internal constant CHAIN_LEN = 1 << W;
    /// WOTS+C chains of a one-time key, each `CHAIN_LEN - 1` steps long.
    uint256 internal constant V = 58;
    uint256 internal constant TARGET_SUM = 106;
    uint256 internal constant LAYER_HEIGHT = 16;
    /// The randomizer, the chain values and the path.
    uint256 internal constant LAYER_SIG_SIZE = N + V * N + LAYER_HEIGHT * N;
    /// The leaf index, then the bottom layer's signature, then the top one's.
    uint256 internal constant SIG_SIZE = 4 + 2 * LAYER_SIG_SIZE;

    uint256 internal constant TWEAK_CHAIN = 1;
    uint256 internal constant TWEAK_LEAF = 2;
    uint256 internal constant TWEAK_NODE = 3;
    uint256 internal constant TWEAK_MSG = 12;
    /// The top layer's flag in an address's `hi`.
    uint256 internal constant TOP = 1 << 23;

    /// The public key is the root then the public parameter. False for a signature of the wrong length.
    function verify(bytes32 publicKey, bytes32 message, bytes calldata signature) external pure returns (bool) {
        if (signature.length != SIG_SIZE) return false;
        bytes16 pp = bytes16(publicKey << 128);
        uint256 leafIndex = swap32(uint32(bytes4(signature[:4])));
        bytes calldata bottom = signature[4:4 + LAYER_SIG_SIZE];
        bytes calldata top = signature[4 + LAYER_SIG_SIZE:];
        (bool ok, bytes16 bottomRoot) = layerRoot(pp, 0, leafIndex, abi.encodePacked(message), bottom);
        if (!ok) return false;
        bytes16 root;
        (ok, root) = layerRoot(pp, 1, leafIndex >> LAYER_HEIGHT, abi.encodePacked(bottomRoot), top);
        return ok && root == bytes16(publicKey);
    }

    /// The root that the signature `sig` of `signed` by key `e` on `layer` reaches, or false if its digest is not a
    /// codeword.
    function layerRoot(bytes16 pp, uint256 layer, uint256 e, bytes memory signed, bytes calldata sig)
        internal
        pure
        returns (bool, bytes16)
    {
        uint256 hi = layer * TOP;
        bytes16 randomizer = bytes16(sig[:N]);
        bytes16 digest = bytes16(keccak256(abi.encodePacked(pp, addr(TWEAK_MSG, 0, hi, e), signed, randomizer)));
        uint256 d = le128(digest);
        if (!isCodeword(d)) return (false, 0);
        bytes16 leaf = wotsLeaf(pp, hi, e, d, sig[N:N + V * N]);
        return (true, pathRoot(pp, hi, e, leaf, sig[N + V * N:]));
    }

    /// The leaf of key `e` that the chain `values` reach from the digits of the codeword `d`.
    function wotsLeaf(bytes16 pp, uint256 hi, uint256 e, uint256 d, bytes calldata values)
        internal
        pure
        returns (bytes16)
    {
        // A step's address carries the position it leaves, and is the same for every chain.
        bytes16[CHAIN_LEN - 1] memory stepAddr;
        for (uint256 step; step < CHAIN_LEN - 1; step++) {
            stepAddr[step] = addr(TWEAK_CHAIN, step, hi, e);
        }
        // The leaf hashes `P | A | ends`, 30 words.
        bytes32[1 + V / 2] memory input;
        input[0] = bytes32(pp) | (bytes32(addr(TWEAK_LEAF, 0, hi, e)) >> 128);
        for (uint256 i; i < V; i++) {
            bytes16 value = bytes16(values[N * i:N * (i + 1)]);
            // The chain index, a 16-byte little-endian integer.
            bytes16 index = bytes16(uint128(i) << 120);
            for (uint256 step = (d >> (W * i)) & (CHAIN_LEN - 1); step < CHAIN_LEN - 1; step++) {
                value = th(pp, stepAddr[step], value, index);
            }
            input[1 + i / 2] |= i % 2 == 0 ? bytes32(value) : bytes32(value) >> 128;
        }
        return bytes16(keccak256(abi.encodePacked(input)));
    }

    /// The root that `leaf`, at index `e`, and its authentication `path` reach.
    function pathRoot(bytes16 pp, uint256 hi, uint256 e, bytes16 leaf, bytes calldata path)
        internal
        pure
        returns (bytes16 node)
    {
        node = leaf;
        for (uint256 z; z < LAYER_HEIGHT; z++) {
            bytes16 sibling = bytes16(path[N * z:N * (z + 1)]);
            bytes16 a = addr(TWEAK_NODE, 0, hi | (z + 1), e >> (z + 1));
            // Bit `z` of `e` says whether the node is the right child.
            node = (e >> z) & 1 == 0 ? th(pp, a, node, sibling) : th(pp, a, sibling, node);
        }
    }

    /// `Th(P, A, x | y)`: the first 16 bytes of the Keccak-256 hash.
    function th(bytes16 pp, bytes16 a, bytes16 x, bytes16 y) internal pure returns (bytes16) {
        return bytes16(keccak256(abi.encodePacked(pp, a, x, y)));
    }

    /// `[lo:4 | hi:3 | t + 32 step:1 | zero:8]`, the fields little-endian.
    function addr(uint256 t, uint256 step, uint256 hi, uint256 lo) internal pure returns (bytes16) {
        return bytes16(uint128((swap32(lo) << 96) | ((swap32(hi) >> 8) << 72) | ((t | (step << 5)) << 64)));
    }

    /// Whether the digest `d`, a little-endian integer, is a codeword: its digits past the `V`th are zero and the
    /// others sum to `TARGET_SUM`.
    function isCodeword(uint256 d) internal pure returns (bool) {
        if (d >> (W * V) != 0) return false;
        uint256 sum;
        for (uint256 i; i < V; i++) {
            sum += (d >> (W * i)) & (CHAIN_LEN - 1);
        }
        return sum == TARGET_SUM;
    }

    /// `b` read as a little-endian integer.
    function le128(bytes16 b) internal pure returns (uint256 x) {
        x = uint128(b);
        x = ((x & 0x00ff00ff00ff00ff00ff00ff00ff00ff) << 8) | ((x >> 8) & 0x00ff00ff00ff00ff00ff00ff00ff00ff);
        x = ((x & 0x0000ffff0000ffff0000ffff0000ffff) << 16) | ((x >> 16) & 0x0000ffff0000ffff0000ffff0000ffff);
        x = ((x & 0x00000000ffffffff00000000ffffffff) << 32) | ((x >> 32) & 0x00000000ffffffff00000000ffffffff);
        x = ((x & 0x0000000000000000ffffffffffffffff) << 64) | (x >> 64);
    }

    /// The low four bytes of `x`, reversed: a 32-bit little-endian field to or from a number.
    function swap32(uint256 x) internal pure returns (uint256) {
        return ((x & 0xff) << 24) | ((x & 0xff00) << 8) | ((x >> 8) & 0xff00) | ((x >> 24) & 0xff);
    }
}
