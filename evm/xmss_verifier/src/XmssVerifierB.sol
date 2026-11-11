// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity 0.8.38;

/// leanXMSS verification in assembly: `XmssVerifierA` with each hash input built in place.
library XmssB {
    /// The leaf index, then two layers of the randomizer, 58 chain values and 16 siblings, 16 bytes each.
    uint256 internal constant SIG_SIZE = 2404;

    /// The public key is the root then the public parameter. False for a signature of the wrong length.
    function verify(bytes32 publicKey, bytes32 message, bytes calldata signature) internal pure returns (bool ok) {
        if (signature.length != SIG_SIZE) return false;
        assembly ("memory-safe") {
            // A hash input starts with the word `P | A`: the public parameter, then the address
            // `[lo:4 | hi:3 | t + 32 step:1 | zero:8]`, the fields little-endian. In that word, `lo` sits at bit 96, the
            // level (the low byte of `hi`) at bit 88, the top layer's flag (bit 23 of `hi`) at bit 79, the type at bit 64
            // and the step at bit 69. A hash value is 16 bytes, kept in the high half of a word.
            //
            // The 64-byte inputs of the chain steps and the nodes are built in the scratch space at 0, the digest's
            // and the leaf's at the free memory pointer.

            /// The low four bytes of `x`, reversed: a 32-bit little-endian field to or from a number.
            function swap32(x) -> y {
                y := or(
                    or(shl(24, and(x, 0xff)), shl(8, and(x, 0xff00))),
                    or(and(shr(8, x), 0xff00), and(shr(24, x), 0xff))
                )
            }

            /// A 16-byte string read as a little-endian integer.
            function le128(x) -> y {
                y := or(
                    shl(8, and(x, 0x00ff00ff00ff00ff00ff00ff00ff00ff)),
                    and(shr(8, x), 0x00ff00ff00ff00ff00ff00ff00ff00ff)
                )
                y := or(
                    shl(16, and(y, 0x0000ffff0000ffff0000ffff0000ffff)),
                    and(shr(16, y), 0x0000ffff0000ffff0000ffff0000ffff)
                )
                y := or(
                    shl(32, and(y, 0x00000000ffffffff00000000ffffffff)),
                    and(shr(32, y), 0x00000000ffffffff00000000ffffffff)
                )
                y := or(shl(64, and(y, 0x0000000000000000ffffffffffffffff)), shr(64, y))
            }

            /// Whether the digest `d`, a little-endian integer, is a codeword: its two-bit digits past the 58th are zero
            /// and the others sum to 106. The digits are summed in pairs, then per byte, then the bytes by a product.
            function isCodeword(d) -> r {
                if iszero(shr(116, d)) {
                    let x :=
                        add(
                            and(d, 0x33333333333333333333333333333333),
                            and(shr(2, d), 0x33333333333333333333333333333333)
                        )
                    x := add(
                        and(x, 0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f),
                        and(shr(4, x), 0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f)
                    )
                    r := eq(byte(16, mul(x, 0x01010101010101010101010101010101)), 106)
                }
            }

            /// The leaf that the chain values at `values` reach from the digits of `d`, its input built at `mem`. `pa`
            /// is `P | A` with `lo` and `hi` set.
            function wotsLeaf(mem, pa, d, values) -> leaf {
                mstore(mem, or(pa, shl(64, 2)))
                let mask := not(0xffffffffffffffffffffffffffffffff)
                // A step's address carries the position it leaves.
                let a0 := or(pa, shl(64, 1))
                let a1 := or(a0, shl(69, 1))
                let a2 := or(a0, shl(69, 2))
                for { let o := 0 } lt(o, 928) { o := add(o, 16) } {
                    // The chain index, a 16-byte little-endian integer after the value.
                    let index := shl(116, o)
                    let w := or(and(calldataload(add(values, o)), mask), index)
                    // The steps from the chain's digit to its end, the most frequent digit first.
                    switch and(d, 3)
                    case 3 {}
                    case 2 {
                        mstore(0, a2)
                        mstore(0x20, w)
                        w := or(and(keccak256(0, 0x40), mask), index)
                    }
                    case 1 {
                        mstore(0, a1)
                        mstore(0x20, w)
                        w := or(and(keccak256(0, 0x40), mask), index)
                        mstore(0, a2)
                        mstore(0x20, w)
                        w := or(and(keccak256(0, 0x40), mask), index)
                    }
                    default {
                        mstore(0, a0)
                        mstore(0x20, w)
                        w := or(and(keccak256(0, 0x40), mask), index)
                        mstore(0, a1)
                        mstore(0x20, w)
                        w := or(and(keccak256(0, 0x40), mask), index)
                        mstore(0, a2)
                        mstore(0x20, w)
                        w := or(and(keccak256(0, 0x40), mask), index)
                    }
                    // The index spills into the next end's place, which the next end overwrites; the last one's lies
                    // past the input.
                    mstore(add(add(mem, 0x20), o), w)
                    d := shr(2, d)
                }
                leaf := and(keccak256(mem, 960), mask)
            }

            /// The root that `node`, at index `e`, and the path at `ptr` reach. `pa` is `P | A` with only the top
            /// layer's flag set.
            function pathRoot(pa, e, node, ptr) -> root {
                let mask := not(0xffffffffffffffffffffffffffffffff)
                let level := shl(88, 1)
                // `lo`, the parent's index, kept little-endian: halving it shifts each byte right by one and moves the
                // low bit of the next byte into its top bit.
                let lo := swap32(e)
                pa := or(pa, shl(64, 3))
                for { let end := add(ptr, 256) } lt(ptr, end) { ptr := add(ptr, 16) } {
                    let sibling := and(calldataload(ptr), mask)
                    // The low bit of `e` says whether the node is the right child: then swap the two.
                    let swap := mul(and(e, 1), xor(node, sibling))
                    e := shr(1, e)
                    lo := or(and(shr(1, lo), 0x7f7f7f7f), and(shl(15, lo), 0x80808000))
                    pa := add(pa, level)
                    mstore(0, or(pa, shl(96, lo)))
                    mstore(0x20, or(xor(node, swap), shr(128, xor(sibling, swap))))
                    node := and(keccak256(0, 0x40), mask)
                }
                root := node
            }

            /// The root that layer `layer`'s signature at `sig`, by key `e`, reaches from `signed`, the first `len`
            /// bytes of a word, and whether its digest is a codeword.
            function layerRoot(mem, p, layer, e, signed, len, sig) -> root, valid {
                let pa := or(p, shl(79, layer))
                let paKey := or(pa, shl(96, swap32(e)))
                mstore(mem, or(paKey, shl(64, 12)))
                mstore(add(mem, 0x20), signed)
                mstore(add(mem, add(0x20, len)), shl(128, shr(128, calldataload(sig))))
                let d := le128(shr(128, keccak256(mem, add(0x30, len))))
                valid := isCodeword(d)
                if valid { root := pathRoot(pa, e, wotsLeaf(mem, paKey, d, add(sig, 16)), add(sig, 944)) }
            }

            let mem := mload(0x40)
            let p := shl(128, publicKey)
            let sig := signature.offset
            let leafIndex := swap32(shr(224, calldataload(sig)))
            let bottomRoot, valid := layerRoot(mem, p, 0, leafIndex, message, 32, add(sig, 4))
            if valid {
                let root, topValid := layerRoot(mem, p, 1, shr(16, leafIndex), bottomRoot, 16, add(sig, 1204))
                ok := and(topValid, eq(root, shl(128, shr(128, publicKey))))
            }
        }
    }
}

contract XmssVerifierB {
    function verify(bytes32 publicKey, bytes32 message, bytes calldata signature) external pure returns (bool) {
        return XmssB.verify(publicKey, message, signature);
    }
}
