// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity 0.8.38;

/// Returns EIP-8450's signing root of `PQKeyPossession(bls_pubkey, xmss_public_key)` for an EIP-8483 add's input, to
/// measure what it would cost in place of `M`: three SHA-256 precompile calls over 64 bytes. The domain depends on the
/// network's genesis, so this one is a placeholder.
contract SigningRoot {
    /// `DOMAIN_PQ_KEY_POSSESSION`, then 28 bytes standing in for the fork data root.
    bytes32 internal constant DOMAIN = 0x13000000eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee;

    fallback() external {
        assembly {
            let p := mload(0x40)
            // The pubkey's root: its 48 bytes, then 16 zero bytes, which fresh memory already holds.
            calldatacopy(p, 0, 48)
            if iszero(staticcall(gas(), 2, p, 64, p, 32)) { revert(0, 0) }
            // The container's root: the pubkey's root, then the leanXMSS key, a 32-byte vector and so its own root.
            calldatacopy(add(p, 32), 48, 32)
            if iszero(staticcall(gas(), 2, p, 64, p, 32)) { revert(0, 0) }
            // The signing root.
            mstore(add(p, 32), DOMAIN)
            if iszero(staticcall(gas(), 2, p, 64, p, 32)) { revert(0, 0) }
            return(p, 32)
        }
    }
}
