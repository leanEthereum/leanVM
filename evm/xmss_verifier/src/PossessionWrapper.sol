// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity 0.8.38;

import {XmssB} from "./XmssVerifierB.sol";

/// Runs the EIP-8483 add on the first 112 bytes of its calldata, the BLS public key and pq_data, through DELEGATECALL,
/// so the queue lives in this contract's storage. The calldata carries a leanXMSS signature after them.
abstract contract Wrapper {
    /// Where the measurement places the EIP-8483 runtime bytecode; the EIP leaves the address to be chosen.
    address internal constant PREDEPLOY = 0x0000000000000000000000000000000000008483;
    uint256 internal constant INPUT_SIZE = 112;

    fallback() external payable {
        require(msg.data.length == INPUT_SIZE + XmssB.SIG_SIZE);
        check();
        assembly ("memory-safe") {
            let p := mload(0x40)
            calldatacopy(p, 0, INPUT_SIZE)
            if iszero(delegatecall(gas(), PREDEPLOY, p, INPUT_SIZE, 0, 0)) {
                returndatacopy(p, 0, returndatasize())
                revert(p, returndatasize())
            }
        }
    }

    function check() internal view virtual;
}

/// C: requires the signature to be a proof of possession, a leanXMSS signature by pq_data's first 32 bytes, at leaf
/// index 0, of `M = keccak256(chainid | bls_pubkey | xmss_public_key)`, the chain ID a 32-byte word.
contract PossessionWrapper is Wrapper {
    function check() internal view override {
        bytes32 m;
        assembly ("memory-safe") {
            let p := mload(0x40)
            mstore(p, chainid())
            calldatacopy(add(p, 32), 0, 80)
            m := keccak256(p, 112)
        }
        require(bytes4(msg.data[INPUT_SIZE:]) == 0);
        require(XmssB.verify(bytes32(msg.data[48:80]), m, msg.data[INPUT_SIZE:]));
    }
}

/// C0: C without the message and the verify, so the difference with C is what checking the proof costs.
contract UncheckedWrapper is Wrapper {
    function check() internal view override {}
}
