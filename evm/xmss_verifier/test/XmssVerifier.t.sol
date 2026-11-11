// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity 0.8.38;

import {Test} from "forge-std/Test.sol";
import {XmssVerifierA} from "../src/XmssVerifierA.sol";
import {Vectors} from "./Vectors.sol";

interface IXmssVerifier {
    function verify(bytes32 publicKey, bytes32 message, bytes calldata signature) external view returns (bool);
}

contract XmssVerifierTest is Test {
    function test_vectorsA() public {
        check(IXmssVerifier(address(new XmssVerifierA())));
    }

    /// Every vector `verify` can take gives its expected result.
    function check(IXmssVerifier verifier) internal view {
        Vectors.Case[] memory cases = Vectors.load();
        uint256 n;
        for (uint256 i; i < cases.length; i++) {
            Vectors.Case memory c = cases[i];
            if (!Vectors.representable(c)) continue;
            assertEq(verifier.verify(bytes32(c.publicKey), bytes32(c.message), c.signature), c.expected, c.name);
            n++;
        }
        assertEq(n, 21);
    }
}
