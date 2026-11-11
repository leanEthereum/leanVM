// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity 0.8.38;

import {Test} from "forge-std/Test.sol";
import {Vectors} from "./Vectors.sol";

contract VectorsTest is Test {
    /// The cases `verify(bytes32, bytes32, bytes)` cannot take are exactly the two whose key or message is short, and both
    /// reject.
    function test_loader() public view {
        Vectors.Case[] memory cases = Vectors.load();
        assertEq(cases.length, 23);
        string[] memory excluded = new string[](cases.length);
        uint256 n;
        for (uint256 i; i < cases.length; i++) {
            if (Vectors.representable(cases[i])) continue;
            assertFalse(cases[i].expected, cases[i].name);
            excluded[n++] = cases[i].name;
        }
        assertEq(n, 2);
        assertTrue(
            (eq(excluded[0], "verify_short_public_key") && eq(excluded[1], "verify_short_message"))
                || (eq(excluded[0], "verify_short_message") && eq(excluded[1], "verify_short_public_key"))
        );
    }

    function eq(string memory a, string memory b) private pure returns (bool) {
        return keccak256(bytes(a)) == keccak256(bytes(b));
    }
}
