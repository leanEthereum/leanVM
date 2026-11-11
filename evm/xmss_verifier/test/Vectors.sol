// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity 0.8.38;

import {Vm} from "forge-std/Vm.sol";

/// EthLib's leanXMSS verify vectors, vendored in `crates/signatures`.
library Vectors {
    Vm private constant vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    string internal constant DIR = "../../crates/signatures/tests/signatures/ethlib/xmss/verify";

    struct Case {
        string name;
        bytes publicKey;
        bytes message;
        bytes signature;
        /// The case's output, with null (an input of the wrong length) as false.
        bool expected;
    }

    function load() internal view returns (Case[] memory cases) {
        Vm.DirEntry[] memory entries = vm.readDir(DIR);
        cases = new Case[](entries.length);
        uint256 n;
        for (uint256 i; i < entries.length; i++) {
            if (!entries[i].isDir) continue;
            cases[n++] = parse(entries[i].path);
        }
        assembly {
            mstore(cases, n)
        }
    }

    /// Whether a case can be passed as `verify(bytes32, bytes32, bytes)`.
    function representable(Case memory c) internal pure returns (bool) {
        return c.publicKey.length == 32 && c.message.length == 32;
    }

    /// The files are flat, so splitting on the quotes yields the three hex strings between fixed separators.
    function parse(string memory dir) private view returns (Case memory c) {
        string[] memory path = vm.split(dir, "/");
        c.name = path[path.length - 1];
        string[] memory parts = vm.split(vm.readFile(string.concat(dir, "/data.yaml")), "'");
        require(parts.length == 7, "unexpected data.yaml");
        require(eq(parts[0], "input:\n  public_key: "), "unexpected data.yaml");
        require(eq(parts[2], "\n  message: "), "unexpected data.yaml");
        require(eq(parts[4], "\n  signature: "), "unexpected data.yaml");
        c.publicKey = vm.parseBytes(parts[1]);
        c.message = vm.parseBytes(parts[3]);
        c.signature = vm.parseBytes(parts[5]);
        if (eq(parts[6], "\noutput: true\n")) c.expected = true;
        else if (!eq(parts[6], "\noutput: false\n") && !eq(parts[6], "\noutput: null\n")) revert("unexpected output");
    }

    function eq(string memory a, string memory b) private pure returns (bool) {
        return keccak256(bytes(a)) == keccak256(bytes(b));
    }
}
