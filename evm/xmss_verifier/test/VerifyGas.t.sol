// SPDX-License-Identifier: MIT OR Apache-2.0
pragma solidity 0.8.38;

import {Test} from "forge-std/Test.sol";
import {Vm} from "forge-std/Vm.sol";
import {XmssVerifierA} from "../src/XmssVerifierA.sol";
import {XmssVerifierB} from "../src/XmssVerifierB.sol";
import {IXmssVerifier} from "./XmssVerifier.t.sol";
import {Vectors} from "./Vectors.sol";

/// Calls a contract and returns the gas of that call's frame.
contract Meter {
    Vm private constant vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    function measure(address to, bytes calldata data) external returns (uint256) {
        (bool ok,) = to.call(data);
        require(ok);
        return vm.lastFrameGas().gasTotalUsed;
    }
}

contract VerifyGasTest is Test {
    Meter meter = new Meter();

    /// For each valid vector, snapshots two numbers per verifier in `snapshots/verify-<hardfork>.json`: the gasUsed of a
    /// transaction calling `verify`, which includes the intrinsic gas or the calldata floor, and the execution of that
    /// call alone, ABI decoding included.
    function test_verifyGas() public {
        vm.skip(!vm.isIsolateMode(), "measures transactions, so needs --isolate");
        string memory group = string.concat("verify-", vm.getEvmVersion());
        address a = address(new XmssVerifierA());
        address b = address(new XmssVerifierB());
        Vectors.Case[] memory cases = Vectors.load();
        uint256 n;
        for (uint256 i; i < cases.length; i++) {
            if (!cases[i].expected) continue;
            snapshot(group, "A", a, cases[i]);
            snapshot(group, "B", b, cases[i]);
            n++;
        }
        assertEq(n, 4);
    }

    function snapshot(string memory group, string memory label, address verifier, Vectors.Case memory c) internal {
        bytes memory data =
            abi.encodeCall(IXmssVerifier.verify, (bytes32(c.publicKey), bytes32(c.message), c.signature));
        // Forge runs a call from the test as its own transaction only if it is a CALL, and `verify` is view.
        (bool ok, bytes memory ret) = verifier.call(data);
        assertTrue(ok && abi.decode(ret, (bool)), c.name);
        vm.snapshotGasLastFrame(group, string.concat(label, " transaction ", c.name));
        vm.snapshotValue(group, string.concat(label, " execution ", c.name), meter.measure(verifier, data));
    }
}
