// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import "../src/NOESISVerifier.sol";

contract NOESISVerifierTest is Test {
    NOESISVerifier internal verifier;

    function setUp() public {
        verifier = new NOESISVerifier();
    }

    function testVerifyCoherenceStoresState() public {
        bytes32 stateHash = keccak256("state-1");
        bool isSAT = verifier.verifyCoherence(stateHash, 1_000_000, bytes32(0));
        assertTrue(isSAT);
        assertEq(verifier.coherenceStates(stateHash), 1_000_000);
        assertEq(verifier.stateCount(), 1);
    }

    function testVerifyCoherenceReturnsFalseBelowThreshold() public {
        bytes32 stateHash = keccak256("state-low");
        bool isSAT = verifier.verifyCoherence(stateHash, 333_333, bytes32(0));
        assertTrue(!isSAT);
        assertEq(verifier.coherenceStates(stateHash), 333_333);
    }

    function testRejectsDuplicateState() public {
        bytes32 stateHash = keccak256("state-dup");
        verifier.verifyCoherence(stateHash, 1_000_000, bytes32(0));
        vm.expectRevert(bytes("State already verified"));
        verifier.verifyCoherence(stateHash, 1_000_000, bytes32(0));
    }
}
