using MocksETH as sETHToken

methods {
    //// ETH balance
    balance(address) returns (uint256) envfree
    //// Regular methods
    totalETHReceived() returns (uint256) envfree
    isKnotRegistered(bytes32) returns (bool) envfree

    isNoLongerPartOfSyndicate(bytes32) returns (bool) envfree
    isPriorityStaker(address) returns (bool) envfree
    priorityStakingEndBlock() returns (uint256) envfree
    numberOfRegisteredKnots() returns (uint256) envfree
    totalFreeFloatingShares() returns (uint256) envfree
    calculateUnclaimedFreeFloatingETHShare(bytes32,address) returns (uint256) envfree
    totalClaimed() returns (uint256) envfree
    claimedPerCollateralizedSlotOwnerOfKnot(bytes32, address) returns (uint256) envfree
    accumulatedETHPerFreeFloatingShare() returns (uint256) envfree
    accumulatedETHPerCollateralizedSlotPerKnot() returns (uint256) envfree
    sETHUserClaimForKnot(bytes32,address) returns (uint256) envfree
    lastSeenETHPerCollateralizedSlotPerKnot() returns (uint256) envfree
    lastSeenETHPerFreeFloating() returns (uint256) envfree
    lastAccumulatedETHPerFreeFloatingShare(bytes32) returns (uint256) envfree

    owner() returns (address) envfree
    initialize(address,uint256,address,address,bytes32,bytes32)


    //// Resolving external calls
	// stakeHouseUniverse
	stakeHouseKnotInfo(bytes32) returns (address,address,address,uint256,uint256,bool) => DISPATCHER(true)
    memberKnotToStakeHouse(bytes32) returns (address) => DISPATCHER(true) // not used directly by Syndicate
    // stakeHouseRegistry
    getMemberInfo(bytes32) returns (address,uint256,uint16,bool) => DISPATCHER(true) // not used directly by Syndicate
    // slotSettlementRegistry
	stakeHouseShareTokens(address) returns (address)  => DISPATCHER(true)
	currentSlashedAmountOfSLOTForKnot(bytes32) returns (uint256)  => DISPATCHER(true)
	numberOfCollateralisedSlotOwnersForKnot(bytes32) returns (uint256)  => DISPATCHER(true)
	getCollateralisedOwnerAtIndex(bytes32, uint256) returns (address) => DISPATCHER(true)
	totalUserCollateralisedSLOTBalanceForKnot(address, address, bytes32) returns (uint256) => DISPATCHER(true)
    // sETH
    sETHToken.balanceOf(address) returns (uint256) envfree
    // ERC20
    name()                                returns (string)  => DISPATCHER(true)
    symbol()                              returns (string)  => DISPATCHER(true)
    decimals()                            returns (string)  => DISPATCHER(true)
    totalSupply()                         returns (uint256) => DISPATCHER(true)
    balanceOf(address)                    returns (uint256) => DISPATCHER(true)
    allowance(address,address)            returns (uint)    => DISPATCHER(true)
    approve(address,uint256)              returns (bool)    => DISPATCHER(true)
    transfer(address,uint256)             returns (bool)    => DISPATCHER(true)
    transferFrom(address,address,uint256) returns (bool)    => DISPATCHER(true)
    //// Harnessing
    // harnessed variables
    accruedEarningPerCollateralizedSlotOwnerOfKnot(bytes32,address) returns (uint256) envfree
    totalETHProcessedPerCollateralizedKnot(bytes32) returns (uint256) envfree
    sETHStakedBalanceForKnot(bytes32,address) returns (uint256) envfree
    sETHTotalStakeForKnot(bytes32) returns (uint256) envfree
    // harnessed functions
    deRegisterKnots(bytes32) 
    deRegisterKnots(bytes32,bytes32)
    stake(bytes32,uint256,address)
    stake(bytes32,bytes32,uint256,uint256,address)
    unstake(address,address,bytes32,uint256)
    unstake(address,address,bytes32,bytes32,uint256,uint256)
    claimAsStaker(address,bytes32)
    claimAsStaker(address,bytes32,bytes32)
    claimAsCollateralizedSLOTOwner(address,bytes32)
    claimAsCollateralizedSLOTOwner(address,bytes32,bytes32)
    registerKnotsToSyndicate(bytes32)
    registerKnotsToSyndicate(bytes32,bytes32)
    addPriorityStakers(address)
    addPriorityStakers(address,address)
    batchUpdateCollateralizedSlotOwnersAccruedETH(bytes32)
    batchUpdateCollateralizedSlotOwnersAccruedETH(bytes32,bytes32)
}

/// We defined additional functions to get around the complexity of defining dynamic arrays in cvl. We filter them in 
/// normal rules and invariants as they serve no purpose.
definition notHarnessCall(method f) returns bool = 
    f.selector != batchUpdateCollateralizedSlotOwnersAccruedETH(bytes32).selector
    && f.selector != batchUpdateCollateralizedSlotOwnersAccruedETH(bytes32,bytes32).selector
    && f.selector != deRegisterKnots(bytes32).selector
    && f.selector != deRegisterKnots(bytes32,bytes32).selector
    && f.selector != stake(bytes32,uint256,address).selector
    && f.selector != stake(bytes32,bytes32,uint256,uint256,address).selector
    && f.selector != unstake(address,address,bytes32,uint256).selector
    && f.selector != unstake(address,address,bytes32,bytes32,uint256,uint256).selector
    && f.selector != claimAsStaker(address,bytes32).selector
    && f.selector != claimAsStaker(address,bytes32,bytes32).selector
    && f.selector != claimAsCollateralizedSLOTOwner(address,bytes32).selector
    && f.selector != claimAsCollateralizedSLOTOwner(address,bytes32,bytes32).selector
    && f.selector != registerKnotsToSyndicate(bytes32).selector
    && f.selector != registerKnotsToSyndicate(bytes32,bytes32).selector
    && f.selector != addPriorityStakers(address).selector
    && f.selector != addPriorityStakers(address,address).selector
    && f.selector != initialize(address,uint256,address,address,bytes32,bytes32).selector;

definition notRegisteredKnot(bytes32 knot) returns bool = !isKnotRegistered(knot) && !isNoLongerPartOfSyndicate(knot);
definition registeredKnot(bytes32 knot) returns bool = isKnotRegistered(knot) && !isNoLongerPartOfSyndicate(knot);
definition deregisteredKnot(bytes32 knot) returns bool = isKnotRegistered(knot) && isNoLongerPartOfSyndicate(knot);

definition PRECISION() returns uint256 = 1000000000000000000000000; //1e24

/*
Total ETH received must not decrease.
*/
rule totalEthReceivedMonotonicallyIncreases(method f) filtered {
    f -> notHarnessCall(f)
}{
    
    uint256 totalEthReceivedBefore = totalETHReceived();

    env e; calldataarg args;
    f(e, args);

    uint256 totalEthReceivedAfter = totalETHReceived();

    assert totalEthReceivedAfter >= totalEthReceivedBefore, "total ether received must not decrease";
}

/*
Address 0 must have zero sETH balance.
*/
invariant addressZeroHasNoBalance()
    sETHToken.balanceOf(0) == 0


/*
State transitions notRegisteredKnot => registeredKnot.
Not registered knot can only move to registered knot state
It can happen only through registerKnotsToSyndicate function.
*/
rule notRegisteredToRegistered(method f, bytes32 knot) filtered {
    f -> notHarnessCall(f) && f.selector != initialize(address,uint256,address[],bytes32[]).selector
} {
    env e;
    calldataarg args;

    require notRegisteredKnot(knot);
    f(e, args);

    if(!notRegisteredKnot(knot)) {
        assert registeredKnot(knot) && f.selector == registerKnotsToSyndicate(bytes32[]).selector;
    } else {
        assert true;
    }
}

/*
State transition registeredKnot => deregisteredKnot
Registered knot can only be move to deregistered state.
It can happen only through: deRegisterKnots, batchUpdateCollateralizedSlotOwnersAccruedETH,
claimAsCollateralizedSLOTOwner, updateCollateralizedSlotOwnersAccruedETH functions.
*/
rule registeredKnotToLaidOffKnot(method f, bytes32 knot) filtered {
    f -> notHarnessCall(f) && f.selector != initialize(address,uint256,address[],bytes32[]).selector
} {
    env e;
    calldataarg args;

    require registeredKnot(knot);
    f(e, args);

    if(!registeredKnot(knot)) {
        assert deregisteredKnot(knot) && (
            f.selector == deRegisterKnots(bytes32[]).selector ||
            f.selector == batchUpdateCollateralizedSlotOwnersAccruedETH(bytes32[]).selector ||
            f.selector == claimAsCollateralizedSLOTOwner(address,bytes32[]).selector ||
            f.selector == updateCollateralizedSlotOwnersAccruedETH(bytes32).selector
        );
    } else {
        assert true;
    }
}

/*
Not possible to change the state of deregistered. deregisteredKnot => X 
There should never be possibility of changing the state of deregistered knot.
*/
rule deregisteredKnotCannotChange(method f, bytes32 knot) filtered {
    f -> notHarnessCall(f) && f.selector != initialize(address,uint256,address[],bytes32[]).selector
} {
    env e;
    calldataarg args;

    require deregisteredKnot(knot);
    f(e, args);
    assert deregisteredKnot(knot), "failed, state change from deregisteredKnot";
}


/*
Only registered knots can stake.
*/
rule onlyRegisteredKnotsCanStake(bytes32 knot1, uint256 amount1, address behalfOf) {
    env e;

    stake@withrevert(e, knot1, amount1, behalfOf);
    bool reverted = lastReverted;

    assert notRegisteredKnot(knot1) || deregisteredKnot(knot1) => reverted,
        "failed, only registered knots should be able to stake";
}

/*
Value of accumulatedETHPerFreeFloatingShare can only increase.
There cannot be a single case of its decreasing.
*/
rule accumulatedETHPerFreeFloatingShareCanOnlyIncrease(method f) filtered {
    f -> notHarnessCall(f)
} {
    env e;
    calldataarg args;

    uint256 accumulatedETHPerFreeFloatingShareBefore = accumulatedETHPerFreeFloatingShare();
    f(e, args);

    assert accumulatedETHPerFreeFloatingShareBefore <= accumulatedETHPerFreeFloatingShare(),
        "failed accumulatedETHPerFreeFloatingShare decreased";
}

/*
Value of accumulatedETHPerCollateralizedSlotPerKnot can only increase.
There cannot be a single case of its decreased.
*/
rule accumulatedETHPerCollateralizedSlotPerKnotCanOnlyIncrease(method f) filtered {
    f -> notHarnessCall(f)
} {
    env e;
    calldataarg args;

    uint256 accumulatedETHPerCollateralizedSlotPerKnotBefore = accumulatedETHPerCollateralizedSlotPerKnot();
    f(e, args);

    assert accumulatedETHPerCollateralizedSlotPerKnotBefore <= accumulatedETHPerCollateralizedSlotPerKnot(),
        "failed accumulatedETHPerCollateralizedSlotPerKnot decreased";
}

/*
Once the priority of the staker has been set to true, it cannot be changed back.
*/
rule isPriorityStakerCannotGoBackToFalse(method f, address staker1) filtered {
    f -> notHarnessCall(f)    
} {
    env e;
    calldataarg args;

    require isPriorityStaker(staker1);
    f(e, args);
    assert isPriorityStaker(staker1),
        "failed, priority has changed back to false";
}


/*
Value of totalClaimed can only increase.
There cannot be case of its decreasing.
*/
rule totalClaimedCanOnlyIncrease(method f) filtered {
    f -> notHarnessCall(f)
} {
    env e;
    calldataarg args;

    uint256 totalClaimedBefore = totalClaimed();
    f(e, args);

    assert totalClaimedBefore <= totalClaimed(),
        "failed totalClaimed decreased";
}

/*
Value of numberOfRegisteredKnots:
- increases only through registerKnotsToSyndicate
- decreases only through deRegisterKnots
*/
rule numberOfRegisteredKnotsIncreaseDecrease(method f) filtered {
    f -> notHarnessCall(f)
} {
    env e;
    calldataarg args;

    require f.selector != initialize(address,uint256,address[],bytes32[]).selector;

    uint256 numberOfRegisteredKnotsBefore = numberOfRegisteredKnots();
    f(e, args);
    uint256 numberOfRegisteredKnotsAfter = numberOfRegisteredKnots();

    if(numberOfRegisteredKnotsBefore < numberOfRegisteredKnotsAfter) {
        assert f.selector == registerKnotsToSyndicate(bytes32[]).selector,
            "failed, numberOfRegisteredKnots increased not by registerKnotsToSyndicate";
    } else if(numberOfRegisteredKnotsBefore > numberOfRegisteredKnotsAfter) {
        assert f.selector == deRegisterKnots(bytes32[]).selector ||
            f.selector == batchUpdateCollateralizedSlotOwnersAccruedETH(bytes32[]).selector ||
            f.selector == updateCollateralizedSlotOwnersAccruedETH(bytes32).selector ||
            f.selector == claimAsCollateralizedSLOTOwner(address,bytes32[]).selector,
            "failed, numberOfRegisteredKnots increased not by registerKnotsToSyndicate";
    } else {
        assert true;
    }
}

/*
Once the knot has been set as no longer part of syndicate it cannot be set back.
*/
rule isNoLongerPartOfSyndicateTrueCannotGoBackFalse(method f, bytes32 knot1) filtered {
    f -> notHarnessCall(f)
} {
    env e;
    calldataarg args;

    require isNoLongerPartOfSyndicate(knot1);
    f(e, args);
    assert isNoLongerPartOfSyndicate(knot1),
        "failed, isNoLongerPartOfSyndicate[knot1] has changed back to false";
}

/*
User cannot stake less than 1 gwei and more than 12 ether total
*/
rule stakeValidAmount(bytes32 knot1, uint256 amount1, address behalfOf) {
    env e;
    uint256 MIN_ETHER = 1000000000; // 1 gwei
    uint256 MAX_ETHER = 12000000000000000000; // 12 ether

    uint256 sETHTotalStakeForKnotBefore = sETHTotalStakeForKnot(knot1);
    require sETHTotalStakeForKnotBefore <= MAX_ETHER;

    stake@withrevert(e, knot1, amount1, behalfOf);
    bool reverted = lastReverted;
    uint256 sETHTotalStakeForKnotAfter = sETHTotalStakeForKnot(knot1);

    if(!reverted) {
        assert sETHTotalStakeForKnotBefore + amount1 == sETHTotalStakeForKnotAfter,
            "failed, sETHTotalStakeForKnotAfter is not sum of amounts";
    } else {
        assert sETHTotalStakeForKnotBefore + amount1 > MAX_ETHER => reverted,
            "failed, it should revert for too much staked";
        assert amount1 < MIN_ETHER => reverted,
            "failed, didnt revert for too small stake";
    }
}

/*
Makes sure that only priority stakers can stake in priority timeframe.
*/
rule onlyPriorityStakersCanStakeBefore(bytes32 knot1, uint256 amount1, address behalfOf) {
    env e;

    stake@withrevert(e, knot1, amount1, behalfOf);
    bool reverted = lastReverted;

    assert e.block.number < priorityStakingEndBlock() && !isPriorityStaker(behalfOf) => reverted,
        "failed to revert for non-priority stakers";
}

/*
updateAccruedETHPerShares can only update values if there are more than 0 knots
*/
rule canOnlyAccrueWhenMoreThanZeroKnots() {
    env e;
    require numberOfRegisteredKnots() == 0;
    uint256 accumulatedETHPerFreeFloatingShareBefore = accumulatedETHPerFreeFloatingShare();
    uint256 lastSeenETHPerFreeFloatingBefore = lastSeenETHPerFreeFloating();
    uint256 accumulatedETHPerCollateralizedSlotPerKnotBefore = accumulatedETHPerCollateralizedSlotPerKnot();
    uint256 lastSeenETHPerCollateralizedSlotPerKnotBefore = lastSeenETHPerCollateralizedSlotPerKnot();
    updateAccruedETHPerShares(e);
    assert accumulatedETHPerFreeFloatingShareBefore == accumulatedETHPerFreeFloatingShare() &&
        lastSeenETHPerFreeFloatingBefore == lastSeenETHPerFreeFloating() &&
        accumulatedETHPerCollateralizedSlotPerKnotBefore == accumulatedETHPerCollateralizedSlotPerKnot() &&
        lastSeenETHPerCollateralizedSlotPerKnotBefore == lastSeenETHPerCollateralizedSlotPerKnot(),
            "failed, accrued when there are no knots";
}
/*
initialize function
- making sure storage variables are updated correctly
- tests the logic for adding priority staking
*/
rule unitTestInitialize(address contractOwner, address priorityStakingBlock, address staker1, address staker2, bytes32 knot1, bytes32 knot2) {
    env e;
    require priorityStakingEndBlock() != priorityStakingBlock;
    require !isPriorityStaker(staker1) && !isPriorityStaker(staker2);
    initialize(e, contractOwner, priorityStakingBlock, staker1, staker2, knot1, knot2);
    assert owner()  == contractOwner, "failed to udpate contract owner";
    assert isKnotRegistered(knot1) && isKnotRegistered(knot2), "failed to register knots";
    if(priorityStakingBlock > e.block.number) {
        assert priorityStakingEndBlock() == priorityStakingBlock,
            "failed to update priorityStakingEndBlock";
        assert isPriorityStaker(staker1) && isPriorityStaker(staker2);
    } else {
        assert priorityStakingEndBlock() != priorityStakingBlock,
            "failed, updated priorityStakingEndBlock and shouldnt";
        assert !isPriorityStaker(staker1) && !isPriorityStaker(staker2);
    }
}
/*
Test of registerKnotsToSyndicate function:
- testing that the list of knots are getting properly registered
*/
rule unitTestRegisterKnotsToSyndicate(bytes32 knot1, bytes32 knot2) {
    env e;
    require !isKnotRegistered(knot1) && !isKnotRegistered(knot2);
    registerKnotsToSyndicate(e, knot1, knot2);
    assert isKnotRegistered(knot1) && isKnotRegistered(knot2),
        "failed to register knots to syndicate";
}
/*
Test of deRegisterKnots function:
- testing that the list of knots are getting properly deregistered
*/
rule unitTestDeRegisterKnots(bytes32 knot1, bytes32 knot2) {
    env e;
    uint256 numberOfRegisteredKnotsBefore = numberOfRegisteredKnots();
    uint256 totalFreeFloatingSharesBefore = totalFreeFloatingShares();
    require isKnotRegistered(knot1) && isKnotRegistered(knot2);
    deRegisterKnots(e, knot1, knot2);
    assert isNoLongerPartOfSyndicate(knot1) && isNoLongerPartOfSyndicate(knot2),
        "failed to deregister knots from syndicate";
    assert lastAccumulatedETHPerFreeFloatingShare(knot1) == accumulatedETHPerFreeFloatingShare() &&
        lastAccumulatedETHPerFreeFloatingShare(knot2) == accumulatedETHPerFreeFloatingShare(),
         "failed to update lastAccumulatedETHPerFreeFloatingShare"; 
    assert totalFreeFloatingSharesBefore - sETHTotalStakeForKnot(knot1) - sETHTotalStakeForKnot(knot2)
        == totalFreeFloatingShares(),
        "failed to update totalFreeFloatingSharesBefore";
    assert numberOfRegisteredKnotsBefore - 2 == numberOfRegisteredKnots(),
        "failed to reduce number of registered knots";
}
/*
Test of addPriorityStakers function:
- testing that it is possible to add new priority stakers
*/
rule unitTestAddPriorityStakers(address staker1, address staker2) {
    env e;
    
    require !isPriorityStaker(staker1) && !isPriorityStaker(staker2);
    addPriorityStakers(e, staker1, staker2);
    assert isPriorityStaker(staker1) && isPriorityStaker(staker2),
        "failed to add priority stakers";
}
/*
Test of updatePriorityStakingBlock function:
- testing that function updates the value of priorityStakingEndBlock
*/
rule unitTestUpdatePriorityStakingBlock(uint256 endBlock) {
    env e;
    updatePriorityStakingBlock(e, endBlock);
    assert priorityStakingEndBlock() == endBlock,
        "failed to update priorityStakingEndBlock";
}
/*
Test of updateAccruedETHPerShares function:
- verify if storage variables are properly updated
*/
rule unitTestUpdateAccruedETHPerShares() {
    env e;
    require numberOfRegisteredKnots() > 0;
    /* calculations of calculateETHForFreeFloatingOrCollateralizedHolders */
    uint256 ethPerKnot = balance(currentContract) + totalClaimed();
    uint256 totalEthPerSlotType = ethPerKnot / 2;

    uint256 accumulatedETHPerFreeFloatingShareBefore = accumulatedETHPerFreeFloatingShare();
    uint256 accumulatedETHPerCollateralizedSlotPerKnotBefore = accumulatedETHPerCollateralizedSlotPerKnot();

    uint256 lastSeenETHPerCollateralizedSlotPerKnotBefore = lastSeenETHPerCollateralizedSlotPerKnot();
    uint256 lastSeenETHPerFreeFloatingBefore = lastSeenETHPerFreeFloating();

    updateAccruedETHPerShares(e);

    if(totalFreeFloatingShares() > 0) {
        assert accumulatedETHPerFreeFloatingShareBefore +
            ((totalEthPerSlotType - lastSeenETHPerFreeFloatingBefore) * PRECISION()) / totalFreeFloatingShares()
            == accumulatedETHPerFreeFloatingShare(),
                "failed to update accumulatedETHPerFreeFloatingShare";
        assert totalEthPerSlotType == lastSeenETHPerFreeFloating(),
            "failed to update totalEthPerSlot";
    }
    uint256 accumulatedETHPerCollateralizedSlotPerKnotAfter = accumulatedETHPerCollateralizedSlotPerKnotBefore +
        (totalEthPerSlotType - lastSeenETHPerCollateralizedSlotPerKnotBefore) / numberOfRegisteredKnots();
    assert accumulatedETHPerCollateralizedSlotPerKnotAfter == accumulatedETHPerCollateralizedSlotPerKnot(),
        "failed to update accumulatedETHPerCollateralizedSlotPerKnot";
    assert totalEthPerSlotType == lastSeenETHPerCollateralizedSlotPerKnot(),
        "failed to update lastSeenETHPerCollateralizedSlotPerKnot";
}
/*
Test of stake function:
- verify if storage variables are properly updated
- sETH are transfered from user to syndicate contract
*/
rule unitTestStake(bytes32 knot1, bytes32 knot2, uint256 amount1, uint256 amount2, address behalfOf) {
    env e;
    require e.msg.sender != currentContract;
    require knot1 != knot2;
    uint256 totalFreeFloatingSharesBefore = totalFreeFloatingShares();
    uint256 knot1StakeBefore = sETHTotalStakeForKnot(knot1);
    uint256 knot2StakeBefore = sETHTotalStakeForKnot(knot2);
    uint256 knot1sETHStakedBalanceForKnotBefore = sETHStakedBalanceForKnot(knot1, behalfOf);
    uint256 knot2sETHStakedBalanceForKnotBefore = sETHStakedBalanceForKnot(knot2, behalfOf);
    uint256 knot1sETHUserClaimForKnotBefore = sETHUserClaimForKnot(knot1, behalfOf);
    uint256 knot2sETHUserClaimForKnotBefore = sETHUserClaimForKnot(knot2, behalfOf);
    uint256 usersETHBalanceBefore = sETHToken.balanceOf(e.msg.sender);
    uint256 syndicatesETHBalanceBefore = sETHToken.balanceOf(currentContract);
    require usersETHBalanceBefore + syndicatesETHBalanceBefore <= max_uint256;
    stake(e, knot1, knot2, amount1, amount2, behalfOf);
    assert totalFreeFloatingSharesBefore + amount1 + amount2 == totalFreeFloatingShares(),
        "failed to increase totalFreeFloatingShares";
    if(knot1 != knot2) {
        assert knot1StakeBefore + amount1 == sETHTotalStakeForKnot(knot1),
            "failed to add stake for knot1";
        assert knot2StakeBefore + amount2 == sETHTotalStakeForKnot(knot2),
            "failed to add stake for knot2";
        assert knot1sETHStakedBalanceForKnotBefore + amount1 == sETHStakedBalanceForKnot(knot1, behalfOf),
            "failed to add staked balance for knot - knot1";
        assert knot2sETHStakedBalanceForKnotBefore + amount2 == sETHStakedBalanceForKnot(knot2, behalfOf),
            "failed to add staked balance for knot - knot2";

        assert knot1sETHUserClaimForKnotBefore + (amount1 * accumulatedETHPerFreeFloatingShare() / PRECISION())
            == sETHUserClaimForKnot(knot1, behalfOf),
            "failed to add stake to claim for knot - knot1";
        assert knot2sETHUserClaimForKnotBefore + (amount2 * accumulatedETHPerFreeFloatingShare() / PRECISION())
            == sETHUserClaimForKnot(knot2, behalfOf),
            "failed to add stake to claim for knot - knot1";

    } else {
        assert knot1StakeBefore + amount1 + amount2 == sETHTotalStakeForKnot(knot1),
            "failed to add stake for knot1/knot2";
        assert knot1sETHStakedBalanceForKnotBefore + amount1 + amount2 == sETHStakedBalanceForKnot(knot1, behalfOf),
            "failed to add stake balance for knot - knot1/knot2";
        assert knot1sETHUserClaimForKnotBefore + (amount1 * accumulatedETHPerFreeFloatingShare() / PRECISION()) +
            (amount2 * accumulatedETHPerFreeFloatingShare() / PRECISION()) == sETHUserClaimForKnot(knot2, behalfOf),
            "failed to add stake to claim for knot - knot1/knot2";
    }

    assert usersETHBalanceBefore - amount1 - amount2 == sETHToken.balanceOf(e.msg.sender),
        "failed to decrease user's sETH balance";
    assert syndicatesETHBalanceBefore + amount1 + amount2 == sETHToken.balanceOf(currentContract),
        "failed to increase syndicate's sETH balance";
}

/*
Test of unstake function:
- verify that storage variables are properly updated
- sETH are transfered from syndicate contract to user
*/
rule unitTestUnstake(address unclaimedRecipient, address sETHRecipient, bytes32 knot1, bytes32 knot2, uint256 amount1, uint256 amount2) {
    env e;
    require sETHRecipient != currentContract;
    require knot1 != knot2;
    uint256 knot1StakeBefore = sETHTotalStakeForKnot(knot1);
    uint256 knot2StakeBefore = sETHTotalStakeForKnot(knot2);
    uint256 usersETHBalanceBefore = sETHToken.balanceOf(sETHRecipient);
    uint256 syndicatesETHBalanceBefore = sETHToken.balanceOf(currentContract);
    require usersETHBalanceBefore + syndicatesETHBalanceBefore <= max_uint256;
    unstake(e, unclaimedRecipient, sETHRecipient, knot1, knot2, amount1, amount2);
    if(knot1 != knot2) {
        assert knot1StakeBefore - amount1 == sETHTotalStakeForKnot(knot1),
            "failed to remove stake for knot1";
        assert knot2StakeBefore - amount2 == sETHTotalStakeForKnot(knot2),
            "failed to remove stake for knot2";
    } else {
        assert knot1StakeBefore - amount1 - amount2 == sETHTotalStakeForKnot(knot1),
            "failed to remove stake knot1/knot2";
    }
    assert usersETHBalanceBefore + amount1 + amount2 == sETHToken.balanceOf(sETHRecipient),
        "failed to decrease user's sETH balance";
    assert syndicatesETHBalanceBefore - amount1 - amount2 == sETHToken.balanceOf(currentContract),
        "failed to increase syndicate's sETH balance";
}
/*
Test of claimAsStaker function:
- making sure that storage variables are properly updated
- ether is sent to staker
*/
rule unitTestClaimAsStaker(address recipient, bytes32 knot1, bytes32 knot2) {
    env e;
    updateAccruedETHPerShares(e);
    uint256 contractBalanceBefore = balance(currentContract);
    uint256 recipientBalanceBefore = balance(recipient);
    require contractBalanceBefore + recipientBalanceBefore <= max_uint256;
    require recipient != currentContract;
    uint256 totalClaimedBefore = totalClaimed();
    uint256 unclaimedUserShareKnot1 = calculateUnclaimedFreeFloatingETHShare(knot1, e.msg.sender);
    uint256 unclaimedUserShareKnot2 = calculateUnclaimedFreeFloatingETHShare(knot2, e.msg.sender);
    claimAsStaker(e, recipient, knot1, knot2);
    if(knot1 != knot2) {
        assert totalClaimedBefore + unclaimedUserShareKnot1 + unclaimedUserShareKnot2 == totalClaimed(),
            "failed to increase totalClaimed";
        assert contractBalanceBefore - unclaimedUserShareKnot1 - unclaimedUserShareKnot2 == balance(currentContract),
            "failed to transfer ETH out of contract";
        assert recipientBalanceBefore + unclaimedUserShareKnot1 + unclaimedUserShareKnot2 == balance(recipient),
            "failed to transfer ETH to recipient";
    } else {
        assert totalClaimedBefore + unclaimedUserShareKnot1 == totalClaimed(),
            "failed to increase totalClaimed with single knot";
        assert contractBalanceBefore - unclaimedUserShareKnot1 == balance(currentContract),
            "failed to transfer ETH out of contract";
        assert recipientBalanceBefore + unclaimedUserShareKnot1 == balance(recipient),
            "failed to transfer ETH to recipient";
    }
}
/*
Test of claimAsCollateralizedSLOTOwner function:
- making sure that storage variables are properly updated
- ether is sent to SLOTowner
*/
rule unitTestClaimAsCollateralizedSLOTOwner(address recipient, bytes32 knot1, bytes32 knot2) {
    env e;
    updateAccruedETHPerShares(e);
    batchUpdateCollateralizedSlotOwnersAccruedETH(e, knot1, knot2);
    uint256 contractBalanceBefore = balance(currentContract);
    uint256 recipientBalanceBefore = balance(recipient);
    require contractBalanceBefore + recipientBalanceBefore <= max_uint256;
    require recipient != currentContract;
    uint256 totalClaimedBefore = totalClaimed();
    uint256 unclaimedUserShareKnot1 = accruedEarningPerCollateralizedSlotOwnerOfKnot(knot1, e.msg.sender) - claimedPerCollateralizedSlotOwnerOfKnot(knot1, e.msg.sender);
    uint256 unclaimedUserShareKnot2 = accruedEarningPerCollateralizedSlotOwnerOfKnot(knot2, e.msg.sender) - claimedPerCollateralizedSlotOwnerOfKnot(knot2, e.msg.sender);
    claimAsCollateralizedSLOTOwner(e, recipient, knot1, knot2);
    if(knot1 != knot2) {
        assert totalClaimedBefore + unclaimedUserShareKnot1 + unclaimedUserShareKnot2 == totalClaimed(),
            "failed to increase totalClaimed";
        assert contractBalanceBefore - unclaimedUserShareKnot1 - unclaimedUserShareKnot2 == balance(currentContract),
            "failed to transfer ETH out of contract";
        assert recipientBalanceBefore + unclaimedUserShareKnot1 + unclaimedUserShareKnot2 == balance(recipient),
            "failed to transfer ETH to recipient";
    } else {
        assert totalClaimedBefore + unclaimedUserShareKnot1 == totalClaimed(),
            "failed to increase totalClaimed with single knot";
        assert contractBalanceBefore - unclaimedUserShareKnot1 == balance(currentContract),
            "failed to transfer ETH out of contract";
        assert recipientBalanceBefore + unclaimedUserShareKnot1 == balance(recipient),
            "failed to transfer ETH to recipient";
    }
}
