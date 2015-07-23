// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.debugger;


import org.kframework.Rewriter;
import org.kframework.definition.Rule;
import org.kframework.kore.K;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.NavigableMap;
import java.util.Optional;
import java.util.TreeMap;

/**
 * Kore Based Debugger Implementation.
 */
public class KoreKDebug implements KDebug {

    private final int DEFAULT_ID = 0;
    private List<DebuggerState> stateList;
    private DebuggerState activeState;
    private Rewriter rewriter;
    private int checkpointInterval;
    private int activeStateNum;


    /**
     * Start a Debugger Session. The initial Configuration becomes a part of the new and only state of the Debugger
     *
     * @param initialK The initial Configuration.
     * @param rewriter The Rewriter being used.
     */
    public KoreKDebug(K initialK, Rewriter rewriter, int checkpointInterval) {
        this.stateList = new ArrayList<>();
        this.rewriter = rewriter;
        this.checkpointInterval = checkpointInterval;
        NavigableMap<Integer, RewriterCheckpoint> checkpointMap = new TreeMap<>();
        checkpointMap.put(DEFAULT_ID, new RewriterCheckpoint(initialK));
        DebuggerState initialState = new DebuggerState(initialK, DEFAULT_ID, checkpointMap);
        stateList.add(initialState);
        activeState = initialState;
        activeStateNum = DEFAULT_ID;
    }

    @Override
    public void setCheckpointInterval(int checkpointInterval) {
        this.checkpointInterval = checkpointInterval;
    }

    @Override
    public DebuggerState step(int steps) {
        K currentK = activeState.getCurrentK();
        int activeStateCheckpoint = activeState.getStepNum();
        int lastCheckpoint = activeState.getlastMapCheckpoint();
        DebuggerState nextActiveState;
        stateList.remove(activeState);
        /* Not enough steps for a new checkpoint */
        if (activeStateCheckpoint + steps < lastCheckpoint + checkpointInterval) {
            currentK = rewriter.execute(currentK, Optional.of(new Integer(steps)));
            activeStateCheckpoint += steps;
            NavigableMap<Integer, RewriterCheckpoint> checkpointMap = activeState.getCheckpointMap();
            nextActiveState = new DebuggerState(currentK, activeStateCheckpoint, checkpointMap);
            stateList.add(activeStateNum, nextActiveState);
            activeState = nextActiveState;
            return nextActiveState;
        }
        /* Move to the next Checkpoint */
        if (lastCheckpoint + checkpointInterval - activeStateCheckpoint < 0) {
            /* Case when checkpointInterval has been modified */
            lastCheckpoint = (activeStateCheckpoint / checkpointInterval) * checkpointInterval;
        }
        currentK = rewriter.execute(currentK, Optional.of(new Integer(lastCheckpoint + checkpointInterval - activeStateCheckpoint)));
        NavigableMap<Integer, RewriterCheckpoint> checkpointMap = activeState.getCheckpointMap();
        steps -= lastCheckpoint + checkpointInterval - activeStateCheckpoint;
        activeStateCheckpoint = lastCheckpoint + checkpointInterval;
        checkpointMap.put(new Integer(activeStateCheckpoint), new RewriterCheckpoint(currentK));
        /* Register Checkpoints and Proceed. Take Jumps equal to the Checkpoint Interval */
        while (steps > checkpointInterval) {
            activeStateCheckpoint += checkpointInterval;
            RewriterCheckpoint newCheckpoint = new RewriterCheckpoint(rewriter.execute(currentK, Optional.of(new Integer(checkpointInterval))));
            steps -= checkpointInterval;
            checkpointMap.put(new Integer(activeStateCheckpoint), newCheckpoint);
            currentK = newCheckpoint.getCheckpointK();
        }

        /* Final remaining steps */
        currentK = rewriter.execute(currentK, Optional.of(new Integer(steps)));
        activeStateCheckpoint += steps;
        nextActiveState = new DebuggerState(currentK, activeStateCheckpoint, checkpointMap);
        activeState = nextActiveState;
        stateList.add(activeStateNum, activeState);
        return nextActiveState;
    }

    @Override
    public DebuggerState backStep(int steps) {
        int currentCheckpoint = activeState.getStepNum();
        int target = currentCheckpoint - steps;
        NavigableMap<Integer, RewriterCheckpoint> currMap = activeState.getCheckpointMap();
        Map.Entry<Integer, RewriterCheckpoint> relevantEntry = currMap.floorEntry(target);
        if (relevantEntry == null) {
            /* Invalid Operation, no need to change the state */
            return null;
        }

        int floorKey = relevantEntry.getKey();
        activeState = new DebuggerState(relevantEntry.getValue().getCheckpointK(), floorKey, new TreeMap<>(currMap.headMap(floorKey, true)));
        stateList.add(activeState);
        activeStateNum = stateList.size() - 1;
        return step(target - floorKey);
    }

    @Override
    public DebuggerState jumpTo(int stateNum) {
        NavigableMap<Integer, RewriterCheckpoint> checkpointMap = activeState.getCheckpointMap();
        int firstKey = checkpointMap.firstKey();
        if (stateNum < firstKey) {
            return null;
        }
        int lastKey = activeState.getStepNum();
        if (stateNum >= lastKey) {
            return step(stateNum - lastKey);
        }
        return backStep(lastKey - stateNum);
    }

    @Override
    public List<? extends Map<? extends K, ? extends K>> search(Optional<Integer> startStateId, Rule searchPattern, Optional<Integer> depth, Optional<Integer> bounds) {
        if (startStateId.isPresent()) {
            jumpTo(startStateId.get());
        }
        return rewriter.search(activeState.getCurrentK(), depth, bounds, searchPattern);
    }

    @Override
    public DebuggerState resume() {
        do {
            step(checkpointInterval);
        } while (!isFinalResult(activeState.getCurrentK()));
        return activeState;
    }

    @Override
    public List<DebuggerState> getStates() {
        return new ArrayList<>(stateList);

    }

    private boolean isFinalResult(K currK) {
        return currK.equals(rewriter.execute(currK, Optional.of(1)));
    }

    @Override
    public DebuggerState setState(int stateNum, Optional<Integer> configurationNum) {
        DebuggerState newActiveState = stateList.get(stateNum);
        if (newActiveState == null) {
            return null;
        }
        activeState = newActiveState;
        activeStateNum = stateNum;
        configurationNum.ifPresent(configNum -> jumpTo(configNum));
        return activeState;
    }

    @Override
    public DebuggerState getActiveState() {
        return activeState;
    }

    private DebuggerState createCopyState(DebuggerState copyState) {
        DebuggerState newState = new DebuggerState(activeState);
        stateList.add(newState);
        return newState;
    }

    @Override
    public DebuggerState peek(Optional<Integer> stateNum, Optional<Integer> configurationNum) {
        if (stateNum.isPresent()) {
            int concreteStateNum = stateNum.get();
            if (concreteStateNum < 0 || concreteStateNum >= stateList.size()) {
                return null;
            }
            DebuggerState requestedState = stateList.get(concreteStateNum);
            if (configurationNum.isPresent()) {
                Integer concreteConfigurationNum = configurationNum.get();
                if (concreteConfigurationNum < 0) {
                    return null;
                }
                DebuggerState tempState = createCopyState(requestedState);
                activeState = tempState;
                DebuggerState resultantState = jumpTo(concreteConfigurationNum);
                return resultantState;
            }
            return requestedState;
        }
        return activeState;
    }
}
