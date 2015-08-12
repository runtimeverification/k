// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.debugger;


import org.kframework.Rewriter;
import org.kframework.definition.Rule;
import org.kframework.kore.K;
import org.kframework.krun.tools.Debugger;

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
    private int activeStateIndex;
    private Rewriter rewriter;
    private int checkpointInterval;


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
        activeStateIndex = DEFAULT_ID;
    }

    @Override
    public void setCheckpointInterval(int checkpointInterval) {
        this.checkpointInterval = checkpointInterval;
    }

    @Override
    public DebuggerState step(int currentStateIndex, int steps) {
        DebuggerState currentState = stateList.get(currentStateIndex);
        stateList.remove(currentStateIndex);
        K currentK = currentState.getCurrentK();
        int activeStateCheckpoint = currentState.getStepNum();
        int lastCheckpoint = currentState.getlastMapCheckpoint();
        DebuggerState nextState;
        /* Not enough steps for a new checkpoint */
        if (activeStateCheckpoint + steps < lastCheckpoint + checkpointInterval) {
            currentK = rewriter.execute(currentK, Optional.of(new Integer(steps)));
            activeStateCheckpoint += steps;
            NavigableMap<Integer, RewriterCheckpoint> checkpointMap = currentState.getCheckpointMap();
            nextState = new DebuggerState(currentK, activeStateCheckpoint, checkpointMap);
            stateList.add(currentStateIndex, nextState);
            return nextState;
        }
        /* Move to the next Checkpoint */
        if (lastCheckpoint + checkpointInterval - activeStateCheckpoint < 0) {
            /* Case when checkpointInterval has been modified */
            lastCheckpoint = (activeStateCheckpoint / checkpointInterval) * checkpointInterval;
        }
        currentK = rewriter.execute(currentK, Optional.of(new Integer(lastCheckpoint + checkpointInterval - activeStateCheckpoint)));
        NavigableMap<Integer, RewriterCheckpoint> checkpointMap = currentState.getCheckpointMap();
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
        nextState = new DebuggerState(currentK, activeStateCheckpoint, checkpointMap);
        stateList.add(currentStateIndex, nextState);
        return nextState;
    }

    @Override
    public DebuggerState backStep(int initialStateNum, int steps) {
        DebuggerState currentState = stateList.get(initialStateNum);
        int currentCheckpoint = currentState.getStepNum();
        int target = currentCheckpoint - steps;
        NavigableMap<Integer, RewriterCheckpoint> currMap = currentState.getCheckpointMap();
        Map.Entry<Integer, RewriterCheckpoint> relevantEntry = currMap.floorEntry(target);
        if (relevantEntry == null) {
            /* Invalid Operation, no need to change the state */
            return null;
        }

        int floorKey = relevantEntry.getKey();
        currentState = new DebuggerState(relevantEntry.getValue().getCheckpointK(), floorKey, new TreeMap<>(currMap.headMap(floorKey, true)));
        stateList.remove(initialStateNum);
        stateList.add(initialStateNum, currentState);
        return step(initialStateNum, target - floorKey);
    }

    @Override
    public DebuggerState jumpTo(int initialStateNum, int configurationNum) {
        DebuggerState currentState = stateList.get(initialStateNum);
        NavigableMap<Integer, RewriterCheckpoint> checkpointMap = currentState.getCheckpointMap();
        int firstKey = checkpointMap.firstKey();
        if (configurationNum < firstKey) {
            return null;
        }
        int lastKey = currentState.getStepNum();
        stateList.remove(initialStateNum);
        stateList.add(currentState);
        if (configurationNum >= lastKey) {
            return step(initialStateNum, configurationNum - lastKey);
        }
        return backStep(initialStateNum, lastKey - configurationNum);
    }

    @Override
    public List<? extends Map<? extends K, ? extends K>> search(Optional<Integer> startStateId, Rule searchPattern, Optional<Integer> depth, Optional<Integer> bounds) {
        if (startStateId.isPresent()) {
            jumpTo(activeStateIndex, startStateId.get());
        }
        return rewriter.search(stateList.get(activeStateIndex).getCurrentK(), depth, bounds, searchPattern);
    }

    @Override
    public DebuggerState resume() {
        DebuggerState activeState = stateList.get(activeStateIndex);
        do {
            step(activeStateIndex, checkpointInterval);
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
        activeStateIndex= stateNum;
        configurationNum.ifPresent(configNum -> jumpTo(stateNum, configNum));
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
        DebuggerState requestedState;
        if (stateNum.isPresent()) {
            int concreteStateNum = stateNum.get();
            if (concreteStateNum < 0 || concreteStateNum >= stateList.size()) {
                return null;
            }
            requestedState = stateList.get(concreteStateNum);
        } else {
            requestedState = activeState;
        }
        if (configurationNum.isPresent()) {
            Integer concreteConfigurationNum = configurationNum.get();
            if (concreteConfigurationNum < 0) {
                return null;
            }
            activeState = createCopyState(requestedState);
            return jumpTo(concreteConfigurationNum);
        }
        return requestedState;
    }

}
