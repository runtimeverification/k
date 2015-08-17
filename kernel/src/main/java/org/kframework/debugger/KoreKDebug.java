// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.debugger;


import org.kframework.Rewriter;
import org.kframework.RewriterResult;
import org.kframework.attributes.Source;
import org.kframework.definition.Rule;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kore.K;
import org.kframework.kore.KVariable;
import org.kframework.krun.KRun;
import org.kframework.krun.KRunOptions;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;

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
    private FileUtil files;
    private final KExceptionManager kem;
    private KRunOptions options;
    private CompiledDefinition compiledDef;

    /**
     * Start a Debugger Session. The initial Configuration becomes a part of the new and only state of the Debugger
     *
     * @param initialK The initial Configuration.
     * @param rewriter The Rewriter being used.
     */
    public KoreKDebug(K initialK, Rewriter rewriter, int checkpointInterval, FileUtil files, KExceptionManager kem, KRunOptions options, CompiledDefinition compiledDef) {
        this.stateList = new ArrayList<>();
        this.rewriter = rewriter;
        this.checkpointInterval = checkpointInterval;
        this.files = files;
        this.kem = kem;
        this.options = options;
        this.compiledDef = compiledDef;
        NavigableMap<Integer, K> checkpointMap = new TreeMap<>();
        checkpointMap.put(DEFAULT_ID, initialK);
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
        RewriterResult result;
        NavigableMap<Integer, K> checkpointMap = currentState.getCheckpointMap();
        while (steps > checkpointInterval) {
            result = rewriter.execute(currentK, Optional.of(checkpointInterval));
            if (isFinalState(checkpointInterval, result)) {
                return getDebuggerState(currentStateIndex, activeStateCheckpoint, result, checkpointMap);
            }
            steps -= checkpointInterval;
            activeStateCheckpoint += checkpointInterval;
            checkpointMap.put(activeStateCheckpoint, result.k());
            currentK = result.k();
        }
        result = rewriter.execute(currentK, Optional.of(steps));
        if (isFinalState(steps, result)) {
            return getDebuggerState(currentStateIndex, activeStateCheckpoint, result, checkpointMap);
        }
        activeStateCheckpoint += steps;
        DebuggerState nextState = new DebuggerState(result.k(), activeStateCheckpoint, checkpointMap);
        stateList.add(nextState);
        return nextState;
    }

    private DebuggerState getDebuggerState(int currentStateIndex, int activeStateCheckpoint, RewriterResult result, NavigableMap<Integer, K> checkpointMap) {
        activeStateCheckpoint += result.rewriteSteps().get();
        DebuggerState nextState = new DebuggerState(result.k(), activeStateCheckpoint, checkpointMap);
        stateList.add(currentStateIndex, nextState);
        return nextState;
    }

    private boolean isFinalState(int steps, RewriterResult result) {
        return result.rewriteSteps().isPresent() && result.rewriteSteps().get() < steps;
    }

    @Override
    public DebuggerState backStep(int initialStateNum, int steps) {
        DebuggerState currentState = stateList.get(initialStateNum);
        int currentCheckpoint = currentState.getStepNum();
        int target = currentCheckpoint - steps;
        NavigableMap<Integer, K> currMap = currentState.getCheckpointMap();
        Map.Entry<Integer, K> relevantEntry = currMap.floorEntry(target);
        if (relevantEntry == null) {
            /* Invalid Operation, no need to change the state */
            return null;
        }

        int floorKey = relevantEntry.getKey();
        currentState = new DebuggerState(relevantEntry.getValue(), floorKey, new TreeMap<>(currMap.headMap(floorKey, true)));
        stateList.remove(initialStateNum);
        stateList.add(initialStateNum, currentState);
        return step(initialStateNum, target - floorKey);
    }

    @Override
    public DebuggerState jumpTo(int initialStateNum, int configurationNum) {
        DebuggerState currentState = stateList.get(initialStateNum);
        NavigableMap<Integer, K> checkpointMap = currentState.getCheckpointMap();
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
    public List<? extends Map<? extends K, ? extends K>> search(Rule searchPattern, Optional<Integer> depth, Optional<Integer> bounds) {
        return rewriter.search(stateList.get(activeStateIndex).getCurrentK(), depth, bounds, searchPattern);
    }

    @Override
    public DebuggerState resume() {
        DebuggerState activeState = stateList.get(activeStateIndex);
        DebuggerState steppedState = activeState;
        do {
            activeState = steppedState;
            steppedState = step(activeStateIndex, checkpointInterval);
        } while (steppedState.getStepNum() - activeState.getStepNum() >= checkpointInterval);
        return steppedState;
    }

    @Override
    public List<DebuggerState> getStates() {
        return new ArrayList<>(stateList);
    }


    @Override
    public DebuggerState setState(int stateNum) {
        if (stateNum > stateList.size() - 1) {
            return null;
        }
        DebuggerState newActiveState = stateList.get(stateNum);
        if (newActiveState == null) {
            return null;
        }
        activeStateIndex = stateNum;
        return newActiveState;
    }

    @Override
    public int getActiveStateId() {
        return activeStateIndex;
    }

    @Override
    public DebuggerState createCopy(int stateNum) {
        DebuggerState newState = new DebuggerState(stateList.get(stateNum));
        stateList.add(newState);
        return newState;
    }

    @Override
    public DebuggerState getActiveState() {
        return stateList.get(activeStateIndex);
    }

    @Override
    public Map<? extends K, ? extends K> match(String pattern) {
        System.out.println("Got Pattern: " + pattern);
        Rule parsedPattern = KRun.pattern(files, kem, pattern, options, compiledDef, Source.apply("Debugger TUI"));
        List<Map<KVariable, K>> subst = rewriter.match(getActiveState().getCurrentK(), parsedPattern);
        return null;
    }
}
