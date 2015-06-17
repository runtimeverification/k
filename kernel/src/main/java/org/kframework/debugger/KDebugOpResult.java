// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.debugger;

import org.kframework.kore.K;

import java.util.NavigableMap;
import java.util.Optional;

/**
 * Created by Manasvi on 6/16/15.
 * <p>
 * The result of using a debugger operation
 */
public class KDebugOpResult {

    private Optional<K> finalK;

    private Optional<NavigableMap<Integer, Checkpoint>> checkpointMap;

    public KDebugOpResult(K finalK, NavigableMap<Integer, Checkpoint> checkpointMap) {
        this.finalK = Optional.ofNullable(finalK);
        this.checkpointMap = Optional.ofNullable(checkpointMap);
    }

    public Optional<K> getFinalK() {
        return finalK;
    }

    public Optional<NavigableMap<Integer, Checkpoint>> getCheckpointMap() {
        return checkpointMap;
    }
}
