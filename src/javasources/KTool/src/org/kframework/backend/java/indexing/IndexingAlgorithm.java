// Copyright (C) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.indexing;

import org.kframework.backend.java.indexing.pathIndex.PathIndex;

public enum IndexingAlgorithm {
    /**
     * Represents an index backed by {@link IndexingTable}
     */
    RULE_TABLE,
    
    /**
     * Represents an index backed by {@link PathIndex}
     */
    PATH
}
