// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.indexing;

public enum IndexingAlgorithm {
    /**
     * Represents an index backed by {@link IndexingTable}
     */
    RULE_TABLE(IndexingTable.class);

    IndexingAlgorithm(Class<? extends RuleIndex> clazz) {
        this.clazz = clazz;
    }

    public final Class<? extends RuleIndex> clazz;
}
