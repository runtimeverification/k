// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import edu.uci.ics.jung.graph.DirectedOrderedSparseMultigraph;
import org.kframework.backend.java.kil.ConstrainedTerm;


/**
 * Backend specific execution graph.
 */
public class ConstrainedExecutionGraph extends DirectedOrderedSparseMultigraph<ConstrainedTerm,
        ConstrainedTransition> {
}
