// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import edu.uci.ics.jung.graph.DirectedOrderedSparseMultigraph;
import org.apache.commons.lang3.tuple.Pair;
import org.kframework.backend.java.kil.ConstrainedTerm;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.Variable;

import java.util.Map;

/**
 * Backend specific execution graph.
 */
public class ConstrainedExecutionGraph extends DirectedOrderedSparseMultigraph<ConstrainedTerm,
        Pair<Rule, Map<Variable, Term>>> {
}
