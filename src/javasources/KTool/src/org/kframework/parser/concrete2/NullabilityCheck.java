package org.kframework.parser.concrete2;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * Helper class in the parser that finds all of the nullable NonTerminals in a grammar.
 */
public class NullabilityCheck {
    /**
     * Starting from the start symbol, find all the non terminals that can match on the empty string.
     * @param startNt The start non terminal.
     * @return A set of all reachable non terminals that are nullable.
     */
    public static Set<Grammar.State> getReachableNullableStates(Grammar.NonTerminal startNt) {
        NullabilityCheck nc = new NullabilityCheck();
        nc.checkNullability2(startNt);
        return nc.nullable;
    }

    // list NonTerminals reachable from the start symbol.
    // the value of the map keeps a reference to all the states which call NonTerminals
    Map<Grammar.NonTerminal, Set<Grammar.NonTerminalState>> reachableNonTerminals = new HashMap<>();
    // accumulate the results here
    Set<Grammar.State> nullable = new HashSet<>();

    /**
     * Nullability of a state is based on the following two implications:
     * A. EntryState state => nullable(state)
     * B. nullable(state) && childNullable(state) => nullable(state.next)
     * Where childNullable(state) is true when it is possible to get from the start of the state to the end of the state without consuming input.
     *
     * The following algorithm is a least fixed-point algorithm for solving those implications.
     * mark(state) is called when we discover an implication implying nullable(state). We can discover this implication one of three ways:
     *
     * 1. A state is an entry state (see rule A)
     * 2. The nullable(state) in rule B becomes true (in which case we check childNullable).)
     * 3. The childNullable(state) in rule B becomes true (in which case we check nullable(state).)
     * (ChildNullable(state) becomes true when an exit state becomes nullable.)
     * @param startNt The start symbol in the grammar.
     * @return A set with all the NonTerminals that can become nullable.
     */
    private void checkNullability2(Grammar.NonTerminal startNt) {
        reachableNonTerminals.put(startNt, new HashSet<Grammar.NonTerminalState>());
        collectReachableNT(startNt.entryState, new HashSet<Grammar.State>());
        // A state is nullable iff the *start* of it is reachable from the entry of its nt without consuming input
        // A non-terminal is nullable if its exit state is nullable
        for (Map.Entry<Grammar.NonTerminal, Set<Grammar.NonTerminalState>> entry : reachableNonTerminals.entrySet()) {
            mark(entry.getKey().entryState);
        }
    }

    /** marks a state as nullable if it is not already, and calls mark on any
     * states that should be nullable as a result.
     */
    private void mark(Grammar.State state) {
        if (!nullable.contains(state)) {
            nullable.add(state);
            if (state instanceof Grammar.NextableState) {
                if (childNullable(state))
                    for (Grammar.State s : ((Grammar.NextableState) state).next)
                        mark(s);
            } else {
                assert state instanceof Grammar.ExitState: "I was expecting this element to be of type ExitState";
                // previous calls to childNullable would have returned False
                // so now we restart those recursions
                for (Grammar.State s : reachableNonTerminals.get(state.nt))
                    if (nullable.contains(s)) {
                        // assert s instanceof Grammar.NonTerminalState : "Intermediary states are NonTerminalStates?";
                        for (Grammar.State child : ((Grammar.NextableState)s).next) {
                            mark(child);
                        }
                    }
            }
        }
    }

    private boolean childNullable(Grammar.State state) {
        if (state instanceof Grammar.EntryState)
            return true;
        if (state instanceof Grammar.PrimitiveState)
            return ((Grammar.PrimitiveState)state).isNullable();
        if (state instanceof Grammar.NonTerminalState)
            if (nullable.contains(((Grammar.NonTerminalState)state).child.exitState))
                return true;
        return false;
    }

    /**
     * Recursive DFS that traverses all the states and returns a set of all reachable {@Link NonTerminal}.
     * @param start The state from which to run the collector.
     * @param visited Start with an empty Set<State>. Used as intermediate data.
     * @return A set of all reachable {@Link NonTerminal}.
     */
    private void collectReachableNT(Grammar.State start, Set<Grammar.State> visited) {
        if (visited.contains(start))
            return;
        visited.add(start);
        if (start instanceof Grammar.NextableState) {
            Grammar.NextableState ns = (Grammar.NextableState) start;
            for (Grammar.State st : ns.next) {
                if (st instanceof Grammar.NonTerminalState) {
                    Grammar.NonTerminalState nts = (Grammar.NonTerminalState) st;
                    if (reachableNonTerminals.containsKey(nts.child)) {
                        reachableNonTerminals.get(nts.child).add(nts);
                    } else {
                        reachableNonTerminals.put(nts.child, new HashSet<Grammar.NonTerminalState>(Arrays.asList(nts)));
                    }
                    collectReachableNT(((Grammar.NonTerminalState) st).child.entryState, visited);
                }
                collectReachableNT(st, visited);
            }
        }
    }
}
