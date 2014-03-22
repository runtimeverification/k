package org.kframework.parser.concrete2;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.kframework.parser.concrete2.Grammar.EntryState;
import org.kframework.parser.concrete2.Grammar.ExitState;
import org.kframework.parser.concrete2.Grammar.NextableState;
import org.kframework.parser.concrete2.Grammar.NonTerminal;
import org.kframework.parser.concrete2.Grammar.NonTerminalState;
import org.kframework.parser.concrete2.Grammar.PrimitiveState;
import org.kframework.parser.concrete2.Grammar.State;

/**
 * Helper class in the parser that finds all of the nullable NonTerminals in a grammar.
 */
public class NullabilityCheck {
    // accumulate the results here (TODO: explain that this is nulable up to the *entry* of the state)
    private Set<State> nullable = new HashSet<>();

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
     * @param grammar the grammar object.
     * @return A set with all the NonTerminals that can become nullable.
     */
    public NullabilityCheck(Grammar grammar) {
        // 1. get all nullable states
        // list NonTerminals reachable from the start symbol.
        // the value of the map keeps a reference to all the states which call NonTerminals
        Map<NonTerminal, Set<NonTerminalState>> nonTerminalCallers = grammar.getNonTerminalCallers();

        // A state is nullable iff the *start* of it is reachable from the entry of its nt without consuming input
        // A non-terminal is nullable if its exit state is nullable
        for (NonTerminal entry : nonTerminalCallers.keySet()) {
            mark(entry.entryState, nonTerminalCallers);
        }
    }

    /** marks a state as nullable if it is not already, and calls mark on any
     * states that should be nullable as a result.
     */
    private void mark(State state, Map<NonTerminal, Set<NonTerminalState>> nonTerminalCallers) {
        if (!nullable.contains(state)) {
            nullable.add(state);
            if (state instanceof NextableState) {
                if (isNullable(state))
                    for (State s : ((NextableState) state).next)
                        mark(s, nonTerminalCallers);
            } else {
                assert state instanceof ExitState: "I was expecting this element to be of type ExitState";
                // previous calls to childNullable would have returned False
                // so now we restart those recursions
                for (State s : nonTerminalCallers.get(state.nt)) {
                    if (nullable.contains(s)) {
                        // assert s instanceof NonTerminalState : "Intermediary states are NonTerminalStates?";
                        for (State child : ((NextableState)s).next) {
                            mark(child, nonTerminalCallers);
                        }
                    }
                }
            }
        }
    }

    /**
     * Checks if a state can parse without consuming characters.
     * @param state The state to check
     * @return true if the state can parse without consuming characters and false otherwise
     */
    public boolean isNullable(State state) {
        return (state instanceof EntryState) ||
               (state instanceof ExitState) ||
               ((state instanceof PrimitiveState) && ((PrimitiveState)state).isNullable()) ||
               ((state instanceof NonTerminalState) && isNullable(((NonTerminalState) state).child));
    }

    public boolean isNullable(NonTerminal nt) {
        return nullable.contains(nt.exitState);
    }
}
