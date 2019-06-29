// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore.kernel;

import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.SetMultimap;
import org.kframework.utils.algorithms.SCCTarjan;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;


/**
 * The classes used by the parser to represent the internal structure of a grammar.
 * A grammar consists of NFAs (Non Finite Automata) generated for each non-terminal from a
 * EBNF style grammar (in this case the K syntax declarations).
 * The main object is the {@link NonTerminal}, containing a unique {@link String} name,
 * and two states: entry and exit.
 *
 * There are five main types of states: {@link EntryState}, {@link NonTerminalState},
 * {@link PrimitiveState}, @{@link RuleState} and {@link ExitState}.
 * The first four extend {@link NextableState} in order to make connections between the sates.
 * ExitState signifies the end of a NonTerminal so it doesn't need a 'next' field.
 *
 * Each {@link NonTerminal} contains exactly one {@link EntryState}
 * and one {@link ExitState}. Depending on the grammar it may contain
 * multiple {@link NonTerminalState}, {@link PrimitiveState} or {@link RuleState}.
 *
 * Example of a NonTerminal NFA structure:
 * E ::= E "+" E   [label(add)]
 *     | E "*" E   [label(mul)]
 *     | {E, ","}+ [label(lst)]
 *
 *     +--[E]---("+")--[E]--<add>--+
 *     |                           |
 * (|--+--[E]---("*")--[E]--<mul>--+--|)
 *     |                           |
 *     |   +----------------<lst>--+
 *     +--[E]---(",")----+
 *         ^-------------+
 *
 * (| - EntryState
 * |) - ExitState
 * [] - NonTerminalState
 * () - PrimitiveState
 * <> - RuleState
 *
 * NOTE: compile() must be called before it is handed to the parser
 */
public class Grammar implements Serializable {

    /** The set of "root" NonTerminals */
    private BiMap<String, NonTerminal> startNonTerminals = HashBiMap.create();

    public boolean add(NonTerminal newNT) {
        if (startNonTerminals.containsKey(newNT.name)) {
            return false;
        } else {
            startNonTerminals.put(newNT.name, newNT);
            return true;
        }
    }

    /**
     * Returns a set of all NonTerminals, including the hidden ones which are not considered
     * start symbols.  This is so Grammar doesn't have to track the hidden NonTerminals itself,
     * and makes it impossible for a user to cause problems by failing to add a NonTerminal.
     * @return a Set of all the {@link NonTerminal}s
     */
    public Set<NonTerminal> getAllNonTerminals() {
        return startNonTerminals.values();
    }

    /**
     * Returns the NonTerminal specific to the given name that is exposed as a start non-terminal by this grammar.
     * @param name of the NonTerminal
     * @return the NonTerminal or null if it couldn't find it
     */
    public NonTerminal get(String name) { return startNonTerminals.get(name); }

    /**
     * Creates a mapping from {@link NonTerminal} to a set of all the {@link NonTerminalState}
     * which have as a child (call) that NonTerminal. Normally the NonTerminal contains a set of
     * NonTerminalStates which calls to other NonTerminals. This creates the inverse relation.
     * @return A mapping from NonTerminal to a Set of NonTerminalStates which call to that
     * NonTerminal
     */
    public SetMultimap<NonTerminal, NonTerminalState> getNonTerminalCallers() {
        SetMultimap<NonTerminal, NonTerminalState> reachableNonTerminals = HashMultimap.create();
        for (NonTerminal nt : startNonTerminals.values()) {
            nt.intermediaryStates.stream().filter(s -> s instanceof NonTerminalState).forEach(s -> {
                NonTerminalState nts = (NonTerminalState)s;
                reachableNonTerminals.put(nts.child, nts);
            });
        }
        return reachableNonTerminals;
    }

    /**
     * Calculates Nullability and OrderingInfo for all the states in the grammar.
     * Must be called before being handed over to the parser, but after
     * the grammar is finished being built.
     */
    public void compile(Scanner scanner) {
        // 1. get all nullable states
        Nullability nullability = new Nullability(this, stateCounter);

        // 2. make an array with all the states
        List<State> allStates = new ArrayList<>();
        for (NonTerminal nonTerminal : getAllNonTerminals()) {
            allStates.addAll(nonTerminal.getReachableStates());
        }
        // 3. prepare the inverse relation
        Map<State, Integer> inverseAllStates = new HashMap<>();
        for (int i = 0; i < allStates.size(); i++) {
            inverseAllStates.put(allStates.get(i), i);
        }

        // prepare the Tarjan input data
        // TODO: java doesn't allow arrays of generic types so we need to move from arrays to ArrayList
        @SuppressWarnings("unchecked")
        List<Integer>[] predecessors = new List[allStates.size()];
        for (int i = 0; i < predecessors.length; i++) {
            predecessors[i] = new ArrayList<>();
        }

        // A state "A" must precede another state "B" if it is possible to get from a StateReturn
        // of A to a StateReturn of B without consuming input.
        // There are three ways for this to happen:
        // (1) A.next contains B and B is nullable
        // (2) A.next contains a NonTerminalState "N" and B is the EntryState of the NonTerminal referenced by N.
        // (3) B is a NonTerminalState and A is the ExitState of the NonTerminal referenced by N.
        for (State s : allStates) {
            if (s instanceof NextableState) {
                NextableState ns = (NextableState) s;
                for (State nextState : ns.next) {
                    // Case 1 (See above)
                    if (nullability.isNullable(nextState)) {
                        predecessors[inverseAllStates.get(nextState)].add(inverseAllStates.get(s));
                    }
                    // Case 2 (See above)
                    if (nextState instanceof NonTerminalState) {
                        EntryState es = ((NonTerminalState) nextState).child.entryState;
                        predecessors[inverseAllStates.get(es)].add(inverseAllStates.get(s));
                    }
                }
                // Case 3 (See above)
                if (ns instanceof NonTerminalState) {
                    ExitState es = ((NonTerminalState) ns).child.exitState;
                    predecessors[inverseAllStates.get(s)].add(inverseAllStates.get(es));
                }
            }
        }

        List<List<Integer>> components = new SCCTarjan().scc(predecessors);

        // assign the OrderingInfo for states
        for (int i = 0; i < components.size(); i++) {
            for (int j : components.get(i)) {
                State state = allStates.get(j);
                state.orderingInfo = new OrderingInfo(i);
            }
        }

        // compute first set of nonterminals
        for (NonTerminal nt : startNonTerminals.values()) {
            nt.nullable = nullability.isNullable(nt);
            nt.firstSet = nullability.getFirstSet(nt, scanner, allStates);
        }
    }

    ///////////////////
    // Inner Classes //
    ///////////////////

    private int ntCounter = 0;

    /**
     * A NonTerminal is the representation of a non-terminal from the left hand side of the
     * original BNF grammar. The non-terminal is represented as a NFA automaton which has only
     * one EntryState and one ExitState.
     */
    public class NonTerminal implements Serializable {
        public final String name;
        private final int hashCode;
        public final int unique;
        /**
         * The first state of the state machine for the non-terminal.
         */
        public final EntryState entryState;
        /**
         * The last state of the state machine for the non-terminal.
         */
        public final ExitState exitState;
        // contains a list of all States found in this NonTerminal other than the EntryState
        // and ExitState
        private final Set<NextableState> intermediaryStates = new HashSet<>();

        private boolean[] firstSet;
        private boolean nullable;

        public NonTerminal(String name) {
            unique = ntCounter++;
            assert name != null && !name.equals("") : "NonTerminal name cannot be null or empty.";
            this.name = name;
            hashCode = name.hashCode();
            this.entryState = new EntryState(name + "-entry", this);
            this.exitState = new ExitState(name + "-exit", this);
        }

        /**
         * NonTerminal references only EntryState and ExitState. This goes through the entire
         * NFA graph and returns all the reachable states in the NonTerminal as one Set object.
         * @return All the states contained in this NonTerminal
         */
        public Set<State> getReachableStates() {
            Set<State> states = new HashSet<>();
            states.add(this.exitState);
            states.add(this.entryState);
            // TODO: replace this with a recursive collector
            states.addAll(this.intermediaryStates);
            return states;
        }

        public Set<NextableState> intermediateStates() {
            return intermediaryStates;
        }

        public boolean lookahead(int token) {
            return firstSet[token];
        }

        public boolean nullable() { return nullable; }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;

            NonTerminal that = (NonTerminal) o;

            if (!name.equals(that.name)) return false;

            return true;
        }

        @Override
        public int hashCode() {
            return hashCode;
        }
    }

    private int stateCounter = 0;

    static class OrderingInfo implements Comparable<OrderingInfo>, Serializable {
        final int key;
        public OrderingInfo(int key) { this.key = key; }
        public int compareTo(OrderingInfo that) { return Integer.compare(this.key, that.key); }
        @Override
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result + key;
            return result;
        }
        @Override
        public boolean equals(Object obj) {
            if (this == obj)
                return true;
            if (obj == null)
                return false;
            if (getClass() != obj.getClass())
                return false;
            OrderingInfo other = (OrderingInfo) obj;
            if (key != other.key)
                return false;
            return true;
        }
        public String toString() { return Integer.toString(key); }
    }

    /**
     * State is the basic element from which the NFA automaton of the grammar is composed.
     * There are two classes which directly extend this one: {@link ExitState} and
     * (@link NextableState}
     */
    public abstract class State implements Comparable<State>, Serializable {
        /** "User friendly" name for the state.  Used only for debugging and error reporting. */
        public final String name;
        /** Counter for generating unique ids for the state. */
        /** The unique id of this state. */
        public final int unique;

        /** A back reference to the NonTerminal that this state is part of. */
        public final NonTerminal nt;
        /** The OrderingInfo for this state. */
        OrderingInfo orderingInfo = null;

        /**
         * Metadata used by the parser used to determine in what order to process StateReturns
         */

        public State(String name, NonTerminal nt) {
            unique = stateCounter++;
            assert nt != null;
            this.name = name + "[" + this.unique + "]";
            this.nt = nt;
        }

        public int compareTo(State that) { return Integer.compare(this.unique, that.unique); }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;

            State state = (State) o;

            if (unique != state.unique) return false;

            return true;
        }

        @Override
        public int hashCode() {
            return unique;
        }

        @Override
        public String toString() {
            return name;
        }
    }

    /**
     * The final state of a NonTerminal. Note that an ExitState has no successors and there is only
     * one per NonTerminal.
     */
    public class ExitState extends State {
        ExitState(String name, NonTerminal nt) { super(name, nt); }
    }

    /**
     * Abstract category of states that may have successors.
     */
    public abstract class NextableState extends State {
        /** States that are successors of this one in the NFA. */
        public final Set<State> next = new HashSet<State>() {
            @Override
            public boolean add(State s) {
                assert s.nt == NextableState.this.nt :
                    "States " + NextableState.this.name + " and " +
                    s.name + " are not in the same NonTerminal.";
                return super.add(s);
            }
        };
        NextableState(String name, NonTerminal nt, boolean intermediary) {
            super(name, nt);
            if (intermediary) { nt.intermediaryStates.add(this); }
        }
    }

    /**
     * The first state of a NonTerminal. Only one per NonTerminal.
     */
    public class EntryState extends NextableState {
        EntryState(String name, NonTerminal nt) { super(name, nt, false); }
    }

    /**
     * NonTerminalState contains a reference to the NonTerminal which has to be called to continue
     * parsing from a particular spot. This is specific to the non-terminals in the right hand side
     * of BNF productions.
     */
    public class NonTerminalState extends NextableState {
        /** The NonTerminal referenced by this NonTerminalState */
        public final NonTerminal child;

        public NonTerminalState(
                String name, NonTerminal nt,
                NonTerminal child) {
            super(name, nt, true);
            assert child != null;
            nt.intermediaryStates.add(this);
            this.child = child;
        }
    }

    /**
     * A RuleState takes a Rule and applies an action to the term parsed up to that point.
     */
    public class RuleState extends NextableState {
        /** The rule to be applied. */
        public final Rule rule;
        public RuleState(String name, NonTerminal nt, Rule rule) {
            super(name, nt, true);
            assert rule != null;
            this.rule = rule;
        }
    }

    /**
     * PrimitiveState is the only State that matches on characters and consumes them.
     * The content of the matched string is stored into a KApp of a #token.
     * TODO: revisit this description once we get the new KORE
     */
    public abstract class PrimitiveState extends NextableState {

        /*
         *  Returns a set of matches at the given position in the given string.
         *  If there are no matches, the returned set will be empty.
         */
        abstract boolean matches(Scanner.Token[] buffer, int startPosition);

        public PrimitiveState(String name, NonTerminal nt) {
            super(name, nt, true);
        }

        /**
         * Checks whether this PrimitiveStates can parse without consuming any tokens.
         *
         * @return true if it can parse without consuming any tokens.
         */
        public boolean isNullable() {
            return false;
        }
    }

    /**
     * Uses java regular expression (@link Matcher} class to consume characters in the
     * char sequence.
     */
    public class RegExState extends PrimitiveState {
        /** The java regular expression pattern. */
        public final int kind;

        public RegExState(String name, NonTerminal nt, int kind) {
            super(name, nt);
            this.kind = kind;
        }

        // Position is an 'int' offset into the text because CharSequence uses 'int'
        boolean matches(Scanner.Token[] buffer, int startPosition) {
            if (startPosition >= buffer.length)
                return false;
            return buffer[startPosition].kind == kind;
        }
    }
}
