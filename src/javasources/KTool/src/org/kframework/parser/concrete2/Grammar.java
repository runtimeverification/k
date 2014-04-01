package org.kframework.parser.concrete2;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;
import org.kframework.kil.KSorts;
import org.kframework.parser.concrete2.Grammar.State.OrderingInfo;
import org.kframework.parser.concrete2.Rule.DeleteRule;


/**
 * The classes used by the parser to represent the internal structure of a grammar.
 * A grammar consists of NFAs generated for each non-terminal from a EBNF style grammar
 * (in this case the K syntax declarations).
 * The main object is the {@link NonTerminal}, containing a unique {@link NonTerminalId},
 * and two states: entry and exit.
 *
 * There are five main types of states: {@link EntryState}, {@link NonTerminalState},
 * {@link PrimitiveState}, @{@link RuleState} and {@link ExitState}.
 * The first four extend {@link NextableState} in order to make accommodate connections
 * between the sates. ExitState signifies the end of a NonTerminal so it doesn't have a 'next' field.
 *
 * Each {@link NonTerminal} contains exactly one {@link EntryState}
 * and one {@link ExitState}. Depending on the grammar it may contain
 * multiple {@link NonTerminalState}, {@link PrimitiveState} or {@link RuleState}.
 *
 * Example of a NonTerminal NFA structure:
 * E ::= E "+" E
 *     | E "*" E
 *     | {E, ","}+
 *
 *     |->[E]-->("+")--->[E]--|
 *     |                      |
 * (|--|->[E]-->("*")--->[E]--|->|)
 *     |                      |
 *     |   |------------------|
 *     |->[E]-->(",")
 *         ^------|
 *
 * (| - EntryState
 * |) - ExitState
 * [] - NonTerminalState
 * () - PrimitiveState
 * <> - RuleState
 *
 * NOTE: compile() must be called on a grammar before it is handed to the parser
 */
public class Grammar implements Serializable {

    /// The set of "root" NonTerminals
    private BiMap<NonTerminalId, NonTerminal> startNonTerminals = HashBiMap.create();

    public boolean add(NonTerminal newNT) {
        if (startNonTerminals.containsKey(newNT.nonTerminalId)) {
            return false;
        } else {
            startNonTerminals.put(newNT.nonTerminalId, newNT);
            return true;
        }
    }

    public Set<NonTerminal> getAllNonTerminals() {
        return getNonTerminalCallers().keySet();
    }

    public NonTerminal get(String ntSymbol) {
        return startNonTerminals.get(new NonTerminalId(ntSymbol));
    }

    public Map<NonTerminal, Set<NonTerminalState>> getNonTerminalCallers() {
        Map<NonTerminal, Set<NonTerminalState>> reachableNonTerminals = new HashMap<>();
        Set<State> visited = new HashSet<>();
        for (NonTerminal nt : startNonTerminals.values()) {
            if (!reachableNonTerminals.containsKey(nt)) {
                // if it is the start symbol it won't have any callers, so add it here first
                reachableNonTerminals.put(nt, new HashSet<NonTerminalState>());
            }
            collectNTCallers(nt.entryState, visited, reachableNonTerminals);
        }
        return reachableNonTerminals;
    }

    public void addWhiteSpace() {
        // create a NonTerminal which parses a list of whitespace characters.
        // the NT is a star list that has 3 branches
        // 1. whitespace, 2. single line comment, 3. multiple lines comment

        // create a whitespace PrimitiveState after every every terminal that can match a character
        for (NonTerminal nonTerminal : getAllNonTerminals()) {
            for (State s : nonTerminal.getReachableStates()) {
                if (s instanceof PrimitiveState) {
                    PrimitiveState ps = ((PrimitiveState) s);
                    addWhitespace(ps);
                }
            }
        }

        // create a new state for every start state that can have whitespace at the beginning
        for (NonTerminal nt : startNonTerminals.values()) {
            // add whitespace to the beginning of every start NonTerminal to allow for
            // whitespace at the beginning of the input
            addWhitespace(nt.entryState);
        }
    }

    String multiLine = "(/\\*([^*]|[\\r\\n]|(\\*+([^*/]|[\\r\\n])))*\\*+/)";
    String singleLine = "(//.*)";
    String whites = "([ \n\r\t])";
    Pattern pattern = Pattern.compile("("+ multiLine +"|"+ singleLine +"|"+ whites +")*");
    int seed = 0;

    /**
     * Add a pair of whitespace-remove whitespace rule to the given state.
     * All children of the given state are moved to the remove whitespace rule.
     * (|-- gets transformed into (|-->(white)--><remove>---
     * @param start NextableState to which to attach the whitespaces
     * @return the remove whitespace state
     */
    private NextableState addWhitespace(NextableState start) {
        PrimitiveState whitespace = new RegExState(
                new StateId("whitespace" + seed++), start.nt, pattern, KSorts.K);
        RuleState deleteToken = new RuleState(
                new StateId("whitespace-D-" + seed++), start.nt, new DeleteRule(1, true));
        whitespace.next.add(deleteToken);
        deleteToken.next.addAll(start.next);
        start.next.clear();
        start.next.add(whitespace);
        return deleteToken;
    }

    public void compile() {
        // 1. get all nullable states
        Nullability nullability = new Nullability(this);

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

        for (State s : allStates) {
            if (s instanceof NextableState) {
                NextableState ns = (NextableState) s;
                for (State nextState : ns.next) {
                    if (nullability.isNullable(nextState)) {
                        predecessors[inverseAllStates.get(nextState)].add(inverseAllStates.get(s));
                    }
                    if (nextState instanceof NonTerminalState) {
                        EntryState es = ((NonTerminalState) nextState).child.entryState;
                        predecessors[inverseAllStates.get(es)].add(inverseAllStates.get(s));
                    }
                }
                if (ns instanceof NonTerminalState) {
                    ExitState es = ((NonTerminalState) ns).child.exitState;
                    predecessors[inverseAllStates.get(es)].add(inverseAllStates.get(s));
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
    }

    /**
     * Recursive DFS that traverses all the states and returns a set of all reachable {@Link NonTerminal}.
     * @param start The state from which to run the collector.
     * @param visited Start with an empty Set<State>. Used as intermediate data.
     * @return A set of all reachable {@Link NonTerminal}.
     */
    private static void collectNTCallers(State start, Set<State> visited,
        Map<NonTerminal, Set<NonTerminalState>> reachableNonTerminals) {
        if (!visited.contains(start)) {
            visited.add(start);
            if (start instanceof NextableState) {
                NextableState ns = (NextableState) start;
                for (State st : ns.next) {
                    if (st instanceof NonTerminalState) {
                        NonTerminalState nts = (NonTerminalState) st;
                        if (!reachableNonTerminals.containsKey(nts.child)) {
                            reachableNonTerminals.put(
                                nts.child, new HashSet<NonTerminalState>(Arrays.asList(nts)));
                        }
                        reachableNonTerminals.get(nts.child).add(nts);
                        collectNTCallers(((NonTerminalState) st).child.entryState,
                            visited, reachableNonTerminals);
                    }
                    collectNTCallers(st, visited, reachableNonTerminals);
                }
            }
        }
    }

    ///////////////////
    // Inner Classes //
    ///////////////////

    public static class StateId implements Comparable<StateId>, Serializable { // Used only by rules
        public final String name;
        public StateId(String name) { this.name = name; }
        public int compareTo(StateId that) { return this.name.compareTo(that.name); }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;

            StateId stateId = (StateId) o;

            if (!name.equals(stateId.name)) return false;

            return true;
        }

        @Override
        public int hashCode() {
            return name.hashCode();
        }
    }

    public static class NonTerminalId implements Comparable<NonTerminalId>, Serializable {
        public final String name;
        public NonTerminalId(String name) { this.name = name; }
        public int compareTo(NonTerminalId that) { return this.name.compareTo(that.name); }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;

            NonTerminalId that = (NonTerminalId) o;

            if (!name.equals(that.name)) return false;

            return true;
        }

        @Override
        public int hashCode() {
            return name.hashCode();
        }
    }

    public static class NonTerminal implements Comparable<NonTerminal>, Serializable {
        public final NonTerminalId nonTerminalId;
        public final EntryState entryState;
        public final ExitState exitState;
        private final Set<NextableState> intermediaryStates = new HashSet<>();
        final OrderingInfo orderingInfo = null; // TODO: unused until we fix lookahead

        static class OrderingInfo implements Comparable<OrderingInfo> {
            final int key;
            public OrderingInfo(int key) { this.key = key; }
            public int compareTo(OrderingInfo that) { return Integer.compare(this.key, that.key); }
        }

        public NonTerminal(NonTerminalId nonTerminalId) {
            this.nonTerminalId = nonTerminalId;
            this.entryState = new EntryState(new StateId(nonTerminalId.name + "-entry"), this);
            this.exitState = new ExitState(new StateId(nonTerminalId.name + "-exit"), this);
        }

        public int compareTo(NonTerminal that) {
            return this.nonTerminalId.compareTo(that.nonTerminalId);
        }

        public Set<State> getReachableStates() {
            Set<State> states = new HashSet<>();
            states.add(this.exitState);
            states.add(this.entryState);
            // TODO: replace this with a recursive collector
            states.addAll(this.intermediaryStates);
            return states;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;

            NonTerminal that = (NonTerminal) o;

            if (!nonTerminalId.equals(that.nonTerminalId)) return false;

            return true;
        }

        @Override
        public int hashCode() {
            return nonTerminalId.hashCode();
        }
    }

    public abstract static class State implements Comparable<State>, Serializable {
        public final StateId stateId;
        public final NonTerminal nt;
        OrderingInfo orderingInfo = null;

        static class OrderingInfo implements Comparable<OrderingInfo>, Serializable {
            final int key;
            public OrderingInfo(int key) { this.key = key; }
            public int compareTo(OrderingInfo that) { return Integer.compare(this.key, that.key); }
        }

        public State(StateId stateId, NonTerminal nt) {
            this.stateId = stateId; this.nt = nt;
        }

        public int compareTo(State that) { return this.stateId.compareTo(that.stateId); }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;

            State state = (State) o;

            if (!nt.equals(state.nt)) return false;
            if (!stateId.equals(state.stateId)) return false;

            return true;
        }

        @Override
        public int hashCode() {
            int result = stateId.hashCode();
            //result = 31 * result + nt.hashCode();
            return result;
        }
    }

    public static class ExitState extends State {
        ExitState(StateId stateId, NonTerminal nt) { super(stateId, nt); }
    }

    public abstract static class NextableState extends State {
        public final Set<State> next = new HashSet<State>() {
            @Override
            public boolean add(State s) {
                assert s.nt == NextableState.this.nt :
                    "States " + NextableState.this.stateId.name + " and " +
                        s.stateId.name + " are not in the same NonTerminal.";
                return super.add(s);
            }
        };
        NextableState(StateId stateId, NonTerminal nt, boolean intermediary) {
            super(stateId, nt);
            if (intermediary) { nt.intermediaryStates.add(this); }
        }
    }

    public static class EntryState extends NextableState {
        EntryState(StateId stateId, NonTerminal nt) { super(stateId, nt, false); }
    }

    public static class NonTerminalState extends NextableState {
        public final NonTerminal child;
        public final boolean isLookahead;

        public NonTerminalState(
                StateId stateId, NonTerminal nt,
                NonTerminal child, boolean isLookahead) {
            super(stateId, nt, true);
            nt.intermediaryStates.add(this);
            this.child = child;
            this.isLookahead = isLookahead;
        }
    }

    public static class RuleState extends NextableState {
        public final Rule rule;
        public RuleState(StateId stateId, NonTerminal nt, Rule rule) {
            super(stateId, nt, true);
            this.rule = rule;
        }
    }

    public abstract static class PrimitiveState extends NextableState {
        /// The sort of the token (or rather the KApp containing this token)
        // to be constructed when parsing this primitive state.
        public final String sort;
        public static class MatchResult {
            final public int matchEnd;
            public MatchResult(int matchEnd) {
                this.matchEnd = matchEnd;
            }
        }

        abstract Set<MatchResult> matches(CharSequence text, int startPosition);

        public PrimitiveState(StateId stateId, NonTerminal nt, String sort) {
            super(stateId, nt, true);
            this.sort = sort;
        }

        public boolean isNullable() {
            Set<MatchResult> matchResults = this.matches("", 0);
            return matchResults.size() != 0;
        }
    }

    public static class RegExState extends PrimitiveState {
        public final Pattern pattern;

        public RegExState(StateId stateId, NonTerminal nt, Pattern pattern, String sort) {
            super(stateId, nt, sort);
            this.pattern = pattern;
        }

        // Position is an 'int' offset into the text because CharSequence uses 'int'
        Set<MatchResult> matches(CharSequence text, int startPosition) {
            Matcher matcher = pattern.matcher(text);
            matcher.region(startPosition, text.length());
            matcher.useAnchoringBounds(false);
            matcher.useTransparentBounds(true);
            Set<MatchResult> results = new HashSet<>();
            if (matcher.lookingAt()) {
                results.add(new MatchResult(matcher.end()));
            }
            return results;
        }
    }
}
