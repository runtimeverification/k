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
import java.util.regex.Pattern;

import org.kframework.kil.Ambiguity;
import org.kframework.kil.KApp;
import org.kframework.kil.KLabel;
import org.kframework.kil.KList;
import org.kframework.kil.KSorts;
import org.kframework.kil.Term;
import org.kframework.kil.Token;
import org.kframework.parser.concrete2.Grammar.State.OrderingInfo;


/**
 * The classes used by the parser to represent the internal structure of a grammar.
 * A grammar represents a NFA generated from EBNF style grammar (in this case the K syntax declarations).
 * The main object is the {@link NonTerminal}, containing a unique {@link NonTerminalId},
 * and two states: entry and exit.
 *
 * There are four main types of states:
 * {@link EntryState}, {@link NonTerminalState}, {@link PrimitiveState} and {@link ExitState}.
 * The first three extend {@link NextableState} in order to make accommodate connections
 * between the sates. ExitState signifies the end of a NonTerminal so it doesn't need a 'next' field.
 *
 * Each {@link org.kframework.parser.concrete2.Grammar.NonTerminal} contains exactly one {@link EntryState}
 * and one {@link org.kframework.parser.concrete2.Grammar.ExitState}. Depending on the grammar it may contain
 * multiple {@link PrimitiveState} and {@link NonTerminalState}.
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
 *
 */
public class Grammar implements Serializable {

    // Contains all start symbol NonTerminals
    private Map<NonTerminalId, NonTerminal> startNonTerminals = new HashMap<>();

    public boolean add(NonTerminal newNT) {
        if (startNonTerminals.containsKey(newNT.nonTerminalId))
            return false;
        else {
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

    public Set<NonTerminal> getStartNonTerminals() {
        return new HashSet<NonTerminal>(startNonTerminals.values());
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
        // TODO: make whitespace include comments too
        // create a NonTerminal which parses a list of whitespace characters.
        // the NT is a star list that has 3 branches
        // 1. whitespace, 2. single line comment, 3. multiple lines comment
        Pattern pattern = Pattern.compile("((/\\*([^*]|[\\r\\n]|(\\*+([^*/]|[\\r\\n])))*\\*+/)|(//.*)|([ \n\r\t]))*");
        int seed = 0;

        // create a whitespace PrimitiveState after every every terminal that can match a character
        for (NonTerminal nonTerminal : getAllNonTerminals()) {
            for (State s : nonTerminal.getReachableStates()) {
                if (s instanceof PrimitiveState) {
                    PrimitiveState ps = ((PrimitiveState) s);
                    if (!ps.isAlwaysNull()) { // add whitespace after
                        PrimitiveState whitespace =
                                new RegExState(
                                        new StateId("whitespace" + seed++),
                                        s.nt, OrderingInfo.ZERO,
                                        pattern,
                                        null, TreeCleanerVisitor.DELETESORT);
                        whitespace.next.addAll(ps.next);
                        ps.next.clear();
                        ps.next.add(whitespace);
                    }
                }
            }
        }
    }

    public void finalize() {
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
        // TODO: java doesn't allow arrays of generic types.
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
    private static void collectNTCallers(State start, Set<State> visited, Map<NonTerminal, Set<NonTerminalState>> reachableNonTerminals) {
        if (visited.contains(start))
            return;
        visited.add(start);
        if (start instanceof NextableState) {
            NextableState ns = (NextableState) start;
            for (State st : ns.next) {
                if (st instanceof NonTerminalState) {
                    NonTerminalState nts = (NonTerminalState) st;
                    if (!reachableNonTerminals.containsKey(nts.child)) {
                        reachableNonTerminals.put(nts.child, new HashSet<NonTerminalState>(Arrays.asList(nts)));
                    }
                    reachableNonTerminals.get(nts.child).add(nts);
                    collectNTCallers(((NonTerminalState) st).child.entryState, visited, reachableNonTerminals);
                }
                collectNTCallers(st, visited, reachableNonTerminals);
            }
        }
    }

    // Positions are 'int' because CharSequence uses 'int' // Position in the text
    public static class StateId implements Comparable<StateId>, Serializable { // Used only by rules
        String name;
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

    public static class NonTerminalId implements Comparable<NonTerminalId>, Serializable { // Used only by rules
        String name;
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
        Set<NextableState> intermediaryStates = new HashSet<NextableState>();

        public NonTerminal(NonTerminalId nonTerminalId,
                           StateId entryStateId, State.OrderingInfo entryOrderingInfo,
                           StateId exitStateId, State.OrderingInfo exitOrderingInfo) {
            this.nonTerminalId = nonTerminalId;
            this.entryState = new EntryState(entryStateId, this, entryOrderingInfo, null, null);
            this.exitState = new ExitState(exitStateId, this, exitOrderingInfo, null, null);
        }

        public int compareTo(NonTerminal that) { return this.nonTerminalId.compareTo(that.nonTerminalId); }

        public Set<NextableState> getIntermediaryStates() {
            return intermediaryStates;
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
        final StateId stateId;
        final NonTerminal nt;
        final KLabel label;
        final String sort;
        OrderingInfo orderingInfo = null;

        static class OrderingInfo implements Comparable<OrderingInfo>, Serializable {
            int key;
            public OrderingInfo(int key) { this.key = key; }
            public int compareTo(OrderingInfo that) { return Integer.compare(this.key, that.key); }
            public static final OrderingInfo ZERO = new OrderingInfo(0);
        }

        public State(StateId stateId, NonTerminal nt, OrderingInfo orderingInfo, KLabel label, String sort) {
            this.stateId = stateId; this.nt = nt; this.orderingInfo = orderingInfo; this.label = label; this.sort = sort;
        }

        public Set<KList> runRule(Set<KList> input) {
            Set<KList> result;
            if (this.label == null) {
                result = input;
            } else {
                result = new HashSet<>();
                for (KList kl : input) {
                    result.add(new KList(Arrays.<Term>asList(new KApp(label, kl))));
                }
            }
            if (this instanceof ExitState) {
                return new HashSet<KList>(Arrays.asList(new KList(Arrays.asList((Term)new Ambiguity(KSorts.K, new ArrayList<Term>(result))))));
            } else {
                return result;
            }
        }

        public int compareTo(State that) {
            int x;
            return
                ((x = this.orderingInfo.compareTo(that.orderingInfo)) != 0) ? x :
                ((x = this.stateId.compareTo(that.stateId)) != 0) ? x :
                this.nt.compareTo(that.nt);
        }

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
        public ExitState(StateId stateId, NonTerminal nt, OrderingInfo orderingInfo, KLabel label, String sort) {
            super(stateId, nt, orderingInfo, label, sort);
        }
    }

    public abstract static class NextableState extends State {
        public final Set<State> next = new HashSet<State>();
        NextableState(StateId stateId, NonTerminal nt, OrderingInfo orderingInfo, boolean intermediary, KLabel label, String sort) {
            super(stateId, nt, orderingInfo, label, sort);
            if (intermediary) { nt.intermediaryStates.add(this); }
        }
    }

    public static class EntryState extends NextableState {
        public EntryState(StateId stateId, NonTerminal nt, OrderingInfo orderingInfo, KLabel label, String sort) {
            super(stateId, nt, orderingInfo, false, label, sort);
        }
    }

    public static class NonTerminalState extends NextableState {
        public final NonTerminal child;
        public final boolean isLookahead;

        public NonTerminalState(
                StateId stateId, NonTerminal nt, OrderingInfo orderingInfo,
                NonTerminal child, boolean isLookahead, KLabel label, String sort) {
            super(stateId, nt, orderingInfo, true, label, sort);
            assert child != null : "here it is null: " + stateId.name;
            nt.intermediaryStates.add(this);
            this.child = child;
            this.isLookahead = isLookahead;
        }
    }

    public abstract static class PrimitiveState extends NextableState {
        public static class MatchResult {
            final public int matchEnd;
            final public Function matchFunction;
            public MatchResult(int matchEnd, Function matchFunction) {
                this.matchEnd = matchEnd;
                this.matchFunction = matchFunction;
            }
        }

        abstract Set<MatchResult> matches(CharSequence text, int startPosition, Function context);

        public PrimitiveState(StateId stateId, NonTerminal nt, OrderingInfo orderingInfo, KLabel label, String sort) {
            super(stateId, nt, orderingInfo, true, label, sort);
        }

        public boolean isNullable() {
            Set<MatchResult> matchResults = this.matches("", 0, null);
            return matchResults.size() != 0;
        }

        abstract public boolean isAlwaysNull();
    }

    public static class RegExState extends PrimitiveState {
        private final java.util.regex.Pattern pattern;

        public RegExState(StateId stateId, NonTerminal nt, OrderingInfo orderingInfo, java.util.regex.Pattern pattern, KLabel label, String sort) {
            super(stateId, nt, orderingInfo, label, sort);
            this.pattern = pattern;
        }

        Set<MatchResult> matches(CharSequence text, int startPosition, Function context) {
            java.util.regex.Matcher matcher = pattern.matcher(text);
            matcher.region(startPosition, text.length());
            matcher.useAnchoringBounds(false);
            matcher.useAnchoringBounds(false);
            Set<MatchResult> results = new HashSet<MatchResult>();
            if (matcher.lookingAt()) {
                results.add(new MatchResult(matcher.end(), Function.constant(Token.kAppOf(this.sort, matcher.group())))); //matchFunction(text, matcher.start(), matcher.end())));
            }
            return results;
        }

        public boolean isAlwaysNull() {
            if (pattern.equals(""))
                return true;
            else
                return false;
        }
    }
}
