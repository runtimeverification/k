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
                                        s.nt,
                                        pattern);
                        whitespace.next.addAll(ps.next);
                        ps.next.clear();
                        ps.next.add(whitespace);
                    }
                }
            }
        }
        // create a new state for every start state that can have whitespace at the beginning
        for (Entry<NonTerminalId, NonTerminal> entry : startNonTerminals.entrySet()) {
            // create a new NT that calls the the startNT and has whitespace available at the beginning.
            // the NonTerminalId is copied into the new NT to keep the reference in the Map
            // the startNT gets another Id to eliminate confusion.
            NonTerminal nt = entry.getValue();
            NonTerminal whiteStartNt = new NonTerminal(
                    new NonTerminalId(nt.nonTerminalId.name),
                    new StateId(nt.nonTerminalId.name+"-whiteEntry"),
                    new StateId(nt.nonTerminalId.name+"-whiteExit"));
            PrimitiveState whitespace = new RegExState(
                    new StateId("whitespace-" + seed++),
                    whiteStartNt,
                    pattern);
            NonTerminalState nts = new NonTerminalState(
                    new StateId("white-calls-" + nt.nonTerminalId.name),
                    whiteStartNt, nt, false);
            nt.nonTerminalId = new NonTerminalId(nt.nonTerminalId.name + "-afterWhite");
            whiteStartNt.entryState.next.add(whitespace);
            whitespace.next.add(nts);
            nts.next.add(whiteStartNt.exitState);
            entry.setValue(whiteStartNt);
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
        public NonTerminalId nonTerminalId;
        public final EntryState entryState;
        public final ExitState exitState;
        Set<NextableState> intermediaryStates = new HashSet<>();
        public final OrderingInfo orderingInfo = null; // TODO

        static class OrderingInfo implements Comparable<OrderingInfo> {
            final int key;
            public OrderingInfo(int key) { this.key = key; }
            public int compareTo(OrderingInfo that) { return Integer.compare(this.key, that.key); }
        }

        public NonTerminal(NonTerminalId nonTerminalId,
                           StateId entryStateId,
                           StateId exitStateId) {
            this.nonTerminalId = nonTerminalId;
            this.entryState = new EntryState(entryStateId, this);
            this.exitState = new ExitState(exitStateId, this);
        }

        public NonTerminal(NonTerminalId nonTerminalId) {
            this.nonTerminalId = nonTerminalId;
            this.entryState = new EntryState(new StateId(nonTerminalId.name + "-entry"), this);
            this.exitState = new ExitState(new StateId(nonTerminalId.name + "-exit"), this);
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
        OrderingInfo orderingInfo = null;

        static class OrderingInfo implements Comparable<OrderingInfo>, Serializable {
            int key;
            public OrderingInfo(int key) { this.key = key; }
            public int compareTo(OrderingInfo that) { return Integer.compare(this.key, that.key); }
            public static final OrderingInfo ZERO = new OrderingInfo(0);
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
        public ExitState(StateId stateId, NonTerminal nt) {
            super(stateId, nt);
        }
    }

    public abstract static class NextableState extends State {
        public final Set<State> next = new HashSet<State>();
        NextableState(StateId stateId, NonTerminal nt, boolean intermediary) {
            super(stateId, nt);
            if (intermediary) { nt.intermediaryStates.add(this); }
        }
    }

    public static class EntryState extends NextableState {
        public EntryState(StateId stateId, NonTerminal nt) {
            super(stateId, nt, false);
        }
    }

    public static class NonTerminalState extends NextableState {
        public final NonTerminal child;
        public final boolean isLookahead;

        public NonTerminalState(
                StateId stateId, NonTerminal nt,
                NonTerminal child, boolean isLookahead) {
            super(stateId, nt, true);
            assert child != null : "here it is null: " + stateId.name;
            nt.intermediaryStates.add(this);
            this.child = child;
            this.isLookahead = isLookahead;
        }
    }

    public static abstract class Rule {}
    public static abstract class ContextFreeRule extends Rule {
        public abstract Set<KList> apply(Set<KList> set);
    }
    public static abstract class KListRule extends ContextFreeRule {
        public Set<KList> apply(Set<KList> set) {
            Set<KList> result = new HashSet<>();
            for (KList klist : set) {
                KList newKList = this.apply(klist);
                if (newKList != null) {
                    result.add(newKList);
                }
            }
            return result;
        }
        protected abstract KList apply(KList set);
    }
    // for putting labels after the fact
    public static class WrapLabelRule extends KListRule {
        KLabel label;
        public WrapLabelRule(KLabel label) { this.label = label; }
        protected KList apply(KList klist) {
            return new KList(Arrays.<Term>asList(new KApp(label, klist)));
        }
    }
    public static abstract class SuffixRule extends KListRule {
        protected abstract boolean rejectSmallKLists();
        protected abstract int getSuffixLength();
        protected abstract Result applySuffix(List<Term> suffix);

        protected abstract class Result {}
        protected class Reject extends Result {}
        protected class Original extends Result {}
        protected class Accept extends Result {
            List<Term> list;
            public Accept(List<Term> list) { this.list = list; }
        }

        protected KList apply(KList klist) {
            List<Term> terms = klist.getContents();
            int i = terms.size() - this.getSuffixLength();
            if (i < 0) {
                return this.rejectSmallKLists() ? null : klist;
            } else {
                List<Term> suffix = new ArrayList<>();
                for (; i < terms.size(); i++) {
                    suffix.add(terms.get(i));
                }
                Result result = this.applySuffix(suffix);
                if (result instanceof Reject) {
                    return null;
                } else if (result instanceof Original) {
                    return klist;
                } else if (result instanceof Accept) {
                    KList prefix = new KList(klist);
                    for (int j = terms.size() - 1;
                         j >= terms.size() - this.getSuffixLength(); j--) {
                        prefix.getContents().remove(j);
                    }
                    for (Term term : ((Accept) result).list) {
                        prefix.add(term);
                    }
                    return prefix;
                } else { assert false : "impossible"; return null; }
            }
        }
    }
    // for deleting tokens
    public static class DeleteRule extends SuffixRule {
        private final int length;
        private final boolean reject;
        public DeleteRule(int length, boolean reject) {
            this.length = length; this.reject = reject;
        }

        protected boolean rejectSmallKLists() { return reject; }
        protected int getSuffixLength() { return length; }
        protected Result applySuffix(List<Term> terms) {
            return new Accept(Arrays.<Term>asList());
        }
    }
    // for adding a constant to a label that was added before the fact
    public static class AppendRule extends SuffixRule {
        private final Term term;
        public AppendRule(Term term) { this.term = term; }
        protected boolean rejectSmallKLists() { return false; }
        protected int getSuffixLength() { return 0; }
        protected Result applySuffix(List<Term> terms) {
            return new Accept(Arrays.<Term>asList(term));
        }
    }
    // for putting labels before the fact
    public static class InsertRule extends SuffixRule {
        private final Term term;
        public InsertRule(Term term) { this.term = term; }
        protected boolean rejectSmallKLists() { return false; }
        protected int getSuffixLength() { return 0; }
        public Result applySuffix(List<Term> set) {
            return new Accept(Arrays.asList(term));
        }
    }
/*  // for adding a non-constant to a label that was added before the fact
    class AdoptionRule extends ContextFreeRule {
        private boolean reject;
        public Set<KList> apply(Set<KList> set) {
            Set<KList> result = new HashSet<>();
            for (KList klist : set) {
                List<Term> contents = klist.getContents();
                if (contents.size() >= 2) {
                    KList newKList = new KList(klist);
                    Term oldFinal = newKList.getContents().remove(contents);
                    Term oldPreFinal = newKList.getContents().remove(...);
                    if (oldPreFinal instanceof KApp) {
                        assert ((KApp) oldPreFinal).getChild() instanceof KList : "unimplemented"; // TODO
                        Term newFinal = new KApp(((KApp) oldPreFinal).getLabel(),
                            KList.append((KList) ((KApp) oldPreFinal).getChild(), oldFinal));
                        newKList.add(newFinal);
                        result.add(newKList);
                    } else if (!reject) { result.add(klist); }
                } else if (!reject) { return.add(klist); }
            }
        }
    }
    */
    public static abstract class ContextSensitiveRule extends Rule {
        abstract Set<KList> apply(KList context, Set<KList> set);
    }
    public static class CheckLabelContextRule {
        private boolean positive;
    }

    public static class RuleState extends NextableState {
        public final Rule rule;
        public RuleState(StateId stateId, NonTerminal nt, Rule rule) {
            super(stateId, nt, true);
            this.rule = rule;
        }
    }

    public abstract static class PrimitiveState extends NextableState {
        public static class MatchResult {
            final public int matchEnd;
            public MatchResult(int matchEnd) {
                this.matchEnd = matchEnd;
            }
        }

        abstract Set<MatchResult> matches(CharSequence text, int startPosition);

        public PrimitiveState(StateId stateId, NonTerminal nt) {
            super(stateId, nt, true);
        }

        public boolean isNullable() {
            Set<MatchResult> matchResults = this.matches("", 0);
            return matchResults.size() != 0;
        }

        abstract public boolean isAlwaysNull();
    }

    public static class RegExState extends PrimitiveState {
        private final java.util.regex.Pattern pattern;

        public RegExState(StateId stateId, NonTerminal nt, java.util.regex.Pattern pattern) {
            super(stateId, nt);
            this.pattern = pattern;
        }

        Set<MatchResult> matches(CharSequence text, int startPosition) {
            java.util.regex.Matcher matcher = pattern.matcher(text);
            matcher.region(startPosition, text.length());
            matcher.useAnchoringBounds(false);
            matcher.useAnchoringBounds(false);
            Set<MatchResult> results = new HashSet<MatchResult>();
            if (matcher.lookingAt()) {
                results.add(new MatchResult(matcher.end())); //matchFunction(text, matcher.start(), matcher.end())));
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
