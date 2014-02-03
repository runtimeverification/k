package org.kframework.parser.concrete2;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

import org.kframework.kil.Ambiguity;
import org.kframework.kil.KList;
import org.kframework.kil.Term;
import org.kframework.kil.Token;

public class Grammar {

// Positions are 'int' because CharSequence uses 'int' // Position in the text
    public static class StateId implements Comparable<StateId> { // Used only by rules
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

    public static class NonTerminalId implements Comparable<NonTerminalId> { // Used only by rules
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

    public static class NonTerminal implements Comparable<NonTerminal> {
        public final NonTerminalId nonTerminalId;
        public final EntryState entryState;
        public final ExitState exitState;
        Set<NextableState> intermediaryStates = new HashSet<NextableState>();

        public NonTerminal(NonTerminalId nonTerminalId,
                           StateId entryStateId, State.OrderingInfo entryOrderingInfo,
                           StateId exitStateId, State.OrderingInfo exitOrderingInfo) {
            this.nonTerminalId = nonTerminalId;
            this.entryState = new EntryState(entryStateId, this, entryOrderingInfo);
            this.exitState = new ExitState(exitStateId, this, exitOrderingInfo);
        }

        public int compareTo(NonTerminal that) { return this.nonTerminalId.compareTo(that.nonTerminalId); }

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

    public abstract static class State implements Comparable<State> {
        final StateId stateId;
        final NonTerminal nt;
        final OrderingInfo orderingInfo;

        static class OrderingInfo implements Comparable<OrderingInfo> {
            int key;
            public OrderingInfo(int key) { this.key = key; }
            public int compareTo(OrderingInfo that) { return Integer.compare(this.key, that.key); }
        }

        public State(StateId stateId, NonTerminal nt, OrderingInfo orderingInfo) {
            this.stateId = stateId; this.nt = nt; this.orderingInfo = orderingInfo;
        }

        public Set<KList> runRule(Set<KList> input) {
            if (this instanceof ExitState) {
                return new HashSet<KList>(Arrays.asList(new KList(Arrays.asList((Term)new Ambiguity("K", new ArrayList<Term>(input))))));
            } else {
                return input;
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
            result = 31 * result + nt.hashCode();
            return result;
        }
    }

    public static class ExitState extends State {
        public ExitState(StateId stateId, NonTerminal nt, OrderingInfo orderingInfo) {
            super(stateId, nt, orderingInfo);
        }
    }

    public abstract static class NextableState extends State {
        public final Set<State> next = new HashSet<State>();
        NextableState(StateId stateId, NonTerminal nt, OrderingInfo orderingInfo, boolean intermediary) {
            super(stateId, nt, orderingInfo);
            if (intermediary) { nt.intermediaryStates.add(this); }
        }
    }

    public static class EntryState extends NextableState {
        public EntryState(StateId stateId, NonTerminal nt, OrderingInfo orderingInfo) {
            super(stateId, nt, orderingInfo, false);
        }
    }

    public static class NonTerminalState extends NextableState {
        public final NonTerminal child;
        public final boolean isLookahead;

        public NonTerminalState(
                StateId stateId, NonTerminal nt, OrderingInfo orderingInfo,
                NonTerminal child, boolean isLookahead) {
            super(stateId, nt, orderingInfo, true);
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

        public PrimitiveState(StateId stateId, NonTerminal nt, OrderingInfo orderingInfo) {
            super(stateId, nt, orderingInfo, true);
        }
    }

    public static class RegExState extends PrimitiveState {
        private final java.util.regex.Pattern pattern;

        public RegExState(StateId stateId, NonTerminal nt, OrderingInfo orderingInfo, java.util.regex.Pattern pattern) {
            super(stateId, nt, orderingInfo);
            this.pattern = pattern;
        }

        Set<MatchResult> matches(CharSequence text, int startPosition, Function context) {
            java.util.regex.Matcher matcher = pattern.matcher(text);
            matcher.region(startPosition, text.length());
            matcher.useAnchoringBounds(false);
            matcher.useAnchoringBounds(false);
            Set<MatchResult> results = new HashSet<MatchResult>();
            if (matcher.lookingAt()) {
                results.add(new MatchResult(matcher.end(), Function.constant(Token.kAppOf("K", matcher.group())))); //matchFunction(text, matcher.start(), matcher.end())));
            }
            return results;
        }
    }
}
