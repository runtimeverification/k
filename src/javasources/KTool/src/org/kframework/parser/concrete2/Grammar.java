package org.kframework.parser.concrete2;

import java.util.*;

import org.kframework.kil.Ambiguity;
import org.kframework.kil.KApp;
import org.kframework.kil.KLabel;
import org.kframework.kil.KList;
import org.kframework.kil.Term;
import org.kframework.kil.Token;
import org.omg.CORBA.Environment;

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
        Set<NextableState> intermediaryStates = new HashSet<>();
        public final OrderingInfo orderingInfo = null; // TODO

        static class OrderingInfo implements Comparable<OrderingInfo> {
            final int key;
            public OrderingInfo(int key) { this.key = key; }
            public int compareTo(OrderingInfo that) { return Integer.compare(this.key, that.key); }
        }

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
            final int key;
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

        public int compareTo(State that) { return this.stateId.compareTo(that.stateId); }
        /*
        public int compareTo(State that) {
            int x;
            return
                ((x = this.orderingInfo.compareTo(that.orderingInfo)) != 0) ? x :
                ((x = this.stateId.compareTo(that.stateId)) != 0) ? x :
                this.nt.compareTo(that.nt);
        }
        */

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
        public final Set<State> next = new HashSet<>();
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

    abstract class Rule {}
    abstract class ContextFreeRule extends Rule {
        public abstract Set<KList> apply(Set<KList> set);
    }
    abstract class KListRule extends ContextFreeRule {
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
    class WrapLabelRule extends KListRule {
        KLabel label;
        public WrapLabelRule(KLabel label) { this.label = label; }
        protected KList apply(KList klist) {
            return new KList(Arrays.<Term>asList(new KApp(label, klist)));
        }
    }
    abstract class SuffixRule extends KListRule {
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
    class DeleteRule extends SuffixRule {
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
    class AppendRule extends SuffixRule {
        private final Term term;
        public AppendRule(Term term) { this.term = term; }
        protected boolean rejectSmallKLists() { return false; }
        protected int getSuffixLength() { return 0; }
        protected Result applySuffix(List<Term> terms) {
            return new Accept(Arrays.<Term>asList(term));
        }
    }
    // for putting labels before the fact
    class InsertRule extends SuffixRule {
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
    abstract class ContextSensitiveRule extends Rule {
        abstract Set<KList> apply(KList context, Set<KList> set);
    }
    class CheckLabelContextRule {
        private boolean positive;
    }

    public static class RuleState extends NextableState {
        public final Rule rule;
        public RuleState(StateId stateId, NonTerminal nt, OrderingInfo orderingInfo, Rule rule) {
            super(stateId, nt, orderingInfo, true);
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
    }
}
