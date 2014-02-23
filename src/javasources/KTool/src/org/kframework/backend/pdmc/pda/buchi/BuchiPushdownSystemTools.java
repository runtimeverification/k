package org.kframework.backend.pdmc.pda.buchi;

import org.apache.commons.lang3.tuple.Pair;
import org.kframework.backend.pdmc.automaton.Transition;
import org.kframework.backend.pdmc.pda.Configuration;
import org.kframework.backend.pdmc.pda.ConfigurationHead;
import org.kframework.backend.pdmc.pda.Rule;
import org.kframework.backend.pdmc.pda.graph.TarjanSCC;
import org.kframework.backend.pdmc.pda.pautomaton.PAutomaton;
import org.kframework.backend.pdmc.pda.pautomaton.PAutomatonState;
import org.kframework.backend.pdmc.pda.pautomaton.util.IndexedTransitions;

import java.util.*;

/**
 * Created by Traian on 07.02.2014.
 */
public class BuchiPushdownSystemTools<Control, Alphabet> {

    static class LabelledAlphabet<Control, Alphabet> {
        Alphabet letter;
        boolean repeated;

        public Rule<Pair<Control, BuchiState>, Alphabet> getRule() {
            return rule;
        }

        public void setRule(Rule<Pair<Control, BuchiState>, Alphabet> rule) {
            this.rule = rule;
        }

        public PAutomatonState<Pair<Control, BuchiState>, Alphabet> getBackState() {
            return backState;
        }

        public void setBackState(PAutomatonState<Pair<Control, BuchiState>, Alphabet> backState) {
            this.backState = backState;
        }

        Rule<Pair<Control, BuchiState>, Alphabet> rule;
        PAutomatonState<Pair<Control, BuchiState>, Alphabet> backState;

        LabelledAlphabet(Alphabet letter, boolean repeated) {
            this.letter = letter;
            this.repeated = repeated;
            rule = null;
            backState = null;
        }

        public static<Control, Alphabet> LabelledAlphabet<Control, Alphabet> of(Alphabet letter, boolean repeated) {
           return new LabelledAlphabet<>(letter, repeated);
        }

        public Alphabet getLeft() {
            return letter;
        }

        public boolean isRepeated() {
            return repeated;
        }


        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;

            LabelledAlphabet that = (LabelledAlphabet) o;

            if (repeated != that.repeated) return false;
            if (letter != null ? !letter.equals(that.letter) : that.letter != null) return false;

            return true;
        }

        @Override
        public int hashCode() {
            int result = letter != null ? letter.hashCode() : 0;
            result = 31 * result + (repeated ? 1 : 0);
            return result;
        }

        @Override
        public String toString() {
            return "<" +
                    "" + letter +
                    ", " + repeated +
                    '>';
        }
    }

    BuchiPushdownSystemInterface<Control, Alphabet> bps;

    public BuchiPushdownSystemTools(BuchiPushdownSystemInterface<Control, Alphabet> bps) {
        this.bps = bps;
    }

    class EpsilonTransitionWatch {
        Map<PAutomatonState<Pair<Control, BuchiState>, Alphabet>,
                Set<Pair<ConfigurationHead<Pair<Control, BuchiState>, Alphabet>, Alphabet>>> transitionsWatchMap;

        EpsilonTransitionWatch() {
            this.transitionsWatchMap = new HashMap<>();
        }

        Set<Pair<ConfigurationHead<Pair<Control, BuchiState>, Alphabet>, Alphabet>> get( PAutomatonState<Pair<Control, BuchiState>, Alphabet>  key) {
            Set<Pair<ConfigurationHead<Pair<Control, BuchiState>, Alphabet>, Alphabet>> set = transitionsWatchMap.get(key);
            if (set == null) {
                set = Collections.EMPTY_SET;
            }
            return set;
        }

        void addWatch(PAutomatonState<Pair<Control, BuchiState>, Alphabet>  key, ConfigurationHead<Pair<Control, BuchiState>, Alphabet> startHead, Alphabet endLetter) {
            Set<Pair<ConfigurationHead<Pair<Control, BuchiState>, Alphabet>, Alphabet>> set = transitionsWatchMap.get(key);
            if (set == null) {
                set = new HashSet<>();
                transitionsWatchMap.put(key, set);
            }
            set.add(Pair.of(startHead, endLetter));
        }
    }

    private PAutomaton<PAutomatonState<Pair<Control, BuchiState>, Alphabet>, LabelledAlphabet<Control, Alphabet>> postStar = null;
    TarjanSCC<ConfigurationHead<Pair<Control, BuchiState>, Alphabet>, Boolean> repeatedHeadsGraph = null;

    public PAutomaton<PAutomatonState<Pair<Control, BuchiState>, Alphabet>, LabelledAlphabet<Control, Alphabet>> getPostStar() {
        if (postStar == null)
            compute();
        return postStar;
    }

    public TarjanSCC<ConfigurationHead<Pair<Control, BuchiState>, Alphabet>, Boolean> getRepeatedHeadsGraph() {
        if (repeatedHeadsGraph == null)
            compute();
        return repeatedHeadsGraph;
    }

    private void compute() {
        EpsilonTransitionWatch watch = new EpsilonTransitionWatch();
        Set<Transition<PAutomatonState<Pair<Control, BuchiState>, Alphabet>, LabelledAlphabet<Control, Alphabet>>> trans =
                new HashSet<>();
        IndexedTransitions<PAutomatonState<Pair<Control, BuchiState>, Alphabet>, LabelledAlphabet<Control, Alphabet>> rel =
                new IndexedTransitions<PAutomatonState<Pair<Control, BuchiState>, Alphabet>, LabelledAlphabet<Control, Alphabet>>() {
                    @Override
                    public boolean isEpsilon(LabelledAlphabet<Control, Alphabet> gamma) {
                        if (gamma == null) return true;
                        return gamma.getLeft() == null;
                    }
                };

        repeatedHeadsGraph = new TarjanSCC<ConfigurationHead<Pair<Control, BuchiState>, Alphabet>, Boolean>();

        Configuration<Pair<Control, BuchiState>, Alphabet> initial = bps.initialConfiguration();
        ConfigurationHead<Pair<Control, BuchiState>, Alphabet> initialHead = initial.getHead();
        PAutomatonState<Pair<Control, BuchiState>, Alphabet> initialState =
                PAutomatonState.of(initialHead.getState());
        assert initial.getStack().isEmpty() : "Only one element in the initial stack accepted at the moment";
        PAutomatonState<Pair<Control, BuchiState>, Alphabet> finalState =
                PAutomatonState.of(initialHead.getState(), initialHead.getLetter());
        trans.add(Transition.of(initialState, LabelledAlphabet.<Control, Alphabet>of(initialHead.getLetter(), false), finalState));

        while (!trans.isEmpty()) {
            Iterator<Transition<PAutomatonState<Pair<Control, BuchiState>, Alphabet>, LabelledAlphabet<Control, Alphabet>>> iterator
                    = trans.iterator();
            Transition<PAutomatonState<Pair<Control, BuchiState>, Alphabet>, LabelledAlphabet<Control, Alphabet>> transition
                    = iterator.next();
            iterator.remove();
            if (transition.getLetter().getLeft() == null) {
                for (Pair<ConfigurationHead<Pair<Control, BuchiState>, Alphabet>, Alphabet> pair :
                        watch.get(transition.getEnd())) {
                    ConfigurationHead<Pair<Control, BuchiState>, Alphabet> endV =
                            ConfigurationHead.of(transition.getStart().getState(), pair.getRight());
                    if (repeatedHeadsGraph.addEdge(pair.getLeft(), endV, transition.getLetter().isRepeated())) {
//                        System.err.println("Forgotten edge from " + pair.getLeft().toString()
//                                + " to " + endV.toString());
                    }
                }

            }
            if (!rel.contains(transition)) {
                rel.add(transition);
                LabelledAlphabet<Control, Alphabet> letter = transition.getLetter();
                Alphabet gamma = letter.getLeft();
                boolean b = letter.isRepeated();
                PAutomatonState<Pair<Control, BuchiState>, Alphabet> tp = transition.getStart();
                PAutomatonState<Pair<Control, BuchiState>, Alphabet> q = transition.getEnd();
                if (gamma != null) {
                    assert tp.getLetter() == null : "Expecting PDS state on the lhs of " + transition;
                    Pair<Control, BuchiState> p = tp.getState();
                    final ConfigurationHead<Pair<Control, BuchiState>, Alphabet> configurationHead
                            = ConfigurationHead.<Pair<Control, BuchiState>, Alphabet>of(p, gamma);
                    Set<Rule<Pair<Control, BuchiState>, Alphabet>> rules =
                            bps.getRules(configurationHead);
                    for (Rule<Pair<Control, BuchiState>, Alphabet> rule : rules) {
                        Pair<Control, BuchiState> pPrime = rule.endState();
                        Stack<Alphabet> stack = rule.endStack();
                        assert  stack.size() <= 2 : "At most 2 elements are allowed in the stack for now";
                        Alphabet gamma1 = null;
                        Alphabet gamma2 = null;
                        LabelledAlphabet<Control, Alphabet> labelledLetter;
                        switch (stack.size()) {
                            case 0:
                                labelledLetter = LabelledAlphabet.<Control, Alphabet>of(null, b || bps.isFinal(pPrime));
                                trans.add(Transition.of(
                                        PAutomatonState.<Pair<Control, BuchiState>, Alphabet>of(pPrime),
                                        labelledLetter, q));
                                break;
                            case 1:
                                gamma1 = stack.peek();
                                repeatedHeadsGraph.addEdge(configurationHead, rule.endConfiguration().getHead(), bps.isFinal(p));
                                labelledLetter = LabelledAlphabet.<Control, Alphabet>of(gamma1, b || bps.isFinal(pPrime));
                                trans.add(Transition.of(
                                        PAutomatonState.<Pair<Control, BuchiState>, Alphabet>of(pPrime),
                                        labelledLetter, q));
                                break;
                            case 2:
                                gamma1 = stack.get(1);
                                repeatedHeadsGraph.addEdge(configurationHead, rule.endConfiguration().getHead(), bps.isFinal(p));
                                gamma2 = stack.get(0);
                                PAutomatonState<Pair<Control, BuchiState>, Alphabet> qPPrimeGamma1
                                        = PAutomatonState.of(pPrime, gamma1);
                                labelledLetter = LabelledAlphabet.<Control, Alphabet>of(gamma1, b || bps.isFinal(pPrime));
                                trans.add(Transition.of(
                                        PAutomatonState.<Pair<Control, BuchiState>, Alphabet>of(pPrime),
                                        labelledLetter, qPPrimeGamma1));
                                labelledLetter = LabelledAlphabet.<Control, Alphabet>of(gamma2, false);
                                rel.add(Transition.of(qPPrimeGamma1, labelledLetter, q));
                                for (Transition<PAutomatonState<Pair<Control, BuchiState>, Alphabet>, LabelledAlphabet<Control, Alphabet>> t :
                                        rel.getBackEpsilonTransitions(qPPrimeGamma1)) {
                                    labelledLetter = LabelledAlphabet.<Control, Alphabet>of(gamma2, t.getLetter().isRepeated());
                                    trans.add(Transition.of(t.getStart(), labelledLetter, q));
                                    ConfigurationHead<Pair<Control, BuchiState>, Alphabet> endV =
                                            ConfigurationHead.of(t.getStart().getState(), gamma2);
                                    repeatedHeadsGraph.addEdge(configurationHead, endV, t.getLetter().isRepeated());
                                }
                                watch.addWatch(qPPrimeGamma1, configurationHead, gamma2);
                        }
                    }
                } else {
                    for (Transition<PAutomatonState<Pair<Control, BuchiState>, Alphabet>, LabelledAlphabet<Control, Alphabet>> t : rel.getFrontTransitions(q)) {
                        LabelledAlphabet<Control, Alphabet> tLetter = t.getLetter();
                        trans.add(Transition.of(tp, LabelledAlphabet.<Control, Alphabet>of(tLetter.getLeft(), tLetter.isRepeated() || b), t.getEnd()));
                    }
                }
            }
        }

        postStar = new PAutomaton<PAutomatonState<Pair<Control, BuchiState>, Alphabet>, LabelledAlphabet<Control, Alphabet>>(
                rel.getTransitions(),
                initialState,
                Collections.singleton(finalState));
    }
}
