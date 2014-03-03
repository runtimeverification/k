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
 * Implements some pushdown model-checking related algorithms from  Stefan Schwoon's Phd Thesis:
 * S. Schwoon.  Model-Checking Pushdown Systems.  Ph.D. Thesis, Technische Universitaet Muenchen, June 2002.
 *
 * @author TraianSF
 */
public class BuchiPushdownSystemTools<Control, Alphabet> {

    /**
     * Implements labeled transitions for the Post*  reachability automate.
     * Labels are added on the letters as specified in Schwoon's thesis,
     * Sec. 3.1.6 Witness generation.
     *
     * @param <Control>  specifies the control state of a pushdwown system
     * @param <Alphabet> specifies the alphabet of a pushdown system
     */
    static class LabelledAlphabet<Control, Alphabet> {
        Alphabet letter;
        //whether this transition corresponds to a repeated head in the pds
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

        // the rule used to label this transition
        Rule<Pair<Control, BuchiState>, Alphabet> rule;
        // if the transition is due to an epsilon transition identify the intermediate state.
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

    /**
     * Class used to track epsilon transitions for the Repeated heads graph generation
     */
    class EpsilonTransitionWatch {
        Map<PAutomatonState<Pair<Control, BuchiState>, Alphabet>,
                Set<Pair<ConfigurationHead<Pair<Control, BuchiState>, Alphabet>,
                        LabelledAlphabet<Control, Alphabet>>>> transitionsWatchMap;

        EpsilonTransitionWatch() {
            this.transitionsWatchMap = new HashMap<>();
        }

        Set<Pair<ConfigurationHead<Pair<Control, BuchiState>, Alphabet>,
                LabelledAlphabet<Control, Alphabet>>> get(PAutomatonState<Pair<Control, BuchiState>, Alphabet> key) {
            Set<Pair<ConfigurationHead<Pair<Control, BuchiState>, Alphabet>, LabelledAlphabet<Control, Alphabet>>> set =
                    transitionsWatchMap.get(key);
            if (set == null) {
                set = Collections.emptySet();
            }
            return set;
        }

        void addWatch(PAutomatonState<Pair<Control, BuchiState>, Alphabet> key,
                      ConfigurationHead<Pair<Control, BuchiState>, Alphabet> startHead,
                      Alphabet endLetter,
                      Rule<Pair<Control, BuchiState>, Alphabet> rule) {
            Set<Pair<ConfigurationHead<Pair<Control, BuchiState>, Alphabet>, LabelledAlphabet<Control, Alphabet>>> set =
                    transitionsWatchMap.get(key);
            if (set == null) {
                set = new HashSet<>();
                transitionsWatchMap.put(key, set);
            }
            LabelledAlphabet<Control, Alphabet> labelledLetter = LabelledAlphabet.of(endLetter, false);
            labelledLetter.setBackState(key);
            labelledLetter.setRule(rule);
            set.add(Pair.of(startHead, labelledLetter));
        }
    }

    private PAutomaton<PAutomatonState<Pair<Control, BuchiState>, Alphabet>,
            LabelledAlphabet<Control, Alphabet>> postStar = null;
    TarjanSCC<ConfigurationHead<Pair<Control, BuchiState>, Alphabet>, Boolean> repeatedHeadsGraph = null;

    public PAutomaton<PAutomatonState<Pair<Control, BuchiState>, Alphabet>,
            LabelledAlphabet<Control, Alphabet>> getPostStar() {
        if (postStar == null)
            compute();
        return postStar;
    }

    public TarjanSCC<ConfigurationHead<Pair<Control, BuchiState>, Alphabet>, Boolean> getRepeatedHeadsGraph() {
        if (repeatedHeadsGraph == null)
            compute();
        return repeatedHeadsGraph;
    }

    /**
     * Main method of the class. Implements the post* algorithm instrumented to also produce the repeated heads graph.
     * The post* algorithm implemented is presented in Figure 3.4, Section 3.1.4 of S. Schwoon's PhD thesis (p. 48)
     * The modification to compute the repeated heads graph is explained in Section 3.2.3 of Schwoon's thesis
     * (see also Algorithm 4 in Figure 3.9, p. 81)
     */
    private void compute() {
        EpsilonTransitionWatch watch = new EpsilonTransitionWatch();
        Set<Transition<PAutomatonState<Pair<Control, BuchiState>, Alphabet>, LabelledAlphabet<Control, Alphabet>>> trans =
                new HashSet<>();
        IndexedTransitions<PAutomatonState<Pair<Control, BuchiState>, Alphabet>,
                LabelledAlphabet<Control, Alphabet>> rel =
                new IndexedTransitions<PAutomatonState<Pair<Control, BuchiState>, Alphabet>,
                        LabelledAlphabet<Control, Alphabet>>() {
                    @Override
                    public boolean isEpsilon(LabelledAlphabet<Control, Alphabet> gamma) {
                        return gamma == null || gamma.getLeft() == null;
                    }
                };

        repeatedHeadsGraph = new TarjanSCC<>();

        Configuration<Pair<Control, BuchiState>, Alphabet> initial = bps.initialConfiguration();
        ConfigurationHead<Pair<Control, BuchiState>, Alphabet> initialHead = initial.getHead();
        PAutomatonState<Pair<Control, BuchiState>, Alphabet> initialState =
                PAutomatonState.of(initialHead.getState());
        assert initial.getStack().isEmpty() : "Only one element in the initial stack accepted at the moment";
        PAutomatonState<Pair<Control, BuchiState>, Alphabet> finalState =
                PAutomatonState.of(initialHead.getState(), initialHead.getLetter());
        trans.add(Transition.of(initialState,
                LabelledAlphabet.<Control, Alphabet>of(initialHead.getLetter(), false),
                finalState));

        while (!trans.isEmpty()) {
            Iterator<Transition<PAutomatonState<Pair<Control, BuchiState>, Alphabet>,
                    LabelledAlphabet<Control, Alphabet>>> iterator = trans.iterator();
            Transition<PAutomatonState<Pair<Control, BuchiState>, Alphabet>,
                    LabelledAlphabet<Control, Alphabet>> transition = iterator.next();
            iterator.remove();
            if (transition.getLetter().getLeft() == null) {
                for (Pair<ConfigurationHead<Pair<Control, BuchiState>, Alphabet>,
                        LabelledAlphabet<Control, Alphabet>> pair : watch.get(transition.getEnd())) {
                    ConfigurationHead<Pair<Control, BuchiState>, Alphabet> endV =
                            ConfigurationHead.of(transition.getStart().getState(), pair.getRight().letter);
                    repeatedHeadsGraph.addEdge(pair.getLeft(), endV, transition.getLetter().isRepeated());
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
                            = ConfigurationHead.of(p, gamma);
                    Set<Rule<Pair<Control, BuchiState>, Alphabet>> rules =
                            bps.getRules(configurationHead);
                    for (Rule<Pair<Control, BuchiState>, Alphabet> rule : rules) {
                        Pair<Control, BuchiState> pPrime = rule.endState();
                        Stack<Alphabet> stack = rule.endStack();
                        assert  stack.size() <= 2 : "At most 2 elements are allowed in the stack for now";
                        Alphabet gamma1, gamma2;
                        LabelledAlphabet<Control, Alphabet> labelledLetter;
                        switch (stack.size()) {
                            case 0:
                                labelledLetter = LabelledAlphabet.of(null, b || bps.isFinal(pPrime));
                                labelledLetter.setRule(rule);
                                trans.add(Transition.of(
                                        PAutomatonState.<Pair<Control, BuchiState>, Alphabet>of(pPrime),
                                        labelledLetter, q));
                                break;
                            case 1:
                                gamma1 = stack.peek();
                                repeatedHeadsGraph.addEdge(configurationHead,
                                        rule.endConfiguration().getHead(),
                                        bps.isFinal(p));
                                labelledLetter = LabelledAlphabet.of(gamma1,
                                        b || bps.isFinal(pPrime));
                                labelledLetter.setRule(rule);
                                trans.add(Transition.of(
                                        PAutomatonState.<Pair<Control, BuchiState>, Alphabet>of(pPrime),
                                        labelledLetter, q));
                                break;
                            case 2:
                                gamma1 = stack.get(1);
                                repeatedHeadsGraph.addEdge(configurationHead,
                                        rule.endConfiguration().getHead(),
                                        bps.isFinal(p));
                                gamma2 = stack.get(0);
                                PAutomatonState<Pair<Control, BuchiState>, Alphabet> qPPrimeGamma1
                                        = PAutomatonState.of(pPrime, gamma1);
                                labelledLetter = LabelledAlphabet.of(gamma1,
                                        b || bps.isFinal(pPrime));
                                labelledLetter.setRule(rule);
                                trans.add(Transition.of(
                                        PAutomatonState.<Pair<Control, BuchiState>, Alphabet>of(pPrime),
                                        labelledLetter, qPPrimeGamma1));
                                labelledLetter = LabelledAlphabet.of(gamma2, false);
                                labelledLetter.setRule(rule);
                                rel.add(Transition.of(qPPrimeGamma1, labelledLetter, q));
                                for (Transition<PAutomatonState<Pair<Control, BuchiState>, Alphabet>,
                                        LabelledAlphabet<Control, Alphabet>> t : rel.getBackEpsilonTransitions(qPPrimeGamma1)) {
                                    labelledLetter = LabelledAlphabet.of(gamma2,
                                            t.getLetter().isRepeated());
                                    labelledLetter.setRule(rule);
                                    labelledLetter.setBackState(qPPrimeGamma1);
                                    trans.add(Transition.of(t.getStart(), labelledLetter, q));
                                    ConfigurationHead<Pair<Control, BuchiState>, Alphabet> endV =
                                            ConfigurationHead.of(t.getStart().getState(), gamma2);
                                    repeatedHeadsGraph.addEdge(configurationHead, endV, t.getLetter().isRepeated());
                                }
                                watch.addWatch(qPPrimeGamma1, configurationHead, gamma2, rule);
                        }
                    }
                } else {
                    for (Transition<PAutomatonState<Pair<Control, BuchiState>, Alphabet>,
                            LabelledAlphabet<Control, Alphabet>> t : rel.getFrontTransitions(q)) {
                        LabelledAlphabet<Control, Alphabet> tLetter = t.getLetter();
                        LabelledAlphabet<Control, Alphabet> labelledLetter = LabelledAlphabet.of(
                                tLetter.getLeft(),
                                tLetter.isRepeated() || b);
                        labelledLetter.setBackState(q);
                        trans.add(Transition.of(tp, labelledLetter, t.getEnd()));
                    }
                }
            }
        }

        postStar = new PAutomaton<>(
                rel.getTransitions(),
                initialState,
                Collections.singleton(finalState));
    }

}
