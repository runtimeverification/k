package org.kframework.backend.pdmc.pda.buchi;

import org.apache.commons.lang3.tuple.Pair;
import org.kframework.backend.java.kil.Collection;
import org.kframework.backend.pdmc.pda.*;
import org.kframework.backend.pdmc.pda.buchi.BuchiAutomaton;
import org.kframework.backend.pdmc.automaton.Transition;
import org.kframework.backend.pdmc.pda.graph.TarjanSCC;
import org.kframework.backend.pdmc.pda.pautomaton.PAutomaton;
import org.kframework.backend.pdmc.pda.pautomaton.PAutomatonState;
import org.kframework.backend.pdmc.pda.pautomaton.util.IndexedTransitions;

import java.util.*;

/**
 * @author Traian
 */
public class BuchiPushdownSystem<Control, Alphabet>
        implements PushdownSystemInterface<Pair<Control, BuchiState>, Alphabet> {
    private PushdownSystemInterface<Control, Alphabet> pds;
    private PromelaBuchi ba;
    private Evaluator atomEvaluator;

    public BuchiPushdownSystem(PushdownSystemInterface<Control, Alphabet> pds,
                               PromelaBuchi ba,
                               Evaluator atomEvaluator) {
        this.pds = pds;
        this.ba = ba;
        this.atomEvaluator = atomEvaluator;
    }

    @Override
    public Configuration<Pair<Control, BuchiState>, Alphabet> initialConfiguration() {
        BuchiState buchiInitial = ba.initialState();
        Configuration<Control, Alphabet> pdsInitial = pds.initialConfiguration();
        ConfigurationHead<Control, Alphabet> pdsHead = pdsInitial.getHead();

        ConfigurationHead<Pair<Control, BuchiState>, Alphabet> initialHead =
                ConfigurationHead.of(Pair.of(pdsHead.getState(), buchiInitial),
                        pdsHead.getLetter());
        Configuration<Pair<Control, BuchiState>, Alphabet> initial =
                new Configuration<Pair<Control, BuchiState>, Alphabet>(initialHead, pdsInitial.getStack());
        return initial;
    }

    @Override
    public Set<Rule<Pair<Control, BuchiState>, Alphabet>> getRules(
            ConfigurationHead<Pair<Control, BuchiState>, Alphabet> configurationHead) {
        ConfigurationHead<Control, Alphabet> pdsConfigurationHead = ConfigurationHead.of(
                configurationHead.getState().getLeft(), configurationHead.getLetter());
        BuchiState buchiState = configurationHead.getState().getRight();
        atomEvaluator.setState(pdsConfigurationHead);
        Set<BuchiState> transitions = ba.getTransitions(buchiState, atomEvaluator);
        Set<Rule<Control, Alphabet>> pdsRules = pds.getRules(pdsConfigurationHead);
        Set<Rule<Pair<Control, BuchiState>, Alphabet>> rules =
                new HashSet<Rule<Pair<Control, BuchiState>, Alphabet>>(pdsRules.size());
        for (Rule<Control, Alphabet> pdsRule : pdsRules) {
            for ( BuchiState buchiEndState : transitions) {
                Configuration<Control, Alphabet> pdsEndConfig = pdsRule.endConfiguration();
                ConfigurationHead<Control, Alphabet> pdsEndConfigHead = pdsEndConfig.getHead();
                Pair<Control, BuchiState> endState = Pair.of(pdsEndConfigHead.getState(), buchiEndState);
                ConfigurationHead<Pair<Control, BuchiState>, Alphabet> endHead =
                        ConfigurationHead.of(endState,
                                pdsConfigurationHead.getLetter());
                Configuration<Pair<Control, BuchiState>, Alphabet> endConfiguration =
                        new Configuration<Pair<Control, BuchiState>, Alphabet>(endHead, pdsEndConfig.getStack());
                rules.add(new Rule<Pair<Control, BuchiState>, Alphabet>(configurationHead, endConfiguration));
            }
        }
        return rules;
    }

    public boolean isFinal(Pair<Control, BuchiState> state) {
        return state.getRight().isFinal();
    }

    public PAutomaton<PAutomatonState<Pair<Control, BuchiState>, Alphabet>, Pair<Alphabet, Boolean>> postStar() {
        Set<Transition<PAutomatonState<Pair<Control, BuchiState>, Alphabet>, Pair<Alphabet, Boolean>>> trans =
                new HashSet<Transition<PAutomatonState<Pair<Control, BuchiState>, Alphabet>, Pair<Alphabet, Boolean>>>();
        IndexedTransitions<PAutomatonState<Pair<Control, BuchiState>, Alphabet>, Pair<Alphabet, Boolean>> rel =
                new IndexedTransitions<PAutomatonState<Pair<Control, BuchiState>, Alphabet>, Pair<Alphabet, Boolean>>() {
                    @Override
                    public boolean isEpsilon(Pair<Alphabet, Boolean> gamma) {
                        if (gamma == null) return true;
                        return gamma.getLeft() == null;
                    }
                };

        TarjanSCC<ConfigurationHead<Pair<Control, BuchiState>, Alphabet>, Boolean> graph
                = new TarjanSCC<ConfigurationHead<Pair<Control, BuchiState>, Alphabet>, Boolean>();

        Configuration<Pair<Control, BuchiState>, Alphabet> initial = initialConfiguration();
        ConfigurationHead<Pair<Control, BuchiState>, Alphabet> initialHead = initial.getHead();
        PAutomatonState<Pair<Control, BuchiState>, Alphabet> initialState =
                PAutomatonState.of(initialHead.getState());
        assert initial.getStack().isEmpty() : "Only one element in the initial stack accepted at the moment";
        PAutomatonState<Pair<Control, BuchiState>, Alphabet> finalState =
                PAutomatonState.of(initialHead.getState(), initialHead.getLetter());
        trans.add(Transition.of(initialState, Pair.of(initialHead.getLetter(), false), finalState));

        while (!trans.isEmpty()) {
            Iterator<Transition<PAutomatonState<Pair<Control, BuchiState>, Alphabet>, Pair<Alphabet, Boolean>>> iterator
                    = trans.iterator();
            Transition<PAutomatonState<Pair<Control, BuchiState>, Alphabet>, Pair<Alphabet, Boolean>> transition
                    = iterator.next();
            iterator.remove();
            if (!rel.contains(transition)) {
                rel.add(transition);
                Pair<Alphabet, Boolean> letter = transition.getLetter();
                Alphabet gamma = letter.getLeft();
                boolean b = letter.getRight().booleanValue();
                PAutomatonState<Pair<Control, BuchiState>, Alphabet> tp = transition.getStart();
                PAutomatonState<Pair<Control, BuchiState>, Alphabet> q = transition.getEnd();
                if (gamma != null) {
                    assert tp.getLetter() == null : "Expecting PDS state on the lhs of " + transition;
                    Pair<Control, BuchiState> p = tp.getState();
                    final ConfigurationHead<Pair<Control, BuchiState>, Alphabet> configurationHead
                            = ConfigurationHead.<Pair<Control, BuchiState>, Alphabet>of(p, gamma);
                    Set<Rule<Pair<Control, BuchiState>, Alphabet>> rules =
                            getRules(configurationHead);
                    for (Rule<Pair<Control, BuchiState>, Alphabet> rule : rules) {
                        Pair<Control, BuchiState> pPrime = rule.endState();
                        Stack<Alphabet> stack = rule.endStack();
                        assert  stack.size() <= 2 : "At most 2 elements are allowed in the stack for now";
                        Alphabet gamma1 = null;
                        Alphabet gamma2 = null;
                        switch (stack.size()) {
                            case 0:
                                trans.add(Transition.of(
                                        PAutomatonState.<Pair<Control, BuchiState>, Alphabet>of(pPrime),
                                        Pair.<Alphabet, Boolean>of(null, b || isFinal(pPrime)), q));
                                break;
                            case 1:
                                gamma1 = stack.peek();
                                ConfigurationHead<Pair<Control, BuchiState>, Alphabet> endConfigurationHead
                                        = ConfigurationHead.<Pair<Control, BuchiState>, Alphabet>of(pPrime, gamma1);
                                graph.addEdge(configurationHead, endConfigurationHead, isFinal(p));
                                trans.add(Transition.of(
                                        PAutomatonState.<Pair<Control, BuchiState>, Alphabet>of(pPrime),
                                        Pair.of(gamma1, b || isFinal(pPrime)), q));
                                break;
                            case 2:
                                gamma1 = stack.get(1);
                                endConfigurationHead = ConfigurationHead.<Pair<Control, BuchiState>, Alphabet>of(pPrime, gamma1);
                                graph.addEdge(configurationHead, endConfigurationHead, isFinal(p));
                                gamma2 = stack.get(0);
                                PAutomatonState<Pair<Control, BuchiState>, Alphabet> qPPrimeGamma1
                                        = PAutomatonState.of(pPrime, gamma1);
                                trans.add(Transition.of(
                                        PAutomatonState.<Pair<Control, BuchiState>, Alphabet>of(pPrime),
                                        Pair.of(gamma1, b || isFinal(pPrime) ), qPPrimeGamma1));
                                rel.add(Transition.of(qPPrimeGamma1, Pair.of(gamma2, false), q));
                                for (Transition<PAutomatonState<Pair<Control, BuchiState>, Alphabet>, Pair<Alphabet, Boolean>> t :
                                        rel.getBackEpsilonTransitions(qPPrimeGamma1)) {
                                    trans.add(Transition.of(t.getStart(), Pair.of(gamma2, t.getLetter().getRight()), q));
                                }
                        }
                    }
                } else {
                    for (Transition<PAutomatonState<Pair<Control, BuchiState>, Alphabet>, Pair<Alphabet, Boolean>> t : rel.getFrontTransitions(q)) {
                        Pair<Alphabet, Boolean> tLetter = t.getLetter();
                        trans.add(Transition.of(tp, Pair.of(tLetter.getLeft(), tLetter.getRight() || b), t.getEnd()));
                    }
                }
            }
        }
        return new PAutomaton<PAutomatonState<Pair<Control, BuchiState>, Alphabet>, Pair<Alphabet, Boolean>>(
                rel.getTransitions(),
                initialState,
                Collections.singleton(finalState));
    }
}
