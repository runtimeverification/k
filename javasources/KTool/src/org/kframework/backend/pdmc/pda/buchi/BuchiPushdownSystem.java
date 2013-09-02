package org.kframework.backend.pdmc.pda.buchi;

import org.apache.commons.lang3.tuple.Pair;
import org.kframework.backend.pdmc.pda.*;
import org.kframework.backend.pdmc.pda.buchi.BuchiAutomaton;
import org.kframework.backend.pdmc.automaton.Transition;

import java.util.HashSet;
import java.util.Set;

/**
 * @author Traian
 */
public class BuchiPushdownSystem<Control, Alphabet, BuchiControl, Atom>
        implements PushdownSystemInterface<Pair<Control, BuchiControl>, Alphabet> {
    private PushdownSystemInterface<Control, Alphabet> pds;
    private BuchiAutomaton<BuchiControl, Atom> ba;
    private LTLValuation<Control, Alphabet, Atom> valuation;

    public BuchiPushdownSystem(PushdownSystemInterface<Control, Alphabet> pds,
                               BuchiAutomaton<BuchiControl, Atom> ba,
                               LTLValuation<Control,Alphabet, Atom> valuation) {
        this.pds = pds;
        this.ba = ba;
        this.valuation = valuation;
    }

    @Override
    public Configuration<Pair<Control, BuchiControl>, Alphabet> initialConfiguration() {
        BuchiControl buchiInitial = ba.initialState();
        Configuration<Control, Alphabet> pdsInitial = pds.initialConfiguration();
        ConfigurationHead<Control, Alphabet> pdsHead = pdsInitial.getHead();

        ConfigurationHead<Pair<Control, BuchiControl>, Alphabet> initialHead =
                ConfigurationHead.<Pair<Control, BuchiControl>, Alphabet>of(Pair.of(pdsHead.getState(), buchiInitial),
                        pdsHead.getLetter());
        Configuration<Pair<Control, BuchiControl>, Alphabet> initial =
                new Configuration<Pair<Control, BuchiControl>, Alphabet>(initialHead, pdsInitial.getStack());
        return initial;
    }

    @Override
    public Set<Rule<Pair<Control, BuchiControl>, Alphabet>> getRules(
            ConfigurationHead<Pair<Control, BuchiControl>, Alphabet> configurationHead) {
        ConfigurationHead<Control, Alphabet> pdsConfigurationHead = ConfigurationHead.<Control, Alphabet>of(
                configurationHead.getState().getLeft(), configurationHead.getLetter());
        BuchiControl buchiState = configurationHead.getState().getRight();
        Set<Atom> buchiLetter = valuation.evaluate(pdsConfigurationHead);
        Set<Transition<BuchiControl, Set<Atom>>> transitions = ba.getTransitions(buchiState, buchiLetter);
        Set<Rule<Control, Alphabet>> pdsRules = pds.getRules(pdsConfigurationHead);
        Set<Rule<Pair<Control, BuchiControl>, Alphabet>> rules =
                new HashSet<Rule<Pair<Control, BuchiControl>, Alphabet>>(pdsRules.size());
        for (Rule<Control, Alphabet> pdsRule : pdsRules) {
            for (Transition<BuchiControl, Set<Atom>> transition : transitions) {
                BuchiControl buchiEndState = transition.getEnd();
                Configuration<Control, Alphabet> pdsEndConfig = pdsRule.endConfiguration();
                ConfigurationHead<Control, Alphabet> pdsEndConfigHead = pdsEndConfig.getHead();
                Pair<Control, BuchiControl> endState = Pair.of(pdsEndConfigHead.getState(), buchiEndState);
                ConfigurationHead<Pair<Control, BuchiControl>, Alphabet> endHead =
                        ConfigurationHead.<Pair<Control, BuchiControl>, Alphabet>of(endState,
                                pdsConfigurationHead.getLetter());
                Configuration<Pair<Control, BuchiControl>, Alphabet> endConfiguration =
                        new Configuration<Pair<Control, BuchiControl>, Alphabet>(endState, pdsEndConfig.getStack());
                rules.add(new Rule<Pair<Control, BuchiControl>, Alphabet>(configurationHead, endConfiguration));
            }
        }
        return rules;
    }

    public boolean isFinal(Pair<Control, BuchiControl> state) {
        return ba.getFinalStates().contains(state.getRight());
    }
}
