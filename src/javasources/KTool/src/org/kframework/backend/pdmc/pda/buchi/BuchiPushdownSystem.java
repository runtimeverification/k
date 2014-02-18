package org.kframework.backend.pdmc.pda.buchi;

import com.google.common.base.Joiner;
import org.apache.commons.lang3.tuple.Pair;
import org.kframework.backend.java.kil.Collection;
import org.kframework.backend.pdmc.pda.*;
import org.kframework.backend.pdmc.pda.buchi.BuchiAutomaton;
import org.kframework.backend.pdmc.automaton.Transition;
import org.kframework.backend.pdmc.pda.graph.TarjanSCC;
import org.kframework.backend.pdmc.pda.pautomaton.PAutomaton;
import org.kframework.backend.pdmc.pda.pautomaton.PAutomatonState;
import org.kframework.backend.pdmc.pda.pautomaton.util.IndexedTransitions;
import org.kframework.utils.StringBuilderUtil;
import org.strategoxt.stratego_lib.dec_string_to_int_0_0;
import org.strategoxt.strc.sdef_key_to_string_0_0;

import java.util.*;

/**
 * @author Traian
 */
//DONE toString method for BuchiPushdownSystem
//DONE Test Product is constructed as supposed
//DONE Test Post* algorithm for product
//DONE Test Post* algorithm for PDS
//DONE toString method for graph
//DONE Compute head reachability graph
//DONE Test head reachibility graph
//DONE Test TarjanSCC
//
//TODO Counterexample generation?
//TODO Integration with K
public class BuchiPushdownSystem<Control, Alphabet>
        implements BuchiPushdownSystemInterface<Control, Alphabet> {
    private PushdownSystemInterface<Control, Alphabet> pds;
    private PromelaBuchi ba;
    private Evaluator<ConfigurationHead<Control, Alphabet>> atomEvaluator;

    public BuchiPushdownSystem(PushdownSystemInterface<Control, Alphabet> pds,
                               PromelaBuchi ba,
                               Evaluator<ConfigurationHead<Control, Alphabet>> atomEvaluator) {
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
                                pdsEndConfigHead.getLetter());
                Configuration<Pair<Control, BuchiState>, Alphabet> endConfiguration =
                        new Configuration<Pair<Control, BuchiState>, Alphabet>(endHead, pdsEndConfig.getStack());
                rules.add(new Rule<Pair<Control, BuchiState>, Alphabet>(configurationHead, endConfiguration));
            }
        }
        return rules;
    }

    @Override
    public boolean isFinal(Pair<Control, BuchiState> state) {
        return state.getRight().isFinal();
    }




    @Override
    public String toString() {
        Configuration<Pair<Control, BuchiState>, Alphabet> cfg = initialConfiguration();
        StringBuilder result = new StringBuilder();
        result.append("Initial Configuration: ");
        result.append(cfg.toString());
        result.append("\n");
        Set<Pair<Control, BuchiState>> states = new HashSet<>();
        Set<Alphabet> letters = new HashSet<>();
        Stack<ConfigurationHead<Pair<Control, BuchiState>, Alphabet> > toBeProcessed = new Stack<>();
        toBeProcessed.push(cfg.getHead());
        states.add(cfg.getHead().getState());
        letters.add(cfg.getHead().getLetter());
        Joiner joiner = Joiner.on(";\n");
        while (!toBeProcessed.empty()) {
            ConfigurationHead<Pair<Control, BuchiState>, Alphabet> head = toBeProcessed.pop();
            System.err.println("To be processed: " + head);
            Set<Rule<Pair<Control, BuchiState>, Alphabet>> rules = getRules(head);
            System.err.println(rules);
            result.append("\n");
            joiner.appendTo(result, rules);
            for (Rule<Pair<Control, BuchiState>, Alphabet> rule : rules) {
                cfg = rule.endConfiguration();
                Stack<Alphabet> newstack = new Stack<>();
                newstack.addAll(cfg.getStack());
                if (cfg.getHead().isProper()) newstack.add(cfg.getHead().getLetter());
                for (Alphabet l : newstack) {
                    if (!letters.contains(l)) {
                        letters.add(l);
                        for (Pair<Control, BuchiState> state : states) {
                            toBeProcessed.push(ConfigurationHead.of(state, l));
                        }
                    }
                }
                Pair<Control, BuchiState> state = cfg.getHead().getState();
                if (!states.contains(state)) {
                    states.add(state);
                    for (Alphabet l : letters) {
                        toBeProcessed.push(ConfigurationHead.of(state, l));
                    }
                }
            }
        }
        return result.toString();
    }
}
