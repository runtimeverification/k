package org.kframework.backend.pdmc.pda.pautomaton;

import org.apache.commons.lang3.tuple.Pair;
import org.kframework.backend.pdmc.automaton.BasicAutomaton;
import org.kframework.backend.pdmc.automaton.Transition;
import org.kframework.backend.pdmc.automaton.TransitionIndex;

import java.util.*;

/**
 * @author Traian
 */
public class PAutomaton<State, Alphabet> extends BasicAutomaton<State, Alphabet> {

    public PAutomaton(Collection<Transition<State, Alphabet>> delta, State initialState, Collection<State> finalStates) {
        super(delta, initialState, finalStates);
    }

    public PAutomaton(Map<TransitionIndex<State, Alphabet>, Set<Transition<State, Alphabet>>> deltaIndex, State initialState, Set<State> finalStates) {
        super(deltaIndex, initialState, finalStates);
    }

    public static PAutomaton<PAutomatonState<String, String>, String> of(String s) {
        ArrayList<Transition<PAutomatonState<String, String>, String>> rules =
                new ArrayList<Transition<PAutomatonState<String, String>, String>>();
        ArrayList<PAutomatonState<String, String>> states = new ArrayList<PAutomatonState<String, String>>();
        String[] stringTransitions = s.split("\\s*;\\s*");
        int n = stringTransitions.length - 2;
        PAutomatonState<String,String> initialState = PAutomatonState.<String,String>of(stringTransitions[n]);
        String[] finalStatesStrings = stringTransitions[n+1].trim().split("\\s+");
        for (String state : finalStatesStrings) {
            states.add(PAutomatonState.ofString(state));
        }
        for (int i = 0; i < n; i++) {
            Transition<PAutomatonState<String, String>, String> rule = Transition.of(stringTransitions[i]);
            rules.add(rule);
        }
        return new PAutomaton<PAutomatonState<String, String>, String>(rules, initialState, states);
    }


}
