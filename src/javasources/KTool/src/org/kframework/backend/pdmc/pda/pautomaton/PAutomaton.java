package org.kframework.backend.pdmc.pda.pautomaton;

import org.kframework.backend.pdmc.automaton.BasicAutomaton;
import org.kframework.backend.pdmc.automaton.Transition;

import java.util.*;

/**
 * A special class of automaton, used to compute all reachable states of a pushdown system.
 *
 * @author TraianSF
 */
public class PAutomaton<State, Alphabet> extends BasicAutomaton<State, Alphabet> {

    public PAutomaton(Collection<Transition<State, Alphabet>> delta, State initialState, Collection<State> finalStates) {
        super(delta, initialState, finalStates);
    }

    public static PAutomaton<PAutomatonState<String, String>, String> of(String s) {
        List<Transition<PAutomatonState<String, String>, String>> rules = new ArrayList<>();
        List<PAutomatonState<String, String>> states = new ArrayList<>();
        String[] stringTransitions = s.split("\\s*;\\s*");
        int n = stringTransitions.length - 2;
        PAutomatonState<String,String> initialState = PAutomatonState.of(stringTransitions[n]);
        String[] finalStatesStrings = stringTransitions[n+1].trim().split("\\s+");
        for (String state : finalStatesStrings) {
            states.add(PAutomatonState.ofString(state));
        }
        for (int i = 0; i < n; i++) {
            Transition<PAutomatonState<String, String>, String> rule = Transition.of(stringTransitions[i]);
            rules.add(rule);
        }
        return new PAutomaton<>(rules, initialState, states);
    }


}
