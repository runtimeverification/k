package org.kframework.backend.pdmc.pda.pautomaton;

import org.kframework.backend.pdmc.automaton.BasicAutomaton;
import org.kframework.backend.pdmc.automaton.Transition;
import org.kframework.backend.pdmc.automaton.TransitionIndex;

import java.util.*;

/**
 * @author Traian
 */
public class PAutomaton<Control, Alphabet> extends BasicAutomaton<PAutomatonState<Control, Alphabet>, Alphabet> {

    public PAutomaton(Collection<Transition<PAutomatonState<Control, Alphabet>, Alphabet>> delta, PAutomatonState<Control, Alphabet> initialState, Collection<PAutomatonState<Control, Alphabet>> finalStates) {
        super(delta, initialState, finalStates);
    }

    public PAutomaton(Map<TransitionIndex<PAutomatonState<Control, Alphabet>, Alphabet>, Set<Transition<PAutomatonState<Control, Alphabet>, Alphabet>>> deltaIndex, PAutomatonState<Control, Alphabet> initialState, Set<PAutomatonState<Control, Alphabet>> finalStates) {
        super(deltaIndex, initialState, finalStates);
    }

    public static PAutomaton<String, String> of(String s) {
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
        return new PAutomaton<String, String>(rules, initialState, states);
    }


}
