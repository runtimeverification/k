package org.kframework.backend.pdmc.pda.automata;

import java.util.*;

/**
 * @author Traian
 */
public class Automata<Control, Alphabet> {
    private final Map<TransitionIndex<Control, Alphabet>, Set<Transition<Control, Alphabet>>> deltaIndex;

    public Set<State<Control, Alphabet>> getFinalStates() {
        return finalStates;
    }

    private final Set<State<Control, Alphabet>> finalStates;

    public Automata(Collection<Transition<Control, Alphabet>> delta, Collection<State<Control, Alphabet>> finalStates) {
        this.finalStates = new HashSet<State<Control, Alphabet>>(finalStates);
        deltaIndex = new HashMap<TransitionIndex<Control, Alphabet>, Set<Transition<Control, Alphabet>>>();
        for (Transition<Control, Alphabet> transition : delta) {
            TransitionIndex<Control, Alphabet> index = transition.getIndex();
            Set<Transition<Control, Alphabet>> transitions = deltaIndex.get(index);
            if (transitions == null) {
                transitions = new HashSet<Transition<Control, Alphabet>>();
                deltaIndex.put(index, transitions);
            }
            transitions.add(transition);
        }

    }

    public Automata(Map<TransitionIndex<Control, Alphabet>, Set<Transition<Control, Alphabet>>> deltaIndex, Set<State<Control, Alphabet>> finalStates) {
        this.deltaIndex = deltaIndex;
        this.finalStates = finalStates;
    }

    public Collection<Set<Transition<Control, Alphabet>>> getTransitions() {
        return deltaIndex.values();
    }

    public static Automata<String, String> of(String s) {
        ArrayList<Transition<String, String>> rules = new ArrayList<Transition<String, String>>();
        ArrayList<State<String, String>> states = new ArrayList<State<java.lang.String, java.lang.String>>();
        String[] stringTransitions = s.split("\\s*;\\s*");
        int n = stringTransitions.length - 1;
        String[] finalStatesStrings = stringTransitions[n].trim().split("\\s+");
        for (String state : finalStatesStrings) {
            states.add(State.ofString(state));
        }
        for (int i = 0; i < n; i++) {

            Transition<String, String> rule = Transition.of(stringTransitions[i]);
            rules.add(rule);
        }
        return new Automata<String, String>(rules, states);
    }

    @Override
    public String toString() {
        String string = "";
        for (Set<Transition<Control, Alphabet>> transitions : deltaIndex.values()) {
            for (Transition<Control, Alphabet> transition : transitions) {
                string += transition + ";";
            }
        }
        boolean notFirst = true;
        for (State<Control, Alphabet> state : finalStates) {
            if (notFirst) {
                string += " ";
            }
            string += state;
        }
        return string;
    }
}
