package org.kframework.backend.pdmc.pda;

import org.kframework.backend.pdmc.pda.pautomaton.PAutomaton;
import org.kframework.backend.pdmc.pda.pautomaton.PAutomatonState;
import org.kframework.backend.pdmc.automaton.Transition;
import org.kframework.backend.pdmc.pda.pautomaton.util.IndexedTransitions;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.Stack;

/**
 * @author Traian
 */
public class PostStar {
    public static <Control, Alphabet> PAutomaton<PAutomatonState<Control, Alphabet>, Alphabet> postStar(
            PushdownSystemInterface<Control, Alphabet> pds,
            PAutomaton<PAutomatonState<Control, Alphabet>, Alphabet> initial) {
        Set<Transition<PAutomatonState<Control, Alphabet>, Alphabet>> trans = new HashSet<Transition<PAutomatonState<Control, Alphabet>, Alphabet>>();
        IndexedTransitions<PAutomatonState<Control, Alphabet>, Alphabet> rel =
                new IndexedTransitions<PAutomatonState<Control, Alphabet>, Alphabet>();
        for (Set<Transition<PAutomatonState<Control, Alphabet>, Alphabet>> transitions : initial.getTransitions()) {
            for (Transition<PAutomatonState<Control, Alphabet>, Alphabet> transition : transitions) {
                if (transition.getStart().getLetter() == null) {
                    trans.add(transition);
                } else {
                    rel.add(transition);
                }
            }
        }
        while (!trans.isEmpty()) {
            Iterator<Transition<PAutomatonState<Control, Alphabet>, Alphabet>> iterator = trans.iterator();
            Transition<PAutomatonState<Control, Alphabet>, Alphabet> transition = iterator.next();
            iterator.remove();
            if (!rel.contains(transition)) {
                rel.add(transition);
                Alphabet gamma = transition.getLetter();
                PAutomatonState<Control, Alphabet> tp = transition.getStart();
                PAutomatonState<Control, Alphabet> q = transition.getEnd();
                if (gamma != null) {
                    assert tp.getLetter() == null : "Expecting PDS state on the lhs of " + transition;
                    Control p = tp.getState();
                    Set<Rule<Control, Alphabet>> rules = pds.getRules(ConfigurationHead.<Control, Alphabet>of(p, gamma));
                    for (Rule<Control, Alphabet> rule : rules) {
                        Control pPrime = rule.endState();
                        Stack<Alphabet> stack = rule.endStack();
                        assert  stack.size() <= 2 : "At most 2 elements are allowed in the stack for now";
                        Alphabet gamma1 = null;
                        Alphabet gamma2 = null;
                        switch (stack.size()) {
                            case 0:
                                trans.add(Transition.<PAutomatonState<Control, Alphabet>, Alphabet>of(tp, null, q));
                                break;
                            case 1:
                                gamma1 = stack.peek();
                                trans.add(Transition.of(
                                        PAutomatonState.<Control,Alphabet>of(pPrime), gamma1, q));
                                break;
                            case 2:
                                gamma1 = stack.get(1);
                                gamma2 = stack.get(0);
                                PAutomatonState<Control, Alphabet> qPPrimeGamma1
                                        = PAutomatonState.<Control, Alphabet>of(pPrime, gamma1);
                                trans.add(Transition.of(
                                        PAutomatonState.<Control,Alphabet>of(pPrime), gamma1, qPPrimeGamma1));
                                rel.add(Transition.of(qPPrimeGamma1, gamma2, q));
                                for (Transition<PAutomatonState<Control, Alphabet>, Alphabet> t :
                                        rel.getBackEpsilonTransitions(qPPrimeGamma1)) {
                                    trans.add(Transition.of(t.getStart(), gamma2, q));
                                }
                        }
                    }
                } else {
                    for (Transition<PAutomatonState<Control, Alphabet>, Alphabet> t : rel.getFrontTransitions(q)) {
                        trans.add(Transition.of(tp, t.getLetter(), t.getEnd()));
                    }
                }
            }
        }
        return new PAutomaton<PAutomatonState<Control, Alphabet>, Alphabet>(rel.getTransitions(), initial.initialState(), initial.getFinalStates());
    }
}
