package org.kframework.backend.pdmc.pda;

import com.google.common.base.Joiner;
import org.kframework.backend.pdmc.pda.automata.Automata;
import org.kframework.backend.pdmc.pda.automata.State;
import org.kframework.backend.pdmc.pda.automata.Transition;
import org.kframework.backend.pdmc.pda.automata.util.IndexedTransitions;

import java.util.*;

/**
 * @author Traian
 */
public class PushdownSystem<Control, Alphabet> {
    Map<ConfigurationHead<Control, Alphabet>, Set<Rule<Control, Alphabet>>> deltaIndex;

    public PushdownSystem(Collection<Rule<Control, Alphabet>> rules) {
        deltaIndex = new HashMap<ConfigurationHead<Control, Alphabet>, Set<Rule<Control, Alphabet>>>();
        for (Rule<Control, Alphabet> rule : rules) {
            ConfigurationHead<Control, Alphabet> head = rule.getHead();
            Set<Rule<Control, Alphabet>> headRules = deltaIndex.get(head);
            if (headRules == null) {
                headRules = new HashSet<Rule<Control, Alphabet>>();
                deltaIndex.put(head, headRules);
            }
            headRules.add(rule);
        }
    }

    Set<Configuration<Control, Alphabet>> getTransitions(Configuration<Control, Alphabet> configuration) {
        if (configuration.isFinal()) return Collections.emptySet();
        Set<Rule<Control,Alphabet>> rules = deltaIndex.get(configuration.getHead());
        if (rules == null) return Collections.emptySet();
        HashSet<Configuration<Control, Alphabet>> configurations = new HashSet<Configuration<Control, Alphabet>>();
        for (Rule<Control,Alphabet> rule : rules) {
            configurations.add(new Configuration<Control, Alphabet>(rule.endConfiguration(), configuration.getStack()));
        }
        return configurations;
    }


    Set<Rule<Control, Alphabet>> getRules(ConfigurationHead configurationHead) {
        Set<Rule<Control, Alphabet>> rules = deltaIndex.get(configurationHead);
        if (rules == null) rules = Collections.<Rule<Control, Alphabet>>emptySet();
        return rules;
    }

    Automata<Control, Alphabet> postStar(Automata<Control, Alphabet> initial) {
        Set<Transition<Control, Alphabet>> trans = new HashSet<Transition<Control, Alphabet>>();
        IndexedTransitions<Control, Alphabet> rel = new IndexedTransitions<Control, Alphabet>();
        for (Set<Transition<Control, Alphabet>> transitions : initial.getTransitions()) {
            for (Transition<Control, Alphabet> transition : transitions) {
                if (transition.getStart().getLetter() == null) {
                    trans.add(transition);
                } else {
                    rel.add(transition);
                }
            }
        }
        while (!trans.isEmpty()) {
            Iterator<Transition<Control, Alphabet>> iterator = trans.iterator();
            Transition<Control, Alphabet> transition = iterator.next();
            iterator.remove();
            if (!rel.contains(transition)) {
                rel.add(transition);
                Alphabet gamma = transition.getLetter();
                State<Control, Alphabet> tp = transition.getStart();
                State<Control, Alphabet> q = transition.getEnd();
                if (gamma != null) {
                    assert tp.getLetter() == null : "Expecting PDS state on the lhs of " + transition;
                    Control p = tp.getState();
                    Set<Rule<Control, Alphabet>> rules = getRules(ConfigurationHead.<Control, Alphabet>of(p, gamma));
                    for (Rule<Control, Alphabet> rule : rules) {
                        Control pPrime = rule.endState();
                        Stack<Alphabet> stack = rule.endStack();
                        assert  stack.size() <= 2 : "At most 2 elements are allowed in the stack for now";
                        Alphabet gamma1 = null;
                        Alphabet gamma2 = null;
                        switch (stack.size()) {
                            case 0:
                                trans.add(Transition.of(tp, null, q));
                                break;
                            case 1:
                                gamma1 = stack.peek();
                                trans.add(Transition.<Control,Alphabet>of(
                                        State.<Control,Alphabet>of(pPrime), gamma1, q));
                                break;
                            case 2:
                                gamma1 = stack.get(0);
                                gamma2 = stack.get(1);
                                State<Control, Alphabet> qPPrimeGamma1 = State.<Control, Alphabet>of(pPrime, gamma1);
                                trans.add(Transition.<Control,Alphabet>of(
                                        State.<Control,Alphabet>of(pPrime), gamma1, qPPrimeGamma1));
                                rel.add(Transition.<Control,Alphabet>of(qPPrimeGamma1, gamma2, q));
                                for (Transition<Control, Alphabet> t : rel.getBackEpsilonTransitions(qPPrimeGamma1)) {
                                    trans.add(Transition.of(t.getStart(), gamma2, q));
                                }
                        }
                    }
                } else {
                    for (Transition<Control, Alphabet> t : rel.getFrontTransitions(q)) {
                        trans.add(Transition.of(tp, t.getLetter(), t.getEnd()));
                    }
                }
            }
        }
        return new Automata<Control, Alphabet>(rel.getTransitions(), initial.getFinalStates());
    }

    public static PushdownSystem<String, String> of(String s) {
        ArrayList<Rule<String, String>> rules = new ArrayList<Rule<String, String>>();
        String[] stringRules = s.split("\\s*;\\s*");
        for (String stringRule : stringRules) {
            Rule<String, String> rule = Rule.of(stringRule);
            rules.add(rule);
        }
        return  new PushdownSystem<String, String>(rules);
    }

    @Override
    public String toString() {
        Joiner joiner = Joiner.on(";\n");
        StringBuilder builder = new StringBuilder();
        joiner.appendTo(builder, getRules());
        return builder.toString();
    }

    private Collection<Rule<Control, Alphabet>> getRules() {
        ArrayList<Rule<Control, Alphabet>> rules = new ArrayList<Rule<Control, Alphabet>>();
        for (Set<Rule<Control, Alphabet>> values : deltaIndex.values()) {
            rules.addAll(values);
        }
        return rules;
    }
}
