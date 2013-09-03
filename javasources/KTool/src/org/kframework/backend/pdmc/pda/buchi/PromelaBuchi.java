package org.kframework.backend.pdmc.pda.buchi;

import com.google.common.base.Joiner;

import java.util.*;

/**
 * @author Traian
 */
public class PromelaBuchi {
    BuchiState initialState;

    public PromelaBuchi() {
        transitionMap = new HashMap<BuchiState, Collection<PromelaTransition>>();
    }

    private Map<BuchiState, Collection<PromelaTransition>> transitionMap;

    public void addTransitions(BuchiState start, Collection<PromelaTransition> transitions) {
        assert !transitionMap.containsKey(start) : "Duplicate state label";
        transitionMap.put(start, transitions);
        if (start.isStart()) initialState = start;
    }

    public BuchiState initialState() {
        return initialState;
    }

    @Override
    public String toString() {
        StringBuilder result = new StringBuilder();
        result.append("never {\n");
        boolean first = true;
        for (Map.Entry<BuchiState, Collection<PromelaTransition>> entry: transitionMap.entrySet()) {
            if (first) first = false; else result.append(";\n");
            result.append(entry.getKey() + " :\n");
            Collection<PromelaTransition> cases = entry.getValue();
            if (cases.isEmpty()) result.append("\tskip");
            else {
                result.append("\tif\n\t");
                Joiner.on("\n\t").appendTo(result, cases);
                result.append("\n\tfi");
            }
        }
        result.append("\n}\n");
        return result.toString();
    }

    public Set<BuchiState> getTransitions(BuchiState buchiState, Evaluator atomEvaluator) {
        Collection<PromelaTransition> transitions = transitionMap.get(buchiState);
        if (transitions == null) return Collections.emptySet();
        Set<BuchiState> states = new HashSet<BuchiState>();
        for (PromelaTransition transition : transitions) {
            if (transition.getCondition().evaluate(atomEvaluator)) {
                states.add(transition.getState());
            }
        }
        if (states.isEmpty()) return Collections.emptySet();
        return states;
    }
}
