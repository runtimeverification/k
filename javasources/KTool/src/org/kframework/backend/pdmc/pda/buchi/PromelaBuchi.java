package org.kframework.backend.pdmc.pda.buchi;

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
