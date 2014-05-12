// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.strategies;

import java.util.Collection;

/**
 * This is a derivation of the CompositeStrategy that always maintains a
 * TransitionStrategy as the top of the stack. It also provides access to
 * the nextIsTransition() method to check whether the next rules to be
 * returned will be transitions or not. This class will be used by the
 * rewrite engine to ensure that structural rules will always be applied
 * before transition rules, while still adding the user to specify more
 * strategies to be used.
 *
 * The actual logic of resetting and getting rules is inherited from
 * CompositeStrategy. All that needs to be changed is pop, and push.
 *
 * @author ericmikida
 *
 */

public class TransitionCompositeStrategy extends CompositeStrategy {
    public TransitionCompositeStrategy(Collection<String> tags) {
        transitionStrategy = new TransitionStrategy(tags);
        super.push(transitionStrategy);
    }

    public boolean nextIsTransition() {
        return transitionStrategy.nextIsTransition();
    }

    // Partially override push and pop to ensure that the transition
    // strategy is always on top of the stack.
    public void push(Strategy s) {
        super.pop();
        super.push(s);
        super.push(transitionStrategy);
    }

    public Strategy pop() {
        super.pop();
        Strategy temp = super.pop();
        super.push(transitionStrategy);
        return temp;
    }

    private TransitionStrategy transitionStrategy;
}
