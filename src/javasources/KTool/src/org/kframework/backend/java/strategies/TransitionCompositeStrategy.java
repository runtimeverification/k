package org.kframework.backend.java.strategies;

import org.kframework.backend.java.kil.Rule;

import java.util.Collection;

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
