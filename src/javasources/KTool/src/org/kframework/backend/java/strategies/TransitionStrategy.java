package org.kframework.backend.java.strategies;

import org.kframework.backend.java.kil.Rule;

import java.util.Collection;
import java.util.LinkedList;

public class TransitionStrategy extends Strategy {
  public TransitionStrategy(Strategy strategy, Collection<String> tags) {
    this.strategy = strategy;
    this.tags = tags;
  }

  public boolean nextIsTransition() {
    return structural == null && transition != null;
  }

  public void apply(Collection<Rule> rules) {
    transition = new LinkedList<Rule>();
    structural = new LinkedList<Rule>();
    for (Rule r : rules) {
      boolean t = false;
      for (String s : tags) {
        if (r.containsAttribute(s)) {
          t = true;
          break;
        }
      }
      if (t) {
        transition.add(r);
      } else {
        structural.add(r);
      }
    }
  }

  public Collection<Rule> next() {
    Collection<Rule> n;
    if (structural != null) {
      n = structural;
      structural = null;
    } else if (transition != null) {
      n = transition;
      transition = null;
    } else {
      apply(strategy.next());
      n = next();
    }
    return n;
  }

  public boolean hasNext() {
    return structural != null || transition != null || strategy.hasNext();
  }

  private Collection<Rule> transition;
  private Collection<Rule> structural;
  private Collection<String> tags;
  private Strategy strategy;
} 
