package org.kframework.backend.java.strategies;

import org.kframework.backend.java.kil.Rule;

import java.util.Collection;
import java.util.List;
import java.util.LinkedList;

public class TransitionStrategy extends Strategy {
  public TransitionStrategy(List<String> tags) {
    rules = new LinkedList<Rule>();
    this.tags = tags;
  }

  public void apply(Collection<Rule> rules) {
    this.rules.clear();
    for (Rule r : rules) {
      for (String s : tags) {
        if (r.containsAttribute(s)) {
          this.rules.add(r);
          break;
        }
      }
    }
  }

  public Rule next() {
    if (!rules.isEmpty()) {
      return rules.pop();
    }
    return null;
  }

  public boolean hasNext() {
    return !(rules.isEmpty());
  }

  private LinkedList<Rule> rules;
  private List<String> tags;
} 
