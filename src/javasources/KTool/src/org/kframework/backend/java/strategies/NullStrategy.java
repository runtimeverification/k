package org.kframework.backend.java.strategies;

import org.kframework.backend.java.kil.Rule;

import java.util.Collection;
import java.util.Iterator;

public class NullStrategy extends Strategy {
  public NullStrategy() {
  }

  public void apply(Collection<Rule> rules) {
    iterator = rules.iterator();
  }

  public Rule next() {
    return iterator.next();
  }

  public boolean hasNext() {
    return iterator.hasNext();
  }

  private Iterator<Rule> iterator;
} 
