package org.kframework.backend.java.strategies;

import org.kframework.backend.java.kil.Rule;

import java.util.Collection;

public abstract class Strategy {
  public abstract void apply(Collection<Rule> rules);
  public abstract Rule next();
  public abstract boolean hasNext();
}
