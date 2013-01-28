package org.kframework.kil.matchers;

import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.kil.rewriter.MapImpl;

public class Lookup extends Binding {
  private MapImpl map;
 
  protected Lookup(){}

  public Lookup(MapImpl m, Term k, Term v){
    super(k, v);
    map = m;
  }

  public MapImpl getMapImpl(){
    return map;
  }
}

