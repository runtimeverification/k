package org.kframework.kil.matchers;

import org.kframework.kil.Term;

public class Binding {
  private Term key;
  private Term value;

  protected Binding(){}

  public Binding(Term k, Term v){
    key = k;
    value = v;
  }

  public Term getKey(){
    return key;
  }

  public Term getValue(){
    return value;
  }

  public String toString(){
    return key.toString() + " |-> " + value.toString();
  }
}
