package org.kframework.kil.rewriter;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Term;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.List;
import java.util.Map;
import java.util.HashMap;

/**
 * This is how maps are implemented within the term to be rewritten
 *
 * It's a thin wrapper around a HashMap, which really makes me wish
 * that either Term were an interface or that Java allowed multiple 
 * inheritance
 */
public class MapImpl extends Term {
  private Map<Term, Term> map;

  public Term get(Term key){
    return map.get(key);
  }

  public void put(Term key, Term value){
    map.put(key, value);
  }

  public void remove(Term key){
    map.remove(key);
  }

  public MapImpl(MapImpl mi){
    map = new HashMap<Term, Term>();
  }

  public MapImpl(){
    map = new HashMap<Term, Term>();
  }

  public String toString(){
    return map.toString();
  }

  @Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
	}

  @Override
	public ASTNode accept(Transformer visitor) throws TransformerException {
		return visitor.transform(this);
	}

  @Override
  public void accept(Matcher matcher, Term toMatch){
    matcher.match(this, toMatch);
  }

  @Override
	public MapImpl shallowCopy() {
		return new MapImpl(this);
	}
}
