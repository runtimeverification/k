package org.kframework.kil.matchers;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Term;
import org.kframework.kil.Map;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.List;
import java.util.ArrayList;

public class MapLookupPattern extends Term {

  private List<Binding> lookups;


  public MapLookupPattern(Map m){
    java.util.List<Term> contents = m.getContents();
    lookups = new ArrayList<Binding>(contents.size());
    for(Term t : contents){
      
    } 
  }

  public MapLookupPattern(MapLookupPattern mp){

  }

  public List<Binding> getLookups(){
    return lookups;
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
	public MapLookupPattern shallowCopy() {
		return new MapLookupPattern(this);
	}

}  

