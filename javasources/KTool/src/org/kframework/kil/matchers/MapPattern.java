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

public class MapPattern extends Term {

  private List<Binding> lookups;


  public MapPattern(Map m){
    lookups = new ArrayList<Binding>(m.getContents().size());
    
  }

  public MapPattern(MapPattern mp){

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
	public MapPattern shallowCopy() {
		return new MapPattern(this);
	}

}  

