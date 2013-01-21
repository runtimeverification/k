package org.kframework.kil;

import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.w3c.dom.Element;

import java.util.List;


/** Map contents have sort Map or MapItem */
public class Map extends Collection {

	public Map(Element element) {
		super(element);
	}

	public Map(String location, String filename) {
		super(location, filename, "Map");
	}

	public Map(Map node) {
		super(node);
	}

	public Map() {
		super("Map");
	}

	public Map(List<Term> col) {
		super("Map", col);
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
  public void accept(Matcher matcher, ASTNode toMatch){
    matcher.match(this, toMatch);
  }
	
	@Override
	public Map shallowCopy() {
		return new Map(this);
	}
}
