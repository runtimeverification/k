package org.kframework.kil.rewriter;

import java.util.HashMap;
import java.util.Map;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Cast;
import org.kframework.kil.MapItem;
import org.kframework.kil.Term;
import org.kframework.kil.matchers.MatchCompilationException;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;

/**
 * This is how maps are implemented within the term to be rewritten
 * 
 * It's a thin wrapper around a HashMap, which really makes me wish that either Term were an interface or that Java allowed multiple inheritance
 */
public class MapImpl extends Term {
	private Map<Term, Term> map;

	public Term get(Term key) {
		return map.get(key);
	}

	public void put(Term key, Term value) {
		map.put(key, value);
	}

	public void remove(Term key) {
		map.remove(key);
	}

	public MapImpl(MapImpl mi) {
		map = mi.map;
	}

	public MapImpl() {
		map = new HashMap<Term, Term>();
	}

	/**
	 * Map must be a ground map
	 */
	public MapImpl(org.kframework.kil.Map m) {
		java.util.List<Term> contents = m.getContents();
		map = new HashMap<Term, Term>();
		for (Term t : contents) {
			if (t instanceof MapItem) {
				MapItem mi = (MapItem) t;
				map.put(mi.getKey(), mi.getValue());
			} else {
				throw new MatchCompilationException("Trying to convert a Map which contains a non-MapItem to a MapImpl. " + "MapImpl can only be created from ground Maps. Map was: " + m);
			}
		}

	}

	public String toString() {
		return map.toString();
	}

	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
	}

	@Override
	public ASTNode accept(Transformer transformer) throws TransformerException {
		return transformer.transform(this);
	}

	@Override
	public void accept(Matcher matcher, Term toMatch) {
		matcher.match(this, toMatch);
	}

	@Override
	public MapImpl shallowCopy() {
		return new MapImpl(this);
	}

	@Override
	public int hashCode() {
		//TODO: finish implementation
		return map.hashCode();
	}

	@Override
	public boolean equals(Object o) {
		if (o == null)
			return false;
		if (this == o)
			return true;
		if (!(o instanceof Cast))
			return false;
		MapImpl c = (MapImpl) o;
		// TODO: finish implementing this equals
		return true;
	}
}
