package org.kframework.kil.rewriter;

import java.util.HashSet;
import java.util.Set;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Cast;
import org.kframework.kil.SetItem;
import org.kframework.kil.Term;
import org.kframework.kil.matchers.MatchCompilationException;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;

/**
 * This is how sets are implemented within the term to be rewritten
 * 
 * It's a thin wrapper around a HashSet, which really makes me wish that either Term were an interface or that Java allowed multiple inheritance
 */
public class SetImpl extends Term {
	private Set<Term> set;

	public boolean contains(Term value) {
		return set.contains(value);
	}

	public void add(Term value) {
		set.add(value);
	}

	public void remove(Term value) {
		set.remove(value);
	}

	public SetImpl(SetImpl si) {
		set = si.set;
	}

	public SetImpl() {
		set = new HashSet<Term>();
	}

	/**
	 * Set must be a ground set
	 */
	public SetImpl(org.kframework.kil.Set s) {
		java.util.List<Term> contents = s.getContents();
		set = new HashSet<Term>();
		for (Term t : contents) {
			if (t instanceof SetItem) {
				SetItem si = (SetItem) t;
				set.add(si.getItem());
			} else {
				throw new MatchCompilationException("Trying to convert a Set which contains a non-SetItem to a SetImpl. " + "SetImpl can only be created from ground Sets. Set was: " + s);
			}
		}

	}

	public String toString() {
		return set.toString();
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
	public SetImpl shallowCopy() {
		return new SetImpl(this);
	}

	@Override
	public int hashCode() {
		//TODO: finish implementation
		return set.hashCode();
	}

	@Override
	public boolean equals(Object o) {
		if (o == null)
			return false;
		if (this == o)
			return true;
		if (!(o instanceof Cast))
			return false;
		SetImpl c = (SetImpl) o;
		// TODO: finish implementing this equals
		return true;
	}
}
