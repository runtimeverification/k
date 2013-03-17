package org.kframework.backend.java.symbolic;

import org.kframework.kil.Ambiguity;
import org.kframework.kil.BackendTerm;
import org.kframework.kil.Bag;
import org.kframework.kil.BagItem;
import org.kframework.kil.Bracket;
import org.kframework.kil.Cast;
import org.kframework.kil.Cell;
import org.kframework.kil.Constant;
import org.kframework.kil.Empty;
import org.kframework.kil.Freezer;
import org.kframework.kil.FreezerHole;
import org.kframework.kil.FreezerSubstitution;
import org.kframework.kil.FreezerVariable;
import org.kframework.kil.Hole;
import org.kframework.kil.KApp;
import org.kframework.kil.KInjectedLabel;
import org.kframework.kil.KList;
import org.kframework.kil.KSequence;
import org.kframework.kil.List;
import org.kframework.kil.ListItem;
import org.kframework.kil.Map;
import org.kframework.kil.MapItem;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Set;
import org.kframework.kil.SetItem;
import org.kframework.kil.Term;
import org.kframework.kil.TermComment;
import org.kframework.kil.TermCons;
import org.kframework.kil.Variable;
import org.kframework.kil.matchers.MapInsertPattern;
import org.kframework.kil.matchers.MapLookupPattern;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.matchers.MatcherException;
import org.kframework.kil.matchers.SetInsertPattern;
import org.kframework.kil.matchers.SetLookupPattern;
import org.kframework.kil.rewriter.MapImpl;
import org.kframework.kil.rewriter.SetImpl;

/**
 * Created with IntelliJ IDEA. User: andrei Date: 3/4/13 Time: 11:28 AM To change this template use File | Settings | File Templates.
 */
public abstract class AbstractMatcher implements Matcher {

	public void fail() {
		throw new MatcherException("matching failed");
	}

	@Override
	public void match(Ambiguity term, Term term2) {
		throw new UnsupportedOperationException(); // To change body of implemented methods use File | Settings | File Templates.
	}

	@Override
	public void match(BackendTerm term, Term term2) {
		throw new UnsupportedOperationException(); // To change body of implemented methods use File | Settings | File Templates.
	}

	@Override
	public void match(Bag term, Term term2) {
		throw new UnsupportedOperationException(); // To change body of implemented methods use File | Settings | File Templates.
	}

	@Override
	public void match(BagItem term, Term term2) {
		throw new UnsupportedOperationException(); // To change body of implemented methods use File | Settings | File Templates.
	}

	@Override
	public void match(Bracket term, Term term2) {
		throw new UnsupportedOperationException(); // To change body of implemented methods use File | Settings | File Templates.
	}

	@Override
	public void match(Cast term, Term term2) {
		throw new UnsupportedOperationException(); // To change body of implemented methods use File | Settings | File Templates.
	}

	@Override
	public void match(Cell term, Term term2) {
		throw new UnsupportedOperationException(); // To change body of implemented methods use File | Settings | File Templates.
	}

	@Override
	public void match(Constant term, Term term2) {
		throw new UnsupportedOperationException(); // To change body of implemented methods use File | Settings | File Templates.
	}

	@Override
	public void match(Empty term, Term term2) {
		throw new UnsupportedOperationException(); // To change body of implemented methods use File | Settings | File Templates.
	}

	@Override
	public void match(Freezer term, Term term2) {
		throw new UnsupportedOperationException(); // To change body of implemented methods use File | Settings | File Templates.
	}

	@Override
	public void match(FreezerHole term, Term term2) {
		throw new UnsupportedOperationException(); // To change body of implemented methods use File | Settings | File Templates.
	}

	@Override
	public void match(FreezerSubstitution subst, Term subst2) {
		throw new UnsupportedOperationException(); // To change body of implemented methods use File | Settings | File Templates.
	}

	@Override
	public void match(FreezerVariable var, Term var2) {
		throw new UnsupportedOperationException(); // To change body of implemented methods use File | Settings | File Templates.
	}

	@Override
	public void match(Hole term, Term term2) {
		throw new UnsupportedOperationException(); // To change body of implemented methods use File | Settings | File Templates.
	}

	@Override
	public void match(KApp term, Term term2) {
		throw new UnsupportedOperationException(); // To change body of implemented methods use File | Settings | File Templates.
	}

	@Override
	public void match(KInjectedLabel term, Term term2) {
		throw new UnsupportedOperationException(); // To change body of implemented methods use File | Settings | File Templates.
	}

	@Override
	public void match(KList term, Term term2) {
		throw new UnsupportedOperationException(); // To change body of implemented methods use File | Settings | File Templates.
	}

	@Override
	public void match(KSequence term, Term term2) {
		throw new UnsupportedOperationException(); // To change body of implemented methods use File | Settings | File Templates.
	}

	@Override
	public void match(List term, Term term2) {
		throw new UnsupportedOperationException(); // To change body of implemented methods use File | Settings | File Templates.
	}

	@Override
	public void match(ListItem term, Term term2) {
		throw new UnsupportedOperationException(); // To change body of implemented methods use File | Settings | File Templates.
	}

	@Override
	public void match(Map term, Term term2) {
		throw new UnsupportedOperationException(); // To change body of implemented methods use File | Settings | File Templates.
	}

	@Override
	public void match(MapItem term, Term term2) {
		throw new UnsupportedOperationException(); // To change body of implemented methods use File | Settings | File Templates.
	}

	@Override
	public void match(MapLookupPattern term, Term term2) {
		throw new UnsupportedOperationException(); // To change body of implemented methods use File | Settings | File Templates.
	}

	@Override
	public void match(MapInsertPattern term, Term term2) {
		throw new UnsupportedOperationException(); // To change body of implemented methods use File | Settings | File Templates.
	}

	@Override
	public void match(MapImpl term, Term term2) {
		throw new UnsupportedOperationException(); // To change body of implemented methods use File | Settings | File Templates.
	}

	@Override
	public void match(SetLookupPattern term, Term term2) {
		throw new UnsupportedOperationException(); // To change body of implemented methods use File | Settings | File Templates.
	}

	@Override
	public void match(SetInsertPattern term, Term term2) {
		throw new UnsupportedOperationException(); // To change body of implemented methods use File | Settings | File Templates.
	}

	@Override
	public void match(SetImpl term, Term term2) {
		throw new UnsupportedOperationException(); // To change body of implemented methods use File | Settings | File Templates.
	}

	@Override
	public void match(Rewrite term, Term term2) {
		throw new UnsupportedOperationException(); // To change body of implemented methods use File | Settings | File Templates.
	}

	@Override
	public void match(Set term, Term term2) {
		throw new UnsupportedOperationException(); // To change body of implemented methods use File | Settings | File Templates.
	}

	@Override
	public void match(SetItem term, Term term2) {
		throw new UnsupportedOperationException(); // To change body of implemented methods use File | Settings | File Templates.
	}

	@Override
	public void match(TermComment term, Term term2) {
		throw new UnsupportedOperationException(); // To change body of implemented methods use File | Settings | File Templates.
	}

	@Override
	public void match(TermCons term, Term term2) {
		throw new UnsupportedOperationException(); // To change body of implemented methods use File | Settings | File Templates.
	}

	@Override
	public void match(Variable term, Term term2) {
		throw new UnsupportedOperationException(); // To change body of implemented methods use File | Settings | File Templates.
	}

	@Override
	public String getName() {
		throw new UnsupportedOperationException(); // To change body of implemented methods use File | Settings | File Templates.
	}

	@Override
	public java.util.Map<Term, Term> getSubstitution() {
		throw new UnsupportedOperationException(); // To change body of implemented methods use File | Settings | File Templates.
	}

	@Override
	public void start(Term t1, Term t2) {
		throw new UnsupportedOperationException(); // To change body of implemented methods use File | Settings | File Templates.
	}
}
