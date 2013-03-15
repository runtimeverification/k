package org.kframework.backend.java.symbolic;

import org.kframework.kil.*;
import org.kframework.kil.List;
import org.kframework.kil.Map;
import org.kframework.kil.Set;
import org.kframework.kil.matchers.*;
import org.kframework.kil.rewriter.MapImpl;
import org.kframework.kil.rewriter.SetImpl;

/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/4/13
 * Time: 11:28 AM
 * To change this template use File | Settings | File Templates.
 */
public abstract class AbstractMatcher implements Matcher {

    public void fail() {
        throw new MatcherException("matching failed");
    }


    @Override
    public void match(Ambiguity term, Term term2) {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public void match(BackendTerm term, Term term2) {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public void match(Bag term, Term term2) {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public void match(BagItem term, Term term2) {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public void match(Bracket term, Term term2) {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public void match(Cell term, Term term2) {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public void match(Constant term, Term term2) {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public void match(Empty term, Term term2) {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public void match(Freezer term, Term term2) {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public void match(FreezerHole term, Term term2) {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public void match(FreezerSubstitution subst, Term subst2) {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public void match(FreezerVariable var, Term var2) {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public void match(Hole term, Term term2) {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public void match(KApp term, Term term2) {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public void match(KInjectedLabel term, Term term2) {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public void match(KList term, Term term2) {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public void match(KSequence term, Term term2) {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public void match(List term, Term term2) {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public void match(ListItem term, Term term2) {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public void match(Map term, Term term2) {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public void match(MapItem term, Term term2) {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public void match(MapLookupPattern term, Term term2) {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public void match(MapInsertPattern term, Term term2) {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public void match(MapImpl term, Term term2) {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public void match(SetLookupPattern term, Term term2) {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public void match(SetInsertPattern term, Term term2) {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public void match(SetImpl term, Term term2) {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public void match(Rewrite term, Term term2) {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public void match(Set term, Term term2) {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public void match(SetItem term, Term term2) {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public void match(TermComment term, Term term2) {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public void match(TermCons term, Term term2) {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public void match(Variable term, Term term2) {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public String getName() {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public java.util.Map<Term, Term> getSubstitution() {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public void start(Term t1, Term t2) {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }
}
