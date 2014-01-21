package org.kframework.kil;

import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;


/**
 * @author AndreiS
 */
public class KLabelInjection extends KLabel {

    private Term term;

    public KLabelInjection(Term term) {
        setTerm(term);
    }

    public KLabelInjection(KLabelInjection kLabelInjection) {
        this(kLabelInjection.term);
    }

    public Term getTerm() {
        return term;
    }

    public String injectedKind() {
        return term.getSort();
    }

    public void setTerm(Term term) {
        assert term.getSort().equals(KSorts.K) || term.getSort().equals(KSorts.KLABEL)
               || term.getSort().equals(KSorts.KLIST);
        this.term = term;
    }

    @Override
    public KLabelInjection shallowCopy() {
        return new KLabelInjection(this);
    }

    @Override
    public int hashCode() {
        return term.hashCode();
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof KLabelInjection)) {
            return false;
        }
        KLabelInjection kLabelInjection = (KLabelInjection) object;

        return term.equals(kLabelInjection.term);
    }

    @Override
    public ASTNode accept(Transformer transformer) throws TransformerException {
        return transformer.transform(this);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

    @Override
    public void accept(Matcher matcher, Term toMatch) {
        throw new UnsupportedOperationException();
    }

}
