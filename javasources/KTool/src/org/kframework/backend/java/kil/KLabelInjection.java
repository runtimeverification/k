package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Utils;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;


/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/18/13
 * Time: 1:50 PM
 * To change this template use File | Settings | File Templates.
 */
public class KLabelInjection extends KLabel {

    private final Term term;

    public KLabelInjection(Term term) {
        this.term = term;
    }

    public Term getTerm() {
        return term;
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
    public boolean isConstructor() {
        return false;
    }

    @Override
    public boolean isFunction() {
        return false;
    }

    @Override
    public int hashCode() {
        int hash = 1;
        hash = hash * Utils.HASH_PRIME + term.hashCode();
        return hash;
    }

    @Override
    public String toString() {
        return "(# " + term + ")";
    }

    /**
     * @return a copy of the ASTNode containing the same fields.
     */
    @Override
    public ASTNode shallowCopy() {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public void accept(Matcher matcher, Term patten) {
        matcher.match(this, patten);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

    @Override
    public ASTNode accept(Transformer transformer) {
        return transformer.transform(this);
    }

}
