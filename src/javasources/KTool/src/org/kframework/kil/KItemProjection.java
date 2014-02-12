package org.kframework.kil;

import org.kframework.backend.java.util.Utils;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;


/**
 * @author AndreiS
 */
public class KItemProjection extends Term {

    private Term term;

    public KItemProjection(String kind, Term term) {
        super(kind);
        this.term = term;
    }

    public KItemProjection(KItemProjection kItemProjection){
        super(kItemProjection);
        this.term = kItemProjection.term;
    }

    public Term getTerm() {
        return term;
    }

    public String projectedKind() {
        return getSort();
    }

    public void setTerm(Term term) {
        this.term = term;
    }
    
    @Override
    public KItemProjection shallowCopy() {
        return new KItemProjection(this);
    }

    @Override
    public int hashCode() {
        int hash = 1;
        hash = hash * Utils.HASH_PRIME + getSort().hashCode();
        hash = hash * Utils.HASH_PRIME + term.hashCode();
        return hash;
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof KItemProjection)) {
            return false;
        }
        KItemProjection kItemProjection = (KItemProjection) object;

        return getSort().equals(kItemProjection.getSort()) && term.equals(kItemProjection.term);
    }
    
    @Override
    public String toString() {
        return "projection(" + term + ")";
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
