package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;


/**
 * @author AndreiS
 */
public class KItemProjection extends Term {

    private final Term term;

    public KItemProjection(Kind kind, Term term) {
        super(kind);
        this.term = term;
    }

    public Term evaluateProjection() {
        if (!(term instanceof KItem)) {
            return this;
        }

        if (!((KItem) term).kList().iterator().hasNext() && !(((KItem) term).kList().hasFrame())) {
            return this;
        }

        if (!(((KItem) term).kLabel() instanceof KLabelInjection)) {
            return this;
        }

        return ((KLabelInjection) ((KItem) term).kLabel()).term();
    }

    public Term term() {
        return term;
    }

    /**
     * Returns {@code true} if a unification task between this term and another term cannot be
     * further decomposed into simpler unification tasks.
     */
    @Override
    public boolean isSymbolic() {
        return true;
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

        if (!(object instanceof KItemProjection)) {
            return false;
        }

        KItemProjection kItemProjection = (KItemProjection) object;
        return term.equals(kItemProjection.term);
    }

    @Override
    public String toString() {
        throw new UnsupportedOperationException();
    }

    @Override
    public void accept(Unifier unifier, Term patten) {
        throw new UnsupportedOperationException();
    }

    @Override
    public ASTNode accept(Transformer transformer) {
        return transformer.transform(this);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

}
