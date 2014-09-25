// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;



/**
 * An injection KLabel.
 *
 * @author AndreiS
 */
public class KLabelInjection extends KLabel {

    /**
     * Returns an injection of the term into a {@link org.kframework.backend.java.kil.KItem}.
     */
    public static KItem injectionOf(Term term, TermContext context) {
        return KItem.of(new KLabelInjection(term), KList.EMPTY, context);
    }

    private final Term term;

    public KLabelInjection(Term term) {
        // TODO(YilongL): enable this assertion
//        if (term instanceof KItem) {
//            assert !(((KItem) term).kLabel() instanceof KLabelInjection);
//        }
        // TODO(YilongL): no need to inject twice; however, this should be prevented in kompilation
//        if (term instanceof KItem && ((KItem) term).kLabel() instanceof KLabelInjection) {
//            this.term = ((KLabelInjection) ((KItem) term).kLabel()).term();
//        } else {
//            this.term = term;
//        }
        this.term = term;
    }

    public Term term() {
        return term;
    }

    @Override
    public final boolean equals(Object object) {
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
    public final boolean isConstructor() {
        return true;
    }

    @Override
    public final boolean isFunction() {
        return false;
    }

    @Override
    public final boolean isPattern() {
        return false;
    }

    @Override
    protected final int computeHash() {
        return term.hashCode();
    }

    @Override
    protected final boolean computeMutability() {
        return term.isMutable();
    }

    @Override
    public String toString() {
        return "(# " + term + ")";
    }

    @Override
    public void accept(Unifier unifier, Term pattern) {
        unifier.unify(this, pattern);
    }

    @Override
    public void accept(Matcher matcher, Term pattern) {
        matcher.match(this, pattern);
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
