package org.kframework.kil;

import org.kframework.kil.visitors.Visitor;

import java.util.Collection;

/**
 * A builtin set
 *
 * @author TraianSF
 */
public class SetBuiltin extends CollectionBuiltin {
    public SetBuiltin(DataStructureSort sort, Collection<Term> baseTerms, java.util.Collection<Term> elements) {
        super(sort, baseTerms, elements);
    }

    @Override
    public <P, R> R accept(Visitor<P, R> visitor, P p) {
        return visitor.visit(this, p);
    }
}
