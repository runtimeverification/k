package org.kframework.backend.java.kil;

import com.google.common.collect.ImmutableList;

import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;


/**
 * @author AndreiS
 */
public class KList extends KCollection {

    private static final String OPERATOR_NAME = ",, ";
    private static final String IDENTITY_NAME = "." + Kind.KLIST;

    public KList(ImmutableList<Term> items, Variable frame) {
        super(items, frame, Kind.KLIST);
    }

    /*
    public KList(ListIterator<Term> itemsIterator, Variable frame) {
        super(itemsIterator, frame, "KList");
    }
    */

    public KList(Variable frame) {
        super(frame, Kind.KLIST);
    }

    public KList(ImmutableList<Term> items) {
        super(items, null, Kind.KLIST);
    }

    /*
    public KList(ListIterator<Term> itemsIterator) {
        super(itemsIterator, null, "KList");
    }
    */

    public KList() {
        super(null, Kind.KLIST);
    }

    @Override
    public KCollection fragment(int length) {
        return new KList(items.subList(length, items.size()), frame);
    }

    @Override
    public String getOperatorName() {
        return KList.OPERATOR_NAME;
    }

    @Override
    public String getIdentityName() {
        return KList.IDENTITY_NAME;
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof KList)) {
            return false;
        }

        KList kList = (KList) object;
        return (super.frame == null ? kList.frame == null : frame.equals(kList.frame))
                && super.items.equals(kList.items);
    }

    @Override
    public void accept(Unifier unifier, Term patten) {
        unifier.unify(this, patten);
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
