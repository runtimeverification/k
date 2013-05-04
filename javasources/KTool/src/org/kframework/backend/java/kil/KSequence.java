package org.kframework.backend.java.kil;

import com.google.common.collect.ImmutableList;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;


/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/18/13
 * Time: 12:42 PM
 * To change this template use File | Settings | File Templates.
 */
public class KSequence extends KCollection {

    private static final String OPERATOR_NAME = " ~> ";
    private static final String IDENTITY_NAME = "." + Kind.K;

    public KSequence(ImmutableList<Term> items, Variable frame) {
        super(items, frame, Kind.K);
    }

    /*
    public KSequence(ListIterator<Term> itemsIterator, Variable frame) {
        super(itemsIterator, frame, "KSequence");
    }
    */

    public KSequence(Variable frame) {
        super(frame, Kind.K);
    }

    public KSequence(ImmutableList<Term> items) {
        super(items, null, Kind.K);
    }

    /*
    public KSequence(ListIterator<Term> itemsIterator) {
        super(itemsIterator, null, "KSequence");
    }
    */

    public KSequence() {
        super(null, Kind.K);
    }

    @Override
    public String getOperatorName() {
        return KSequence.OPERATOR_NAME;
    }

    @Override
    public String getIdentityName() {
        return KSequence.IDENTITY_NAME;
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof KSequence)) {
            return false;
        }

        KSequence kSequence = (KSequence) object;
        return super.frame == null ? kSequence.frame == null : frame.equals(kSequence.frame)
                && super.items.equals(kSequence.items);
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
