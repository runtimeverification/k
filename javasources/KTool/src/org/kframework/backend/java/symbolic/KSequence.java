package org.kframework.backend.java.symbolic;

import com.google.common.collect.ImmutableList;

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
    private static final String IDENTITY_NAME = ".K";

    public KSequence(ImmutableList<Term> items, Variable frame) {
        super(items, frame, "KSequence");
    }

    /*
    public KSequence(ListIterator<Term> itemsIterator, Variable frame) {
        super(itemsIterator, frame, "KSequence");
    }
    */

    public KSequence(Variable frame) {
        super(frame, "KSequence");
    }

    public KSequence(ImmutableList<Term> items) {
        super(items, null, "KSequence");
    }

    /*
    public KSequence(ListIterator<Term> itemsIterator) {
        super(itemsIterator, null, "KSequence");
    }
    */

    public KSequence() {
        super(null, "KSequence");
    }

    @Override
    public String getOperatorName() {
        return KSequence.OPERATOR_NAME;
    }

    @Override
    public String getIdentityName() {
        return KSequence.IDENTITY_NAME;
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
