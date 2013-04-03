package org.kframework.backend.java.symbolic;

import com.google.common.collect.ImmutableList;

import org.kframework.kil.ASTNode;


/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/18/13
 * Time: 12:36 PM
 * To change this template use File | Settings | File Templates.
 */
public class KList extends KCollection {

    private static final String OPERATOR_NAME = ",, ";
    private static final String IDENTITY_NAME = ".KList";

    public KList(ImmutableList<Term> items, Variable frame) {
        super(items, frame, "KList");
    }

    /*
    public KList(ListIterator<Term> itemsIterator, Variable frame) {
        super(itemsIterator, frame, "KList");
    }
    */

    public KList(Variable frame) {
        super(frame, "KList");
    }

    public KList(ImmutableList<Term> items) {
        super(items, null, "KList");
    }

    /*
    public KList(ListIterator<Term> itemsIterator) {
        super(itemsIterator, null, "KList");
    }
    */

    public KList() {
        super(null, "KList");
    }

    @Override
    public String getOperatorName() {
        return KList.OPERATOR_NAME;
    }

    @Override
    public String getIdentityName() {
        return KList.IDENTITY_NAME;
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
