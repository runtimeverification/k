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
 * Time: 12:36 PM
 * To change this template use File | Settings | File Templates.
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
        return super.frame == null ? kList.frame == null : frame.equals(kList.frame)
                && super.items.equals(kList.items);
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
