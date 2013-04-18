package org.kframework.kil;

import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;


/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 4/17/13
 * Time: 12:21 PM
 * To change this template use File | Settings | File Templates.
 */
public class BoolBuiltin extends Builtin {

    public static final String SORT_NAME = "#Bool";

    public static final String TRUE_STRING = "true";
    public static final String FALSE_STRING = "false";

    public static final BoolBuiltin TRUE = new BoolBuiltin(Boolean.TRUE);
    public static final BoolBuiltin FALSE = new BoolBuiltin(Boolean.FALSE);

    public static BoolBuiltin of(String value) {
        assert value.equals(TRUE_STRING) || value.equals(FALSE_STRING);

        if (value.equals(BoolBuiltin.TRUE_STRING)) {
            return BoolBuiltin.TRUE;
        } else {
            return BoolBuiltin.FALSE;
        }
    }

    private final Boolean value;

    private BoolBuiltin(Boolean value) {
        super(BoolBuiltin.SORT_NAME);
        this.value = value;
    }

    @Override
    public String getValue() {
        return value.toString();
    }

    @Override
    public Term shallowCopy() {
        /* this object is immutable */
        return this;
    }

    @Override
    public int hashCode() {
        return value.hashCode();
    }

    @Override
    public boolean equals(Object object) {
        /* uniqueness of logically equal object instances */
        return this == object;
    }

    @Override
    public String toString() {
        return getValue();
    }

    @Override
    public void accept(Matcher matcher, Term toMatch) {
        throw new UnsupportedOperationException();
    }

    @Override
    public ASTNode accept(Transformer transformer) throws TransformerException {
        return transformer.transform(this);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

}
