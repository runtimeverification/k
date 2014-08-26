// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.visitors.Visitor;
import org.kframework.utils.StringUtil;
import org.kframework.utils.xml.XML;
import org.w3c.dom.Element;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * The AST representation of tokens. This should be used only in the front end,
 * and should be flattened into KIL classes after FlattenSyntax.
 */
public class Constant extends ProductionReference {
    protected String value;

    public Constant(Sort sort, String value) {
        super(sort, null);
        this.value = value;
    }

    public Constant(Sort sort, String value, Production p) {
        super(sort, p);
        this.value = value;
    }

    public Constant(Constant node) {
        super(node);
        this.value = node.value;
        assert this.production != null;
    }

    @Override
    public String toString() {
        return "#token(" + StringUtil.enquoteKString(sort.getName()) + "," +
                StringUtil.enquoteKString(value) + ")(.KList)";
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }

    @Override
    public Constant shallowCopy() {
        return new Constant(this);
    }

    public String getValue() {
        return value;
    }

    public void setValue(String value) {
        this.value = value;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof Constant)) return false;

        Constant constant = (Constant) o;

        if (!value.equals(constant.value)) return false;
        if (!sort.equals(constant.sort)) return false;

        return true;
    }

    @Override
    public int hashCode() {
        return value.hashCode() + 31 * sort.hashCode();
    }
}
