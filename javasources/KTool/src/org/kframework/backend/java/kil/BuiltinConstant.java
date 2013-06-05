package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Utils;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;


/**
 *
 *
 * @author AndreiS
 */
public class BuiltinConstant extends KLabel {

    private final String value;
    private final String sort;

    public BuiltinConstant(String value, String sort) {
        this.value = value;
        this.sort = sort;
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof BuiltinConstant)) {
            return false;
        }

        BuiltinConstant builtinConstant = (BuiltinConstant) object;
        return value.equals(builtinConstant.value) && sort.equals(builtinConstant.sort);
    }

    public String getSort() {
        return sort;
    }

    public String getValue() {
        return value;
    }

    @Override
    public boolean isConstructor() {
        return true;
    }

    @Override
    public boolean isFunction() {
        return false;
    }

    @Override
    public boolean isSymbolic() {
        return false;
    }

    @Override
    public int hashCode() {
        int hash = 1;
        hash = hash * Utils.HASH_PRIME + value.hashCode();
        hash = hash * Utils.HASH_PRIME + sort.hashCode();
        return hash;
    }

    @Override
    public String toString() {
        return value + "." + sort;
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
