package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;

/**
 * A primitive integer token. Generic type T may be instantiated with one of
 * {@code Byte}, {@code Short}, {@code Integer}, or {@code Long}.
 *
 * @author AndreiS
 */
public final class PrimitiveIntToken<T extends Number> extends BitVector<T> {

    private PrimitiveIntToken(T value, int bitwidth) {
        super(value, bitwidth);
    }

    /**
     * Returns a {@code PrimitiveIntToken} representation of the given primitive integer value.
     */
    public static <T extends Number> PrimitiveIntToken of(T value) {
        if (value instanceof Byte) {
            return new PrimitiveIntToken<>(value, Byte.SIZE);
        } else if (value instanceof Short) {
            return new PrimitiveIntToken<>(value, Short.SIZE);
        } else if (value instanceof Integer) {
            return new PrimitiveIntToken<>(value, Integer.SIZE);
        } else if (value instanceof Long) {
            return new PrimitiveIntToken<>(value, Long.SIZE);
        } else {
            assert false : "unexpected class type for " + value;
            /* dead code */
            return null;
        }
    }

    /**
     * Returns an {@code T} representation of the (interpreted) value of this PrimitiveIntToken.
     */
    public T primitiveIntValue() {
        return value;
    }

    /**
     * Returns an {@code long} representation of the (interpreted) value of this PrimitiveIntToken.
     */
    public long longValue() {
        if (value instanceof Byte) {
            return (Byte) value;
        } else if (value instanceof Short) {
            return (Short) value;
        } else if (value instanceof Integer) {
            return (Integer) value;
        } else if (value instanceof Long) {
            return (Long) value;
        } else {
            assert false;
            /* dead code */
            return 0;
        }
    }

    @Override
    public boolean equals(Object object) {
        return object instanceof PrimitiveIntToken
                && value.equals(((PrimitiveIntToken) object).value);
    }

    @Override
    public int hashCode() {
        if (hashCode == 0) {
            hashCode = value.hashCode();
        }
        return hashCode;
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
    public ASTNode accept(Transformer transformer) {
        return transformer.transform(this);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

}
