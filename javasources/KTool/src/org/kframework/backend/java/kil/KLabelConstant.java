package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.Production;
import org.kframework.kil.loader.Context;

import java.io.Serializable;
import java.util.HashMap;
import java.util.List;

import com.google.common.collect.ImmutableList;


/**
 * A KLabel constant.
 *
 * @author AndreiS
 */
public class KLabelConstant extends KLabel {

    /* KLabelConstant cache */
    private static final HashMap<String, KLabelConstant> cache = new HashMap<String, KLabelConstant>();

    /* un-escaped label */
    private final String label;
    /* unmodifiable view of a list of productions generating this {@code KLabelConstant} */
    private final List<Production> productions;
    /*
     * boolean flag set iff a production tagged with "function" or "predicate" generates this
     * {@code
     * KLabelConstant}
     */
    private final boolean isFunction;

    private KLabelConstant(String label, Context context) {
        this.label = label;
        productions = ImmutableList.copyOf(context.productionsOf(label));

        boolean isFunction = false;
        if (!label.startsWith("is")) {
            for (Production production : productions) {
                if (production.containsAttribute(Attribute.FUNCTION.getKey())) {
                    isFunction = true;
                    break;
                }
                if (production.containsAttribute(Attribute.PREDICATE.getKey())) {
                    isFunction = true;
                    break;
                }
            }
        } else {
            /* a KLabel beginning with "is" represents a sort membership predicate */
            isFunction = true;
        }
        this.isFunction = isFunction;
    }

    /**
     * Returns a {@code KLabelConstant} representation of label. The {@code KLabelConstant}
     * instances are cached to ensure uniqueness (subsequent invocations
     * of this method with the same label return the same {@code KLabelConstant} object).
     *
     * @param label string representation of the KLabel; must not be '`' escaped;
     * @return AST term representation the the KLabel;
     */
    public static KLabelConstant of(String label, Context context) {
        assert label != null;

        KLabelConstant kLabelConstant = cache.get(label);
        if (kLabelConstant == null) {
            kLabelConstant = new KLabelConstant(label, context);
            cache.put(label, kLabelConstant);
        }
        return kLabelConstant;
    }

    /**
     * Returns true iff no production tagged with "function" or "predicate" generates this {@code
     * KLabelConstant}.
     */
    @Override
    public boolean isConstructor() {
        return !isFunction;
    }

    /**
     * Returns true iff a production tagged with "function" or "predicate" generates this {@code
     * KLabelConstant}.
     */
    @Override
    public boolean isFunction() {
        return isFunction;
    }

    public String label() {
        return label;
    }

    /**
     * Returns a unmodifiable view of a list of productions generating this {@code KLabelConstant}.
     */
    public List<Production> productions() {
        return productions;
    }

    @Override
    public boolean equals(Object object) {
        /* {@code KLabelConstant} objects are cached to ensure uniqueness */
        return this == object;
    }

    @Override
    public int hashCode() {
        return label.hashCode();
    }

    @Override
    public String toString() {
        return label;
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

    /**
     * Returns the cached instance rather than the de-serialized instance if there is a cached
     * instance.
     */
    private Object readResolve() {
        KLabelConstant kLabelConstant = cache.get(label);
        if (kLabelConstant == null) {
            kLabelConstant = this;
            cache.put(label, kLabelConstant);
        }
        return kLabelConstant;
    }

}
