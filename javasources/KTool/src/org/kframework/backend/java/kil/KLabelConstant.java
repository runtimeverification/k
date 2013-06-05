package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.Production;
import org.kframework.kil.loader.Context;

import java.util.HashMap;
import java.util.List;

import com.google.common.collect.ImmutableList;


/**
 *
 * @author AndreiS
 */
public class KLabelConstant extends KLabel {

    /**
     * HashMap caches the constants to ensure uniqueness.
     */
    private static final HashMap<String, KLabelConstant> cache = new HashMap<String, KLabelConstant>();

    /* un-escaped label */
    private final String label;
    /* unmodifiable view of the production list */
    private final List<Production> productions;
    private final boolean isFunction;

    public KLabelConstant(String label, Context context) {
        this.label = label;
        productions = ImmutableList.copyOf(context.productionsOf(label));

        boolean isFunction = false;
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
        this.isFunction = isFunction;
    }

    /**
     * Returns a {@code KLabelConstant} representing the label. The function
     * caches the {@code KLabelConstant} objects; subsequent calls with the same label return
     * the same object.
     *
     * @param label string representation of the KLabel; must not be '`' escaped;
     * @return AST term representation the KLabel;
     */
    public static final KLabelConstant of(String label, Context context) {
        assert label != null;

        KLabelConstant kLabelConstant = cache.get(label);
        if (kLabelConstant == null) {
            kLabelConstant = new KLabelConstant(label, context);
            cache.put(label, kLabelConstant);
        }
        return kLabelConstant;
    }

    @Override
    public boolean isConstructor() {
        return !isFunction;
    }

    @Override
    public boolean isFunction() {
        return isFunction;
    }

    public String label() {
        return label;
    }

    /**
     * @return unmodifiable list of productions generating this {@code KLabelConstant}
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
