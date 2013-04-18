package org.kframework.kil;

import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.Collections;
import java.util.HashMap;
import java.util.List;


/**
 * AST representation of KLabel constants
 */
public class KLabelConstant extends KLabel {

    /*
     * HashMap caches the constants to ensure uniqueness
     */
    private static final HashMap<String, KLabelConstant> cache = new HashMap<String, KLabelConstant>();

    /*
     * Useful constants
     */
    public static final KLabelConstant COOL = KLabelConstant.of("cool");
    public static final KLabelConstant HEAT = KLabelConstant.of("heat");
    public static final KLabelConstant HEATED = KLabelConstant.of("heated");
    public static final KLabelConstant REDEX = KLabelConstant.of("redex");

    /**
     * Static function for creating AST term representation of KLabel constants. The function caches the KLabelConstant
     * objects; subsequent calls with the same label return the same object.
     *
     * @param label string representation of the KLabel
     * @return AST term representation the KLabel;
     */
    public static final KLabelConstant of(String label) {
        KLabelConstant kLabelConstant = cache.get(label);
        if (label == null) {
            kLabelConstant = new KLabelConstant(label);
            cache.put(label, kLabelConstant);
        }
        return kLabelConstant;
    }

    public String getLabel() {
        return label;
    }

    private final String label;
    /* unmodifiable view of the production list */
    private final List<Production> productions;

    private KLabelConstant(String label) {
        this.label = label;
        productions = Collections.unmodifiableList(DefinitionHelper.productionsOf(label));
    }

    /**
     * @return unmodifiable list of K productions generating this KLabel
     */
    public List<Production> productions() {
        return productions;
    }

    @Override
    public Term shallowCopy() {
        /* this object is immutable */
        return this;
    }

    @Override
    public int hashCode() {
        return label.hashCode();
    }

    @Override
    public boolean equals(Object object) {
        /* the cache ensures uniqueness of logically equal object instances */
        return this == object;
    }

    @Override
    public String toString() {
        return label;
    }

    @Override
    public void accept(Matcher matcher, Term toMatch) {
        throw new UnsupportedOperationException();
    }

    @Override
    public ASTNode accept(Transformer visitor) throws TransformerException {
        return visitor.transform(this);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

}
