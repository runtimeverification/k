package org.kframework.kil;

import org.kframework.compile.transformers.AddPredicates;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;

import org.w3c.dom.Element;

import java.util.Collections;
import java.util.HashMap;
import java.util.List;


/**
 * AST representation of a KLabel constant.
 */
public class KLabelConstant extends KLabel {

    /**
     * HashMap caches the constants to ensure uniqueness.
     */
    private static final HashMap<String, KLabelConstant> cache = new HashMap<String, KLabelConstant>();

    /*
     * Useful constants.
     */
    public static final KLabelConstant COOL_KLABEL = of("cool");
    public static final KLabelConstant HEAT_KLABEL = of("heat");
    public static final KLabelConstant HEATED_KLABEL = of("heated");
    public static final KLabelConstant REDEX_KLABEL = of("redex");
    public static final KLabelConstant KNEQ_KLABEL = of("'_=/=K_");
    public static final KLabelConstant KEQ_KLABEL = of("'_==K_");
    public static final KLabelConstant KEQ = of("'_=K_");
    public static final KLabelConstant KLIST_EQUALITY = of("'_=" + MetaK.Constants.KList + "_");
    public static final KLabelConstant ANDBOOL_KLABEL = of("'#andBool");
    public static final KLabelConstant BOOL_ANDBOOL_KLABEL = of("'_andBool_");
    public static final KLabelConstant BOOL_ANDTHENBOOL_KLABEL = of("'_andThenBool_");
    public static final KLabelConstant KRESULT_PREDICATE = of(AddPredicates.predicate("KResult"));
    public static final KLabelConstant STRING_PLUSSTRING_KLABEL = of("'_+String_");

    /**
     * Static function for creating AST term representation of KLabel constants. The function caches the KLabelConstant
     * objects; subsequent calls with the same label return the same object.
     *
     * @param label string representation of the KLabel; must not be '`' escaped;
     * @return AST term representation the KLabel;
     */
    public static final KLabelConstant of(String label) {
        assert label != null;

        KLabelConstant kLabelConstant = cache.get(label);
        if (kLabelConstant == null) {
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

    public KLabelConstant(Element element) {
        super(element);
        label = element.getAttribute(Constants.VALUE_value_ATTR);
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
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof KLabelConstant)) {
            return false;
        }

        KLabelConstant kLabelConstant = (KLabelConstant) object;
        return label.equals(kLabelConstant.label);
    }

    @Override
    public int hashCode() {
        return label.hashCode();
    }

    @Override
    public String toString() {
        return getLabel();
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
