package org.kframework.kil;

import org.kframework.compile.transformers.AddPredicates;
import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;

import org.kframework.utils.StringUtil;
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
    public static final KLabelConstant COOL_KLABEL = ofStatic("cool");
    public static final KLabelConstant HEAT_KLABEL = ofStatic("heat");
    public static final KLabelConstant HEATED_KLABEL = ofStatic("heated");
    public static final KLabelConstant REDEX_KLABEL = ofStatic("redex");
    public static final KLabelConstant KNEQ_KLABEL = ofStatic("'_=/=K_");
    public static final KLabelConstant KEQ_KLABEL = ofStatic("'_==K_");
    public static final KLabelConstant KEQ = ofStatic("'_=K_");
    public static final KLabelConstant KLIST_EQUALITY = ofStatic("'_=" + KSorts.KLIST + "_");
    public static final KLabelConstant ANDBOOL_KLABEL = ofStatic("'#andBool");
    public static final KLabelConstant BOOL_ANDBOOL_KLABEL = ofStatic("'_andBool_");
    public static final KLabelConstant BOOL_ANDTHENBOOL_KLABEL = ofStatic("'_andThenBool_");
    public static final KLabelConstant KRESULT_PREDICATE = ofStatic(AddPredicates.predicate(KSorts.KRESULT));
    public static final KLabelConstant STRING_PLUSSTRING_KLABEL = ofStatic("'_+String_");

    /**
     * Static function for creating AST term representation of KLabel constants. The function caches the KLabelConstant
     * objects; subsequent calls with the same label return the same object.
     *
     * @param label string representation of the KLabel; must not be '`' escaped;
     * @return AST term representation the KLabel;
     */
    public static final KLabelConstant of(String label, DefinitionHelper definitionHelper) {
        assert label != null;

        KLabelConstant kLabelConstant = cache.get(label);
        if (kLabelConstant == null) {
            kLabelConstant = new KLabelConstant(label, definitionHelper);
            cache.put(label, kLabelConstant);
        }
        return kLabelConstant;
    }

    /**
     * Static function for creating AST term representation of KLabel constants. The function caches the KLabelConstant
     * objects; subsequent calls with the same label return the same object.
     * As opposed to "of", does not inspect for list of productions. Should be used for builtins only.
     *
     * @param label string representation of the KLabel; must not be '`' escaped;
     * @return AST term representation the KLabel;
     */
    public static final KLabelConstant ofStatic(String label) {
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

    /* un-escaped label */
    private final String label;
    /* unmodifiable view of the production list */
    private final List<Production> productions;
    
    private KLabelConstant(String label) {
        this.label = label;
        productions = (List<Production>)Collections.EMPTY_LIST;
    }

    private KLabelConstant(String label, DefinitionHelper definitionHelper) {
        this.label = label;
        productions = Collections.unmodifiableList(definitionHelper.productionsOf(label));
    }

    /**
     * Constructs a {@link KLabelConstant} from an XML {@link Element} representing a constant.
     * The KLabel string representation in the element is escaped according to Maude conventions.
     */
    public KLabelConstant(Element element, DefinitionHelper definitionHelper) {
        super(element);
        label = StringUtil.unescapeMaude(element.getAttribute(Constants.VALUE_value_ATTR));
        productions = Collections.unmodifiableList(definitionHelper.productionsOf(label));
    }

    public KLabelConstant(Element element) {
    	super(element);
        label = StringUtil.unescapeMaude(element.getAttribute(Constants.VALUE_value_ATTR));
        productions = (List<Production>)Collections.EMPTY_LIST;
	}

	/**
     * @return unmodifiable list of productions generating this KLabel
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
