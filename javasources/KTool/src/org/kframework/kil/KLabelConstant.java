package org.kframework.kil;

import java.util.Collections;
import java.util.HashMap;
import java.util.List;

import org.kframework.compile.transformers.AddPredicates;
import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.Context;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.StringUtil;
import org.w3c.dom.Element;

import aterm.ATermAppl;

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
	public static final KLabelConstant KLIST_EQUALITY = of("'_=" + KSorts.KLIST + "_");
	public static final KLabelConstant ANDBOOL_KLABEL = of("'#andBool");
	public static final KLabelConstant BOOL_ANDBOOL_KLABEL = of("'_andBool_");
	public static final KLabelConstant NOTBOOL_KLABEL = of("'notBool_");
	public static final KLabelConstant BOOL_ANDTHENBOOL_KLABEL = of("'_andThenBool_");
	public static final KLabelConstant KRESULT_PREDICATE = of(AddPredicates.predicate(KSorts.KRESULT));
    public static final KLabelConstant STREAM_PREDICATE = of(AddPredicates.predicate("Stream"));
	public static final KLabelConstant STRING_PLUSSTRING_KLABEL = of("'_+String_");

	/**
	 * Static function for creating AST term representation of KLabel constants. The function caches the KLabelConstant objects; subsequent calls with the same label return
	 * the same object.
	 * 
	 * @param label
	 *            string representation of the KLabel; must not be '`' escaped;
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

	/**
	 * Static function for creating AST term representation of KLabel constants. The function caches the KLabelConstant objects; subsequent calls with the same label return
	 * the same object. As opposed to "of", does not inspect for list of productions. Should be used for builtins only.
	 * 
	 * @param label
	 *            string representation of the KLabel; must not be '`' escaped;
	 * @return AST term representation the KLabel;
	 */
	public static KLabelConstant of(String label) {
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
		productions = Collections.emptyList();
	}

	private KLabelConstant(String label, Context context) {
		this.label = label;
		productions = Collections.unmodifiableList(context.productionsOf(label));
	}

	/**
	 * Constructs a {@link KLabelConstant} from an XML {@link Element} representing a constant. The KLabel string representation in the element is escaped according to Maude
	 * conventions.
	 */
	public KLabelConstant(Element element, org.kframework.kil.loader.Context context) {
		super(element);
		label = StringUtil.unescapeMaude(element.getAttribute(Constants.VALUE_value_ATTR));
		productions = Collections.unmodifiableList(context.productionsOf(label));
	}

	@SuppressWarnings("unchecked")
	public KLabelConstant(Element element) {
		super(element);
		label = StringUtil.unescapeMaude(element.getAttribute(Constants.VALUE_value_ATTR));
		productions = (List<Production>) Collections.EMPTY_LIST;
	}

	@SuppressWarnings("unchecked")
	public KLabelConstant(ATermAppl atm) {
		super(atm);
		label = StringUtil.unescapeMaude(((ATermAppl) atm.getArgument(0)).getName());
		productions = (List<Production>) Collections.EMPTY_LIST;
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
	public ASTNode accept(Transformer transformer) throws TransformerException {
		return transformer.transform(this);
	}

	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
	}
}
