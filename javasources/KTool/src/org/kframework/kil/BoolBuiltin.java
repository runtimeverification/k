package org.kframework.kil;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.w3c.dom.Element;

import aterm.ATermAppl;

/**
 * Class representing a builtin boolean token.
 */
public class BoolBuiltin extends Token {

	public static final String SORT_NAME = "#Bool";

	public static final String TRUE_STRING = "true";
	public static final String FALSE_STRING = "false";

	/**
	 * #token("#Bool", "true")
	 */
	public static final BoolBuiltin TRUE_TOKEN = new BoolBuiltin(Boolean.TRUE);
	/**
	 * #token("#Bool", "false")
	 */
	public static final BoolBuiltin FALSE_TOKEN = new BoolBuiltin(Boolean.FALSE);

	/**
	 * #token("#Bool", "true")(.KList)
	 */
	public static final KApp TRUE = KApp.of(BoolBuiltin.TRUE_TOKEN);
	/**
	 * #token("#Bool", "false")(.KList)
	 */
	public static final KApp FALSE = KApp.of(BoolBuiltin.FALSE_TOKEN);

	/**
	 * Returns a {@link BoolBuiltin} representing a {@link boolean} value with the given {@link String} representation.
	 * 
	 * @param value
	 * @return
	 */
	public static BoolBuiltin of(String value) {
		checkValue(value);

		if (value.equals(BoolBuiltin.TRUE_STRING)) {
			return BoolBuiltin.TRUE_TOKEN;
		} else {
			return BoolBuiltin.FALSE_TOKEN;
		}
	}

	/**
	 * Returns a {@link KApp} representing a {@link BoolBuiltin} with the given value applied to an empty {@link KList}.
	 * 
	 * @param value
	 * @return
	 */
	public static KApp kAppOf(String value) {
		checkValue(value);

		if (value.equals(BoolBuiltin.TRUE_STRING)) {
			return BoolBuiltin.TRUE;
		} else {
			return BoolBuiltin.FALSE;
		}
	}

	private static void checkValue(String value) {
		assert value.equals(BoolBuiltin.TRUE_STRING) || value.equals(BoolBuiltin.FALSE_STRING) : "unexpected value " + value + " for a builtin bool token; expected one of "
				+ BoolBuiltin.TRUE_STRING + " or " + BoolBuiltin.FALSE_STRING;
	}

	private final Boolean value;

	private BoolBuiltin(Boolean value) {
		this.value = value;
	}

	protected BoolBuiltin(Element element) {
		super(element);
		String s = element.getAttribute(Constants.VALUE_value_ATTR);

		checkValue(s);

		value = Boolean.valueOf(s);
	}

	protected BoolBuiltin(ATermAppl atm) {
		super(atm);
		// TODO: get first child and then get the value
		String s = ((ATermAppl) atm.getArgument(0)).getName();

		checkValue(s);

		value = Boolean.valueOf(s);
	}

	/**
	 * Returns a {@link Boolean} representing the (interpreted) value of the boolean token.
	 */
	public Boolean booleanValue() {
		return value;
	}

	/**
	 * Returns a {@link String} representing the sort name of a boolean token.
	 * 
	 * @return
	 */
	@Override
	public String tokenSort() {
		return BoolBuiltin.SORT_NAME;
	}

	/**
	 * Returns a {@link String} representing the (uninterpreted) value of the boolean token.
	 * 
	 * @return
	 */
	@Override
	public String value() {
		return value.toString();
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
