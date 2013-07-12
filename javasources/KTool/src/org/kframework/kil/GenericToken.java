package org.kframework.kil;

import org.kframework.kil.loader.Constants;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.StringUtil;
import org.w3c.dom.Element;

import aterm.ATermAppl;

import java.util.Map;
import java.util.HashMap;

/**
 * Generic class representing an (uninterpreted) token.
 */
public class GenericToken extends Token {
	/* Token cache */
	private static Map<GenericToken, GenericToken> tokenCache = new HashMap<GenericToken, GenericToken>();
	/* KApp cache */
	private static Map<GenericToken, KApp> kAppCache = new HashMap<GenericToken, KApp>();

	/**
	 * Returns a {@link GenericToken} of the given sort with the given value.
	 * 
	 * @param sort
	 *            different than #Bool, #Int, or #String
	 * @param value
	 * @return
	 */
	public static GenericToken of(String sort, String value) {
		GenericToken genericToken = new GenericToken(sort, value);
		GenericToken cachedGenericToken = tokenCache.get(genericToken);
		if (cachedGenericToken == null) {
			cachedGenericToken = genericToken;
			tokenCache.put(genericToken, cachedGenericToken);
		}
		return cachedGenericToken;
	}

	/**
	 * Returns a {@link KApp} representing a {@link GenericToken} of the given sort with the given value applied to an empty {@link KList}.
	 * 
	 * @param sort
	 *            different than #Bool, #Int, or #String
	 * @param value
	 * @return
	 */
	public static KApp kAppOf(String sort, String value) {
		GenericToken genericToken = new GenericToken(sort, value);
		KApp kApp = kAppCache.get(genericToken);
		if (kApp == null) {
			kApp = KApp.of(genericToken);
			kAppCache.put(genericToken, kApp);
		}
		return kApp;
	}

	private final String tokenSort;
	private final String value;

	private GenericToken(String sort, String value) {
		this.tokenSort = sort;
		this.value = value;
	}

	protected GenericToken(Element element) {
		super(element);
		this.tokenSort = element.getAttribute(Constants.SORT_sort_ATTR);
		this.value = element.getAttribute(Constants.VALUE_value_ATTR);
	}

	protected GenericToken(ATermAppl atm) {
		super(atm);
		this.tokenSort = StringUtil.getSortNameFromCons(atm.getName());
		this.value = ((ATermAppl) atm.getArgument(0)).getName();
	}

	/**
	 * Returns a {@link String} representing the sort of the token.
	 * 
	 * @return
	 */
	@Override
	public String tokenSort() {
		return tokenSort;
	}

	/**
	 * Returns a {@link String} representing the (uninterpreted) value of the token.
	 * 
	 * @return
	 */
	@Override
	public String value() {
		return value;
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
